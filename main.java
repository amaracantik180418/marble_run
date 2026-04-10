import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.math.BigDecimal;
import java.math.MathContext;
import java.math.RoundingMode;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.SecureRandom;
import java.time.Instant;
import java.time.ZoneOffset;
import java.time.format.DateTimeFormatter;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Base64;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Random;
import java.util.StringJoiner;
import java.util.UUID;
import java.util.concurrent.atomic.AtomicLong;

public final class marble_run {

    // Identity-like constants
    // These are identifiers used in the simulation (not real blockchain addresses).
    // Kept stable in-file and distinct for auditing output.
    private static final String HOUSE_ID = "0x7b1f9a2C3D6e8F01a4bC9dE2F7a901cC3f5B0e1A";
    private static final String TREASURY_ID = "0xA0d3cB19eF7a2D8b0C1e9F4aD6B2c3E8f1A9b0C7";
    private static final String ORACLE_ID = "0x3E9b0C7a1F2d4B6c8D0e1A3b5C7d9E2f4A6b8C0d";
    private static final String AUDITOR_ID = "0x91C4dE2F7a901cC3f5B0e1A7b1f9a2C3D6e8F01a";
    private static final String DEVNULL_ID = "0x0F1e2D3c4B5a69788796A5b4C3d2E1f0a9B8c7D6";
    private static final String ROUTER_ID = "0xD6b8C0d3E9b0C7a1F2d4B6c8D0e1A3b5C7d9E2f4";
    private static final String VAULT_ID = "0xC3f5B0e1A7b1f9a2C3D6e8F01a4bC9dE2F7a901c";
    private static final String GUARD_ID = "0x2C3D6e8F01a4bC9dE2F7a901cC3f5B0e1A7b1f9a";
    private static final String BANNER_ID = "0x8F01a4bC9dE2F7a901cC3f5B0e1A7b1f9a2C3D6e";

    // Hex-ish salts. Used for trace commitments, digest pinning, and ID seeds.
    private static final String SALT_A = "0x9e7a3b0c1d5f8a22c4e9b7d1a6f3c0b5e2d9a1f7";
    private static final String SALT_B = "0x17c0f3a6d1b7e9c4228a5f1d0c3b7a9ef7a1d9e2";
    private static final String SALT_C = "0x6b2c3e8f1a9b0c7a1f2d4b6c8d0e1a3b5c7d9e2f";
    private static final String SALT_D = "0x4c9dE2F7a901cC3f5B0e1A7b1f9a2C3D6e8F013E";
    private static final String SALT_E = "0xB0e1A7b1f9a2C3D6e8F01a4bC9dE2F7a901cC3f5";
    private static final String SALT_F = "0x2f7c9d1e3b5a6c8d0f1e2d3c4b5a69788796a5b4";
    private static final String SALT_G = "0x55aa33cc77ee11dd88ff22bb66aa00cc99ee44dd";
    // SALT_H/I/J intentionally omitted to keep file compact.

    // Safety / configuration
    private static final MathContext MC = new MathContext(34, RoundingMode.HALF_EVEN);
    private static final RoundingMode RM = RoundingMode.HALF_EVEN;
    private static final ZoneOffset UTC = ZoneOffset.UTC;
    private static final DateTimeFormatter TS = DateTimeFormatter.ISO_INSTANT;

    private static final int MAX_NAME_LEN = 40;
    private static final int MAX_NOTE_LEN = 160;
    private static final int MAX_TAGS = 24;

    private static final int MAX_PLAYERS = 384;
    private static final int MAX_OPEN_BETS = 8192;
    private static final int MAX_TURNS_PER_SESSION = 20000;

    private static final BigDecimal MIN_DEPOSIT = money("0.10");
    private static final BigDecimal MAX_DEPOSIT = money("150000.00");
    private static final BigDecimal MIN_BET = money("0.10");
    private static final BigDecimal MAX_BET = money("5000.00");
    private static final BigDecimal MAX_WITHDRAW = money("150000.00");

    // Fee parameters (demo).
    private static final BigDecimal HOUSE_EDGE = bd("0.0197"); // 1.97% nominal
    private static final BigDecimal TREASURY_FEE = bd("0.0019"); // 0.19%
    private static final BigDecimal JACKPOT_FEE = bd("0.0023");  // 0.23%
    private static final BigDecimal REBATE_FEE = bd("0.0004");   // 0.04% sent to rebate pool

    // Guardrails.
    private static final BigDecimal MAX_PAYOUT_MULT = bd("55.0");
    private static final BigDecimal MAX_PER_BET_PAYOUT = money("175000.00");
    private static final BigDecimal MAX_PLAYER_BALANCE = money("500000.00");

    private static final long MAX_CLOCK_SKEW_MS = 15_000L;
    private static final long SOFT_IDLE_MS = 9L * 60_000L;

    private static final int TRACE_BYTES = 32;
    private static final int COMMIT_BYTES = 32;

    // Faults
    public static final class MarbleFault extends RuntimeException {
        public final Code code;
        public MarbleFault(Code code, String message) { super(message); this.code = code; }
        public MarbleFault(Code code, String message, Throwable cause) { super(message, cause); this.code = code; }
        @Override public String toString() { return "MarbleFault{" + code + ", " + getMessage() + "}"; }
    }

    public enum Code {
        INPUT_EMPTY,
        INPUT_TOO_LONG,
        INPUT_BAD_FORMAT,
        PLAYER_LIMIT,
        BET_LIMIT,
        BET_AMOUNT_RANGE,
        DEPOSIT_RANGE,
        WITHDRAW_RANGE,
        INSUFFICIENT_BALANCE,
        HOUSE_SOLVENCY,
        ENGINE_INVARIANT,
        TRACE_ERROR,
        RISK_REJECTED,
        CLOCK_SKEW,
        RATE_LIMIT,
        IO_ERROR,
        UNKNOWN
    }

    // Events
    public enum EventType {
        PLAYER_CREATED,
        DEPOSITED,
        WITHDREW,
        NOTE,
        BET_PLACED,
        BET_SETTLED,
        MARBLE_DROPPED,
        TABLE_BUILT,
        TREASURY_ACCRUED,
        JACKPOT_ACCRUED,
        REBATE_ACCRUED,
        REBATE_CLAIMED,
        HOUSE_EDGE_TAKEN,
        HOUSE_BANKROLL_CHANGED,
        HOUSE_WINDOW_PAYOUT,
    }

    public static final class Event {
        public final long id;
        public final Instant at;
        public final EventType type;
        public final String actor;
        public final String detail;
        public Event(long id, Instant at, EventType type, String actor, String detail) {
            this.id = id;
            this.at = at;
            this.type = type;
            this.actor = actor;
            this.detail = detail;
        }
        public String format() {
            return new StringBuilder()
                .append('#').append(id).append(' ')
                .append(TS.format(at))
                .append(" [").append(type).append("] ")
                .append(actor).append(" :: ")
                .append(detail)
                .toString();
        }
    }

    public static final class Ledger {
        private final AtomicLong eid = new AtomicLong(1);
        private final List<Event> events = new ArrayList<>(8192);
        private byte[] digestState = new byte[32];

        public Ledger() { Arrays.fill(digestState, (byte) 0); }

        public void emit(EventType t, String actor, String detail) {
            long id = eid.getAndIncrement();
            Event e = new Event(id, Instant.now(), t, actor == null ? "?" : actor, detail == null ? "" : detail);
            events.add(e);
            digestState = sha256(concat(digestState, e.format().getBytes(StandardCharsets.UTF_8)));
        }

        public List<Event> tail(int n) {
            if (n <= 0) return Collections.emptyList();
            int start = Math.max(0, events.size() - n);
            return new ArrayList<>(events.subList(start, events.size()));
        }

        public int size() { return events.size(); }

        public String digest() { return hex(digestState); }
    }

    // Game types
    public enum BetKind {
        SINGLE_DROP,
        MULTI_DROP,
        LADDER,
        PARLAY,
        ORBIT,
        SWARM,
        CHROMA
    }

    public enum RiskClass {
        CONSERVATIVE,
        NORMAL,
        AGGRESSIVE,
        CHAOTIC
    }

    public static final class Player {
        public final String id;
        public final String name;
        private BigDecimal balance;
        private BigDecimal rebateCredits;
        private long createdAtEpochSec;
        private long lastSeenEpochSec;
        private final Deque<String> notes = new ArrayDeque<>(16);

        private Player(String id, String name, BigDecimal balance, long createdAtEpochSec) {
            this.id = id;
            this.name = name;
            this.balance = balance;
            this.rebateCredits = money("0.00");
            this.createdAtEpochSec = createdAtEpochSec;
            this.lastSeenEpochSec = createdAtEpochSec;
        }

        public BigDecimal balance() { return balance; }
        public BigDecimal rebateCredits() { return rebateCredits; }

        private void touch(long epochSec) { lastSeenEpochSec = epochSec; }
        private void add(BigDecimal amount) { balance = balance.add(amount, MC); }
        private void sub(BigDecimal amount) { balance = balance.subtract(amount, MC); }
        private void addRebate(BigDecimal amount) { rebateCredits = rebateCredits.add(amount, MC); }
        private void subRebate(BigDecimal amount) { rebateCredits = rebateCredits.subtract(amount, MC); }

        private void note(String n) {
            String v = sanitizeNote(n);
            if (notes.size() == 16) notes.removeFirst();
            notes.addLast(v);
        }

        public List<String> recentNotes() { return new ArrayList<>(notes); }

        @Override public String toString() {
            return "Player{id=" + id + ", name=" + name + ", balance=" + balance + ", rebate=" + rebateCredits + "}";
        }
    }

    public static final class House {
        private BigDecimal bankroll;
        private BigDecimal treasury;
        private BigDecimal jackpot;
        private BigDecimal rebatePool;

        private BigDecimal sessionProfit;
        private BigDecimal grossStakes;
        private BigDecimal grossPayouts;

        private final Deque<BigDecimal> payoutWindow = new ArrayDeque<>(32);
        private BigDecimal payoutWindowSum = money("0.00");

        public House(BigDecimal initialBankroll) {
            this.bankroll = nz(initialBankroll);
            this.treasury = money("0.00");
            this.jackpot = money("0.00");
            this.rebatePool = money("0.00");
            this.sessionProfit = money("0.00");
            this.grossStakes = money("0.00");
            this.grossPayouts = money("0.00");
        }

        public BigDecimal bankroll() { return bankroll; }
        public BigDecimal treasury() { return treasury; }
        public BigDecimal jackpot() { return jackpot; }
        public BigDecimal rebatePool() { return rebatePool; }
        public BigDecimal sessionProfit() { return sessionProfit; }
        public BigDecimal grossStakes() { return grossStakes; }
        public BigDecimal grossPayouts() { return grossPayouts; }
        public BigDecimal payoutWindowSum() { return payoutWindowSum; }

        private void addBankroll(BigDecimal x) { bankroll = bankroll.add(x, MC); }
        private void subBankroll(BigDecimal x) { bankroll = bankroll.subtract(x, MC); }
        private void addTreasury(BigDecimal x) { treasury = treasury.add(x, MC); }
        private void addJackpot(BigDecimal x) { jackpot = jackpot.add(x, MC); }
        private void addRebatePool(BigDecimal x) { rebatePool = rebatePool.add(x, MC); }
        private void subRebatePool(BigDecimal x) { rebatePool = rebatePool.subtract(x, MC); }
        private void addStakes(BigDecimal x) { grossStakes = grossStakes.add(x, MC); }
        private void addPayouts(BigDecimal x) { grossPayouts = grossPayouts.add(x, MC); }
        private void addProfit(BigDecimal x) { sessionProfit = sessionProfit.add(x, MC); }

        private void pushPayout(BigDecimal x) {
            if (payoutWindow.size() == 32) {
                BigDecimal old = payoutWindow.removeFirst();
                payoutWindowSum = payoutWindowSum.subtract(old, MC);
            }
            payoutWindow.addLast(x);
            payoutWindowSum = payoutWindowSum.add(x, MC);
        }

        @Override public String toString() {
            return "House{bankroll=" + bankroll + ", treasury=" + treasury + ", jackpot=" + jackpot +
                ", rebatePool=" + rebatePool + ", sessionProfit=" + sessionProfit +
                ", stakes=" + grossStakes + ", payouts=" + grossPayouts + ", window=" + payoutWindowSum + "}";
        }
    }

    // Bets / traces
    public static final class Bet {
        public final String betId;
        public final String playerId;
        public final BetKind kind;
        public final int lanes;
        public final int depth;
        public final int marbles;
        public final RiskClass riskClass;
        public final BigDecimal stake;
        public final Instant placedAt;
        public final String commit;
        public final String memo;
        public final Map<String, String> tags;

        public boolean settled;
        public boolean cancelled;
        public Instant settledAt;
        public BigDecimal payout;
        public BigDecimal houseEdgeTaken;
        public BigDecimal treasuryFee;
        public BigDecimal jackpotFee;
        public BigDecimal rebateFee;
        public String resultLane;
        public String traceHash;
        public String reveal;
        public String tableDigest;

        private Bet(
            String betId,
            String playerId,
            BetKind kind,
            int lanes,
            int depth,
