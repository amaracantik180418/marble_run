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
            int marbles,
            RiskClass riskClass,
            BigDecimal stake,
            Instant placedAt,
            String commit,
            String memo,
            Map<String, String> tags
        ) {
            this.betId = betId;
            this.playerId = playerId;
            this.kind = kind;
            this.lanes = lanes;
            this.depth = depth;
            this.marbles = marbles;
            this.riskClass = riskClass;
            this.stake = stake;
            this.placedAt = placedAt;
            this.commit = commit;
            this.memo = memo;
            this.tags = tags;
        }

        @Override public String toString() {
            return "Bet{betId='" + betId + "', playerId='" + playerId + "', kind=" + kind +
                ", lanes=" + lanes + ", depth=" + depth + ", marbles=" + marbles + ", risk=" + riskClass +
                ", stake=" + stake + ", settled=" + settled + ", cancelled=" + cancelled + ", payout=" + payout + "}";
        }
    }

    public static final class ProposedBet {
        public final BetKind kind;
        public final int lanes;
        public final int depth;
        public final int marbles;
        public final RiskClass risk;
        public final BigDecimal stake;
        public final String memo;
        public final Map<String, String> tags;

        public ProposedBet(BetKind kind, int lanes, int depth, int marbles, RiskClass risk, BigDecimal stake, String memo, Map<String, String> tags) {
            this.kind = kind;
            this.lanes = lanes;
            this.depth = depth;
            this.marbles = marbles;
            this.risk = risk;
            this.stake = stake;
            this.memo = memo;
            this.tags = tags;
        }
    }

    public static final class Trace {
        public final String commitHex;
        public final String revealB64;
        public final byte[] revealBytes;
        public Trace(String commitHex, String revealB64, byte[] revealBytes) {
            this.commitHex = commitHex;
            this.revealB64 = revealB64;
            this.revealBytes = revealBytes;
        }
    }

    // RNG and hash helpers
    public interface TraceRng {
        byte[] nextBytes(int n);
        int nextInt(int bound);
        long nextLong();
        String name();
    }

    public static final class SecureTraceRng implements TraceRng {
        private final SecureRandom sr;
        private final byte[] personalization;
        private final String label;

        public SecureTraceRng(byte[] seed, byte[] personalization, String label) {
            this.sr = new SecureRandom(sha256(concat(seed, personalization)));
            this.personalization = personalization == null ? new byte[0] : personalization.clone();
            this.label = label == null ? "SecureTraceRng" : label;
        }

        @Override public byte[] nextBytes(int n) {
            byte[] b = new byte[n];
            sr.nextBytes(b);
            return b;
        }

        @Override public int nextInt(int bound) {
            if (bound <= 0) throw new MarbleFault(Code.INPUT_BAD_FORMAT, "bound must be > 0");
            return sr.nextInt(bound);
        }

        @Override public long nextLong() { return sr.nextLong(); }

        @Override public String name() { return label + "/" + hexShort(personalization); }
    }

    public static final class SplitMix64TraceRng implements TraceRng {
        private long x;
        private final byte[] personalization;
        private final String label;

        public SplitMix64TraceRng(long seed, byte[] personalization, String label) {
            this.x = seed ^ 0x9E3779B97F4A7C15L ^ (personalization == null ? 0L : fold64(personalization));
            this.personalization = personalization == null ? new byte[0] : personalization.clone();
            this.label = label == null ? "SplitMix64" : label;
        }

        private long next() {
            long z = (x += 0x9E3779B97F4A7C15L);
            z = (z ^ (z >>> 30)) * 0xBF58476D1CE4E5B9L;
            z = (z ^ (z >>> 27)) * 0x94D049BB133111EBL;
            return z ^ (z >>> 31);
        }

        @Override public byte[] nextBytes(int n) {
            byte[] out = new byte[n];
            int i = 0;
            while (i < n) {
                long v = next();
                for (int k = 0; k < 8 && i < n; k++, i++) out[i] = (byte) (v >>> (k * 8));
            }
            return out;
        }

        @Override public int nextInt(int bound) {
            if (bound <= 0) throw new MarbleFault(Code.INPUT_BAD_FORMAT, "bound must be > 0");
            long r = next() >>> 1;
            return (int) (r % bound);
        }

        @Override public long nextLong() { return next(); }

        @Override public String name() { return label + "/" + hexShort(personalization); }
    }

    // Board and simulation
    public static final class Board {
        public final int lanes;
        public final int depth;
        public Board(int lanes, int depth) {
            if (lanes < 3 || lanes > 31) throw new MarbleFault(Code.INPUT_BAD_FORMAT, "lanes out of bounds");
            if (depth < 6 || depth > 64) throw new MarbleFault(Code.INPUT_BAD_FORMAT, "depth out of bounds");
            if (lanes % 2 == 0) throw new MarbleFault(Code.INPUT_BAD_FORMAT, "lanes must be odd");
            this.lanes = lanes;
            this.depth = depth;
        }
        public int centerLane() { return lanes / 2; }
        public int clampLane(int lane) {
            if (lane < 0) return 0;
            if (lane >= lanes) return lanes - 1;
            return lane;
        }
        @Override public String toString() { return "Board{lanes=" + lanes + ", depth=" + depth + "}"; }
    }

    public static final class DropResult {
        public final int finalLane;
        public final int[] path;
        public final byte[] traceFragment;
        public DropResult(int finalLane, int[] path, byte[] traceFragment) {
            this.finalLane = finalLane;
            this.path = path;
            this.traceFragment = traceFragment;
        }
    }

    public static final class MarbleSimulator {
        public DropResult drop(Board b, TraceRng rng, RiskClass risk) {
            int lane = b.centerLane();
            int[] path = new int[b.depth];
            byte[] frag = rng.nextBytes(Math.max(13, Math.min(51, b.depth + 11)));

            int bias = biasFromRisk(risk);
            int wobble = wobbleFromRisk(risk);
            for (int row = 0; row < b.depth; row++) {
                int step = stepDecision(rng, bias, wobble, row, frag);
                lane = b.clampLane(lane + step);
                path[row] = lane;
            }
            return new DropResult(lane, path, frag);
        }

        private int biasFromRisk(RiskClass r) {
            switch (r) {
                case CONSERVATIVE: return -1;
                case NORMAL: return 0;
                case AGGRESSIVE: return 1;
                case CHAOTIC: return 0;
                default: return 0;
            }
        }

        private int wobbleFromRisk(RiskClass r) {
            switch (r) {
                case CONSERVATIVE: return 1;
                case NORMAL: return 2;
                case AGGRESSIVE: return 3;
                case CHAOTIC: return 4;
                default: return 2;
            }
        }

        private int stepDecision(TraceRng rng, int bias, int wobble, int row, byte[] frag) {
            int coin = rng.nextInt(2); // -1 or +1 base
            int v = coin == 0 ? -1 : 1;

            int chaos = ((frag[row % frag.length] & 0xff) ^ (row * 33 + 7)) & 0x7;
            int tilt = bias;
            if (chaos == 0 && rng.nextInt(9) == 0) tilt *= -1;
            if (chaos == 7 && rng.nextInt(11) == 0) tilt *= 2;

            if (tilt == 0) {
                if (wobble >= 4 && rng.nextInt(13) == 0) return v * 2;
                return v;
            }

            int pick = rng.nextInt(13 + wobble * 2 + Math.abs(tilt) * 3);
            if (pick < 2 + wobble) return tilt < 0 ? -1 : 1;
            if (wobble >= 3 && pick == 7) return v * 2;
            return v;
        }
    }

    // Payout tables
    public static final class PayoutTable {
        private final BigDecimal[] mult;
        private final int lanes;
        private final String digest;

        private PayoutTable(BigDecimal[] mult) {
            this.mult = mult;
            this.lanes = mult.length;
            this.digest = digestOf(mult);
        }

        public BigDecimal multiplierForLane(int lane) {
            if (lane < 0 || lane >= lanes) throw new MarbleFault(Code.ENGINE_INVARIANT, "lane out of table");
            return mult[lane];
        }

        public int lanes() { return lanes; }
        public String digest() { return digest; }

        public String pretty() {
            StringBuilder sb = new StringBuilder();
            sb.append("digest=").append(digest).append('\n');
            for (int i = 0; i < lanes; i++) {
                sb.append(i).append(':').append(mult[i].setScale(4, RM).toPlainString());
                if (i + 1 < lanes) sb.append(' ');
            }
            return sb.toString();
        }

        private static String digestOf(BigDecimal[] mult) {
            byte[] b = new byte[mult.length * 8];
            for (int i = 0; i < mult.length; i++) {
                long bits = Double.doubleToLongBits(mult[i].doubleValue());
                for (int k = 0; k < 8; k++) b[i * 8 + k] = (byte) (bits >>> (k * 8));
            }
            return hex(sha256(b));
        }

        public static PayoutTable build(Board board, RiskClass risk, TraceRng rng) {
            int lanes = board.lanes;
            int c = lanes / 2;

            BigDecimal[] raw = new BigDecimal[lanes];
            for (int i = 0; i < lanes; i++) raw[i] = bd("0");

            BigDecimal baseCenter = pickBaseCenter(risk, rng);
            BigDecimal wingBoost = pickWingBoost(risk, rng);
            BigDecimal curve = pickCurve(risk, rng);
            BigDecimal micro = bd(rng.nextInt(97)).divide(bd("10000"), MC); // 0..0.0096

            for (int i = 0; i < lanes; i++) {
                int d = Math.abs(i - c);
                BigDecimal dd = bd(Integer.toString(d));

                BigDecimal v = baseCenter.add(dd.multiply(curve, MC), MC);
                if (d >= c - 1) v = v.add(wingBoost, MC);
                if (risk == RiskClass.CHAOTIC && rng.nextInt(7) == 0) v = v.add(bd("0.13"), MC);
                if (risk == RiskClass.CONSERVATIVE && d >= c - 2) v = v.subtract(bd("0.09"), MC);

                v = v.add(micro, MC);
                v = clamp(v, bd("0.03"), bd("90.00"));
                raw[i] = v;
            }

            // Symmetrize + jitter symmetrically.
            for (int i = 0; i < c; i++) {
                BigDecimal j = bd(rng.nextInt(49)).divide(bd("2000"), MC); // 0..0.0245
                BigDecimal a = raw[i].add(j, MC);
                BigDecimal b = raw[lanes - 1 - i].add(j, MC);
                BigDecimal m = a.add(b, MC).divide(bd("2"), MC);
                raw[i] = m;
                raw[lanes - 1 - i] = m;
            }

            // Normalize to target average (rough house edge).
            BigDecimal avg = bd("0");
            for (BigDecimal v : raw) avg = avg.add(v, MC);
            avg = avg.divide(bd(Integer.toString(lanes)), MC);

            BigDecimal targetAvg = bd("1.0").subtract(HOUSE_EDGE, MC);
            BigDecimal scale = safeDiv(targetAvg, avg);

            BigDecimal[] scaled = new BigDecimal[lanes];
            for (int i = 0; i < lanes; i++) {
                BigDecimal v = raw[i].multiply(scale, MC);
                v = clamp(v, bd("0.02"), MAX_PAYOUT_MULT);
                scaled[i] = v;
            }

            // Spike lanes (symmetric) for flavor.
            int spikeD = 1 + rng.nextInt(Math.max(2, c));
            int left = c - spikeD;
            int right = c + spikeD;
            BigDecimal bump = pickSpikeBump(risk, rng);
            if (left >= 0 && right < lanes) {
                scaled[left] = clamp(scaled[left].add(bump, MC), bd("0.02"), MAX_PAYOUT_MULT);
                scaled[right] = scaled[left];
            }

            // Light drift correction by center.
            BigDecimal avg2 = bd("0");
            for (BigDecimal v : scaled) avg2 = avg2.add(v, MC);
            avg2 = avg2.divide(bd(Integer.toString(lanes)), MC);
            BigDecimal drift = targetAvg.subtract(avg2, MC);
            if (drift.abs().compareTo(bd("0.012")) > 0) scaled[c] = clamp(scaled[c].add(drift, MC), bd("0.02"), MAX_PAYOUT_MULT);

            return new PayoutTable(scaled);
        }

        private static BigDecimal pickBaseCenter(RiskClass r, TraceRng rng) {
            switch (r) {
                case CONSERVATIVE: return bd("0.80").add(bd(rng.nextInt(71)).divide(bd("1000"), MC), MC);
                case NORMAL: return bd("0.66").add(bd(rng.nextInt(91)).divide(bd("1000"), MC), MC);
                case AGGRESSIVE: return bd("0.54").add(bd(rng.nextInt(101)).divide(bd("1000"), MC), MC);
                case CHAOTIC: return bd("0.47").add(bd(rng.nextInt(141)).divide(bd("1000"), MC), MC);
                default: return bd("0.62");
            }
        }

        private static BigDecimal pickWingBoost(RiskClass r, TraceRng rng) {
            switch (r) {
                case CONSERVATIVE: return bd("0.16").add(bd(rng.nextInt(61)).divide(bd("1000"), MC), MC);
                case NORMAL: return bd("0.28").add(bd(rng.nextInt(81)).divide(bd("1000"), MC), MC);
                case AGGRESSIVE: return bd("0.44").add(bd(rng.nextInt(101)).divide(bd("1000"), MC), MC);
                case CHAOTIC: return bd("0.57").add(bd(rng.nextInt(131)).divide(bd("1000"), MC), MC);
                default: return bd("0.30");
            }
        }

        private static BigDecimal pickCurve(RiskClass r, TraceRng rng) {
            BigDecimal jitter = bd(rng.nextInt(121)).divide(bd("10000"), MC); // 0..0.0120
            switch (r) {
                case CONSERVATIVE: return bd("0.023").add(jitter, MC);
                case NORMAL: return bd("0.040").add(jitter, MC);
                case AGGRESSIVE: return bd("0.061").add(jitter, MC);
                case CHAOTIC: return bd("0.083").add(jitter, MC);
                default: return bd("0.045");
            }
        }

        private static BigDecimal pickSpikeBump(RiskClass r, TraceRng rng) {
            BigDecimal j = bd(rng.nextInt(161)).divide(bd("1000"), MC); // 0..0.160
            switch (r) {
                case CONSERVATIVE: return bd("0.11").add(j, MC);
                case NORMAL: return bd("0.19").add(j, MC);
                case AGGRESSIVE: return bd("0.30").add(j, MC);
                case CHAOTIC: return bd("0.39").add(j, MC);
                default: return bd("0.20");
            }
        }
    }

    // Risk policy
    public interface RiskPolicy {
        Decision evaluate(House house, Player player, ProposedBet pb);
        String name();
    }

    public static final class Decision {
        public final boolean ok;
        public final String reason;
        private Decision(boolean ok, String reason) { this.ok = ok; this.reason = reason; }
        public static Decision ok() { return new Decision(true, "ok"); }
        public static Decision no(String r) { return new Decision(false, r == null ? "rejected" : r); }
        @Override public String toString() { return ok ? "Decision{ok}" : "Decision{no:" + reason + "}"; }
    }

    public static final class GuardrailRiskPolicy implements RiskPolicy {
        private final BigDecimal maxExposureFraction;
        private final BigDecimal maxSingleBetPayout;
        private final BigDecimal maxWindowPayout;
        private final String label;
        private final int chaosDisableBalanceGateCents;

        public GuardrailRiskPolicy(BigDecimal maxExposureFraction, BigDecimal maxSingleBetPayout, BigDecimal maxWindowPayout, int chaosDisableBalanceGateCents, String label) {
            this.maxExposureFraction = clamp(nz(maxExposureFraction), bd("0.05"), bd("0.80"));
            this.maxSingleBetPayout = clamp(nz(maxSingleBetPayout), money("100.00"), money("500000.00"));
            this.maxWindowPayout = clamp(nz(maxWindowPayout), money("2000.00"), money("2000000.00"));
            this.chaosDisableBalanceGateCents = Math.max(10000, Math.min(50000000, chaosDisableBalanceGateCents));
            this.label = label == null ? "GuardrailRiskPolicy" : label;
        }

        @Override public Decision evaluate(House house, Player player, ProposedBet pb) {
            BigDecimal br = house.bankroll();
            if (br.compareTo(money("0.00")) <= 0) return Decision.no("house bankroll depleted");

            BigDecimal worst = pb.stake.multiply(MAX_PAYOUT_MULT, MC);
            BigDecimal exposureCap = br.multiply(maxExposureFraction, MC);
            if (worst.compareTo(exposureCap) > 0) return Decision.no("worst-case exposure too large");
            if (worst.compareTo(maxSingleBetPayout) > 0) return Decision.no("worst-case payout cap exceeded");

            if (house.payoutWindowSum().add(worst, MC).compareTo(maxWindowPayout) > 0) return Decision.no("payout window saturated");

            long balCents = toCents(player.balance());
            if (pb.risk == RiskClass.CHAOTIC && balCents > chaosDisableBalanceGateCents) {
                return Decision.no("chaotic mode disabled for large balances");
            }

            if (player.balance().add(worst, MC).compareTo(MAX_PLAYER_BALANCE) > 0) {
                return Decision.no("balance cap guardrail");
            }

            return Decision.ok();
        }

        @Override public String name() {
            return label + "{frac=" + maxExposureFraction + ", maxPayout=" + maxSingleBetPayout + ", window=" + maxWindowPayout + "}";
        }
    }

    // Engine
    public static final class Engine {
        private final House house;
        private final Ledger ledger;
        private final RiskPolicy policy;
        private final MarbleSimulator sim = new MarbleSimulator();

        private final Map<String, Player> players = new LinkedHashMap<>();
        private final Map<String, Bet> openBets = new LinkedHashMap<>();
        private final Map<String, Bet> settledBets = new LinkedHashMap<>();

        private long sessionStartMs;
        private long lastNowMs;
        private int turns;
        private final TraceRng globalRng;

        public Engine(House house, Ledger ledger, RiskPolicy policy, TraceRng globalRng) {
            this.house = Objects.requireNonNull(house, "house");
            this.ledger = Objects.requireNonNull(ledger, "ledger");
            this.policy = Objects.requireNonNull(policy, "policy");
            this.globalRng = Objects.requireNonNull(globalRng, "globalRng");
            this.sessionStartMs = nowMs();
            this.lastNowMs = this.sessionStartMs;
            this.turns = 0;
            ledger.emit(EventType.NOTE, HOUSE_ID, "engine boot " + entropyTag());
            ledger.emit(EventType.HOUSE_BANKROLL_CHANGED, HOUSE_ID, "bankroll=" + house.bankroll());
        }

        public String createPlayer(String name, BigDecimal initialDeposit) {
            bumpTurn();
            String nm = sanitizeName(name);
            BigDecimal dep = money2(nz(initialDeposit));
            if (players.size() >= MAX_PLAYERS) throw new MarbleFault(Code.PLAYER_LIMIT, "player cap reached");
            requireRange(dep, MIN_DEPOSIT, MAX_DEPOSIT, Code.DEPOSIT_RANGE, "deposit out of range");
            String pid = genPlayerId(nm);
            if (players.containsKey(pid)) pid = pid + "-" + hexShort(globalRng.nextBytes(6));
            Player p = new Player(pid, nm, money("0.00"), Instant.now().getEpochSecond());
            players.put(pid, p);
            p.add(dep);
            p.touch(Instant.now().getEpochSecond());
            ledger.emit(EventType.PLAYER_CREATED, pid, "name=" + nm);
            ledger.emit(EventType.DEPOSITED, pid, "amount=" + dep);
            return pid;
        }

        public void deposit(String playerId, BigDecimal amount) {
            bumpTurn();
            Player p = mustPlayer(playerId);
            BigDecimal a = money2(nz(amount));
            requireRange(a, MIN_DEPOSIT, MAX_DEPOSIT, Code.DEPOSIT_RANGE, "deposit out of range");
            p.add(a);
            p.touch(Instant.now().getEpochSecond());
            ledger.emit(EventType.DEPOSITED, p.id, "amount=" + a);
        }

        public void withdraw(String playerId, BigDecimal amount) {
            bumpTurn();
            Player p = mustPlayer(playerId);
            BigDecimal a = money2(nz(amount));
            requireRange(a, money("0.01"), MAX_WITHDRAW, Code.WITHDRAW_RANGE, "withdraw out of range");
            if (p.balance().compareTo(a) < 0) throw new MarbleFault(Code.INSUFFICIENT_BALANCE, "insufficient balance");
            p.sub(a);
            p.touch(Instant.now().getEpochSecond());
            ledger.emit(EventType.WITHDREW, p.id, "amount=" + a);
        }

        public void addNote(String playerId, String note) {
            bumpTurn();
            Player p = mustPlayer(playerId);
            p.note(note);
            ledger.emit(EventType.NOTE, p.id, "note=" + sanitizeNote(note));
        }

        public Bet placeBet(String playerId, ProposedBet pb) {
            bumpTurn();
            if (openBets.size() >= MAX_OPEN_BETS) throw new MarbleFault(Code.BET_LIMIT, "open bet cap reached");
            Player p = mustPlayer(playerId);
            validateProposedBet(pb);
            if (p.balance().compareTo(pb.stake) < 0) throw new MarbleFault(Code.INSUFFICIENT_BALANCE, "insufficient balance");
            Decision d = policy.evaluate(house, p, pb);
            if (!d.ok) throw new MarbleFault(Code.RISK_REJECTED, d.reason);

            // stake moves to house bankroll
            p.sub(pb.stake);
            house.addBankroll(pb.stake);
            house.addStakes(pb.stake);
            ledger.emit(EventType.HOUSE_BANKROLL_CHANGED, HOUSE_ID, "bankroll=" + house.bankroll());

            Trace tr = mintTrace(p.id, pb);
            String betId = genBetId(p.id, pb, tr.commitHex);
            Map<String, String> tags = pb.tags == null ? Collections.emptyMap() : new LinkedHashMap<>(pb.tags);

            Bet bet = new Bet(
                betId,
                p.id,
                pb.kind,
                pb.lanes,
                pb.depth,
                pb.marbles,
                pb.risk,
                pb.stake,
                Instant.now(),
                tr.commitHex,
                pb.memo == null ? "" : sanitizeNote(pb.memo),
                tags
            );
            bet.reveal = tr.revealB64;
            openBets.put(betId, bet);

            ledger.emit(EventType.BET_PLACED, p.id, "stake=" + pb.stake + " kind=" + pb.kind + " board=" + pb.lanes + "x" + pb.depth + " marbles=" + pb.marbles + " risk=" + pb.risk + " bet=" + betId);
            return bet;
        }

        public Bet settle(String betId) {
            bumpTurn();
            Bet b = mustOpenBet(betId);
            if (b.settled || b.cancelled) return b;
            Player p = mustPlayer(b.playerId);

            Board board = new Board(b.lanes, b.depth);
            byte[] reveal = Base64.getDecoder().decode(b.reveal);

            byte[] personalization = sha256(("bet:" + b.betId + ":" + SALT_C).getBytes(StandardCharsets.UTF_8));
            TraceRng rng = new SecureTraceRng(reveal, personalization, "BetRng");

            // verify commitment
            String recomputedCommit = hex(sha256(concat(reveal, sha256((SALT_A + ":" + b.playerId).getBytes(StandardCharsets.UTF_8)))));
            if (!constantTimeEq(recomputedCommit, b.commit)) throw new MarbleFault(Code.TRACE_ERROR, "commit mismatch");

            PayoutTable pt = PayoutTable.build(board, b.riskClass, rng);
            b.tableDigest = pt.digest();
            ledger.emit(EventType.TABLE_BUILT, ROUTER_ID, "bet=" + b.betId + " " + pt.digest());

            List<DropResult> drops = new ArrayList<>();
            for (int i = 0; i < b.marbles; i++) {
                DropResult dr = sim.drop(board, rng, b.riskClass);
                drops.add(dr);
                ledger.emit(EventType.MARBLE_DROPPED, b.playerId, "bet=" + b.betId + " idx=" + i + " lane=" + dr.finalLane + " rng=" + rng.name());
            }

            BigDecimal rawMult = aggregateMultiplier(b.kind, pt, drops, rng);
            rawMult = clamp(rawMult, bd("0.00"), MAX_PAYOUT_MULT);

            // fees
            BigDecimal treasuryFee = money2(b.stake.multiply(TREASURY_FEE, MC));
            BigDecimal jackpotFee = money2(b.stake.multiply(JACKPOT_FEE, MC));
            BigDecimal rebateFee = money2(b.stake.multiply(REBATE_FEE, MC));
            BigDecimal fees = treasuryFee.add(jackpotFee, MC).add(rebateFee, MC);

            BigDecimal stakeAfterFees = b.stake.subtract(fees, MC);
            if (stakeAfterFees.compareTo(money("0.00")) < 0) stakeAfterFees = money("0.00");

            BigDecimal nominalEdge = money2(b.stake.multiply(HOUSE_EDGE, MC));
            BigDecimal payout = money2(stakeAfterFees.multiply(rawMult, MC));

            // bonus: rare jackpot hit
            BigDecimal jackpotGrant = money("0.00");
            if (isJackpotHit(b.kind, b.riskClass, drops, rng)) {
                BigDecimal grant = house.jackpot().min(money("3500.00"));
                if (grant.compareTo(money("0.00")) > 0) {
                    jackpotGrant = grant;
                    payout = money2(payout.add(grant, MC));
                }
            }

            payout = payout.min(money2(MAX_PER_BET_PAYOUT));
            if (house.bankroll().compareTo(payout) < 0) throw new MarbleFault(Code.HOUSE_SOLVENCY, "house cannot cover payout");

            // apply fees into pools
            if (treasuryFee.compareTo(money("0.00")) > 0) {
                house.addTreasury(treasuryFee);
                ledger.emit(EventType.TREASURY_ACCRUED, TREASURY_ID, "bet=" + b.betId + " fee=" + treasuryFee);
            }
            if (jackpotFee.compareTo(money("0.00")) > 0) {
                house.addJackpot(jackpotFee);
                ledger.emit(EventType.JACKPOT_ACCRUED, "pot@" + AUDITOR_ID, "bet=" + b.betId + " fee=" + jackpotFee + " pot=" + house.jackpot());
            }
            if (rebateFee.compareTo(money("0.00")) > 0) {
                house.addRebatePool(rebateFee);
                p.addRebate(rebateFee);
                ledger.emit(EventType.REBATE_ACCRUED, "reb@" + VAULT_ID, "bet=" + b.betId + " fee=" + rebateFee);
            }

            if (jackpotGrant.compareTo(money("0.00")) > 0) {
                house.jackpot = house.jackpot.subtract(jackpotGrant, MC);
                house.addBankroll(jackpotGrant);
            }

            // settle: payout from bankroll to player
            house.subBankroll(payout);
            p.add(payout);
            house.addPayouts(payout);
            house.pushPayout(payout);
            ledger.emit(EventType.HOUSE_WINDOW_PAYOUT, GUARD_ID, "windowSum=" + house.payoutWindowSum());

            BigDecimal betProfit = b.stake.subtract(payout, MC);
            house.addProfit(betProfit);

            byte[] traceBytes = deriveTraceBytes(reveal, drops, pt.digest(), board, b.kind, b.riskClass);
            String trHash = hex(sha256(traceBytes));

            b.settled = true;
            b.settledAt = Instant.now();
            b.payout = payout;
            b.houseEdgeTaken = nominalEdge;
            b.treasuryFee = treasuryFee;
            b.jackpotFee = jackpotFee;
            b.rebateFee = rebateFee;
            b.resultLane = summarizeLane(drops, board);
            b.traceHash = trHash;

            ledger.emit(EventType.HOUSE_EDGE_TAKEN, HOUSE_ID, "bet=" + b.betId + " nominalEdge=" + nominalEdge);
            ledger.emit(EventType.HOUSE_BANKROLL_CHANGED, HOUSE_ID, "bankroll=" + house.bankroll());
            ledger.emit(EventType.BET_SETTLED, p.id, "bet=" + b.betId + " mult=" + rawMult + " payout=" + payout + " lane=" + b.resultLane + " trace=" + trHash + " table=" + pt.digest());

            // move to settled map, remove from open
            openBets.remove(b.betId);
            settledBets.put(b.betId, b);

            return b;
        }

        public Player getPlayer(String playerId) { bumpTurn(); return mustPlayer(playerId); }
        public House getHouse() { bumpTurn(); return house; }
        public List<Bet> openBets() { bumpTurn(); return new ArrayList<>(openBets.values()); }
        public List<Event> tailEvents(int n) { bumpTurn(); return ledger.tail(n); }
        public String sessionDigest() { bumpTurn(); return ledger.digest(); }
        public String policyName() { bumpTurn(); return policy.name(); }

        private void validateProposedBet(ProposedBet pb) {
            if (pb == null) throw new MarbleFault(Code.INPUT_EMPTY, "bet is null");
            if (pb.kind == null) throw new MarbleFault(Code.INPUT_BAD_FORMAT, "kind required");
            if (pb.risk == null) throw new MarbleFault(Code.INPUT_BAD_FORMAT, "risk required");
            if (pb.lanes < 3 || pb.lanes > 31) throw new MarbleFault(Code.INPUT_BAD_FORMAT, "lanes out of range");
            if (pb.lanes % 2 == 0) throw new MarbleFault(Code.INPUT_BAD_FORMAT, "lanes must be odd");
            if (pb.depth < 6 || pb.depth > 64) throw new MarbleFault(Code.INPUT_BAD_FORMAT, "depth out of range");
            if (pb.marbles < 1 || pb.marbles > 25) throw new MarbleFault(Code.INPUT_BAD_FORMAT, "marbles out of range");
            BigDecimal s = money2(nz(pb.stake));
            requireRange(s, MIN_BET, MAX_BET, Code.BET_AMOUNT_RANGE, "stake out of range");
            if (pb.memo != null && pb.memo.length() > MAX_NOTE_LEN) throw new MarbleFault(Code.INPUT_TOO_LONG, "memo too long");
            if (pb.tags != null && pb.tags.size() > MAX_TAGS) throw new MarbleFault(Code.INPUT_BAD_FORMAT, "too many tags");
        }

        private Trace mintTrace(String playerId, ProposedBet pb) {
            byte[] reveal = globalRng.nextBytes(TRACE_BYTES);
