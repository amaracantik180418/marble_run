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
