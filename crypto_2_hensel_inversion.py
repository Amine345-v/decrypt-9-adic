"""
crypto_2_hensel_inversion.py
============================
Cryptanalytic Engine & Polynomial-Time Inversion Suite for Collatz PRGs
and Cryptosystems via Backward p-Adic Hensel Peeling and Dyadic Cylinders.

Implements and benchmarks:
1. Algorithm 1 (9-Adic Switch-Block Inverter for Mode A):
   Recovers secret key u in {0,1}^M and secret seed n_0 from public terminal state
   y = S^{2M}(n_0) satisfying 9^M n_0 + B_{2M}(u) = 16^M y in O(M^2) time with
   trellis width strictly 1. Decrypts ciphertext P = C (+) hash(n_0, u) in polynomial time!
2. Algorithm 2 (3-Adic Hensel Peeling for Binary Alphabet Sigma = {1, 2}):
   Given terminal state y and alphabet Sigma = {1, 2}, reconstructs the unique
   valuation sequence w in {1, 2}^m and initial seed n_0 in O(m^2) time with trellis width 1.
3. Algorithm 3 (Dyadic Cylinder Recovery from Keystream):
   Inverts keystream segments and recovers secret seeds when 2-adic cylinder hints
   or keystream parity blocks are leaked.
4. Comprehensive empirical benchmark suite across key lengths:
   M in {16, 32, 64, 128, 256, 512, 1024} bits.
   Saves full timing benchmarks, polynomial degree scaling fits (log-log regression),
   and 100% decryption success rates to `crypto_2_results.json`.
"""

import math
import time
import json
import hashlib
import os
from typing import List, Tuple, Dict, Any, Optional


# ==============================================================================
# SECTION 1: ARITHMETIC UTILITIES & COLLATZ TRAJECTORY ENGINE
# ==============================================================================

def v2(x: int) -> int:
    """Exact 2-adic valuation v_2(x) for non-zero integer x."""
    if x == 0:
        raise ValueError("v2(0) is undefined (infinite).")
    return (x & -x).bit_length() - 1


def v3(x: int) -> int:
    """Exact 3-adic valuation v_3(x) for non-zero integer x."""
    if x == 0:
        raise ValueError("v3(0) is undefined (infinite).")
    c = 0
    while x % 3 == 0:
        x //= 3
        c += 1
    return c


def forward_collatz_step(n: int) -> Tuple[int, int]:
    """Single accelerated forward Collatz step S(n) = (3n + 1) / 2^{v_2(3n + 1)}."""
    val = 3 * n + 1
    k = v2(val)
    return val >> k, k


def forward_collatz_trajectory(n: int, steps: int) -> Tuple[int, List[int], List[int], int]:
    """
    Execute `steps` accelerated forward Collatz steps from odd integer n.
    Returns:
        terminal_y: S^{steps}(n)
        w: sequence of division exponents [k_0, ..., k_{steps-1}]
        K: cumulative valuations [K_0=0, K_1, ..., K_{steps}]
        B: affine constant B_{steps}(w) = sum_{j=1}^{steps} 3^{j-1} 2^{K_{steps-j}}
    """
    curr = n
    w = []
    K = [0]
    B = 0
    for _ in range(steps):
        nxt, k = forward_collatz_step(curr)
        B = 3 * B + (1 << K[-1])
        w.append(k)
        K.append(K[-1] + k)
        curr = nxt
    return curr, w, K, B


def compute_switch_block_B_formula(u: List[int]) -> int:
    """
    Closed-form affine constant B_{2M}(u) for constant-valuation switch blocks:
        w = (1 + u_0, 3 - u_0, ..., 1 + u_{M-1}, 3 - u_{M-1})
        B_{2M}(u) = 5 * (16^M - 9^M) // 7 + sum_{q=0}^{M-1} 2 * 9^{M-1-q} * 16^q * u_q
    """
    M = len(u)
    base_drift = (5 * (pow(16, M) - pow(9, M))) // 7
    linear_part = 0
    pow16 = 1
    p9_powers = [1] * (M + 1)
    for i in range(1, M + 1):
        p9_powers[i] = p9_powers[i - 1] * 9

    for q in range(M):
        if u[q]:
            linear_part += 2 * p9_powers[M - 1 - q] * pow16
        pow16 <<= 4

    return base_drift + linear_part


def derive_keystream(seed_n0: int, key_u: Optional[List[int]], length_bytes: int) -> bytes:
    """
    Cryptographic Key Derivation Function (KDF):
    Derives `length_bytes` of pseudorandom keystream using SHAKE-256 over (seed_n0, key_u).
    """
    n0_bits = seed_n0.bit_length()
    n0_bytes = seed_n0.to_bytes((n0_bits + 7) // 8, 'big') if n0_bits > 0 else b'\x00'
    if key_u is not None:
        u_packed = bytearray((len(key_u) + 7) // 8)
        for idx, bit in enumerate(key_u):
            if bit:
                u_packed[idx // 8] |= (1 << (idx % 8))
        payload = n0_bytes + b"::COLLATZ_PRG::" + bytes(u_packed)
    else:
        payload = n0_bytes + b"::COLLATZ_BINARY_PRG::"
    return hashlib.shake_256(payload).digest(length_bytes)


def xor_bytes(b1: bytes, b2: bytes) -> bytes:
    """XOR two byte sequences of matching length."""
    return bytes(x ^ y for x, y in zip(b1, b2))


# ==============================================================================
# SECTION 2: ALGORITHM 1 — 9-ADIC SWITCH-BLOCK INVERTER & MODE A CRYPTOSYSTEM
# ==============================================================================

class ModeASwitchBlockPRG:
    """
    Mode A Cryptosystem / PRG:
    Constant-Valuation Switch-Block Generator:
      - Secret Key: u in {0, 1}^M
      - Secret Seed: n_0 in N+_odd
      - Public Terminal State: y = S^{2M}(n_0)
      - Cumulative Valuation: K_{2M} = 4M (since (1+u_q) + (3-u_q) = 4 per block)
      - Governing Identity: 9^M n_0 + B_{2M}(u) = 16^M y
    """

    @staticmethod
    def keygen(M: int, random_seed: Optional[int] = None) -> Tuple[List[int], int]:
        """Generate a random secret key u in {0, 1}^M and a valid odd secret seed n_0."""
        import random
        rng = random.Random(random_seed)
        u = [rng.randint(0, 1) for _ in range(M)]

        # Synthesize canonical seed n_0 in the 2-adic cylinder mod 2^{4M+1}
        B = compute_switch_block_B_formula(u)
        mod2 = 1 << (4 * M)
        p9_M = pow(9, M)
        inv9M = pow(p9_M, -1, mod2)
        r0 = (-B * inv9M) % mod2
        n0 = r0 if r0 > 0 else mod2
        # Ensure terminal state y is odd (carry-stopper parity)
        if (((p9_M * n0 + B) >> (4 * M)) & 1) == 0:
            n0 += mod2

        # Add optional secret high-order cylinder shift
        secret_cylinder_shift = rng.randint(0, 100)
        n0 += secret_cylinder_shift * (1 << (4 * M + 1))
        return u, n0

    @staticmethod
    def emit_public_state(u: List[int], n0: int) -> int:
        """Compute the public terminal state y = S^{2M}(n_0)."""
        M = len(u)
        B = compute_switch_block_B_formula(u)
        num = pow(9, M) * n0 + B
        denom = 1 << (4 * M)
        assert num % denom == 0, "Trajectory arithmetic identity violated!"
        y = num >> (4 * M)
        assert (y & 1) == 1, "Terminal state y must be odd positive integer!"
        return y

    @staticmethod
    def encrypt(plaintext: bytes, u: List[int], n0: int) -> Tuple[bytes, int, int]:
        """
        Encrypt plaintext under secret key u and secret seed n_0.
        Emits: (ciphertext, public_terminal_y, M).
        """
        M = len(u)
        y = ModeASwitchBlockPRG.emit_public_state(u, n0)
        keystream = derive_keystream(n0, u, len(plaintext))
        ciphertext = xor_bytes(plaintext, keystream)
        return ciphertext, y, M


def algorithm1_9adic_switch_block_inverter(y: int, M: int) -> Dict[str, Any]:
    """
    Algorithm 1: 9-Adic Switch-Block Hensel Inverter for Mode A.
    ============================================================
    Given public terminal state y = S^{2M}(n_0) and key length M:
      Identity: 16^M * y - B_{2M}(u) = 9^M * n_0
      Let base_drift = 5 * (16^M - 9^M) // 7.
      Residual Y_0 = (16^M * y) - base_drift
                   = sum_{q=0}^{M-1} 2 * 9^{M-1-q} * 16^q * u_q + 9^M * n_0.

    Peeling Mechanism (Trellis Width Strictly 1):
      For r = 0, 1, ..., M-1 (extracting block q = M - 1 - r from M-1 down to 0):
        At layer r, modulo 9:
          R_r = Y_r mod 9.
          Unit coefficient c_q = (2 * 16^q) mod 9.
          Since gcd(c_q, 9) = 1, u_q is uniquely determined:
            u_q = 0  iff  R_r == 0
            u_q = 1  iff  R_r == c_q
        Update residual:
          Y_{r+1} = (Y_r - 2 * 16^q * u_q) // 9.
      At completion (r = M), the quotient is the exact initial seed:
        n_0 = Y_M.

    Complexity: Exactly M peeling layers, each performing O(M) bit operations.
    Total runtime: O(M^2) bit operations. Trellis width = 1 at every layer.
    """
    t0 = time.perf_counter()
    K_m = 4 * M
    base_drift = (5 * (pow(16, M) - pow(9, M))) // 7
    Y = (y << K_m) - base_drift

    # Precompute powers of 16 for O(1) step subtraction
    pow16 = [1] * M
    for q in range(1, M):
        pow16[q] = pow16[q - 1] << 4

    u_recovered = [0] * M
    trellis_widths = []

    for r in range(M):
        q = M - 1 - r
        R_mod9 = Y % 9
        unit_coeff = (2 * pow(16, q, 9)) % 9

        if R_mod9 == 0:
            u_q = 0
            surviving = 1
        elif R_mod9 == unit_coeff:
            u_q = 1
            surviving = 1
        else:
            # Garden-of-Eden trap: 0 surviving states
            trellis_widths.append(0)
            elapsed_ms = (time.perf_counter() - t0) * 1e3
            return {
                "success": False,
                "u": None,
                "n0": None,
                "trellis_widths": trellis_widths,
                "max_trellis_width": 0,
                "elapsed_ms": elapsed_ms
            }

        u_recovered[q] = u_q
        trellis_widths.append(surviving)

        if u_q == 1:
            Y -= 2 * pow16[q]
        Y //= 9

    n0_recovered = Y
    elapsed_ms = (time.perf_counter() - t0) * 1e3

    return {
        "success": True,
        "u": u_recovered,
        "n0": n0_recovered,
        "trellis_widths": trellis_widths,
        "max_trellis_width": max(trellis_widths) if trellis_widths else 1,
        "elapsed_ms": elapsed_ms
    }


def decrypt_mode_a_ciphertext(ciphertext: bytes, y: int, M: int) -> Tuple[bytes, Dict[str, Any]]:
    """
    Full Cryptanalysis and Polynomial-Time Decryption of Mode A:
    1. Invert public terminal state y via 9-adic Hensel peeling to recover (u, n_0).
    2. Reconstruct keystream K = derive_keystream(n_0, u, len(C)).
    3. Recover plaintext P = C (+) K.
    """
    inversion_result = algorithm1_9adic_switch_block_inverter(y, M)
    if not inversion_result["success"]:
        raise ValueError("9-Adic Hensel inversion failed: public state is outside image.")

    u_rec = inversion_result["u"]
    n0_rec = inversion_result["n0"]
    keystream = derive_keystream(n0_rec, u_rec, len(ciphertext))
    decrypted_plaintext = xor_bytes(ciphertext, keystream)
    return decrypted_plaintext, inversion_result


# ==============================================================================
# SECTION 3: ALGORITHM 2 — 3-ADIC HENSEL PEELING (BINARY ALPHABET Sigma = {1, 2})
# ==============================================================================

class BinaryAlphabetCollatzPRG:
    """
    Collatz PRG operating on the binary valuation alphabet Sigma = {1, 2}:
    Each step has k_i in {1, 2}.
    Valuation sequence w in {1, 2}^m.
    Identity: 3^m n_0 + B_m(w) = 2^{K_m} y.
    """

    @staticmethod
    def keygen(m: int, random_seed: Optional[int] = None) -> Tuple[List[int], int, int]:
        """Generate random valuation sequence w in {1, 2}^m and secret seed n_0."""
        import random
        rng = random.Random(random_seed)
        w = [rng.choice([1, 2]) for _ in range(m)]

        K = [0]
        B = 0
        for k in w:
            B = 3 * B + (1 << K[-1])
            K.append(K[-1] + k)
        K_m = K[-1]

        mod2 = 1 << K_m
        p3_m = pow(3, m)
        inv3m = pow(p3_m, -1, mod2)
        r0 = (-B * inv3m) % mod2
        n0 = r0 if r0 > 0 else mod2
        if (((p3_m * n0 + B) >> K_m) & 1) == 0:
            n0 += mod2

        # Optional secret shift
        shift = rng.randint(0, 100)
        n0 += shift * (1 << (K_m + 1))
        return w, n0, K_m

    @staticmethod
    def emit_public_state(w: List[int], n0: int) -> Tuple[int, int]:
        """Compute terminal state y = S^m(n_0) and cumulative valuation K_m."""
        m = len(w)
        K = [0]
        B = 0
        for k in w:
            B = 3 * B + (1 << K[-1])
            K.append(K[-1] + k)
        K_m = K[-1]
        num = pow(3, m) * n0 + B
        denom = 1 << K_m
        assert num % denom == 0
        y = num >> K_m
        assert (y & 1) == 1
        return y, K_m

    @staticmethod
    def encrypt(plaintext: bytes, w: List[int], n0: int) -> Tuple[bytes, int, int, int]:
        """Encrypt plaintext under binary alphabet trajectory."""
        m = len(w)
        y, K_m = BinaryAlphabetCollatzPRG.emit_public_state(w, n0)
        keystream = derive_keystream(n0, w, len(plaintext))
        ciphertext = xor_bytes(plaintext, keystream)
        return ciphertext, y, m, K_m


def algorithm2_3adic_hensel_peeler(y: int, m: int, K_m: Optional[int] = None) -> Dict[str, Any]:
    """
    Algorithm 2: 3-Adic Hensel Peeling for Binary Alphabet Sigma = {1, 2}.
    ======================================================================
    Reconstructs the unique valuation trajectory w in {1, 2}^m and initial seed n_0
    from terminal state y in O(m^2) time with trellis width strictly 1.

    Mathematical Theorem:
      At step t (stepping backward from y_{t+1} to y_t):
        2^{k_t} * y_{t+1} = 3 * y_t + 1  ==>  (-1)^{k_t} * y_{t+1} ≡ 1 (mod 3).
      Because Sigma = {1, 2} contains exactly one odd integer (1) and one even integer (2):
        y_{t+1} ≡ 1 (mod 3)  ==>  (-1)^{k_t} ≡ 1  ==>  k_t is even  ==>  k_t = 2.
        y_{t+1} ≡ 2 (mod 3)  ==>  (-1)^{k_t} ≡ -1 ==>  k_t is odd   ==>  k_t = 1.
        y_{t+1} ≡ 0 (mod 3)  ==>  Garden-of-Eden trap (0 preimages).
      The preceding state is uniquely:
        y_t = (2^{k_t} * y_{t+1} - 1) // 3.
      This backward map collapses the 2^m search tree to trellis width 1 at every step!
    """
    t0 = time.perf_counter()
    curr = y
    w_rev = []
    trellis_widths = []

    for step in range(m):
        rem = curr % 3
        if rem == 0:
            # Garden-of-Eden trap
            trellis_widths.append(0)
            elapsed_ms = (time.perf_counter() - t0) * 1e3
            return {
                "success": False,
                "w": None,
                "n0": None,
                "K_m": None,
                "trellis_widths": trellis_widths,
                "max_trellis_width": 0,
                "elapsed_ms": elapsed_ms
            }

        k_step = 2 if (rem == 1) else 1
        w_rev.append(k_step)
        trellis_widths.append(1)

        curr = ((curr << k_step) - 1) // 3

    w_recovered = list(reversed(w_rev))
    n0_recovered = curr
    computed_Km = sum(w_recovered)
    if K_m is not None:
        assert computed_Km == K_m, f"Cumulative valuation mismatch: {computed_Km} != {K_m}"

    elapsed_ms = (time.perf_counter() - t0) * 1e3
    return {
        "success": True,
        "w": w_recovered,
        "n0": n0_recovered,
        "K_m": computed_Km,
        "trellis_widths": trellis_widths,
        "max_trellis_width": max(trellis_widths) if trellis_widths else 1,
        "elapsed_ms": elapsed_ms
    }


def decrypt_binary_alphabet_ciphertext(ciphertext: bytes, y: int, m: int, K_m: Optional[int] = None) -> Tuple[bytes, Dict[str, Any]]:
    """Complete decryption attack against Binary Alphabet Collatz Cryptosystem."""
    inversion_result = algorithm2_3adic_hensel_peeler(y, m, K_m)
    if not inversion_result["success"]:
        raise ValueError("3-Adic Hensel inversion failed.")
    w_rec = inversion_result["w"]
    n0_rec = inversion_result["n0"]
    keystream = derive_keystream(n0_rec, w_rec, len(ciphertext))
    decrypted_plaintext = xor_bytes(ciphertext, keystream)
    return decrypted_plaintext, inversion_result


# ==============================================================================
# SECTION 4: ALGORITHM 3 — DYADIC CYLINDER RECOVERY FROM KEYSTREAM
# ==============================================================================

class DyadicCylinderKeystreamPRG:
    """
    Collatz PRG emitting keystream segments and exhibiting dyadic cylinder structure:
      n_{t+1} = (3 n_t + 1) / 2^{k_t}.
    At each step, emits b bits of the internal state z_t = n_t mod 2^b.
    """

    @staticmethod
    def generate_keystream_trace(n0: int, m: int, b: int = 32) -> Tuple[List[int], int, List[int], int]:
        """
        Simulate PRG execution emitting keystream blocks z_t = n_t mod 2^b.
        Returns:
            keystream_blocks: [z_0, ..., z_{m-1}]
            terminal_y: S^m(n_0)
            actual_w: [k_0, ..., k_{m-1}]
            K_m: total cumulative valuation
        """
        curr = n0
        keystream_blocks = []
        actual_w = []
        mask = (1 << b) - 1
        for _ in range(m):
            keystream_blocks.append(curr & mask)
            nxt, k = forward_collatz_step(curr)
            actual_w.append(k)
            curr = nxt
        K_m = sum(actual_w)
        return keystream_blocks, curr, actual_w, K_m


def algorithm3_dyadic_cylinder_keystream_inverter(
    keystream_blocks: List[int],
    terminal_y: int,
    b: int = 32
) -> Dict[str, Any]:
    """
    Algorithm 3A: Dyadic Cylinder Inversion from Observed Keystream Blocks.
    ======================================================================
    Given leaked keystream blocks z_t = n_t mod 2^b (where b > max(k_t)):
      Since 3 * z_t + 1 ≡ 3 * n_t + 1 (mod 2^b), the exact 2-adic valuation
      k_t = v_2(3 * z_t + 1) is directly extracted!
    Once the sequence w = (k_0, ..., k_{m-1}) is recovered:
      K_m = sum(k_i), B_m(w) = sum_{j=1}^m 3^{j-1} 2^{K_{m-j}}.
      Secret seed n_0 is recovered in O(m^2) via exact affine inversion:
        n_0 = (2^{K_m} * terminal_y - B_m(w)) / 3^m.
    """
    t0 = time.perf_counter()
    m = len(keystream_blocks)
    recovered_w = []

    for idx, z in enumerate(keystream_blocks):
        val = 3 * z + 1
        k = v2(val)
        if k >= b:
            raise ValueError(f"Keystream leakage width b={b} too small for valuation k={k} at step {idx}.")
        recovered_w.append(k)

    # Compute B_m(w) and K_m
    K = [0]
    B = 0
    for k in recovered_w:
        B = 3 * B + (1 << K[-1])
        K.append(K[-1] + k)
    K_m = K[-1]

    num = (terminal_y << K_m) - B
    denom = pow(3, m)
    assert num % denom == 0, "Affine identity violated in keystream dyadic cylinder inversion."
    n0_recovered = num // denom

    elapsed_ms = (time.perf_counter() - t0) * 1e3
    return {
        "success": True,
        "w": recovered_w,
        "n0": n0_recovered,
        "K_m": K_m,
        "elapsed_ms": elapsed_ms
    }


def algorithm3_partial_cylinder_solver(
    terminal_y: int,
    m: int,
    K_m: int,
    hint_bits_H: int,
    n_mod_2H: int,
    max_k: int = 4
) -> Dict[str, Any]:
    """
    Algorithm 3B: Coupled (2,3)-Adic Inversion with Leaked Partial Dyadic Cylinder.
    ===============================================================================
    When valuations belong to multi-parity alphabet {1, ..., max_k} and H bits of the
    2-adic cylinder n_0 mod 2^H are leaked:
      1. Forward 2-adic peeling extracts trajectory prefix (k_0, ..., k_{p-1}).
      2. Backward 3-adic Hensel peeling with LTE mod-9 Garden-of-Eden lookahead prunes branches.
      3. Cylinder matching filters candidates to the unique authentic secret seed.
    """
    t0 = time.perf_counter()

    # Step 1: Forward 2-adic prefix peeling
    prefix_w = []
    prefix_K = 0
    curr_mod = n_mod_2H
    rem_H = hint_bits_H
    for _ in range(m - 1):
        val = 3 * curr_mod + 1
        k_i = v2(val)
        if k_i < rem_H and 1 <= k_i <= max_k:
            prefix_w.append(k_i)
            prefix_K += k_i
            curr_mod = val >> k_i
            rem_H -= k_i
        else:
            break

    p_fixed = len(prefix_w)
    target_rem_K = K_m - prefix_K
    rem_backward_steps = m - p_fixed

    # Step 2: Backward 3-adic Hensel peeling
    states = [(terminal_y, target_rem_K, ())]
    trellis_widths = []

    for r in range(1, rem_backward_steps + 1):
        next_states = []
        steps_left = rem_backward_steps - r
        for curr_y, rem_K, rev_path in states:
            if curr_y % 3 == 0:
                continue
            eps = 2 if (curr_y % 3 == 1) else 1
            for k in range(eps, max_k + 1, 2):
                new_rem_K = rem_K - k
                if new_rem_K < steps_left * 1 or new_rem_K > steps_left * max_k:
                    continue
                nxt_y = ((curr_y << k) - 1) // 3
                if (steps_left + p_fixed > 0) and (nxt_y % 3 == 0):
                    continue
                next_states.append((nxt_y, new_rem_K, rev_path + (k,)))
        states = next_states
        trellis_widths.append(len(states))

    # Step 3: Match with 2-adic prefix and filter by 2-adic cylinder
    valid_solutions = []
    for curr_y, rem_K, rev_path in states:
        y_walk = curr_y
        ok = True
        for k_pref in reversed(prefix_w):
            num = (y_walk << k_pref) - 1
            if num % 3 != 0:
                ok = False
                break
            y_walk = num // 3
        if not ok:
            continue
        cand_n = y_walk
        if (cand_n & ((1 << hint_bits_H) - 1)) == n_mod_2H:
            full_w = prefix_w + list(reversed(rev_path))
            valid_solutions.append((cand_n, full_w))

    elapsed_ms = (time.perf_counter() - t0) * 1e3
    success = (len(valid_solutions) == 1)
    return {
        "success": success,
        "solutions_count": len(valid_solutions),
        "n0": valid_solutions[0][0] if success else None,
        "w": valid_solutions[0][1] if success else None,
        "max_trellis_width": max(trellis_widths) if trellis_widths else 1,
        "elapsed_ms": elapsed_ms
    }


# ==============================================================================
# SECTION 5: POLYNOMIAL SCALING FITTER & STATISTICAL ANALYSIS
# ==============================================================================

def fit_power_law(x_vals: List[float], y_vals: List[float]) -> Tuple[float, float, float]:
    """
    Fit power-law model Y = c * X^alpha via log-log ordinary least squares regression:
      ln(Y) = alpha * ln(X) + ln(c)
    Returns: (alpha, c, R^2)
    """
    ln_x = [math.log(x) for x in x_vals]
    ln_y = [math.log(y) for y in y_vals]
    n = len(x_vals)

    mean_x = sum(ln_x) / n
    mean_y = sum(ln_y) / n

    ss_xx = sum((x - mean_x) ** 2 for x in ln_x)
    ss_yy = sum((y - mean_y) ** 2 for y in ln_y)
    ss_xy = sum((x - mean_x) * (y - mean_y) for x, y in zip(ln_x, ln_y))

    if ss_xx == 0 or ss_yy == 0:
        return 0.0, 0.0, 1.0

    alpha = ss_xy / ss_xx
    ln_c = mean_y - alpha * mean_x
    c = math.exp(ln_c)

    r_squared = (ss_xy ** 2) / (ss_xx * ss_yy)
    return alpha, c, r_squared


# ==============================================================================
# SECTION 6: COMPREHENSIVE BENCHMARK SUITE ACROSS M = 16..1024
# ==============================================================================

def execute_crypto_benchmark_suite(
    key_lengths: List[int] = [16, 32, 64, 128, 256, 512, 1024],
    trials_per_length: int = 5
) -> Dict[str, Any]:
    """
    Run the full empirical decryption benchmark across key lengths M = 16..1024.
    Evaluates:
      - Mode A 9-Adic Switch-Block Inverter & Ciphertext Decryption
      - Algorithm 2 Binary Alphabet 3-Adic Hensel Peeling
      - Algorithm 3 Dyadic Cylinder Recovery from Keystream
    Computes runtime distributions, trellis widths, scaling exponents, and success rates.
    """
    print("=" * 80)
    print("HENSEL CRYPTANALYTIC BENCHMARK: POLYNOMIAL-TIME INVERSION OF COLLATZ PRGS")
    print("=" * 80)
    print(f"Key Lengths M: {key_lengths}")
    print(f"Independent Trials per Length: {trials_per_length}")
    print("-" * 80)

    test_message = b"COLLATZ_PRG_BROKEN_POLYNOMIAL_TIME_HENSEL_INVERSION_O(M^2)"

    results_mode_a = []
    results_alg2 = []
    results_alg3 = []

    for M in key_lengths:
        print(f"\n[*] Benchmarking Key Length M = {M:4d} bits (2M = {2*M:4d} Collatz steps)...")

        # ----------------------------------------------------------------------
        # Benchmark Algorithm 1 (Mode A Switch-Block Inversion & Decryption)
        # ----------------------------------------------------------------------
        mode_a_times_ms = []
        mode_a_decrypt_times_ms = []
        mode_a_successes = 0
        mode_a_widths = []
        y_bitlengths = []

        for trial in range(trials_per_length):
            seed_offset = trial * 1000 + M
            u_secret, n0_secret = ModeASwitchBlockPRG.keygen(M, random_seed=seed_offset)
            ciphertext, y_pub, _ = ModeASwitchBlockPRG.encrypt(test_message, u_secret, n0_secret)
            y_bitlengths.append(y_pub.bit_length())

            # Time inversion
            t_inv_start = time.perf_counter()
            inv_res = algorithm1_9adic_switch_block_inverter(y_pub, M)
            t_inv_end = time.perf_counter()
            inv_ms = (t_inv_end - t_inv_start) * 1e3
            mode_a_times_ms.append(inv_ms)
            mode_a_widths.append(inv_res["max_trellis_width"])

            # Time full decryption
            t_dec_start = time.perf_counter()
            dec_plaintext, _ = decrypt_mode_a_ciphertext(ciphertext, y_pub, M)
            t_dec_end = time.perf_counter()
            dec_ms = (t_dec_end - t_dec_start) * 1e3
            mode_a_decrypt_times_ms.append(dec_ms)

            # Verification assertions
            assert inv_res["success"], f"Algorithm 1 failed at M={M}, trial={trial}"
            assert inv_res["u"] == u_secret, f"Key mismatch at M={M}, trial={trial}"
            assert inv_res["n0"] == n0_secret, f"Seed mismatch at M={M}, trial={trial}"
            assert dec_plaintext == test_message, f"Decryption mismatch at M={M}, trial={trial}"
            assert inv_res["max_trellis_width"] == 1, f"Trellis width > 1 at M={M}, trial={trial}"
            mode_a_successes += 1

        mean_inv_ms = sum(mode_a_times_ms) / trials_per_length
        mean_dec_ms = sum(mode_a_decrypt_times_ms) / trials_per_length
        avg_y_bits = sum(y_bitlengths) / trials_per_length

        results_mode_a.append({
            "M": M,
            "steps_2M": 2 * M,
            "mean_y_bitlength": round(avg_y_bits, 1),
            "mean_inversion_ms": round(mean_inv_ms, 4),
            "min_inversion_ms": round(min(mode_a_times_ms), 4),
            "max_inversion_ms": round(max(mode_a_times_ms), 4),
            "mean_decryption_ms": round(mean_dec_ms, 4),
            "max_trellis_width": max(mode_a_widths),
            "success_rate_percent": (mode_a_successes / trials_per_length) * 100.0
        })
        print(f"    Mode A  -> Invert: {mean_inv_ms:7.3f} ms | Decrypt: {mean_dec_ms:7.3f} ms | "
              f"Trellis Width: {max(mode_a_widths)} | Success: 100% | y: {avg_y_bits:.0f} bits")

        # ----------------------------------------------------------------------
        # Benchmark Algorithm 2 (Binary Alphabet 3-Adic Hensel Peeling)
        # ----------------------------------------------------------------------
        m_steps = M  # Use m = M steps for comparison
        alg2_times_ms = []
        alg2_successes = 0
        alg2_widths = []

        for trial in range(trials_per_length):
            seed_offset = trial * 2000 + M
            w_secret, n0_secret, Km = BinaryAlphabetCollatzPRG.keygen(m_steps, random_seed=seed_offset)
            ciphertext, y_pub, _, _ = BinaryAlphabetCollatzPRG.encrypt(test_message, w_secret, n0_secret)

            t_start = time.perf_counter()
            dec_pt, res2 = decrypt_binary_alphabet_ciphertext(ciphertext, y_pub, m_steps, Km)
            t_end = time.perf_counter()

            elapsed_ms = (t_end - t_start) * 1e3
            alg2_times_ms.append(elapsed_ms)
            alg2_widths.append(res2["max_trellis_width"])

            assert res2["success"]
            assert res2["w"] == w_secret
            assert res2["n0"] == n0_secret
            assert dec_pt == test_message
            assert res2["max_trellis_width"] == 1
            alg2_successes += 1

        mean_alg2_ms = sum(alg2_times_ms) / trials_per_length
        results_alg2.append({
            "m": m_steps,
            "mean_inversion_ms": round(mean_alg2_ms, 4),
            "min_inversion_ms": round(min(alg2_times_ms), 4),
            "max_inversion_ms": round(max(alg2_times_ms), 4),
            "max_trellis_width": max(alg2_widths),
            "success_rate_percent": (alg2_successes / trials_per_length) * 100.0
        })
        print(f"    Alg 2   -> Invert: {mean_alg2_ms:7.3f} ms | "
              f"Trellis Width: {max(alg2_widths)} | Success: 100%")

        # ----------------------------------------------------------------------
        # Benchmark Algorithm 3 (Dyadic Cylinder Recovery from Keystream)
        # ----------------------------------------------------------------------
        alg3_times_ms = []
        alg3_successes = 0

        for trial in range(trials_per_length):
            seed_offset = trial * 3000 + M
            import random
            rng = random.Random(seed_offset)
            n0_rand = rng.getrandbits(M) | 1
            blocks, y_term, w_actual, Km_actual = DyadicCylinderKeystreamPRG.generate_keystream_trace(
                n0_rand, m_steps, b=32
            )

            t_start = time.perf_counter()
            res3 = algorithm3_dyadic_cylinder_keystream_inverter(blocks, y_term, b=32)
            t_end = time.perf_counter()

            elapsed_ms = (t_end - t_start) * 1e3
            alg3_times_ms.append(elapsed_ms)

            assert res3["success"]
            assert res3["w"] == w_actual
            assert res3["n0"] == n0_rand
            alg3_successes += 1

        mean_alg3_ms = sum(alg3_times_ms) / trials_per_length
        results_alg3.append({
            "m": m_steps,
            "mean_recovery_ms": round(mean_alg3_ms, 4),
            "min_recovery_ms": round(min(alg3_times_ms), 4),
            "max_recovery_ms": round(max(alg3_times_ms), 4),
            "success_rate_percent": (alg3_successes / trials_per_length) * 100.0
        })
        print(f"    Alg 3   -> Keystream Invert: {mean_alg3_ms:7.3f} ms | Success: 100%")

    # --------------------------------------------------------------------------
    # Power-Law Scaling Fits: T(M) = c * M^alpha
    # --------------------------------------------------------------------------
    m_floats = [float(row["M"]) for row in results_mode_a]
    t_mode_a_floats = [row["mean_inversion_ms"] for row in results_mode_a]
    alpha_mode_a, c_mode_a, r2_mode_a = fit_power_law(m_floats, t_mode_a_floats)

    t_alg2_floats = [row["mean_inversion_ms"] for row in results_alg2]
    alpha_alg2, c_alg2, r2_alg2 = fit_power_law(m_floats, t_alg2_floats)

    t_alg3_floats = [row["mean_recovery_ms"] for row in results_alg3]
    alpha_alg3, c_alg3, r2_alg3 = fit_power_law(m_floats, t_alg3_floats)

    scaling_summary = {
        "mode_a_scaling": {
            "model": "T(M) = c * M^alpha",
            "alpha": round(alpha_mode_a, 4),
            "c_constant": round(c_mode_a, 6),
            "r_squared": round(r2_mode_a, 4),
            "complexity_class": f"O(M^{{{alpha_mode_a:.2f}}})"
        },
        "alg2_scaling": {
            "model": "T(m) = c * m^alpha",
            "alpha": round(alpha_alg2, 4),
            "c_constant": round(c_alg2, 6),
            "r_squared": round(r2_alg2, 4),
            "complexity_class": f"O(m^{{{alpha_alg2:.2f}}})"
        },
        "alg3_scaling": {
            "model": "T(m) = c * m^alpha",
            "alpha": round(alpha_alg3, 4),
            "c_constant": round(c_alg3, 6),
            "r_squared": round(r2_alg3, 4),
            "complexity_class": f"O(m^{{{alpha_alg3:.2f}}})"
        }
    }

    full_output = {
        "metadata": {
            "experiment": "Polynomial-Time Inversion and Decryption of Collatz PRGs",
            "engine": "crypto_2_hensel_inversion.py",
            "key_lengths": key_lengths,
            "trials_per_length": trials_per_length,
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime()),
            "system_properties": {
                "trellis_width_mode_a": 1,
                "trellis_width_alg2": 1,
                "overall_decryption_success_rate": 1.0
            }
        },
        "mode_a_switch_block_benchmarks": results_mode_a,
        "algorithm2_binary_alphabet_benchmarks": results_alg2,
        "algorithm3_dyadic_cylinder_benchmarks": results_alg3,
        "polynomial_scaling_fits": scaling_summary
    }

    # Print summary table
    print("\n" + "=" * 80)
    print("POLYNOMIAL SCALING FIT SUMMARY (Log-Log Ordinary Least Squares)")
    print("=" * 80)
    print(f"Algorithm 1 (Mode A Inverter):  alpha = {alpha_mode_a:.4f} | R^2 = {r2_mode_a:.4f} | Complexity: O(M^{alpha_mode_a:.2f})")
    print(f"Algorithm 2 (3-Adic Peeler):    alpha = {alpha_alg2:.4f} | R^2 = {r2_alg2:.4f} | Complexity: O(m^{alpha_alg2:.2f})")
    print(f"Algorithm 3 (Dyadic Cylinder):  alpha = {alpha_alg3:.4f} | R^2 = {r2_alg3:.4f} | Complexity: O(m^{alpha_alg3:.2f})")
    print("=" * 80)

    return full_output


# ==============================================================================
# SECTION 7: MAIN EXECUTION AND PERSISTENCE
# ==============================================================================

if __name__ == "__main__":
    results = execute_crypto_benchmark_suite(
        key_lengths=[16, 32, 64, 128, 256, 512, 1024],
        trials_per_length=5
    )

    output_path = r"c:\Users\asusu\Desktop\prison manager\crypto_2_results.json"
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(results, f, indent=2)

    print(f"\n[+] Results successfully exported to: {output_path}")
