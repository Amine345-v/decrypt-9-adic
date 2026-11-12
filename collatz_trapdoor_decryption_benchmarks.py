"""
collatz_trapdoor_decryption_benchmarks.py
==========================================
Polynomial-Time Collatz Trapdoor Decryption Engine with Standard Cryptographic Hashing.

Decapsulation and Decryption Architecture:
1. Public Token Decapsulation via Collatz Trapdoor:
   Given the encapsulated public token y = S^{2M}(n_0), backward 9-adic Hensel peeling
   inverts y -> n_0 in deterministic polynomial time O(M^2) with trellis width strictly 1.
2. Standard Cryptographic Key Derivation (KDF):
   Derives a 256-bit symmetric session key K from decrypted seed n_0 using:
   - SHA-256
   - SHA3-256
   - HKDF-SHA256 (RFC 5869)
   - BLAKE2s
3. Authenticated Symmetric Decryption:
   Decrypts AES-256-GCM ciphertext (C, tag) with nonce, verifying 100% exact round-trip match.
4. Comprehensive Decryption Latency Breakdown:
   Quantifies exact microsecond-level timing and scaling breakdown between:
   (a) Collatz Trapdoor Hensel Inversion (y -> n_0)
   (b) Standard Hashing + Symmetric AEAD Decryption (n_0 -> K -> Plaintext)
   across key lengths M in {32, 64, 128, 256, 512, 1024} and payloads {32 B, 1 KB, 10 KB, 100 KB}.
"""

import math
import time
import json
import hashlib
import os
from typing import List, Tuple, Dict, Any, Optional

from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.hkdf import HKDF
from cryptography.hazmat.primitives import hashes


# ==============================================================================
# SECTION 1: COLLATZ TRAPDOOR ARITHMETIC & 9-ADIC HENSEL INVERTER
# ==============================================================================

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


def sample_collatz_encapsulation(M: int, random_seed: Optional[int] = None) -> Tuple[int, int, List[int]]:
    """
    Simulate sender token encapsulation:
    Samples ephemeral secret switch key u in {0,1}^M and secret seed n_0 in N+_odd,
    and computes the public terminal token y = S^{2M}(n_0) satisfying:
        9^M n_0 + B_{2M}(u) = 16^M y.
    Returns: (public_token_y, secret_n0, secret_u)
    """
    import random
    rng = random.Random(random_seed)
    u = [rng.randint(0, 1) for _ in range(M)]

    B = compute_switch_block_B_formula(u)
    mod2 = 1 << (4 * M)
    p9_M = pow(9, M)
    inv9M = pow(p9_M, -1, mod2)
    r0 = (-B * inv9M) % mod2
    n0 = r0 if r0 > 0 else mod2
    # Ensure y is odd positive integer (canonical carry-stopper)
    if (((p9_M * n0 + B) >> (4 * M)) & 1) == 0:
        n0 += mod2

    # Secret cylinder offset
    offset = rng.randint(1, 500)
    n0 += offset * (1 << (4 * M + 1))

    # Public token y
    num = p9_M * n0 + B
    denom = 1 << (4 * M)
    assert num % denom == 0
    y = num >> (4 * M)
    assert (y & 1) == 1
    return y, n0, u


def collatz_trapdoor_9adic_hensel_inversion(y: int, M: int) -> Tuple[int, List[int], int, float]:
    """
    Polynomial-Time Collatz Trapdoor Inversion (y -> n_0):
    =====================================================
    Applies backward 9-adic Hensel peeling to public token y.
    Recovers secret seed n_0 and switch key u in O(M^2) time with trellis width 1.

    Returns:
        (recovered_n0, recovered_u, max_trellis_width, elapsed_ms)
    """
    t0 = time.perf_counter()
    K_m = 4 * M
    base_drift = (5 * (pow(16, M) - pow(9, M))) // 7
    Y = (y << K_m) - base_drift

    # Precompute powers of 16
    pow16 = [1] * M
    for q in range(1, M):
        pow16[q] = pow16[q - 1] << 4

    u_rec = [0] * M
    trellis_widths = []

    for r in range(M):
        q = M - 1 - r
        R_mod9 = Y % 9
        c_q = (2 * pow(16, q, 9)) % 9

        if R_mod9 == 0:
            u_q = 0
            w = 1
        elif R_mod9 == c_q:
            u_q = 1
            w = 1
        else:
            trellis_widths.append(0)
            elapsed_ms = (time.perf_counter() - t0) * 1e3
            raise ValueError(f"9-Adic Hensel inversion failed at layer r={r}")

        u_rec[q] = u_q
        trellis_widths.append(w)

        if u_q == 1:
            Y -= 2 * pow16[q]
        Y //= 9

    n0_rec = Y
    elapsed_ms = (time.perf_counter() - t0) * 1e3
    max_w = max(trellis_widths) if trellis_widths else 1
    return n0_rec, u_rec, max_w, elapsed_ms


# ==============================================================================
# SECTION 2: STANDARD HASHING & KEY DERIVATION FUNCTIONS (KDF)
# ==============================================================================

def derive_symmetric_key_from_seed(n0: int, algo: str) -> Tuple[bytes, float]:
    """
    Pass the decrypted seed n_0 to standard cryptographic hash functions
    to re-derive the 256-bit symmetric session key K:
      - 'SHA-256'
      - 'SHA3-256'
      - 'HKDF-SHA256'
      - 'BLAKE2s'
    Returns: (key_256, elapsed_ms)
    """
    t0 = time.perf_counter()
    n0_bitlen = n0.bit_length()
    n0_bytes = n0.to_bytes((n0_bitlen + 7) // 8, 'big') if n0_bitlen > 0 else b'\x00'

    if algo == "SHA-256":
        key = hashlib.sha256(n0_bytes).digest()
    elif algo == "SHA3-256":
        key = hashlib.sha3_256(n0_bytes).digest()
    elif algo == "HKDF-SHA256":
        hkdf = HKDF(
            algorithm=hashes.SHA256(),
            length=32,
            salt=b"Collatz-Trapdoor-Salt-v1",
            info=b"Collatz-Trapdoor-KEM-SessionKey"
        )
        key = hkdf.derive(n0_bytes)
    elif algo == "BLAKE2s":
        key = hashlib.blake2s(n0_bytes).digest()
    else:
        raise ValueError(f"Unsupported hash algorithm: {algo}")

    elapsed_ms = (time.perf_counter() - t0) * 1e3
    assert len(key) == 32, f"Derived key must be exactly 32 bytes (256 bits), got {len(key)}"
    return key, elapsed_ms


# ==============================================================================
# SECTION 3: AUTHENTICATED SYMMETRIC ENCRYPTION / DECRYPTION (AES-256-GCM)
# ==============================================================================

def symmetric_aead_encrypt(key: bytes, plaintext: bytes) -> Tuple[bytes, bytes]:
    """Encrypt plaintext using AES-256-GCM with a fresh 12-byte nonce."""
    aesgcm = AESGCM(key)
    nonce = os.urandom(12)
    ciphertext_and_tag = aesgcm.encrypt(nonce, plaintext, None)
    return nonce, ciphertext_and_tag


def symmetric_aead_decrypt(key: bytes, nonce: bytes, ciphertext_and_tag: bytes) -> Tuple[bytes, float]:
    """
    Decrypt AES-256-GCM ciphertext and verify 16-byte authentication tag.
    Returns: (decrypted_plaintext, elapsed_ms)
    """
    t0 = time.perf_counter()
    aesgcm = AESGCM(key)
    plaintext = aesgcm.decrypt(nonce, ciphertext_and_tag, None)
    elapsed_ms = (time.perf_counter() - t0) * 1e3
    return plaintext, elapsed_ms


# ==============================================================================
# SECTION 4: COMPLETE COLLATZ TRAPDOOR DECRYPTION PIPELINE
# ==============================================================================

def execute_trapdoor_decryption_pipeline(
    public_token_y: int,
    M: int,
    nonce: bytes,
    ciphertext_and_tag: bytes,
    hash_algo: str,
    expected_plaintext: bytes
) -> Dict[str, Any]:
    """
    Complete Decryption / Decapsulation Pipeline:
      Phase 1: Collatz Trapdoor Hensel Inversion (y -> n_0) in O(M^2) time.
      Phase 2: Standard Key Derivation (n_0 -> K) via chosen standard hash function.
      Phase 3: Authenticated Symmetric AEAD Decryption (K, nonce, C, tag -> Plaintext).
      Verification: Check exact 100% round-trip match against original plaintext.
    """
    # Phase 1: Collatz Trapdoor Inversion
    n0_rec, u_rec, max_w, t_inversion_ms = collatz_trapdoor_9adic_hensel_inversion(public_token_y, M)

    # Phase 2: Standard Hash Key Derivation
    key_rec, t_hash_ms = derive_symmetric_key_from_seed(n0_rec, hash_algo)

    # Phase 3: Authenticated Symmetric Decryption
    pt_rec, t_sym_decrypt_ms = symmetric_aead_decrypt(key_rec, nonce, ciphertext_and_tag)

    # Verification
    roundtrip_match = (pt_rec == expected_plaintext)
    t_hash_and_sym_ms = t_hash_ms + t_sym_decrypt_ms
    t_total_ms = t_inversion_ms + t_hash_and_sym_ms

    inversion_ratio_pct = (t_inversion_ms / t_total_ms) * 100.0 if t_total_ms > 0 else 0.0
    sym_ratio_pct = (t_hash_and_sym_ms / t_total_ms) * 100.0 if t_total_ms > 0 else 0.0

    return {
        "roundtrip_match": roundtrip_match,
        "max_trellis_width": max_w,
        "n0_recovered": n0_rec,
        "u_recovered": u_rec,
        "y_bitlength": public_token_y.bit_length(),
        "n0_bitlength": n0_rec.bit_length(),
        "timing_breakdown_ms": {
            "collatz_trapdoor_inversion_ms": t_inversion_ms,
            "standard_hash_kdf_ms": t_hash_ms,
            "symmetric_aead_decrypt_ms": t_sym_decrypt_ms,
            "hash_and_sym_decrypt_total_ms": t_hash_and_sym_ms,
            "total_decryption_ms": t_total_ms
        },
        "latency_ratios_percent": {
            "collatz_trapdoor_ratio": inversion_ratio_pct,
            "hash_and_sym_ratio": sym_ratio_pct
        }
    }


# ==============================================================================
# SECTION 5: PAYLOAD GENERATORS
# ==============================================================================

def generate_payloads() -> Dict[str, bytes]:
    """
    Generate test payloads for benchmarking:
      - '32B_key': 32 random bytes (e.g. encapsulated symmetric key)
      - '1KB_text': 1,024 bytes of structured plaintext
      - '10KB_json': 10,240 bytes of realistic structured JSON document
      - '100KB_binary': 102,400 bytes of entropy-dense binary payload
    """
    p32 = os.urandom(32)

    text_base = (
        b"The Collatz dynamical mapping S(n) = (3n+1)/2^k admits an exact polynomial-time "
        b"trapdoor inversion under backward 9-adic Hensel lifting on constant-valuation switch blocks. "
    )
    p1k = (text_base * 10)[:1024]

    json_doc = {
        "benchmark_metadata": {
            "system": "Collatz-Trapdoor-Decryption-Engine",
            "version": "2.0.0",
            "security_eval": "Polynomial-Time Inversion Audit"
        },
        "records": [
            {
                "record_id": i,
                "token_hash": hashlib.sha256(f"tok_{i}".encode()).hexdigest(),
                "status": "decrypted",
                "attributes": {
                    "priority": i % 5,
                    "zone": f"sector_{i % 12}",
                    "tags": ["hensel", "9adic", "collatz", "trapdoor"]
                }
            }
            for i in range(75)
        ]
    }
    raw_json = json.dumps(json_doc, indent=2).encode('utf-8')
    if len(raw_json) < 10240:
        p10k = raw_json + b" " * (10240 - len(raw_json))
    else:
        p10k = raw_json[:10240]

    p100k = os.urandom(102400)

    assert len(p32) == 32
    assert len(p1k) == 1024
    assert len(p10k) == 10240
    assert len(p100k) == 102400

    return {
        "32B_key": p32,
        "1KB_text": p1k,
        "10KB_json": p10k,
        "100KB_binary": p100k
    }


# ==============================================================================
# SECTION 6: POWER-LAW REGRESSION FITTER
# ==============================================================================

def fit_power_law(x_vals: List[float], y_vals: List[float]) -> Tuple[float, float, float]:
    """Fit Y = c * X^alpha via log-log ordinary least squares regression."""
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
# SECTION 7: FULL BENCHMARK EXECUTION SUITE
# ==============================================================================

def run_trapdoor_decryption_benchmarks(
    key_lengths: List[int] = [32, 64, 128, 256, 512, 1024],
    hash_algorithms: List[str] = ["SHA-256", "SHA3-256", "HKDF-SHA256", "BLAKE2s"],
    trials_per_config: int = 5
) -> Dict[str, Any]:
    """
    Execute comprehensive decryption benchmarks across:
      - Key lengths M in {32, 64, 128, 256, 512, 1024} bits
      - Payloads: 32B_key, 1KB_text, 10KB_json, 100KB_binary
      - Hash Algorithms: SHA-256, SHA3-256, HKDF-SHA256, BLAKE2s
    """
    print("=" * 95)
    print("COLLATZ TRAPDOOR DECRYPTION ENGINE: BENCHMARK WITH STANDARD HASHING & AEAD")
    print("=" * 95)
    print(f"Key Lengths M:       {key_lengths}")
    print(f"Hash Algorithms:     {hash_algorithms}")
    print(f"Payloads:            ['32B_key', '1KB_text', '10KB_json', '100KB_binary']")
    print(f"Trials per Config:   {trials_per_config}")
    print("-" * 95)

    payloads = generate_payloads()
    all_config_results = []
    aggregated_by_M: Dict[int, Dict[str, List[float]]] = {M: {
        "inv_ms": [], "hash_ms": [], "sym_ms": [], "hash_sym_ms": [], "total_ms": [], "y_bits": []
    } for M in key_lengths}
    aggregated_by_payload: Dict[str, Dict[str, List[float]]] = {p_name: {
        "sym_ms": [], "total_ms": []
    } for p_name in payloads}
    aggregated_by_hash: Dict[str, Dict[str, List[float]]] = {h_algo: {
        "hash_ms": [], "total_ms": []
    } for h_algo in hash_algorithms}

    total_runs = len(key_lengths) * len(payloads) * len(hash_algorithms) * trials_per_config
    current_run = 0

    header_fmt = "{:<5} | {:<12} | {:<11} | {:>9} | {:>9} | {:>9} | {:>9} | {:>7} | {:>7}"
    print(header_fmt.format("M", "Payload", "Hash Algo", "Trapdoor", "Hash KDF", "Sym Dec", "Total Dec", "% Trap", "Match%"))
    print("-" * 95)

    for M in key_lengths:
        for p_name, p_bytes in payloads.items():
            for h_algo in hash_algorithms:
                inv_times = []
                hash_times = []
                sym_times = []
                hash_sym_times = []
                total_times = []
                matches = 0
                y_bits_list = []

                for trial in range(trials_per_config):
                    seed_idx = trial * 10000 + M * 100 + len(p_bytes)
                    # Sender encapsulation
                    y_pub, n0_sec, u_sec = sample_collatz_encapsulation(M, random_seed=seed_idx)
                    # Sender key derivation
                    key_enc, _ = derive_symmetric_key_from_seed(n0_sec, h_algo)
                    # Sender AEAD encryption
                    nonce, ct = symmetric_aead_encrypt(key_enc, p_bytes)

                    # Receiver / Trapdoor Decryption
                    res = execute_trapdoor_decryption_pipeline(
                        public_token_y=y_pub,
                        M=M,
                        nonce=nonce,
                        ciphertext_and_tag=ct,
                        hash_algo=h_algo,
                        expected_plaintext=p_bytes
                    )

                    current_run += 1
                    assert res["roundtrip_match"], f"Decryption failed at M={M}, {p_name}, {h_algo}"
                    assert res["max_trellis_width"] == 1, f"Trellis width > 1 at M={M}"

                    matches += 1
                    t_b = res["timing_breakdown_ms"]
                    inv_times.append(t_b["collatz_trapdoor_inversion_ms"])
                    hash_times.append(t_b["standard_hash_kdf_ms"])
                    sym_times.append(t_b["symmetric_aead_decrypt_ms"])
                    hash_sym_times.append(t_b["hash_and_sym_decrypt_total_ms"])
                    total_times.append(t_b["total_decryption_ms"])
                    y_bits_list.append(res["y_bitlength"])

                mean_inv = sum(inv_times) / trials_per_config
                mean_hash = sum(hash_times) / trials_per_config
                mean_sym = sum(sym_times) / trials_per_config
                mean_hash_sym = sum(hash_sym_times) / trials_per_config
                mean_total = sum(total_times) / trials_per_config
                trap_pct = (mean_inv / mean_total) * 100.0 if mean_total > 0 else 0.0
                match_pct = (matches / trials_per_config) * 100.0
                avg_y_bits = sum(y_bits_list) / trials_per_config

                # Accumulate for aggregations
                aggregated_by_M[M]["inv_ms"].append(mean_inv)
                aggregated_by_M[M]["hash_ms"].append(mean_hash)
                aggregated_by_M[M]["sym_ms"].append(mean_sym)
                aggregated_by_M[M]["hash_sym_ms"].append(mean_hash_sym)
                aggregated_by_M[M]["total_ms"].append(mean_total)
                aggregated_by_M[M]["y_bits"].append(avg_y_bits)

                aggregated_by_payload[p_name]["sym_ms"].append(mean_sym)
                aggregated_by_payload[p_name]["total_ms"].append(mean_total)

                aggregated_by_hash[h_algo]["hash_ms"].append(mean_hash)
                aggregated_by_hash[h_algo]["total_ms"].append(mean_total)

                config_entry = {
                    "M": M,
                    "steps_2M": 2 * M,
                    "payload_name": p_name,
                    "payload_bytes": len(p_bytes),
                    "hash_algorithm": h_algo,
                    "mean_y_bitlength": round(avg_y_bits, 1),
                    "mean_trapdoor_inversion_ms": round(mean_inv, 4),
                    "mean_hash_kdf_ms": round(mean_hash, 4),
                    "mean_symmetric_decrypt_ms": round(mean_sym, 4),
                    "mean_hash_and_sym_total_ms": round(mean_hash_sym, 4),
                    "mean_total_decryption_ms": round(mean_total, 4),
                    "trapdoor_latency_ratio_percent": round(trap_pct, 2),
                    "symmetric_latency_ratio_percent": round(100.0 - trap_pct, 2),
                    "max_trellis_width": 1,
                    "roundtrip_match_success_percent": match_pct
                }
                all_config_results.append(config_entry)

                # Print summary row for select representative configs to keep console clean
                if (p_name in ["32B_key", "100KB_binary"]) and (h_algo in ["SHA-256", "HKDF-SHA256"]):
                    print(header_fmt.format(
                        M, p_name, h_algo,
                        f"{mean_inv:.3f} ms",
                        f"{mean_hash:.3f} ms",
                        f"{mean_sym:.3f} ms",
                        f"{mean_total:.3f} ms",
                        f"{trap_pct:.1f}%",
                        f"{match_pct:.0f}%"
                    ))

    # --------------------------------------------------------------------------
    # Aggregated Summary by Key Length M
    # --------------------------------------------------------------------------
    summary_by_M = []
    for M in key_lengths:
        m_inv = sum(aggregated_by_M[M]["inv_ms"]) / len(aggregated_by_M[M]["inv_ms"])
        m_hash = sum(aggregated_by_M[M]["hash_ms"]) / len(aggregated_by_M[M]["hash_ms"])
        m_sym = sum(aggregated_by_M[M]["sym_ms"]) / len(aggregated_by_M[M]["sym_ms"])
        m_tot = sum(aggregated_by_M[M]["total_ms"]) / len(aggregated_by_M[M]["total_ms"])
        avg_y_bits = sum(aggregated_by_M[M]["y_bits"]) / len(aggregated_by_M[M]["y_bits"])
        trap_pct = (m_inv / m_tot) * 100.0 if m_tot > 0 else 0.0

        summary_by_M.append({
            "M": M,
            "steps_2M": 2 * M,
            "mean_y_bitlength": round(avg_y_bits, 1),
            "mean_trapdoor_inversion_ms": round(m_inv, 4),
            "mean_hash_kdf_ms": round(m_hash, 4),
            "mean_symmetric_decrypt_ms": round(m_sym, 4),
            "mean_total_decryption_ms": round(m_tot, 4),
            "trapdoor_share_percent": round(trap_pct, 2),
            "trellis_width": 1,
            "success_rate_percent": 100.0
        })

    # --------------------------------------------------------------------------
    # Aggregated Summary by Payload Size
    # --------------------------------------------------------------------------
    summary_by_payload = []
    for p_name, p_bytes in payloads.items():
        m_sym = sum(aggregated_by_payload[p_name]["sym_ms"]) / len(aggregated_by_payload[p_name]["sym_ms"])
        m_tot = sum(aggregated_by_payload[p_name]["total_ms"]) / len(aggregated_by_payload[p_name]["total_ms"])
        summary_by_payload.append({
            "payload_name": p_name,
            "payload_bytes": len(p_bytes),
            "mean_symmetric_decrypt_ms": round(m_sym, 4),
            "mean_total_decryption_ms": round(m_tot, 4)
        })

    # --------------------------------------------------------------------------
    # Aggregated Summary by Hash Algorithm
    # --------------------------------------------------------------------------
    summary_by_hash = []
    for h_algo in hash_algorithms:
        m_hash = sum(aggregated_by_hash[h_algo]["hash_ms"]) / len(aggregated_by_hash[h_algo]["hash_ms"])
        m_tot = sum(aggregated_by_hash[h_algo]["total_ms"]) / len(aggregated_by_hash[h_algo]["total_ms"])
        summary_by_hash.append({
            "hash_algorithm": h_algo,
            "mean_hash_kdf_ms": round(m_hash, 4),
            "mean_total_decryption_ms": round(m_tot, 4)
        })

    # --------------------------------------------------------------------------
    # Power-Law Scaling Fits
    # --------------------------------------------------------------------------
    m_floats = [float(row["M"]) for row in summary_by_M]
    t_inv_floats = [row["mean_trapdoor_inversion_ms"] for row in summary_by_M]
    t_tot_floats = [row["mean_total_decryption_ms"] for row in summary_by_M]

    alpha_inv, c_inv, r2_inv = fit_power_law(m_floats, t_inv_floats)
    alpha_tot, c_tot, r2_tot = fit_power_law(m_floats, t_tot_floats)

    scaling_fits = {
        "trapdoor_inversion_scaling": {
            "model": "T_inv(M) = c * M^alpha",
            "alpha": round(alpha_inv, 4),
            "c_constant": round(c_inv, 6),
            "r_squared": round(r2_inv, 4),
            "complexity_class": f"O(M^{{{alpha_inv:.2f}}})"
        },
        "total_decryption_scaling": {
            "model": "T_total(M) = c * M^alpha",
            "alpha": round(alpha_tot, 4),
            "c_constant": round(c_tot, 6),
            "r_squared": round(r2_tot, 4),
            "complexity_class": f"O(M^{{{alpha_tot:.2f}}})"
        }
    }

    full_output = {
        "metadata": {
            "experiment": "Collatz Trapdoor Decryption with Standard Hashing & AEAD",
            "engine": "collatz_trapdoor_decryption_benchmarks.py",
            "key_lengths": key_lengths,
            "hash_algorithms": hash_algorithms,
            "payload_sizes_bytes": {k: len(v) for k, v in payloads.items()},
            "trials_per_config": trials_per_config,
            "total_benchmark_runs": total_runs,
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime()),
            "system_properties": {
                "trellis_width": 1,
                "decryption_roundtrip_success_rate": 1.0,
                "symmetric_cipher": "AES-256-GCM"
            }
        },
        "scaling_fits": scaling_fits,
        "aggregated_by_key_length": summary_by_M,
        "aggregated_by_payload": summary_by_payload,
        "aggregated_by_hash_algorithm": summary_by_hash,
        "detailed_configuration_benchmarks": all_config_results
    }

    # Print summary
    print("\n" + "=" * 95)
    print("COLLATZ TRAPDOOR DECRYPTION: AGGREGATED BENCHMARK BY KEY LENGTH M")
    print("=" * 95)
    sum_fmt = "{:<5} | {:<9} | {:>10} | {:>12} | {:>10} | {:>10} | {:>10} | {:>7}"
    print(sum_fmt.format("M", "Steps 2M", "y Bitlen", "Trapdoor Inv", "Hash KDF", "Sym Dec", "Total Dec", "Trap%"))
    print("-" * 95)
    for row in summary_by_M:
        print(sum_fmt.format(
            row["M"], row["steps_2M"], f"{row['mean_y_bitlength']:.0f} b",
            f"{row['mean_trapdoor_inversion_ms']:.3f} ms",
            f"{row['mean_hash_kdf_ms']:.4f} ms",
            f"{row['mean_symmetric_decrypt_ms']:.4f} ms",
            f"{row['mean_total_decryption_ms']:.3f} ms",
            f"{row['trapdoor_share_percent']:.1f}%"
        ))

    print("\n" + "=" * 95)
    print("POWER-LAW COMPLEXITY FITS (Log-Log OLS)")
    print("=" * 95)
    print(f"Collatz Trapdoor Inversion:  alpha = {alpha_inv:.4f} | R^2 = {r2_inv:.4f} | Fit: T(M) = {c_inv:.6f} * M^{alpha_inv:.2f} ms")
    print(f"Total Decryption Latency:   alpha = {alpha_tot:.4f} | R^2 = {r2_tot:.4f} | Fit: T(M) = {c_tot:.6f} * M^{alpha_tot:.2f} ms")
    print("=" * 95)

    return full_output


# ==============================================================================
# SECTION 8: ENTRY POINT & JSON EXPORT
# ==============================================================================

if __name__ == "__main__":
    benchmark_data = run_trapdoor_decryption_benchmarks(
        key_lengths=[32, 64, 128, 256, 512, 1024],
        hash_algorithms=["SHA-256", "SHA3-256", "HKDF-SHA256", "BLAKE2s"],
        trials_per_config=5
    )

    out_file = r"c:\Users\asusu\Desktop\prison manager\collatz_trapdoor_decryption_results.json"
    with open(out_file, "w", encoding="utf-8") as f:
        json.dump(benchmark_data, f, indent=2)

    print(f"\n[+] Full decryption benchmark dataset successfully written to: {out_file}")
