#!/usr/bin/env python3
"""
GPU-accelerated (Apple MPS) verification of FRI char-2 extension.
Uses batch matrix operations on MPS for exhaustive RS distance computations.

GF(2^m) arithmetic is done via lookup tables on CPU;
the distance-minimization sweep is done on GPU.
"""
import torch
import numpy as np
import time

device = torch.device("mps" if torch.backends.mps.is_available() else "cpu")
print(f"Using device: {device}")

# ============================================================
# GF(2^m) arithmetic via lookup tables
# ============================================================

def build_gf_tables(m):
    """Build log/exp tables for GF(2^m) using Conway polynomials."""
    # Standard irreducible polynomials for small m
    # These are the Conway polynomials (minimal weight)
    irred = {
        4: 0b10011,       # x^4 + x + 1
        5: 0b100101,      # x^5 + x^2 + 1
        6: 0b1000011,     # x^6 + x + 1
        7: 0b10000011,    # x^7 + x + 1
        8: 0b100011101,   # x^8 + x^4 + x^3 + x^2 + 1
        10: 0b10000001001, # x^10 + x^3 + 1
        12: 0b1000001010011, # x^12 + x^6 + x^4 + x + 1
    }
    q = 2**m
    poly = irred[m]

    exp_table = [0] * (2 * q)
    log_table = [0] * q

    x = 1
    for i in range(q - 1):
        exp_table[i] = x
        log_table[x] = i
        x <<= 1
        if x >= q:
            x ^= poly
    for i in range(q - 1, 2 * q):
        exp_table[i] = exp_table[i - (q - 1)]

    return q, exp_table, log_table

def gf_mul(a, b, q, exp_table, log_table):
    if a == 0 or b == 0:
        return 0
    return exp_table[log_table[a] + log_table[b]]

def gf_inv(a, q, exp_table, log_table):
    assert a != 0
    return exp_table[(q - 1) - log_table[a]]

def gf_div(a, b, q, exp_table, log_table):
    if a == 0:
        return 0
    return gf_mul(a, gf_inv(b, q, exp_table, log_table), q, exp_table, log_table)

# ============================================================
# Subspace and folding operations
# ============================================================

def make_subspace(m, dim, q, exp_table):
    """Build F_2-linear subspace using primitive element powers as basis."""
    basis = [exp_table[i] for i in range(dim)]
    L = []
    for mask in range(2**dim):
        e = 0
        for j in range(dim):
            if mask & (1 << j):
                e ^= basis[j]
        L.append(e)
    return L, basis

def additive_fold_raw(f_vals, L, beta, q, exp_table, log_table):
    """Raw GF arithmetic additive fold."""
    n = len(L)
    fibers = {}
    for i, x in enumerate(L):
        # s(x) = x^2 + beta*x = x*x XOR beta*x in GF(2^m)
        x_sq = gf_mul(x, x, q, exp_table, log_table)
        bx = gf_mul(beta, x, q, exp_table, log_table)
        sx = x_sq ^ bx
        if sx not in fibers:
            fibers[sx] = []
        fibers[sx].append((i, x))

    L_prime = sorted(fibers.keys())
    assert len(L_prime) == n // 2

    beta_inv = gf_inv(beta, q, exp_table, log_table)
    f0_vals, f1_vals = [], []
    for sy in L_prime:
        (i0, x0), (i1, x1) = fibers[sy]
        f_sum = f_vals[i0] ^ f_vals[i1]  # f(x) + f(x+beta) in GF(2^m) = XOR
        f1y = gf_mul(f_sum, beta_inv, q, exp_table, log_table)
        f0y = f_vals[i0] ^ gf_mul(x0, f1y, q, exp_table, log_table)
        f0_vals.append(f0y)
        f1_vals.append(f1y)

    return L_prime, f0_vals, f1_vals


# ============================================================
# GPU-accelerated RS distance computation
# ============================================================

def build_all_codewords_gpu(L, k, q, exp_table, log_table):
    """
    Build matrix of all RS_k codeword evaluations on L.
    Returns tensor of shape (q^k, n) on GPU.
    """
    n = len(L)
    total = q**k

    # Build Vandermonde: V[i,j] = L[i]^j
    V = np.zeros((n, k), dtype=np.int64)
    for i, x in enumerate(L):
        val = 1
        for j in range(k):
            V[i, j] = val
            val = gf_mul(val, x, q, exp_table, log_table)

    # Generate all coefficient vectors
    all_coeffs = np.zeros((total, k), dtype=np.int64)
    for idx in range(total):
        v = idx
        for j in range(k):
            all_coeffs[idx, j] = v % q
            v //= q

    # Compute all codewords using GF multiplication
    # codewords[c, i] = sum_j all_coeffs[c,j] * V[i,j]  (in GF arithmetic)
    # This is O(total * n * k) GF operations - do it on CPU then transfer
    codewords = np.zeros((total, n), dtype=np.int64)
    for c in range(total):
        for i in range(n):
            val = 0
            for j in range(k):
                term = gf_mul(int(all_coeffs[c, j]), int(V[i, j]), q, exp_table, log_table)
                val ^= term
            codewords[c, i] = val

    return torch.tensor(codewords, dtype=torch.int64, device=device)


def rs_distance_gpu(f_vals_int, codewords_gpu, n):
    """Compute min Hamming distance using GPU broadcast comparison."""
    f_gpu = torch.tensor(f_vals_int, dtype=torch.int64, device=device).unsqueeze(0)  # (1, n)
    # Compare f with all codewords: (num_cw, n)
    mismatches = (codewords_gpu != f_gpu).sum(dim=1)  # (num_cw,)
    min_errors = mismatches.min().item()
    return min_errors / n


def joint_distance_gpu(f0_int, f1_int, cw_gpu_half, n_half):
    """Compute min joint distance using GPU."""
    num_cw = cw_gpu_half.shape[0]
    f0_gpu = torch.tensor(f0_int, dtype=torch.int64, device=device).unsqueeze(0)
    f1_gpu = torch.tensor(f1_int, dtype=torch.int64, device=device).unsqueeze(0)

    min_joint = n_half
    # For each pair (g0, g1):
    BATCH = 1000
    for i in range(0, num_cw, BATCH):
        g0_batch = cw_gpu_half[i:i+BATCH]  # (B, n_half)
        mismatch0 = (g0_batch != f0_gpu)    # (B, n_half)
        for j in range(0, num_cw, BATCH):
            g1_batch = cw_gpu_half[j:j+BATCH]  # (B2, n_half)
            mismatch1 = (g1_batch != f1_gpu)    # (B2, n_half)
            # joint: position y is an error if f0!=g0 OR f1!=g1
            # For all pairs (i_idx, j_idx):
            for ii in range(mismatch0.shape[0]):
                m0 = mismatch0[ii]  # (n_half,)
                joint = (m0.unsqueeze(0) | mismatch1).sum(dim=1)  # (B2,)
                local_min = joint.min().item()
                if local_min < min_joint:
                    min_joint = local_min
                    if min_joint == 0:
                        return 0.0

    return min_joint / n_half


# ============================================================
# Main verification
# ============================================================

print("=" * 70)
print("GPU-ACCELERATED VERIFICATION: FRI Char-2 Extension")
print(f"Device: {device}")
print("=" * 70)

t0 = time.time()
ALL_PASS = True

# We test on GF(2^4) with n=8, k=4 and k=2
# Also GF(2^5) with n=16, k=4 for a larger test
configs = [
    (4, 3, 2, "GF(16), n=8, k=2"),
    (4, 3, 4, "GF(16), n=8, k=4"),
    (5, 4, 4, "GF(32), n=16, k=4"),
]

for m, dim, k, label in configs:
    print(f"\n{'='*60}")
    print(f"Config: {label}")
    print(f"{'='*60}")

    q, exp_table, log_table = build_gf_tables(m)
    L, basis = make_subspace(m, dim, q, exp_table)
    n = len(L)
    beta = basis[0]
    k_half = k // 2

    # Pre-compute all codewords on GPU
    t1 = time.time()
    print(f"  Building {q**k} codewords for RS_{k}(L)...", end=" ", flush=True)
    cw_gpu = build_all_codewords_gpu(L, k, q, exp_table, log_table)
    print(f"done ({time.time()-t1:.1f}s)")

    L_prime_example, _, _ = additive_fold_raw([0]*n, L, beta, q, exp_table, log_table)
    n_half = len(L_prime_example)

    t1 = time.time()
    print(f"  Building {q**k_half} codewords for RS_{k_half}(L')...", end=" ", flush=True)
    cw_half_gpu = build_all_codewords_gpu(L_prime_example, k_half, q, exp_table, log_table)
    print(f"done ({time.time()-t1:.1f}s)")

    # ---- Test: Isomorphism ----
    print(f"\n  [Isomorphism] Testing 200 random codewords...")
    iso_ok = True
    np.random.seed(42)
    for trial in range(200):
        # Random codeword
        coeffs = [np.random.randint(0, q) for _ in range(k)]
        f_vals = []
        for x in L:
            val = 0
            xpow = 1
            for c in coeffs:
                val ^= gf_mul(c, xpow, q, exp_table, log_table)
                xpow = gf_mul(xpow, x, q, exp_table, log_table)
            f_vals.append(val)

        L_prime, f0, f1 = additive_fold_raw(f_vals, L, beta, q, exp_table, log_table)

        # Check f0, f1 are in RS_{k/2}
        d0 = rs_distance_gpu(f0, cw_half_gpu, n_half)
        d1 = rs_distance_gpu(f1, cw_half_gpu, n_half)
        if d0 > 0 or d1 > 0:
            iso_ok = False
            print(f"    FAIL: f0 dist={d0}, f1 dist={d1}")
            break

    print(f"    {'✓' if iso_ok else '✗'} Isomorphism: all codewords decompose correctly")
    ALL_PASS = ALL_PASS and iso_ok

    # ---- Test: Coupling Lemma ----
    print(f"\n  [Coupling] Testing 200 random functions...")
    coupling_ok = True
    np.random.seed(123)
    for trial in range(200):
        f_vals = [np.random.randint(0, q) for _ in range(n)]
        L_prime, f0, f1 = additive_fold_raw(f_vals, L, beta, q, exp_table, log_table)

        d_f = rs_distance_gpu(f_vals, cw_gpu, n)
        d_joint = joint_distance_gpu(f0, f1, cw_half_gpu, n_half)

        if d_f > d_joint + 1e-10:
            coupling_ok = False
            print(f"    VIOLATION: Δ(f)={d_f:.4f} > Δ_joint={d_joint:.4f}")

    print(f"    {'✓' if coupling_ok else '✗'} Coupling: Δ(f,RS_k) ≤ Δ_joint always holds")
    ALL_PASS = ALL_PASS and coupling_ok

    # ---- Test: Proximity Gap ----
    print(f"\n  [Proximity Gap] Testing proximity gap ≤ 2 bad alphas...")
    gap_ok = True
    max_bad = 0
    tests_done = 0
    np.random.seed(456)

    for trial in range(200):
        f_vals = [np.random.randint(0, q) for _ in range(n)]
        d_f = rs_distance_gpu(f_vals, cw_gpu, n)

        for delta in [0.3, 0.4, 0.5]:
            if d_f <= delta:
                continue

            L_prime, f0, f1 = additive_fold_raw(f_vals, L, beta, q, exp_table, log_table)

            bad_count = 0
            for a in range(q):
                # fold = f0 + alpha * f1
                fold = [f0[i] ^ gf_mul(a, f1[i], q, exp_table, log_table) for i in range(n_half)]
                d_fold = rs_distance_gpu(fold, cw_half_gpu, n_half)
                if d_fold <= delta / 3:
                    bad_count += 1

            max_bad = max(max_bad, bad_count)
            tests_done += 1

            if bad_count > 2:
                gap_ok = False
                print(f"    VIOLATION: {bad_count} bad alphas at δ={delta}, Δ(f)={d_f:.3f}")

    print(f"    {'✓' if gap_ok else '✗'} Proximity gap: {tests_done} tests, max bad α = {max_bad}")
    ALL_PASS = ALL_PASS and gap_ok

    # ---- Test: Multi-round ----
    print(f"\n  [Multi-round] Testing {int(np.log2(k))}-round FRI...")
    R = int(np.log2(k))
    mr_ok = True
    np.random.seed(789)

    for trial in range(200):
        coeffs = [np.random.randint(0, q) for _ in range(k)]
        f_vals = []
        for x in L:
            val = 0
            xpow = 1
            for c in coeffs:
                val ^= gf_mul(c, xpow, q, exp_table, log_table)
                xpow = gf_mul(xpow, x, q, exp_table, log_table)
            f_vals.append(val)

        cur_L, cur_f = L[:], f_vals[:]
        # Track a basis for the current subspace
        cur_sub_basis = basis[:]
        for r in range(R):
            beta_r = cur_sub_basis[0]
            L_next, f0, f1 = additive_fold_raw(cur_f, cur_L, beta_r, q, exp_table, log_table)
            alpha_r = np.random.randint(0, q)
            cur_f = [f0[i] ^ gf_mul(alpha_r, f1[i], q, exp_table, log_table)
                     for i in range(len(L_next))]
            cur_L = L_next
            # Update basis: s(b) = b^2 + beta*b for remaining basis elements
            new_basis = []
            for b in cur_sub_basis[1:]:
                sb = gf_mul(b, b, q, exp_table, log_table) ^ gf_mul(beta_r, b, q, exp_table, log_table)
                new_basis.append(sb)
            cur_sub_basis = new_basis

        if not all(v == cur_f[0] for v in cur_f):
            mr_ok = False
            print(f"    FAIL: codeword not constant after {R} folds")
            break

    print(f"    {'✓' if mr_ok else '✗'} Multi-round: 200 codewords all fold to constants")
    ALL_PASS = ALL_PASS and mr_ok

# ---- F_2-linearity check ----
print(f"\n{'='*60}")
print("Structural check: s(x) F_2-linear, L' is subspace")
print(f"{'='*60}")

for m, dim in [(4, 4), (6, 5), (8, 6)]:
    q, exp_table, log_table = build_gf_tables(m)
    L, basis = make_subspace(m, dim, q, exp_table)
    beta = basis[0]

    # F_2-linearity: s(x+y) = s(x) + s(y) in char 2
    lin_ok = True
    for i in range(min(len(L), 50)):
        for j in range(i+1, min(len(L), 50)):
            x, y = L[i], L[j]
            xy = x ^ y
            sxy = gf_mul(xy, xy, q, exp_table, log_table) ^ gf_mul(beta, xy, q, exp_table, log_table)
            sx = gf_mul(x, x, q, exp_table, log_table) ^ gf_mul(beta, x, q, exp_table, log_table)
            sy = gf_mul(y, y, q, exp_table, log_table) ^ gf_mul(beta, y, q, exp_table, log_table)
            if sxy != (sx ^ sy):
                lin_ok = False
                break

    # L' subspace
    L_prime_set = set()
    for x in L:
        sx = gf_mul(x, x, q, exp_table, log_table) ^ gf_mul(beta, x, q, exp_table, log_table)
        L_prime_set.add(sx)

    sub_ok = True
    L_prime_list = sorted(L_prime_set)
    for i in range(min(len(L_prime_list), 30)):
        for j in range(i+1, min(len(L_prime_list), 30)):
            if (L_prime_list[i] ^ L_prime_list[j]) not in L_prime_set:
                sub_ok = False
                break

    ok = lin_ok and sub_ok
    print(f"  {'✓' if ok else '✗'} GF(2^{m}), dim={dim}: linear={lin_ok}, subspace={sub_ok}, |L'|={len(L_prime_set)}")
    ALL_PASS = ALL_PASS and ok

# ============================================================
elapsed = time.time() - t0
print(f"\n{'='*70}")
print(f"COMPLETED in {elapsed:.1f}s on {device}")
if ALL_PASS:
    print("████ ALL TESTS PASSED ████")
else:
    print("████ SOME TESTS FAILED ████")
