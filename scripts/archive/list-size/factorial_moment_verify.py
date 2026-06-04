#!/usr/bin/env python3
"""
Factorial moment verification for Vandermonde intersection / Poisson approximation.

Key claim: M(s) = #{B ⊂ L, |B|=w : s ∈ Im(V_B)} is approximately Poisson(λ)
where λ = C(n,w)/p^c, c = n-k-w.

Verifies:
1. E[M^{(k)}] ≈ λ^k (factorial moments match Poisson)
2. dim(Im(V_{B1}) ∩ Im(V_{B2})) = max(|B1∩B2|, d) for Vandermonde
3. Full distribution of M vs Poisson(λ)
4. Var[M] ≈ λ

Two modes:
- FULL: enumerate all B ∈ C(L,w), accumulate M(s). For small configs.
- SAMPLE: sample random syndromes, compute M(s). For larger configs.

Multi-core numpy acceleration.
"""

import numpy as np
from itertools import combinations
from collections import Counter
from math import comb, factorial, exp, floor, sqrt
from multiprocessing import Pool, cpu_count
import time
import sys

def vandermonde_matrix(L, B, nk, p):
    """Build (n-k) x w Vandermonde matrix V_B over F_p."""
    w = len(B)
    V = np.zeros((nk, w), dtype=np.int64)
    for j, alpha in enumerate(B):
        col = np.ones(nk, dtype=np.int64)
        for i in range(1, nk):
            col[i] = (col[i-1] * alpha) % p
        V[:, j] = col
    return V

def gauss_rank_mod_p(M, p):
    """Compute rank of matrix over F_p via Gaussian elimination."""
    A = M.copy() % p
    rows, cols = A.shape
    rank = 0
    for col in range(cols):
        pivot = None
        for row in range(rank, rows):
            if A[row, col] % p != 0:
                pivot = row
                break
        if pivot is None:
            continue
        A[[rank, pivot]] = A[[pivot, rank]]
        inv_pivot = pow(int(A[rank, col]), p - 2, p)
        A[rank] = (A[rank] * inv_pivot) % p
        for row in range(rows):
            if row != rank and A[row, col] % p != 0:
                factor = A[row, col]
                A[row] = (A[row] - factor * A[rank]) % p
        rank += 1
    return rank

def solve_vandermonde_mod_p(V, s, p):
    """Solve V·e = s mod p. Returns e if solvable, None otherwise.
    V is (n-k)×w with n-k ≥ w. Uses least-squares via normal equations."""
    nk, w = V.shape
    # Augmented matrix [V | s]
    A = np.zeros((nk, w + 1), dtype=np.int64)
    A[:, :w] = V % p
    A[:, w] = s % p

    # Gauss elimination
    rank_aug = gauss_rank_mod_p(A, p)
    rank_V = gauss_rank_mod_p(V, p)

    if rank_aug > rank_V:
        return None  # inconsistent

    # Back-substitution (V has full column rank w)
    A2 = np.zeros((nk, w + 1), dtype=np.int64)
    A2[:, :w] = V % p
    A2[:, w] = s % p

    pivot_cols = []
    row = 0
    for col in range(w):
        found = False
        for r in range(row, nk):
            if A2[r, col] % p != 0:
                A2[[row, r]] = A2[[r, row]]
                found = True
                break
        if not found:
            continue
        pivot_cols.append(col)
        inv = pow(int(A2[row, col]), p - 2, p)
        A2[row] = (A2[row] * inv) % p
        for r in range(nk):
            if r != row and A2[r, col] % p != 0:
                f = A2[r, col]
                A2[r] = (A2[r] - f * A2[row]) % p
        row += 1

    if len(pivot_cols) < w:
        return None  # underdetermined (shouldn't happen for Vandermonde with w ≤ n-k)

    e = A2[:w, w] % p  # solution
    return e

def full_mode(n, p, k, w):
    """Full enumeration: iterate over all B, accumulate M(s)."""
    L = list(range(p))[:n]  # eval set = {0, 1, ..., n-1}
    nk = n - k
    c = nk - w
    d = w - c
    lam = comb(n, w) / p**c

    print(f"\n{'='*60}")
    print(f"FULL MODE: n={n}, k={k}, p={p}, w={w}, c={c}, d={d}")
    print(f"C(n,w) = {comb(n,w)}, λ = C(n,w)/p^c = {lam:.6f}")
    print(f"{'='*60}")

    # Dictionary: syndrome tuple -> M count
    M_counts = Counter()

    all_B = list(combinations(L, w))
    print(f"Enumerating {len(all_B)} subsets...")

    t0 = time.time()
    for idx, B in enumerate(all_B):
        V = vandermonde_matrix(L, B, nk, p)
        # Enumerate all e ∈ (F_p^*)^w
        # For each e, compute s = V·e mod p
        # This is the set of syndromes compatible with B

        # Generate all e ∈ {1,...,p-1}^w using numpy
        ranges = [np.arange(1, p) for _ in range(w)]
        grids = np.meshgrid(*ranges, indexing='ij')
        E = np.stack([g.ravel() for g in grids], axis=1)  # (p-1)^w × w

        # Compute S = V @ E^T mod p -> (n-k) × (p-1)^w
        S = (V @ E.T) % p

        # Each column of S is a syndrome
        for j in range(S.shape[1]):
            s_tuple = tuple(S[:, j].tolist())
            M_counts[s_tuple] += 1

        if (idx + 1) % 50 == 0:
            print(f"  {idx+1}/{len(all_B)} subsets processed ({time.time()-t0:.1f}s)")

    print(f"Done in {time.time()-t0:.1f}s")

    # Add zero counts for syndromes not seen
    total_syndromes = p**nk
    zero_count = total_syndromes - len(M_counts)

    # Build M distribution
    M_values = list(M_counts.values())
    M_dist = Counter(M_values)
    M_dist[0] = zero_count

    print(f"\nM distribution:")
    for m in sorted(M_dist.keys()):
        print(f"  M={m}: {M_dist[m]} syndromes ({M_dist[m]/total_syndromes*100:.4f}%)")

    # Factorial moments
    print(f"\nFactorial moments (vs Poisson(λ={lam:.6f})):")
    for kk in range(1, 6):
        # E[M^{(k)}] = E[M(M-1)...(M-k+1)]
        fac_mom = 0
        for m, count in M_dist.items():
            if m >= kk:
                prod = 1
                for i in range(kk):
                    prod *= (m - i)
                fac_mom += prod * count
        fac_mom /= total_syndromes
        poisson_pred = lam**kk
        ratio = fac_mom / poisson_pred if poisson_pred > 0 else float('inf')
        print(f"  k={kk}: E[M^{{({kk})}}] = {fac_mom:.6f}, λ^{kk} = {poisson_pred:.6f}, ratio = {ratio:.6f}")

    # Variance
    mean_M = sum(m * count for m, count in M_dist.items()) / total_syndromes
    var_M = sum(m**2 * count for m, count in M_dist.items()) / total_syndromes - mean_M**2
    print(f"\nE[M] = {mean_M:.6f} (pred: {lam:.6f})")
    print(f"Var[M] = {var_M:.6f} (Poisson pred: {lam:.6f})")
    print(f"Var/E = {var_M/mean_M:.6f} (Poisson: 1.000)")

    # Compare with Poisson distribution
    print(f"\nPoisson({lam:.4f}) comparison:")
    for m in sorted(M_dist.keys()):
        observed = M_dist[m] / total_syndromes
        poisson = exp(-lam) * lam**m / factorial(m) if m <= 20 else 0
        print(f"  P(M={m}): observed={observed:.6f}, Poisson={poisson:.6f}")

    return M_dist, M_counts

def sample_mode(n, p, k, w, num_samples=50000):
    """Sample random syndromes, compute M(s) for each."""
    L = list(range(p))[:n]
    nk = n - k
    c = nk - w
    d = w - c
    lam = comb(n, w) / p**c

    print(f"\n{'='*60}")
    print(f"SAMPLE MODE: n={n}, k={k}, p={p}, w={w}, c={c}, d={d}")
    print(f"C(n,w) = {comb(n,w)}, λ = C(n,w)/p^c = {lam:.6f}")
    print(f"Sampling {num_samples} syndromes")
    print(f"{'='*60}")

    # Precompute all Vandermonde matrices
    all_B = list(combinations(L, w))
    num_B = len(all_B)
    print(f"Precomputing {num_B} Vandermonde matrices...")

    V_list = []
    for B in all_B:
        V = vandermonde_matrix(L, B, nk, p)
        V_list.append(V)

    # Sample syndromes
    t0 = time.time()
    M_samples = []

    for trial in range(num_samples):
        s = np.random.randint(0, p, size=nk)
        M = 0
        for V in V_list:
            e = solve_vandermonde_mod_p(V, s, p)
            if e is not None and np.all(e % p != 0):
                M += 1
        M_samples.append(M)

        if (trial + 1) % 1000 == 0:
            print(f"  {trial+1}/{num_samples} ({time.time()-t0:.1f}s)")

    print(f"Done in {time.time()-t0:.1f}s")

    M_dist = Counter(M_samples)

    print(f"\nM distribution (from {num_samples} samples):")
    for m in sorted(M_dist.keys()):
        print(f"  M={m}: {M_dist[m]} ({M_dist[m]/num_samples*100:.2f}%)")

    # Factorial moments
    print(f"\nFactorial moments (vs Poisson(λ={lam:.6f})):")
    for kk in range(1, 6):
        fac_mom = 0
        for m in M_samples:
            if m >= kk:
                prod = 1
                for i in range(kk):
                    prod *= (m - i)
                fac_mom += prod
        fac_mom /= num_samples
        poisson_pred = lam**kk
        ratio = fac_mom / poisson_pred if poisson_pred > 0 else float('inf')
        print(f"  k={kk}: E[M^{{({kk})}}] = {fac_mom:.6f}, λ^{kk} = {poisson_pred:.6f}, ratio = {ratio:.6f}")

    mean_M = np.mean(M_samples)
    var_M = np.var(M_samples)
    print(f"\nE[M] = {mean_M:.6f} (pred: {lam:.6f})")
    print(f"Var[M] = {var_M:.6f} (Poisson pred: {lam:.6f})")
    print(f"Var/E = {var_M/mean_M:.6f} (Poisson: 1.000)")

    return M_dist

def verify_vandermonde_intersection(n, p, k, w, num_pairs=500):
    """Verify dim(Im(V_{B1}) ∩ Im(V_{B2})) = max(|B1∩B2|, d)."""
    L = list(range(p))[:n]
    nk = n - k
    c = nk - w
    d = w - c

    print(f"\n{'='*60}")
    print(f"VANDERMONDE INTERSECTION: n={n}, k={k}, p={p}, w={w}, c={c}, d={d}")
    print(f"{'='*60}")

    all_B = list(combinations(L, w))

    results = {}  # j -> list of actual dims

    for trial in range(num_pairs):
        idx1, idx2 = np.random.choice(len(all_B), 2, replace=False)
        B1, B2 = set(all_B[idx1]), set(all_B[idx2])
        j = len(B1 & B2)

        V1 = vandermonde_matrix(L, sorted(B1), nk, p)
        V2 = vandermonde_matrix(L, sorted(B2), nk, p)

        # Stack and compute rank
        V_union = np.hstack([V1, V2])
        rank_union = gauss_rank_mod_p(V_union, p)
        rank_1 = gauss_rank_mod_p(V1, p)
        rank_2 = gauss_rank_mod_p(V2, p)

        dim_intersection = rank_1 + rank_2 - rank_union
        predicted = max(j, d)

        if j not in results:
            results[j] = []
        results[j].append((dim_intersection, predicted))

    print(f"\nResults ({num_pairs} random pairs):")
    all_match = True
    for j in sorted(results.keys()):
        dims = results[j]
        matches = sum(1 for d_act, d_pred in dims if d_act == d_pred)
        mismatches = [(d_act, d_pred) for d_act, d_pred in dims if d_act != d_pred]
        print(f"  j={j}: {len(dims)} pairs, {matches}/{len(dims)} match max(j,d)={max(j,d)}")
        if mismatches:
            all_match = False
            print(f"    MISMATCHES: {mismatches[:5]}")

    print(f"\nAll match: {all_match}")
    return all_match

def factorial_moment_theory(n, p, k, w):
    """Compute theoretical factorial moments from Vandermonde intersection formula."""
    nk = n - k
    c = nk - w
    d = w - c
    lam = comb(n, w) / p**c

    print(f"\n{'='*60}")
    print(f"THEORETICAL FACTORIAL MOMENTS: n={n}, k={k}, p={p}, w={w}, c={c}, d={d}")
    print(f"λ = {lam:.6f}")
    print(f"{'='*60}")

    # E[M^{(2)}] = C(n,w)/p^{n-k} · Σ_{j=0}^{w-1} C(w,j)C(n-w,w-j) · p^{max(j,d)}
    # (excluding j=w which is B1=B2)

    total = 0.0
    print("\nContributions by overlap j:")
    for j in range(w):  # j = 0 to w-1
        N_j = comb(w, j) * comb(n - w, w - j)
        dim = max(j, d)
        contrib = N_j * (p ** dim)
        total += contrib
        if N_j > 0:
            normalized = comb(n, w) * contrib / p**nk
            print(f"  j={j}: N_j={N_j}, dim=max({j},{d})={dim}, "
                  f"contrib/p^{{n-k}}={comb(n,w)*contrib/p**nk:.6e}")

    E_M2_fact = comb(n, w) * total / p**nk
    print(f"\nE[M(M-1)] = {E_M2_fact:.6f}")
    print(f"λ^2 = {lam**2:.6f}")
    print(f"Ratio = {E_M2_fact/lam**2:.6f}" if lam > 0 else "λ = 0")

    # E[M] for reference
    E_M = comb(n, w) / p**c
    print(f"E[M] = {E_M:.6f}")

    # Var[M] = E[M(M-1)] + E[M] - E[M]^2
    Var_M = E_M2_fact + E_M - E_M**2
    print(f"Var[M] = {Var_M:.6f} (Poisson: {E_M:.6f})")

    return E_M2_fact

def main():
    configs = []

    # FULL mode configs (small enough for complete enumeration)
    # Need (p-1)^w * C(n,w) manageable, and p^{n-k} manageable
    full_configs = [
        # (n, p, k, w) - Johnson radius w = n - floor(sqrt(n(k-1)))
        (6, 7, 3, 2),     # c=1, d=1, lam = C(6,2)/7 = 15/7 ≈ 2.14
        (7, 7, 3, 3),     # c=1, d=2, lam = C(7,3)/7 = 5
        (8, 11, 4, 3),    # c=1, d=2
        (8, 11, 4, 2),    # c=2, d=0
        (10, 11, 5, 4),   # c=1, d=3
        (10, 11, 5, 3),   # c=2, d=1
        (8, 17, 4, 3),    # c=1, d=2
        (10, 17, 5, 4),   # c=1, d=3
        (10, 17, 5, 3),   # c=2, d=1
    ]

    # Verify Vandermonde intersection formula
    print("=" * 70)
    print("PART 1: VANDERMONDE INTERSECTION VERIFICATION")
    print("=" * 70)
    test_configs = [(10, 11, 5, 4), (10, 17, 5, 3), (12, 13, 6, 5)]
    for n, p, k, w in test_configs:
        verify_vandermonde_intersection(n, p, k, w, num_pairs=300)

    # Theoretical factorial moments
    print("\n" + "=" * 70)
    print("PART 2: THEORETICAL FACTORIAL MOMENTS")
    print("=" * 70)
    theory_configs = [
        (10, 11, 5, 4), (10, 11, 5, 3),
        (10, 17, 5, 4), (10, 17, 5, 3),
        (10, 31, 5, 4), (10, 31, 5, 3),
        (10, 101, 5, 4), (10, 101, 5, 3),
        (16, 17, 8, 6), (16, 97, 8, 6),
        (20, 41, 10, 7), (20, 101, 10, 7),
    ]
    for n, p, k, w in theory_configs:
        factorial_moment_theory(n, p, k, w)

    # Full enumeration
    print("\n" + "=" * 70)
    print("PART 3: FULL ENUMERATION (exact M distribution)")
    print("=" * 70)

    # Only do configs where (p-1)^w * C(n,w) is feasible
    # (p-1)^w ≤ 10^6 and C(n,w) ≤ 10^3
    feasible_full = []
    for n, p, k, w in full_configs:
        nk = n - k
        c = nk - w
        d = w - c
        work = (p - 1)**w * comb(n, w)
        if work <= 5e8 and c > 0:
            feasible_full.append((n, p, k, w))
            print(f"  Will enumerate: n={n}, p={p}, k={k}, w={w}, c={c}, d={d}, "
                  f"work={(p-1)**w}*{comb(n,w)}={work:.0f}")

    for n, p, k, w in feasible_full:
        full_mode(n, p, k, w)

    # Sample mode for larger configs
    print("\n" + "=" * 70)
    print("PART 4: SAMPLE MODE (larger configs)")
    print("=" * 70)
    sample_configs = [
        (10, 31, 5, 3, 20000),   # c=2, d=1
        (10, 101, 5, 3, 20000),  # c=2, d=1
        (12, 13, 6, 5, 10000),   # c=1, d=4
        (16, 17, 8, 6, 5000),    # c=2, d=4
    ]
    for n, p, k, w, ns in sample_configs:
        sample_mode(n, p, k, w, num_samples=ns)

if __name__ == "__main__":
    main()
