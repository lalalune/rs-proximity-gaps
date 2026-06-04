#!/usr/bin/env python3
"""
Pairwise Rank Lemma — computational exploration.

For RS[n,k] on multiplicative subgroup L = <omega> of order n:
Each error set B (|B|=w) with agreement set S = L\B (|S|=n-w) imposes
(n-w-k) linear conditions on the syndrome s in F_p^{n-k}.

The conditions come from the LEFT KERNEL of V_S (the Vandermonde submatrix).

For two error sets B1, B2 with |B1 ∩ B2| = s:
Combined conditions = (n-w-k) from B1 + (n-w-k) from B2.
But some may be dependent.

Question: what is the RANK of the combined conditions?
Answer: 2(n-w-k) - Φ(s) for some function Φ(s).

This script computes Φ(s) for all pairs (B1, B2).
"""

from itertools import combinations
from math import comb


def find_primitive_root(p):
    factors = set()
    temp = p - 1
    d = 2
    while d * d <= temp:
        while temp % d == 0:
            factors.add(d)
            temp //= d
        d += 1
    if temp > 1:
        factors.add(temp)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in factors):
            return g


def find_omega(n, p):
    g = find_primitive_root(p)
    return pow(g, (p - 1) // n, p)


def rank_mod_p(mat, p):
    """Rank of matrix over F_p. mat is list of lists."""
    if not mat or not mat[0]:
        return 0
    m = len(mat)
    nn = len(mat[0])
    M = [row[:] for row in mat]  # copy
    for i in range(m):
        for j in range(nn):
            M[i][j] %= p
    rank = 0
    for col in range(nn):
        pivot = -1
        for row in range(rank, m):
            if M[row][col] % p != 0:
                pivot = row
                break
        if pivot == -1:
            continue
        M[rank], M[pivot] = M[pivot], M[rank]
        inv_pivot = pow(M[rank][col], p - 2, p)
        for row in range(m):
            if row != rank and M[row][col] % p != 0:
                factor = M[row][col] * inv_pivot % p
                for j in range(nn):
                    M[row][j] = (M[row][j] - factor * M[rank][j]) % p
        rank += 1
    return rank


def left_kernel_mod_p(mat, p):
    """Compute left kernel of mat over F_p.
    Returns list of vectors u such that u * mat = 0 mod p.
    mat is m x n. Left kernel has dimension m - rank(mat).
    """
    m = len(mat)
    n = len(mat[0])
    # Augment: [mat | I_m]^T, then row reduce mat^T and track
    # Actually: u * mat = 0 means mat^T * u^T = 0, so kernel of mat^T.
    # Transpose mat
    matT = [[mat[i][j] for i in range(m)] for j in range(n)]
    # matT is n x m. Find kernel of matT.
    return right_kernel_mod_p(matT, p)


def right_kernel_mod_p(mat, p):
    """Kernel of mat over F_p. mat is m x n. Returns basis of {x : mat*x = 0}."""
    if not mat:
        return []
    m = len(mat)
    n = len(mat[0])
    # Augment with identity
    aug = [mat[i][:] + [1 if j == i else 0 for j in range(m)] for i in range(m)]
    # Row reduce to find pivot columns
    M = [row[:] for row in mat]
    for i in range(m):
        for j in range(n):
            M[i][j] %= p

    pivot_cols = []
    rank = 0
    col_perm = list(range(n))

    for col in range(n):
        pivot = -1
        for row in range(rank, m):
            if M[row][col] % p != 0:
                pivot = row
                break
        if pivot == -1:
            continue
        M[rank], M[pivot] = M[pivot], M[rank]
        inv_pivot = pow(M[rank][col], p - 2, p)
        # Normalize pivot row
        for j in range(n):
            M[rank][j] = M[rank][j] * inv_pivot % p
        for row in range(m):
            if row != rank and M[row][col] % p != 0:
                factor = M[row][col]
                for j in range(n):
                    M[row][j] = (M[row][j] - factor * M[rank][j]) % p
        pivot_cols.append(col)
        rank += 1

    # Free columns
    free_cols = [c for c in range(n) if c not in pivot_cols]
    kernel = []
    for fc in free_cols:
        vec = [0] * n
        vec[fc] = 1
        for i, pc in enumerate(pivot_cols):
            vec[pc] = (-M[i][fc]) % p
        kernel.append(vec)
    return kernel


def get_conditions(S, L, k, p):
    """
    For agreement set S (list of indices into L), compute the
    (n-w-k) condition vectors in F_p^n.

    Each condition is a vector v in F_p^n such that v^T c = 0
    for any c that has a degree-<k polynomial passing through c|_S.

    These are the left kernel vectors of V_S (the Vandermonde submatrix).
    """
    n_w = len(S)
    # V_S: n_w x k matrix, V_S[j][l] = L[S[j]]^l mod p
    V_S = [[pow(L[S[j]], l, p) for l in range(k)] for j in range(n_w)]

    # Left kernel: vectors u (length n_w) with u^T V_S = 0
    lk = left_kernel_mod_p(V_S, p)

    # Embed into F_p^n
    n = len(L)
    conditions = []
    for u in lk:
        v = [0] * n
        for j, idx in enumerate(S):
            v[idx] = u[j] % p
        conditions.append(v)

    return conditions


def pairwise_rank_analysis(n, k, p, w):
    """Main analysis: for all pairs (B1, B2), compute combined rank vs overlap."""
    omega = find_omega(n, p)
    L = [pow(omega, i, p) for i in range(n)]
    conds_per_B = n - w - k

    print(f"=== n={n}, k={k}, p={p}, w={w} ===")
    print(f"  conds/B = {conds_per_B}, syndrome_dim = {n-k}")
    print(f"  #error_sets = C({n},{w}) = {comb(n, w)}")

    # Precompute all agreement sets and their conditions
    all_B = list(combinations(range(n), w))
    all_S = [[i for i in range(n) if i not in B] for B in all_B]
    all_conds = [get_conditions(S, L, k, p) for S in all_S]

    # Verify: each has conds_per_B conditions
    for i, conds in enumerate(all_conds):
        assert len(conds) == conds_per_B, f"B[{i}] has {len(conds)} conditions, expected {conds_per_B}"

    # Verify individual rank
    for i, conds in enumerate(all_conds):
        r = rank_mod_p(conds, p)
        assert r == conds_per_B, f"B[{i}] conditions have rank {r}, expected {conds_per_B}"

    # Full normal matrix rank
    all_flat = []
    for conds in all_conds:
        all_flat.extend(conds)
    full_rank = rank_mod_p(all_flat, p)
    print(f"  Full normal matrix rank: {full_rank} (should be {n-k})")

    # Pairwise analysis
    # For each pair (i, j), compute:
    #   overlap = |B_i ∩ B_j|
    #   combined_rank = rank of [conds_i ; conds_j]
    #   redundancy = 2*conds_per_B - combined_rank

    from collections import defaultdict
    overlap_to_ranks = defaultdict(list)

    num_pairs = len(all_B) * (len(all_B) - 1) // 2
    print(f"  Analyzing {num_pairs} pairs...")

    for i in range(len(all_B)):
        for j in range(i + 1, len(all_B)):
            overlap = len(set(all_B[i]) & set(all_B[j]))
            combined = all_conds[i] + all_conds[j]
            cr = rank_mod_p(combined, p)
            redundancy = 2 * conds_per_B - cr
            overlap_to_ranks[overlap].append((cr, redundancy, i, j))

    print(f"\n  overlap s | #pairs | combined_rank | redundancy Φ(s)")
    print(f"  {'-'*60}")
    for s in sorted(overlap_to_ranks.keys()):
        data = overlap_to_ranks[s]
        ranks = [d[0] for d in data]
        redunds = [d[1] for d in data]
        min_r, max_r = min(ranks), max(ranks)
        min_red, max_red = min(redunds), max(redunds)
        rank_str = f"{min_r}" if min_r == max_r else f"{min_r}-{max_r}"
        red_str = f"{min_red}" if min_red == max_red else f"{min_red}-{max_red}"
        print(f"  s={s:3d}     | {len(data):5d} | rank={rank_str:10s} | Φ={red_str}")

    # Also: for M-tuples (M = 3, 4, ...), compute the combined rank
    print(f"\n  Multi-set rank analysis:")
    for M in range(3, min(8, len(all_B) + 1)):
        # Sample some M-tuples
        import random
        random.seed(42)
        max_rank_seen = 0
        min_rank_seen = n
        trials = min(500, comb(len(all_B), M))
        if comb(len(all_B), M) <= 500:
            # Exhaustive
            for combo in combinations(range(len(all_B)), M):
                combined = []
                for idx in combo:
                    combined.extend(all_conds[idx])
                cr = rank_mod_p(combined, p)
                max_rank_seen = max(max_rank_seen, cr)
                min_rank_seen = min(min_rank_seen, cr)
        else:
            # Sample
            for _ in range(trials):
                combo = tuple(sorted(random.sample(range(len(all_B)), M)))
                combined = []
                for idx in combo:
                    combined.extend(all_conds[idx])
                cr = rank_mod_p(combined, p)
                max_rank_seen = max(max_rank_seen, cr)
                min_rank_seen = min(min_rank_seen, cr)

        print(f"  M={M}: rank in [{min_rank_seen}, {max_rank_seen}], max possible = min({M}*{conds_per_B}, {n-k}) = {min(M*conds_per_B, n-k)}")

    return overlap_to_ranks


# Run for small cases
print("="*70)
pairwise_rank_analysis(6, 3, 7, 2)

print("\n" + "="*70)
pairwise_rank_analysis(8, 4, 17, 3)

print("\n" + "="*70)
pairwise_rank_analysis(10, 5, 11, 3)

print("\n" + "="*70)
pairwise_rank_analysis(12, 6, 13, 4)

# Also test n=14, k=7
print("\n" + "="*70)
pairwise_rank_analysis(14, 7, 29, 5)
