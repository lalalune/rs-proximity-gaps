#!/usr/bin/env python3
"""
Deep rank analysis: find worst-case M-tuples and their full rank structure.

For each (n,k,w,p):
1. Find the syndrome achieving maximum M
2. List the M error sets
3. Show pairwise overlaps
4. Show rank of every subset of the M error sets' conditions
5. Identify the exact dependencies
"""

from itertools import combinations
from math import comb
from collections import defaultdict


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
    if not mat or not mat[0]:
        return 0
    m = len(mat)
    nn = len(mat[0])
    M = [row[:] for row in mat]
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
    m = len(mat)
    n = len(mat[0])
    matT = [[mat[i][j] for i in range(m)] for j in range(n)]
    return right_kernel_mod_p(matT, p)


def right_kernel_mod_p(mat, p):
    if not mat:
        return []
    m = len(mat)
    n = len(mat[0])
    M = [row[:] for row in mat]
    for i in range(m):
        for j in range(n):
            M[i][j] %= p
    pivot_cols = []
    rank = 0
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
        for j in range(n):
            M[rank][j] = M[rank][j] * inv_pivot % p
        for row in range(m):
            if row != rank and M[row][col] % p != 0:
                factor = M[row][col]
                for j in range(n):
                    M[row][j] = (M[row][j] - factor * M[rank][j]) % p
        pivot_cols.append(col)
        rank += 1
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
    n_w = len(S)
    V_S = [[pow(L[S[j]], l, p) for l in range(k)] for j in range(n_w)]
    lk = left_kernel_mod_p(V_S, p)
    n = len(L)
    conditions = []
    for u in lk:
        v = [0] * n
        for j, idx in enumerate(S):
            v[idx] = u[j] % p
        conditions.append(v)
    return conditions


def find_worst_case(n, k, p, w):
    """Find worst-case syndrome and its M error sets using exhaustive FFT-like approach."""
    omega = find_omega(n, p)
    L = [pow(omega, i, p) for i in range(n)]

    # For each center c in F_p^n, count list size at distance w.
    # Too expensive for large p^n. Instead:
    # For each error set B, the condition on c is: V_S * a = c|_S for some degree-<k poly.
    # This means c|_S ∈ col(V_S).
    #
    # Strategy: find syndromes with max list size.
    # Use the syndrome representation: s = Hc where H is parity check.
    # Each error set B defines a (n-w-k)-codimensional affine subspace of syndromes.
    # Find the syndrome in the most subspaces.

    # For small syndrome space: enumerate all syndromes.
    syn_dim = n - k
    if p ** syn_dim > 5_000_000:
        print(f"  Syndrome space too large ({p}^{syn_dim}={p**syn_dim}), using sampling")
        return None

    # Parity check matrix H: H[r][i] = L[i]^(k+r) mod p
    H = [[pow(L[i], k + r, p) for i in range(n)] for r in range(syn_dim)]

    # For each error set B with agreement S:
    # The condition on syndrome s: ∃ poly a of degree <k with V_S*a = c|_S
    # where c is such that Hc = s.
    # Since the condition is "c|_S lies in col(V_S)", and col(V_S) has dimension k,
    # the condition on c|_S has codimension n-w-k in the |S|-dim space.
    # Translating to syndrome space...

    # Actually, let me use a different approach.
    # For each error set B (|B| = w):
    #   The set of valid syndromes = {Hc : c agrees with some RS codeword on S}
    #   = {Hc : c - f vanishes on S for some f ∈ RS_k}
    #   = {Hc : c_i = f(L[i]) for i ∈ S, f degree <k}
    #   = {H(f + e) : f ∈ RS_k, supp(e) ⊆ B}
    #   = {Hf + He : f ∈ RS_k, supp(e) ⊆ B}
    #   = {He : supp(e) ⊆ B}  (since Hf = 0 for f ∈ RS_k)

    # So the valid syndrome set for B = {He : supp(e) ⊆ B} = span{H_col[b] : b ∈ B}
    # Wait, He = sum_{b ∈ B} e_b * H_col[b] where H_col[b] = (L[b]^k, ..., L[b]^{n-1}).
    # So the valid syndromes form a w-dimensional subspace (since H restricted to B has rank w,
    # assuming w ≤ n-k, which it is at Johnson).

    # Actually w ≤ n-k only if w ≤ n-k. For rate 1/2, w ≈ 0.29n < 0.5n = n-k. Yes.

    # So the valid syndrome set for B is a w-dimensional subspace of F_p^{n-k}.
    # The syndrome s achieves list codeword via B iff s ∈ span{H_col[b] : b ∈ B}.

    # Now: M = max_s |{B : s ∈ span(H_B)}|.

    # For each B, the valid syndromes are a w-dim subspace.
    # Each subspace has p^w elements.
    # Total incidences = C(n,w) * p^w.
    # Average per syndrome = C(n,w) * p^w / p^{n-k} = C(n,w) / p^{n-k-w}.

    # For our cases: this is small. The max M is what we want.

    # Compute: for each syndrome s, count the number of error sets B with s ∈ span(H_B).

    # s ∈ span(H_B) iff s = sum_{b ∈ B} e_b H_col[b], i.e., s is in the column span
    # of the matrix H_B = [H_col[b] for b ∈ B].

    # Equivalently: the augmented matrix [H_B | s] has the same rank as H_B.
    # Since H_B has rank w (MDS): [H_B | s] has rank w iff s ∈ col(H_B).

    all_B = list(combinations(range(n), w))

    # For each B, compute col(H_B) as a set of syndrome vectors
    # This is a w-dim subspace of F_p^{n-k}.
    # Represent each subspace by its reduced basis.

    # For small p^{n-k}: just enumerate all syndromes in each subspace.

    print(f"  Computing valid syndromes for {len(all_B)} error sets...")

    # H columns: syn_dim-dimensional vectors
    H_cols = [[H[r][i] % p for r in range(syn_dim)] for i in range(n)]

    syndrome_count = defaultdict(list)  # syndrome_tuple -> list of B indices

    for b_idx, B in enumerate(all_B):
        # Enumerate all syndromes in span(H_cols[b] for b in B)
        # This is p^w elements. For w ≤ 5 and p small, feasible.
        cols = [H_cols[b] for b in B]
        # Generate all linear combinations
        if p ** w > 500000:
            # Too many — use membership test instead
            # Compute the subspace basis
            continue

        def enum_span(cols, p, dim):
            """Enumerate all elements of span(cols) over F_p."""
            if not cols:
                yield tuple([0] * dim)
                return
            first = cols[0]
            rest = cols[1:]
            for sub in enum_span(rest, p, dim):
                for c in range(p):
                    yield tuple((c * first[r] + sub[r]) % p for r in range(dim))

        for s_tuple in enum_span(cols, p, syn_dim):
            syndrome_count[s_tuple].append(b_idx)

    if not syndrome_count:
        print("  Too large, skipping")
        return None

    # Find max M
    max_M = 0
    best_syndrome = None
    best_B_indices = None
    for s, b_list in syndrome_count.items():
        if len(b_list) > max_M:
            max_M = len(b_list)
            best_syndrome = s
            best_B_indices = b_list

    print(f"  Max M = {max_M}")
    return all_B, best_syndrome, best_B_indices, H_cols, L


def deep_analysis(n, k, p, w):
    print(f"\n{'='*70}")
    print(f"Deep analysis: n={n}, k={k}, p={p}, w={w}")
    print(f"conds/B = {n-w-k}, syndrome_dim = {n-k}")

    result = find_worst_case(n, k, p, w)
    if result is None:
        return

    all_B, best_syndrome, best_B_indices, H_cols, L = result
    M = len(best_B_indices)

    # Get conditions for the M worst-case error sets
    all_S = [[i for i in range(n) if i not in all_B[idx]] for idx in best_B_indices]
    all_conds = [get_conditions(S, L, k, p) for S in all_S]

    c_per_B = n - w - k

    print(f"\n  Worst-case M = {M} error sets:")
    for i, idx in enumerate(best_B_indices):
        B = all_B[idx]
        S = all_S[i]
        print(f"    B_{i} = {B}, S_{i} = {S}")

    # Pairwise overlaps
    print(f"\n  Pairwise overlap matrix (|B_i ∩ B_j|):")
    for i in range(M):
        row = []
        for j in range(M):
            if i == j:
                row.append(f"{w:2d}")
            else:
                ov = len(set(all_B[best_B_indices[i]]) & set(all_B[best_B_indices[j]]))
                row.append(f"{ov:2d}")
        print(f"    [{', '.join(row)}]")

    # Agreement set overlaps
    print(f"\n  Agreement set overlap (|S_i ∩ S_j|):")
    for i in range(M):
        row = []
        for j in range(M):
            if i == j:
                row.append(f"{n-w:2d}")
            else:
                ov = len(set(all_S[i]) & set(all_S[j]))
                row.append(f"{ov:2d}")
        print(f"    [{', '.join(row)}]")

    # Cumulative rank: rank of conditions from first i error sets
    print(f"\n  Cumulative rank (adding error sets one by one):")
    cumulative = []
    for i in range(M):
        cumulative.extend(all_conds[i])
        r = rank_mod_p(cumulative, p)
        print(f"    After B_0..B_{i}: rank = {r} (added {c_per_B}, expected {min((i+1)*c_per_B, n-k)})")

    # Rank of every pair
    if M <= 10:
        print(f"\n  Pairwise combined rank:")
        for i in range(M):
            for j in range(i+1, M):
                combined = all_conds[i] + all_conds[j]
                r = rank_mod_p(combined, p)
                ov = len(set(all_B[best_B_indices[i]]) & set(all_B[best_B_indices[j]]))
                redundancy = 2*c_per_B - r
                print(f"    B_{i},B_{j}: overlap={ov}, rank={r}, Φ={redundancy}")

    # Rank of every triple
    if M >= 3 and M <= 8:
        print(f"\n  Triple combined rank (sample):")
        count = 0
        for combo in combinations(range(M), 3):
            combined = []
            for idx in combo:
                combined.extend(all_conds[idx])
            r = rank_mod_p(combined, p)
            expected = min(3 * c_per_B, n - k)
            redundancy = 3 * c_per_B - r
            overlaps = []
            for a, b in combinations(combo, 2):
                ov = len(set(all_B[best_B_indices[a]]) & set(all_B[best_B_indices[b]]))
                overlaps.append(ov)
            print(f"    {combo}: rank={r}/{expected}, Φ={redundancy}, overlaps={overlaps}")
            count += 1
            if count >= 35:
                print(f"    ... ({comb(M,3) - 35} more)")
                break

    # Full M-set rank
    all_combined = []
    for conds in all_conds:
        all_combined.extend(conds)
    full_r = rank_mod_p(all_combined, p)
    print(f"\n  Full {M}-set rank: {full_r} (max {n-k}, total conditions = {M*c_per_B})")
    print(f"  Total redundancy: {M*c_per_B - full_r}")

    # The condition vectors themselves
    if n <= 10:
        print(f"\n  Condition vectors (in F_{p}^{n}):")
        for i, conds in enumerate(all_conds):
            for j, v in enumerate(conds):
                print(f"    B_{i} cond {j}: {v}")


# Run for key cases
# conds/B = 1
deep_analysis(6, 3, 7, 2)
deep_analysis(8, 4, 17, 3)

# conds/B = 2
deep_analysis(10, 5, 11, 3)
deep_analysis(12, 6, 13, 4)

# conds/B = 3
# n=16, k=8, w_J = ceil(0.293*16) = 5. conds/B = 16-5-8 = 3
# Need p with n | (p-1), so 16 | (p-1). p=17 works.
deep_analysis(16, 8, 17, 5)
