#!/usr/bin/env python3
"""
Distribution of M across random centers.

For given (n, p), sample many centers c_high and compute M(c_high)
via the linear compatibility conditions. Build histogram.

Key question: is M always ≈ C · N/p^c, or are there outlier centers?
"""

import math
import random
from itertools import combinations
from collections import Counter

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
    return pow(find_primitive_root(p), (p - 1) // n, p)


def elem_sym(roots, p):
    w = len(roots)
    e = [0] * (w + 1)
    e[0] = 1
    for r in roots:
        for j in range(w, 0, -1):
            e[j] = (e[j] + e[j - 1] * r) % p
    return e


def johnson_radius(n, k):
    return math.ceil((1 - math.sqrt(k / n)) * n)


# ================================================================
print("=" * 70)
print("M DISTRIBUTION ACROSS CENTERS")
print("=" * 70)

for n, p in [(6, 7), (8, 17), (10, 11), (10, 31), (12, 13), (12, 37),
             (14, 29), (14, 43), (16, 17), (16, 97)]:
    if (p - 1) % n != 0:
        continue
    k = n // 2
    w = johnson_radius(n, k)
    nk = n - k
    conds = nk - w
    N = math.comb(n, w)
    omega = find_omega(n, p)
    L = [pow(omega, i, p) for i in range(n)]

    print(f"\n{'='*70}")
    print(f"n={n}, k={k}, w={w}, conds={conds}, p={p}, N={N}, N/p^c={N/p**conds:.4f}")

    # Precompute σ for all B
    all_B = list(combinations(range(n), w))
    all_sigma = []  # all_sigma[b_idx] = [σ_0=1, σ_1, ..., σ_w]
    for B in all_B:
        roots = [L[i] for i in B]
        all_sigma.append(elem_sym(roots, p))

    # Sample centers and compute M
    n_centers = min(p**conds, 10000)  # sample at most 10000, or all if small
    if p**conds <= 10000:
        # Enumerate all centers
        centers = []
        def enum_centers(dim, prefix):
            if dim == 0:
                centers.append(prefix[:])
                return
            for v in range(p):
                prefix.append(v)
                enum_centers(dim - 1, prefix)
                prefix.pop()
        enum_centers(conds, [])
        # Actually for nk dims but the center is c_high = (c_k, ..., c_{n-1})
        # Wait, we need to be more careful. c_high has nk = n-k components.
        # The compatibility conditions use conds conditions, each involving
        # c_high values. Let me think...
        #
        # Actually, the conditions are:
        # D_m(σ) = Σ_{j=0}^{w} (-1)^j σ_j c_{m+j} = 0
        # for m = k, k+1, ..., n-1-w  (that's conds = nk-w equations)
        # Wait, let me recheck...
        # From Note 0064/0065: compatibility conditions are indexed by
        # m = k+w, ..., n-1, so there are n-1-(k+w)+1 = n-k-w = conds conditions.
        # D_m(σ) = Σ_{j=0}^w (-1)^j σ_j c_{m-w+j}
        # where c_{k}, ..., c_{n-1} are the "high" coefficients of the center.

        # So c_high has nk = n-k components: (c_k, c_{k+1}, ..., c_{n-1})
        # This is nk-dimensional, which could be large.
        # But M depends on c_high through the conds × w matrix D.
        # Two different c_high values can give the same D matrix.
        # Actually no, D depends on all of c_high.

        # For enumeration: we need to enumerate c_high ∈ F_p^{nk}, which is p^{nk}.
        # That's too many. Let's just sample randomly.
        pass

    # Random sampling
    M_values = []
    n_sample = min(10000, p**min(conds, 4))

    for _ in range(n_sample):
        c_high = [random.randint(0, p-1) for _ in range(nk)]

        # Compute M: count B's satisfying all conds compatibility conditions
        M = 0
        for b_idx in range(N):
            sigma = all_sigma[b_idx]
            compatible = True
            for m_off in range(conds):
                # Condition: Σ_{j=0}^{w} (-1)^j σ_j c_{k + (w + m_off) - w + j}
                # = Σ_j (-1)^j σ_j c_{k + m_off + j}
                # c_{k + m_off + j} = c_high[m_off + j] (since c_high[i] = c_{k+i})
                val = 0
                for j in range(w + 1):
                    idx = m_off + j
                    if idx < nk:
                        val = (val + pow(-1, j, p) * sigma[j] * c_high[idx]) % p
                if val % p != 0:
                    compatible = False
                    break
            if compatible:
                M += 1

        M_values.append(M)

    M_hist = Counter(M_values)
    print(f"  Sampled {n_sample} centers")
    print(f"  M histogram: {dict(sorted(M_hist.items()))}")
    print(f"  max M = {max(M_values)}")
    print(f"  avg M = {sum(M_values)/len(M_values):.2f}")
    print(f"  E[M] = N/p^c = {N/p**conds:.4f}")

    # Concentration: what fraction of centers have M > 2·N/p^c?
    threshold = max(2, int(2 * N / p**conds) + 1)
    frac_above = sum(1 for m in M_values if m > threshold) / len(M_values)
    print(f"  P(M > {threshold}) = {frac_above:.4f}")

    # The critical quantity: max M / (N/p^c)
    if N/p**conds > 0.01:
        print(f"  max M / (N/p^c) = {max(M_values) / (N/p**conds):.2f}")
