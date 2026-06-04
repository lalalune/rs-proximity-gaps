#!/usr/bin/env python3
"""
Verify the generalization of pairwise independence from c=1 to c>=2.

Paper proved (c=1): error-locator normals are pairwise independent.
  => E[M] = C(n,w)/p, Var[M] = E[M](1-1/p)

We verify (c>=2): for the Berlekamp parallelism problem,
  X(b) = #{E : pi_E(a) || pi_E(b)} = #{E : a in W_E(b)}
  where W_E(b) = V_E + <b>, codim m-1.

Claim: for |E1 cap E2| <= w - m, the indicators 1_{a in W_{E1}(b)}
and 1_{a in W_{E2}(b)} are pairwise uncorrelated (for random a).

This would give:
  E[X] = C(n,w)/p^{m-1}
  Var[X] = E[X](1 - 1/p^{m-1}) + (correction from pairs with j > w-m)

Strategy:
1. For each pair (E1, E2) with intersection size j, compute
   P(a in W_{E1}(b) ∩ W_{E2}(b)) empirically
2. Compare with 1/p^{2(m-1)} (independence) vs actual

Also verify the algebraic claim: the 2c normals from E1, E2
(coefficients of Lambda_E * x^i) are linearly independent when j <= w-c.
"""
import numpy as np
from itertools import combinations
from math import comb
import sys

sys.stdout = open(sys.stdout.fileno(), mode='w', buffering=1)
np.random.seed(42)


def build_parity_check(L, k, p):
    """Build (n-k) x n Vandermonde parity-check matrix."""
    n = len(L)
    nk = n - k
    H = np.zeros((nk, n), dtype=np.int64)
    for i in range(nk):
        for j in range(n):
            H[i, j] = pow(int(L[j]), i, p)
    return H


def error_locator_coeffs(subset, L, p):
    """Compute coefficients of Lambda_E(x) = prod(x - alpha_e) mod p."""
    # Returns [Lambda_0, ..., Lambda_w] where Lambda_w = 1 (monic)
    w = len(subset)
    coeffs = [1]  # start with constant polynomial 1
    for idx in subset:
        alpha = L[idx]
        new_coeffs = [0] * (len(coeffs) + 1)
        for i, c in enumerate(coeffs):
            new_coeffs[i + 1] = (new_coeffs[i + 1] + c) % p  # x * old
            new_coeffs[i] = (new_coeffs[i] - alpha * c) % p   # -alpha * old
        coeffs = new_coeffs
    return [c % p for c in coeffs]


def rank_mod_p(M, p):
    """Rank of integer matrix mod p."""
    M = M.copy() % p
    rows, cols = M.shape
    rank = 0
    for col in range(cols):
        pivot = -1
        for row in range(rank, rows):
            if M[row, col] % p != 0:
                pivot = row
                break
        if pivot == -1:
            continue
        M[[rank, pivot]] = M[[pivot, rank]]
        inv = pow(int(M[rank, col]), p - 2, p)
        M[rank] = (M[rank] * inv) % p
        for row in range(rows):
            if row != rank and M[row, col] != 0:
                M[row] = (M[row] - int(M[row, col]) * M[rank]) % p
        rank += 1
    return rank


def test_normal_independence(p, n, k, w):
    """Test that 2c normals from (E1, E2) are lin. indep. when j <= w-c."""
    L = list(range(1, n + 1))
    c = n - k - w  # = m
    D = n - k

    print(f"\n{'='*70}")
    print(f"TEST: Normal independence for RS[F_{p}, n={n}, k={k}], w={w}, c=m={c}")
    print(f"Prediction: 2c={2*c} normals independent when j <= w-c = {w-c}")
    print(f"{'='*70}")

    all_subsets = list(combinations(range(n), w))
    if len(all_subsets) > 2000:
        # Sample pairs
        num_pairs = 3000
        pairs = []
        for _ in range(num_pairs):
            i1, i2 = np.random.choice(len(all_subsets), 2, replace=False)
            pairs.append((all_subsets[i1], all_subsets[i2]))
    else:
        pairs = [(all_subsets[i], all_subsets[j])
                 for i in range(len(all_subsets))
                 for j in range(i+1, len(all_subsets))]
        if len(pairs) > 5000:
            idx = np.random.choice(len(pairs), 5000, replace=False)
            pairs = [pairs[i] for i in idx]

    # Group by intersection size j
    results = {}  # j -> (num_tested, num_full_rank)

    for E1, E2 in pairs:
        j = len(set(E1) & set(E2))

        # Build 2c normal vectors
        # For E_i: normals are coeff vectors of Lambda_{E_i}(x) * x^r, r=0,...,c-1
        # Each such polynomial has degree w + r < D = w + c, fits in D coords

        coeffs1 = error_locator_coeffs(E1, L, p)  # degree w, w+1 coefficients
        coeffs2 = error_locator_coeffs(E2, L, p)

        normal_matrix = np.zeros((2 * c, D), dtype=np.int64)

        for r in range(c):
            # Lambda_{E1} * x^r: shift coefficients by r positions
            for i, coeff in enumerate(coeffs1):
                if i + r < D:
                    normal_matrix[r, i + r] = coeff % p
            # Lambda_{E2} * x^r
            for i, coeff in enumerate(coeffs2):
                if i + r < D:
                    normal_matrix[c + r, i + r] = coeff % p

        rk = rank_mod_p(normal_matrix, p)

        if j not in results:
            results[j] = [0, 0]
        results[j][0] += 1
        if rk == 2 * c:
            results[j][1] += 1

    print(f"\n{'j':>3} | {'tested':>7} | {'rank=2c':>7} | {'rate':>7} | {'prediction':>12}")
    print("-" * 55)
    for j in sorted(results.keys()):
        tested, full = results[j]
        rate = full / tested if tested > 0 else 0
        pred = "INDEPENDENT" if j <= w - c else f"dep (rank<{2*c})"
        print(f"{j:3d} | {tested:7d} | {full:7d} | {rate:7.4f} | {pred}")


def test_berlekamp_pairwise(p, n, k, w, num_b=5, num_a=2000):
    """
    Empirically verify pairwise independence of Berlekamp indicators.

    For fixed b, X = #{E : a in W_E(b)}, where W_E(b) = V_E + <b>.
    Compute P(a in W_{E1}(b) ∩ W_{E2}(b)) grouped by j = |E1∩E2|.
    Compare with 1/p^{2(m-1)} (independent) vs 1/p^{codim} (actual).
    """
    L = list(range(1, n + 1))
    m = n - k - w
    D = n - k
    H = build_parity_check(L, k, p)

    print(f"\n{'='*70}")
    print(f"BERLEKAMP PAIRWISE: RS[F_{p}, n={n}, k={k}], w={w}, m={m}")
    print(f"E[X] = C(n,w)/p^(m-1) = {comb(n,w)}/{p**(m-1)} = {comb(n,w)/p**(m-1):.2f}")
    print(f"Independent P = 1/p^{{2(m-1)}} = {1/p**(2*(m-1)):.2e}")
    print(f"{'='*70}")

    all_subsets = list(combinations(range(n), w))
    num_subsets = len(all_subsets)

    # Precompute projection matrices for each E
    # pi_E: F_p^D -> V_E^perp (dim m)
    # We store the null space basis of V_E^T (the rows that annihilate V_E)
    print(f"Precomputing {num_subsets} projection bases...")

    null_bases = []
    for E in all_subsets:
        H_E = H[:, list(E)]  # D x w
        # Row reduce H_E^T to find null space of H_E^T
        A = H_E.T.copy() % p  # w x D
        pivot_cols = []
        rank = 0
        for col in range(D):
            found = -1
            for row in range(rank, w):
                if A[row, col] % p != 0:
                    found = row
                    break
            if found == -1:
                continue
            A[[rank, found]] = A[[found, rank]]
            inv = pow(int(A[rank, col]), p - 2, p)
            A[rank] = (A[rank] * inv) % p
            for row in range(w):
                if row != rank and A[row, col] != 0:
                    A[row] = (A[row] - int(A[row, col]) * A[rank]) % p
            pivot_cols.append(col)
            rank += 1

        free_cols = [c for c in range(D) if c not in pivot_cols]
        null_basis = np.zeros((len(free_cols), D), dtype=np.int64)
        for idx, fc in enumerate(free_cols):
            null_basis[idx, fc] = 1
            for r, pc in enumerate(pivot_cols):
                null_basis[idx, pc] = (-A[r, fc]) % p
        null_bases.append(null_basis % p)

    # Sample pairs grouped by j
    # For each b, for each pair, count how many random a's are in both W_E1(b) and W_E2(b)

    # Select representative pairs for each j value
    print("Selecting representative pairs...")
    pairs_by_j = {}
    max_pairs_per_j = 50

    for _ in range(20000):
        i1, i2 = np.random.choice(num_subsets, 2, replace=False)
        E1, E2 = all_subsets[i1], all_subsets[i2]
        j = len(set(E1) & set(E2))
        if j not in pairs_by_j:
            pairs_by_j[j] = []
        if len(pairs_by_j[j]) < max_pairs_per_j:
            pairs_by_j[j].append((i1, i2))

    print(f"\nj values found: {sorted(pairs_by_j.keys())}")

    # For each b, for each (E1, E2) pair, empirically compute joint probability
    joint_probs = {j: [] for j in pairs_by_j}

    for b_trial in range(num_b):
        b = np.random.randint(0, p, size=D).astype(np.int64)
        while np.all(b == 0):
            b = np.random.randint(0, p, size=D).astype(np.int64)

        # Precompute pi_E(b) for each E
        pi_b = []
        for basis in null_bases:
            proj = np.array([(basis[i] @ b) % p for i in range(len(basis))], dtype=np.int64)
            pi_b.append(proj % p)

        for j, pair_list in pairs_by_j.items():
            for i1, i2 in pair_list:
                # Check: a in W_{E1}(b) iff pi_{E1}(a) || pi_{E1}(b)
                # i.e., pi_{E1}(a) = lambda * pi_{E1}(b)
                # For random a, count how many satisfy BOTH conditions

                pb1 = pi_b[i1]  # m-vector
                pb2 = pi_b[i2]

                # Skip if b in V_E (pi_E(b) = 0)
                if np.all(pb1 == 0) or np.all(pb2 == 0):
                    continue

                basis1 = null_bases[i1]
                basis2 = null_bases[i2]

                count_both = 0
                count_e1 = 0
                count_e2 = 0

                for _ in range(num_a):
                    a = np.random.randint(0, p, size=D).astype(np.int64)

                    # pi_{E1}(a)
                    pa1 = np.array([(basis1[r] @ a) % p for r in range(m)],
                                   dtype=np.int64) % p
                    # pi_{E2}(a)
                    pa2 = np.array([(basis2[r] @ a) % p for r in range(m)],
                                   dtype=np.int64) % p

                    # Check parallelism: pa || pb iff all 2x2 minors = 0
                    def is_parallel(u, v, p_val):
                        for i in range(len(u)):
                            for j2 in range(i+1, len(u)):
                                if (int(u[i])*int(v[j2]) - int(u[j2])*int(v[i])) % p_val != 0:
                                    return False
                        return True

                    par1 = is_parallel(pa1, pb1, p)
                    par2 = is_parallel(pa2, pb2, p)

                    if par1:
                        count_e1 += 1
                    if par2:
                        count_e2 += 1
                    if par1 and par2:
                        count_both += 1

                p_both = count_both / num_a
                p_e1 = count_e1 / num_a
                p_e2 = count_e2 / num_a
                p_indep = p_e1 * p_e2

                joint_probs[j].append((p_both, p_indep, p_e1, p_e2))

    # Report
    print(f"\n{'j':>3} | {'pairs':>5} | {'P(both)':>10} | {'P(E1)P(E2)':>10} | "
          f"{'ratio':>7} | {'1/p^2(m-1)':>10} | {'theory':>10}")
    print("-" * 80)

    indep_val = 1 / p**(2*(m-1))

    for j in sorted(joint_probs.keys()):
        data = joint_probs[j]
        if not data:
            continue
        avg_both = np.mean([d[0] for d in data])
        avg_indep = np.mean([d[1] for d in data])
        avg_e1 = np.mean([d[2] for d in data])

        ratio = avg_both / indep_val if indep_val > 0 else float('inf')

        # Theoretical codimension
        if j <= w - m:
            theory_codim = 2 * (m - 1)
            theory_p = 1 / p**theory_codim
        elif j <= w - m + 1:
            theory_codim = 2 * (m - 1)  # still independent for j = w-m+1 in Berlekamp
            theory_p = 1 / p**theory_codim
        else:
            overlap_dim = j - (w - m) - 1  # dim of (V1^perp ∩ V2^perp) ∩ b^perp
            theory_codim = 2 * (m - 1) - overlap_dim
            theory_p = 1 / p**theory_codim

        print(f"{j:3d} | {len(data):5d} | {avg_both:10.6f} | {avg_indep:10.6f} | "
              f"{ratio:7.2f} | {indep_val:10.2e} | {theory_p:10.2e}")


# Test 1: Normal independence (algebraic verification)
test_normal_independence(251, 18, 9, 7)  # c=m=2, w-c=5
test_normal_independence(251, 20, 10, 7)  # c=m=3, w-c=4

# Test 2: Berlekamp pairwise independence (empirical)
print("\n" + "=" * 70)
print("EMPIRICAL VERIFICATION OF BERLEKAMP PAIRWISE INDEPENDENCE")
print("=" * 70)
test_berlekamp_pairwise(251, 18, 9, 7, num_b=3, num_a=3000)
# n=20 has m=3, so 1/p^{2(m-1)} = 1/251^4 ~ very small, need many samples
# Use smaller p for n=20 test
test_berlekamp_pairwise(31, 12, 6, 4, num_b=3, num_a=5000)  # m=2, p=31
