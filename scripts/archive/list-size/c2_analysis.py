#!/usr/bin/env python3
"""
Analyze the failure pattern of c ≥ 2 pairwise independence.

Key insight from c2_moment_bound.py:
- Failures happen EXACTLY when |E₁ ∩ E₂| ≥ w - 1

Why: at codimension c, the left kernel of V_E is spanned by
  {Λ_E(x), x·Λ_E(x), ..., x^{c-1}·Λ_E(x)}
where Λ_E is the error-locator polynomial.

When E₁ = S∪{a} and E₂ = S∪{b} share w-1 elements:
  Λ_{E₁} = (x-α_a)·Λ_S,  Λ_{E₂} = (x-α_b)·Λ_S
The 2c kernel vectors span only 2c-1 dimensions (not 2c).

This means: Pr[s ∈ flat_{E₁} ∩ flat_{E₂}] = 1/p^{2c-1} (not 1/p^{2c}).

Questions to answer:
1. Does E[M] = C(n,w)/p^c still hold? (YES - it's just first moment)
2. What is the exact Var[M]?
3. For which overlap levels does independence hold?
"""

from itertools import combinations
from math import comb
import time


def make_eval_points(n, p):
    assert p > n
    return list(range(1, n + 1))


def left_kernel_polys(alpha, E, D, p):
    """
    Return a basis for the left kernel of V_E as polynomials.

    The left kernel consists of coefficient vectors of polynomials P(x) of degree ≤ D-1
    that vanish at all α_e for e ∈ E.

    Basis: {Λ_E, x·Λ_E, ..., x^{c-1}·Λ_E} where c = D - |E|.
    """
    w = len(E)
    c = D - w

    # Error-locator polynomial Λ_E(x) = ∏(x - α_e)
    # Compute coefficients (degree w)
    coeffs = [1]  # start with 1
    for e in E:
        a = alpha[e]
        # Multiply by (x - a)
        new_coeffs = [0] * (len(coeffs) + 1)
        for i, c_val in enumerate(coeffs):
            new_coeffs[i + 1] = (new_coeffs[i + 1] + c_val) % p  # x term
            new_coeffs[i] = (new_coeffs[i] - a * c_val) % p       # constant term
        coeffs = new_coeffs

    # coeffs has degree w, length w+1
    # Pad to length D
    lambda_E = coeffs + [0] * (D - len(coeffs))

    # Basis: Λ_E, x·Λ_E, ..., x^{c-1}·Λ_E (as length-D coefficient vectors)
    basis = []
    current = lambda_E[:D]
    for shift in range(c):
        if shift == 0:
            vec = lambda_E[:D]
        else:
            # x^shift · Λ_E: shift coefficients up by `shift`
            vec = [0] * shift + lambda_E[:D - shift]
        basis.append([x % p for x in vec])

    return basis


def rank_of_vectors(vectors, p):
    """Compute rank of a list of vectors over F_p."""
    if not vectors:
        return 0
    n = len(vectors[0])
    m = len(vectors)

    M = [row[:] for row in vectors]
    current_row = 0
    for col in range(n):
        pivot = None
        for row in range(current_row, m):
            if M[row][col] % p != 0:
                pivot = row
                break
        if pivot is None:
            continue
        M[current_row], M[pivot] = M[pivot], M[current_row]
        inv = pow(M[current_row][col], p - 2, p)
        for j in range(n):
            M[current_row][j] = (M[current_row][j] * inv) % p
        for row in range(m):
            if row == current_row:
                continue
            factor = M[row][col]
            if factor != 0:
                for j in range(n):
                    M[row][j] = (M[row][j] - factor * M[current_row][j]) % p
        current_row += 1

    return current_row


def analyze_overlap_vs_rank(n, k, w, p):
    """
    For each pair (E₁, E₂) of w-subsets, compute:
    - overlap = |E₁ ∩ E₂|
    - combined rank of the 2c kernel vectors

    Group results by overlap.
    """
    alpha = make_eval_points(n, p)
    D = n - k
    c = D - w

    all_subsets = list(combinations(range(n), w))

    # Precompute kernel bases
    kernels = {}
    for E in all_subsets:
        kernels[E] = left_kernel_polys(alpha, E, D, p)

    # Analyze pairs
    overlap_rank = {}  # overlap -> list of ranks

    for i in range(len(all_subsets)):
        for j in range(i + 1, len(all_subsets)):
            E1, E2 = all_subsets[i], all_subsets[j]
            overlap = len(set(E1) & set(E2))
            combined = kernels[E1] + kernels[E2]
            r = rank_of_vectors(combined, p)

            key = overlap
            if key not in overlap_rank:
                overlap_rank[key] = {}
            overlap_rank[key][r] = overlap_rank[key].get(r, 0) + 1

    return overlap_rank, c


def compute_exact_moments(n, k, w, p):
    """
    Compute E[M] and Var[M] by direct enumeration over all syndromes.
    Only feasible for small parameters.
    """
    alpha = make_eval_points(n, p)
    D = n - k
    c = D - w

    all_subsets = list(combinations(range(n), w))

    # For each E, compute kernel basis
    kernels = {}
    for E in all_subsets:
        kernels[E] = left_kernel_polys(alpha, E, D, p)

    num_syndromes = p ** D
    if num_syndromes > 200000:
        return None

    # For each syndrome, count M(s)
    total_M = 0
    total_M2 = 0
    M_max = 0

    def iter_synd(dim, base):
        if dim == 0:
            yield ()
            return
        for x in range(base):
            for rest in iter_synd(dim - 1, base):
                yield (x,) + rest

    for s in iter_synd(D, p):
        M_s = 0
        for E in all_subsets:
            # Check if all kernel vectors annihilate s
            ok = True
            for nvec in kernels[E]:
                dot = sum(nvec[j] * s[j] for j in range(D)) % p
                if dot != 0:
                    ok = False
                    break
            if ok:
                M_s += 1
        total_M += M_s
        total_M2 += M_s * M_s
        if M_s > M_max:
            M_max = M_s

    E_M = total_M / num_syndromes
    E_M2 = total_M2 / num_syndromes
    Var_M = E_M2 - E_M * E_M

    return E_M, Var_M, M_max


def main():
    print("=" * 70)
    print("OVERLAP vs RANK ANALYSIS for c ≥ 2")
    print("=" * 70)

    cases = [
        (8, 4, 2, "RS[8,4] c=2 w=2"),
        (10, 5, 3, "RS[10,5] c=2 w=3"),
        (12, 6, 4, "RS[12,6] c=2 w=4"),
        (8, 4, 1, "RS[8,4] c=3 w=1"),
        (10, 5, 2, "RS[10,5] c=3 w=2"),
        (12, 6, 3, "RS[12,6] c=3 w=3"),
    ]

    p = 31  # large enough prime

    for n, k, w, desc in cases:
        if p <= n:
            continue
        D = n - k
        c = D - w

        print(f"\n{desc}: n={n}, k={k}, w={w}, D={D}, c={c}")
        overlap_rank, c_val = analyze_overlap_vs_rank(n, k, w, p)

        print(f"  Overlap | Rank distribution (expected full rank = 2c = {2*c})")
        for overlap in sorted(overlap_rank.keys(), reverse=True):
            rank_dist = overlap_rank[overlap]
            dist_str = ", ".join(f"rank={r}: {cnt}" for r, cnt in sorted(rank_dist.items()))
            total = sum(rank_dist.values())
            max_rank = max(rank_dist.keys())
            full = "✓ FULL" if max_rank == 2 * c and len(rank_dist) == 1 else f"✗ MAX={max_rank}"
            print(f"  |E₁∩E₂|={overlap:2d} | {total:6d} pairs | {full} | {dist_str}")

    # Now verify E[M] = C(n,w)/p^c for small cases
    print(f"\n{'=' * 70}")
    print("EXACT E[M] and Var[M] VERIFICATION")
    print(f"{'=' * 70}")

    small_cases = [
        (6, 3, 1, [7, 11, 13]),     # c=2, w=1
        (8, 4, 2, [11, 13]),         # c=2, w=2
        (8, 4, 1, [11, 13]),         # c=3, w=1
        (6, 3, 2, [7, 11, 13]),      # c=1, w=2 (baseline)
    ]

    for n, k, w, primes in small_cases:
        D = n - k
        c = D - w
        print(f"\nRS[{n},{k}] c={c} w={w}, C(n,w)={comb(n,w)}")

        for p in primes:
            if p <= n:
                continue
            predicted_EM = comb(n, w) / p ** c
            result = compute_exact_moments(n, k, w, p)
            if result is None:
                print(f"  p={p}: too large to enumerate")
                continue
            E_M, Var_M, M_max = result

            # Predicted variance from overlap analysis
            # Pairs with overlap = w-1 contribute extra covariance
            # Cov = 1/p^{2c-1} - 1/p^{2c} = (p-1)/p^{2c}
            num_overlap_pairs = comb(n, w) * w * (n - w) // 2  # unordered pairs sharing w-1
            # Actually this overcounts... let me just count: for each E, #E' with |E∩E'|=w-1
            # = w * (n-w) (replace one element)
            # Total unordered = C(n,w) * w * (n-w) / 2

            # But there might be other overlap levels contributing too
            # For now just check E[M]

            match_EM = abs(E_M - predicted_EM) < 1e-9
            print(f"  p={p:4d}: E[M] = {E_M:.6f}, predicted C(n,w)/p^c = {predicted_EM:.6f}, match = {match_EM}")
            print(f"          Var[M] = {Var_M:.6f}, E[M](1-1/p^c) = {predicted_EM*(1-1/p**c):.6f}, M_max = {M_max}")

            # Check: is Var[M] exactly = E[M](1-1/p^c) + something?
            pairwise_var = predicted_EM * (1 - 1 / p ** c)
            extra_var = Var_M - pairwise_var
            print(f"          Extra variance (beyond pairwise): {extra_var:.6f}")

    # Compute the theoretical extra variance from overlap
    print(f"\n{'=' * 70}")
    print("THEORETICAL VARIANCE PREDICTION")
    print(f"{'=' * 70}")

    for n, k, w, primes in small_cases:
        D = n - k
        c = D - w
        print(f"\nRS[{n},{k}] c={c} w={w}")

        for p in primes:
            if p <= n:
                continue

            alpha = make_eval_points(n, p)
            all_subsets = list(combinations(range(n), w))

            # Compute exact second moment via overlap structure
            # E[M²] = E[M] + sum_{E₁≠E₂} Pr[s ∈ flat_{E₁} ∩ flat_{E₂}]
            # = E[M] + sum_{E₁≠E₂} 1/p^{rank(combined normals)}

            kernels = {}
            for E in all_subsets:
                kernels[E] = left_kernel_polys(alpha, E, D, p)

            sum_joint = 0.0
            for i in range(len(all_subsets)):
                for j in range(i + 1, len(all_subsets)):
                    E1, E2 = all_subsets[i], all_subsets[j]
                    combined = kernels[E1] + kernels[E2]
                    r = rank_of_vectors(combined, p)
                    sum_joint += 2.0 / p ** r  # factor 2 for both orderings

            predicted_EM = comb(n, w) / p ** c
            predicted_EM2 = predicted_EM + sum_joint
            predicted_var = predicted_EM2 - predicted_EM ** 2

            result = compute_exact_moments(n, k, w, p)
            if result:
                E_M, Var_M, M_max = result
                print(f"  p={p}: Var predicted={predicted_var:.6f}, actual={Var_M:.6f}, match={abs(predicted_var-Var_M)<1e-6}")
            else:
                print(f"  p={p}: Var predicted={predicted_var:.6f} (exact enum too large)")


if __name__ == "__main__":
    main()
