#!/usr/bin/env python3
"""
Verify k-wise independence of error-locator normals.

Key question: for k distinct w-subsets E_1,...,E_k with pairwise |E_i ∩ E_j| ≤ w-c,
are the kc normal vectors {Λ_{E_i} · x^r : 1 ≤ i ≤ k, 0 ≤ r < c} linearly independent?

If YES for all k ≤ D/c: then M(s) ≤ D/c for ALL syndromes s.
This would resolve OP2 (worst-case bound).

We also compute the actual worst-case M(s) = max_s |{E : s ∈ W_E}| by brute force.
"""
import sys
from itertools import combinations
from math import comb
import random

sys.stdout = open(sys.stdout.fileno(), mode='w', buffering=1)


def poly_coeffs(roots, p):
    """Compute coefficients of Λ_E = ∏(x - r) mod p. Returns [a_0, a_1, ..., a_w] (a_w = 1)."""
    coeffs = [1]
    for r in roots:
        new = [0] * (len(coeffs) + 1)
        for i, c in enumerate(coeffs):
            new[i] = (new[i] - c * r) % p
            new[i + 1] = (new[i + 1] + c) % p
        coeffs = new
    return coeffs


def poly_mult_xr(coeffs, r, max_deg, p):
    """Multiply polynomial by x^r, return coefficient vector of length max_deg+1."""
    result = [0] * (max_deg + 1)
    for i, c in enumerate(coeffs):
        if i + r <= max_deg:
            result[i + r] = c % p
    return result


def rank_mod_p(matrix, p):
    """Compute rank of matrix over F_p via Gaussian elimination."""
    if not matrix:
        return 0
    m = len(matrix)
    n = len(matrix[0])
    mat = [row[:] for row in matrix]
    rank = 0
    for col in range(n):
        pivot = None
        for row in range(rank, m):
            if mat[row][col] % p != 0:
                pivot = row
                break
        if pivot is None:
            continue
        mat[rank], mat[pivot] = mat[pivot], mat[rank]
        inv = pow(mat[rank][col], p - 2, p)
        for j in range(n):
            mat[rank][j] = (mat[rank][j] * inv) % p
        for row in range(m):
            if row != rank and mat[row][col] % p != 0:
                factor = mat[row][col]
                for j in range(n):
                    mat[row][j] = (mat[row][j] - factor * mat[rank][j]) % p
        rank += 1
    return rank


def test_kwise_independence(n, w, p, k_max=None, sample_size=1000):
    """Test k-wise independence for RS[F_p, n, k_code] with w errors."""
    L = list(range(n))
    D = n  # parity check has D rows (for our syndrome space, D = n - k_code, but
           # we parameterize by c = D - w directly)
    # Actually, we need to be careful. In the paper:
    # RS[F_p, n, k] has dimension k, distance D = n - k (or n-k+1 for MDS)
    # c = D - w = codimension excess
    # We test with specific (n, w, c) values

    all_E = list(combinations(L, w))
    print(f"\nParameters: n={n}, w={w}, p={p}")
    print(f"Total {w}-subsets: {len(all_E)}")

    # For each c value, test k-wise independence
    for c in range(1, w + 1):
        D = w + c
        if D > n:
            continue
        k_code = n - D

        if k_max is None:
            k_test = min(D // c + 2, 8)  # test up to D/c + 2
        else:
            k_test = k_max

        print(f"\n--- c={c}, D={D}, k_code={k_code}, D/c={D/c:.1f} ---")
        print(f"Testing k-wise independence for k = 2, ..., {k_test}")

        # Precompute all Λ_E coefficient vectors
        all_lambdas = {}
        for E in all_E:
            all_lambdas[E] = poly_coeffs(E, p)

        # For each k, sample random k-tuples and check independence
        for k in range(2, k_test + 1):
            independent_count = 0
            tested = 0
            all_pairwise_ok = 0  # count of k-tuples where all pairs have |∩| ≤ w-c

            # Sample random k-tuples
            for _ in range(sample_size):
                indices = random.sample(range(len(all_E)), k)
                Es = [all_E[i] for i in indices]

                # Check pairwise intersection constraint
                pairwise_ok = True
                for i in range(k):
                    for j in range(i + 1, k):
                        j_size = len(set(Es[i]) & set(Es[j]))
                        if j_size > w - c:
                            pairwise_ok = False
                            break
                    if not pairwise_ok:
                        break

                if not pairwise_ok:
                    continue

                all_pairwise_ok += 1

                # Build the kc × D matrix of normal vectors
                rows = []
                for E in Es:
                    lam = all_lambdas[E]
                    for r in range(c):
                        row = poly_mult_xr(lam, r, D - 1, p)
                        rows.append(row)

                rk = rank_mod_p(rows, p)
                if rk == k * c:
                    independent_count += 1
                tested += 1

            if tested > 0:
                rate = independent_count / tested
                print(f"  k={k}: {independent_count}/{tested} independent "
                      f"({rate:.4f}), {all_pairwise_ok} pairwise-ok tuples found")
            else:
                print(f"  k={k}: no valid k-tuples found (all pairs have |∩| > w-c)")


def compute_worst_case_M(n, w, c, p):
    """Compute worst-case M(s) = max_s |{E : s ∈ W_E}| by brute force.

    For c=1: W_E is a hyperplane with normal Λ_E (coefficients in F_p^D).
    s ∈ W_E iff ⟨Λ_E, s⟩ = 0.

    For general c: W_E has codimension c, with normals {Λ_E · x^r, r=0,...,c-1}.
    s ∈ W_E iff ⟨Λ_E · x^r, s⟩ = 0 for all r < c.
    """
    L = list(range(n))
    D = w + c
    k_code = n - D
    all_E = list(combinations(L, w))

    print(f"\n{'='*60}")
    print(f"WORST-CASE M: n={n}, w={w}, c={c}, D={D}, p={p}")
    print(f"D/c = {D/c:.1f}, C(n,w) = {comb(n,w)}, E[M] = {comb(n,w)/p**c:.4f}")
    print(f"{'='*60}")

    # Precompute normal matrix for each E: c rows of D columns
    E_normals = {}
    for E in all_E:
        lam = poly_coeffs(E, p)
        normals = []
        for r in range(c):
            row = poly_mult_xr(lam, r, D - 1, p)
            normals.append(row)
        E_normals[E] = normals

    # For each s ∈ F_p^D, count M(s) = |{E : s ∈ W_E}|
    # s ∈ W_E iff ⟨normal_r, s⟩ = 0 for all r < c
    # Brute force over all s (only feasible for small p^D)

    total_s = p ** D
    if total_s > 500000:
        print(f"p^D = {total_s} too large for brute force, sampling instead")
        return sample_worst_case_M(n, w, c, p, all_E, E_normals)

    # Represent s as a tuple, iterate
    max_M = 0
    max_s = None
    M_histogram = {}

    def iterate_s(D, p):
        """Generate all s ∈ F_p^D."""
        if D == 0:
            yield []
            return
        for rest in iterate_s(D - 1, p):
            for v in range(p):
                yield rest + [v]

    for s in iterate_s(D, p):
        M = 0
        for E in all_E:
            # Check if s ∈ W_E: all normals orthogonal to s
            in_WE = True
            for normal in E_normals[E]:
                dot = sum(normal[i] * s[i] for i in range(D)) % p
                if dot != 0:
                    in_WE = False
                    break
            if in_WE:
                M += 1

        M_histogram[M] = M_histogram.get(M, 0) + 1
        if M > max_M:
            max_M = M
            max_s = s[:]

    print(f"\nM histogram (M : count):")
    for m in sorted(M_histogram.keys()):
        pct = M_histogram[m] / total_s * 100
        print(f"  M={m}: {M_histogram[m]} ({pct:.2f}%)")

    print(f"\nmax M(s) = {max_M}, achieved at s = {max_s}")
    print(f"D/c = {D/c:.1f}")
    print(f"Bound holds: max_M ≤ D/c = {D/c:.1f}? {'YES' if max_M <= D/c else 'NO'}")

    return max_M


def sample_worst_case_M(n, w, c, p, all_E, E_normals, num_samples=50000):
    """Sample random syndromes to estimate worst-case M."""
    D = w + c
    max_M = 0
    max_s = None
    M_histogram = {}

    for _ in range(num_samples):
        s = [random.randint(0, p - 1) for _ in range(D)]
        M = 0
        for E in all_E:
            in_WE = True
            for normal in E_normals[E]:
                dot = sum(normal[i] * s[i] for i in range(D)) % p
                if dot != 0:
                    in_WE = False
                    break
            if in_WE:
                M += 1

        M_histogram[M] = M_histogram.get(M, 0) + 1
        if M > max_M:
            max_M = M
            max_s = s[:]

    print(f"\nM histogram (sampled, {num_samples} syndromes):")
    for m in sorted(M_histogram.keys()):
        pct = M_histogram[m] / num_samples * 100
        print(f"  M={m}: {M_histogram[m]} ({pct:.2f}%)")

    print(f"\nmax M(s) observed = {max_M}")
    print(f"D/c = {D/c:.1f}")

    return max_M


# ============================================================
# TESTS
# ============================================================
random.seed(42)

print("=" * 60)
print("PART 1: k-WISE INDEPENDENCE OF ERROR-LOCATOR NORMALS")
print("=" * 60)

# Small cases
test_kwise_independence(8, 3, 7, k_max=5, sample_size=2000)
test_kwise_independence(10, 4, 11, k_max=5, sample_size=2000)
test_kwise_independence(12, 5, 13, k_max=5, sample_size=2000)

print("\n\n" + "=" * 60)
print("PART 2: WORST-CASE M(s) BY BRUTE FORCE")
print("=" * 60)

# Very small cases for brute force
for n, w, c, p in [
    (5, 2, 1, 5),    # D/c = 3
    (6, 2, 1, 5),    # D/c = 3
    (6, 3, 1, 5),    # D/c = 4
    (6, 2, 2, 5),    # D/c = 2
    (7, 3, 1, 7),    # D/c = 4
    (7, 3, 2, 7),    # D/c = 2.5
    (7, 2, 1, 7),    # D/c = 3
    (8, 3, 1, 7),    # D/c = 4
    (8, 3, 2, 7),    # D/c = 2.5
    (8, 4, 1, 7),    # D/c = 5
    (8, 4, 2, 7),    # D/c = 3
]:
    if p ** (w + c) <= 500000:
        compute_worst_case_M(n, w, c, p)

# Larger p, small D for exact computation
print("\n\n" + "=" * 60)
print("PART 3: WORST-CASE M WITH LARGER p")
print("=" * 60)

for n, w, c, p in [
    (5, 2, 1, 11),   # D/c = 3, p^D = 1331
    (5, 2, 1, 31),   # D/c = 3, p^D = 29791
    (6, 3, 1, 7),    # D/c = 4, p^D = 2401
    (6, 3, 1, 11),   # D/c = 4, p^D = 14641
    (6, 2, 2, 7),    # D/c = 2, p^D = 2401
    (6, 2, 2, 11),   # D/c = 2, p^D = 14641
    (7, 3, 2, 5),    # D/c = 2.5, p^D = 3125*25 too large
]:
    if p ** (w + c) <= 500000:
        compute_worst_case_M(n, w, c, p)
