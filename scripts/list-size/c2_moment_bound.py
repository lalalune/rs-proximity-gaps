#!/usr/bin/env python3
"""
c ≥ 2 moment bound verification.

For RS[n,k] over F_p, codimension excess c = n-k-w (where w = error weight):
  - Each w-subset E defines a codimension-c flat in syndrome space F_p^D (D = n-k)
  - The flat is the kernel of a c × D system derived from the Vandermonde submatrix

Goal: verify that for distinct E₁ ≠ E₂, the combined 2c normal vectors are
linearly independent (so flats intersect with codimension 2c), giving:
  E[M] = C(n,w)/p^c,  Var[M] = E[M](1 - 1/p^c)

Step 1: Compute the normal vectors (left kernel of V_E) for each w-subset E
Step 2: Check 4-wise independence (c=2) for all pairs E₁ ≠ E₂
Step 3: Verify E[M] = C(n,w)/p^c by direct enumeration
"""

from itertools import combinations
from math import comb
import time


def make_eval_points(n, p):
    """Use 1, 2, ..., n as evaluation points (avoid 0 for Vandermonde regularity)."""
    assert p > n, f"Need p > n, got p={p}, n={n}"
    return list(range(1, n + 1))


def vandermonde_submatrix(alpha, E, D, p):
    """
    Build the D × |E| Vandermonde submatrix V_E.
    V_E[j, i] = alpha[E[i]]^(k+j)  for j=0..D-1, i=0..|E|-1
    where k = n - D (dimension of RS code), and syndrome indices are k, k+1, ..., n-1.

    Actually, for the syndrome equations: sum_{i in E} e_i * alpha_i^j = s_j
    for j = k, k+1, ..., n-1 (D equations).
    So V_E[j, i] = alpha[E[i]]^(k+j) where j ranges over syndrome indices.

    Wait, let me be more careful. The syndrome vector for error pattern e supported on E is:
    s_j = sum_{i in E} e_i * alpha[i]^j,  for j = k, k+1, ..., n-1

    So V_E is D × w where V_E[r, c] = alpha[E[c]]^(k+r), r=0..D-1
    """
    n = len(alpha)
    k = n - D
    w = len(E)
    V = []
    for r in range(D):
        row = []
        for c in range(w):
            row.append(pow(alpha[E[c]], k + r, p))
        V.append(row)
    return V


def left_kernel(V, p):
    """
    Compute a basis for the left kernel of V (mod p).
    V is D × w. Left kernel = {u ∈ F_p^D : u·V = 0}.
    This is the kernel of V^T.

    Returns a list of vectors (each vector is a list of D elements).
    """
    D = len(V)
    w = len(V[0])

    # Transpose: w × D
    VT = [[V[r][c] for r in range(D)] for c in range(w)]

    # Augmented matrix [V^T | I_w] — no, we want kernel of V^T
    # Kernel of V^T: solve V^T · u = 0 where u is D-dimensional
    # Use row reduction on V^T (w × D matrix), find null space

    # Work with V^T as w × D matrix
    M = [row[:] for row in VT]  # copy
    rows = w
    cols = D

    # Row echelon form
    pivot_cols = []
    current_row = 0
    for col in range(cols):
        # Find pivot
        pivot = None
        for row in range(current_row, rows):
            if M[row][col] % p != 0:
                pivot = row
                break
        if pivot is None:
            continue
        # Swap
        M[current_row], M[pivot] = M[pivot], M[current_row]
        pivot_cols.append(col)
        # Scale pivot row
        inv = pow(M[current_row][col], p - 2, p)
        for j in range(cols):
            M[current_row][j] = (M[current_row][j] * inv) % p
        # Eliminate
        for row in range(rows):
            if row == current_row:
                continue
            factor = M[row][col]
            if factor != 0:
                for j in range(cols):
                    M[row][j] = (M[row][j] - factor * M[current_row][j]) % p
        current_row += 1

    # Free variables = cols not in pivot_cols
    rank = len(pivot_cols)
    free_cols = [c for c in range(cols) if c not in pivot_cols]
    kernel_dim = cols - rank  # = D - rank(V^T) = D - rank(V)

    # For each free variable, construct a kernel vector
    kernel_basis = []
    for fc in free_cols:
        vec = [0] * cols
        vec[fc] = 1
        # For each pivot col, solve
        for i, pc in enumerate(pivot_cols):
            # Row i has pivot at pc, and M[i][fc] gives the coefficient
            vec[pc] = (-M[i][fc]) % p
        kernel_basis.append(vec)

    return kernel_basis


def check_independence(vectors, p):
    """Check if a list of vectors over F_p are linearly independent."""
    if not vectors:
        return True
    n = len(vectors[0])
    m = len(vectors)

    # Build matrix m × n, row reduce
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

    return current_row == m  # rank == number of vectors


def compute_M_exact(alpha, n, k, w, p):
    """
    For each syndrome s, count M(s) = number of w-subsets E such that
    the syndrome equations are compatible.
    Returns dict: syndrome_tuple -> M count.

    For small cases only.
    """
    D = n - k
    all_subsets = list(combinations(range(n), w))

    # For each E, compute the syndrome flat (set of compatible syndromes)
    syndrome_counts = {}

    for E in all_subsets:
        V = vandermonde_submatrix(alpha, E, D, p)
        # The set of syndromes compatible with E is: {V · e : e ∈ F_p^w, e_i ≠ 0 ∀i}
        # But for M computation, we just need: the affine subspace V · (F_p^w \ {hyperplanes})
        # Actually, M(s) counts E such that ∃ nonzero e supported on E with syndrome s
        # For our purposes (above Johnson), we count ALL e (including those with zeros)
        # since we're counting agreement patterns, not error patterns.
        #
        # Actually, M(s) = |{E : s ∈ Im(V_E)}| where Im(V_E) is the column span of V_E.
        # If rank(V_E) = w (which it is for w ≤ D, Vandermonde), then Im(V_E) is a
        # w-dimensional subspace, and s ∈ Im(V_E) iff the left-kernel normals annihilate s.

        # The syndrome s is compatible with E iff n·s = 0 for all n in left_kernel(V_E)
        kern = left_kernel(V, p)

        if not kern:
            # Full column rank, Im = all of F_p^D (happens when w ≥ D)
            # Every syndrome is compatible
            continue  # skip, contributes to all syndromes

        # The flat is {s : <n, s> = 0 for all n in kern}
        # This is a (D - c)-dimensional affine subspace through origin
        # where c = dim(kern) = D - w

        # For enumeration: iterate over all syndromes and check
        # (only feasible for small D and p)
        pass

    # Simpler approach: for each syndrome s, count how many E have s in their image
    # For small cases, just enumerate everything

    syndrome_M = {}

    for E in all_subsets:
        V = vandermonde_submatrix(alpha, E, D, p)
        kern = left_kernel(V, p)
        c = len(kern)

        if c == 0:
            # Every syndrome works — but this shouldn't happen when w < D
            # Actually w < D always in our setting (c ≥ 1)
            raise ValueError(f"Unexpected: kernel dim = 0 for |E|={w}, D={D}")

        # s is compatible with E iff <kern[i], s> = 0 for all i
        # Enumerate all s ∈ F_p^D (only for small D, p)
        # Just mark which syndromes are hit
        for s_tuple in iter_syndromes(D, p):
            compatible = True
            for n_vec in kern:
                dot = sum(n_vec[j] * s_tuple[j] for j in range(D)) % p
                if dot != 0:
                    compatible = False
                    break
            if compatible:
                syndrome_M[s_tuple] = syndrome_M.get(s_tuple, 0) + 1

    return syndrome_M


def iter_syndromes(D, p):
    """Iterate over all syndromes in F_p^D. Only for small D, p."""
    if D == 0:
        yield ()
        return
    for rest in iter_syndromes(D - 1, p):
        for x in range(p):
            yield rest + (x,)


def verify_pairwise_kernel_independence(n, k, w, p):
    """
    For RS[n,k] over F_p with error weight w:
    - Compute left kernel of V_E for each w-subset E
    - Check that for all pairs E₁ ≠ E₂, the combined kernels span 2c dimensions

    Returns (total_pairs, independent_pairs, failed_pairs_examples)
    """
    alpha = make_eval_points(n, p)
    D = n - k
    c = D - w  # codimension excess

    all_subsets = list(combinations(range(n), w))
    num_subsets = len(all_subsets)

    # Precompute kernels
    kernels = {}
    for E in all_subsets:
        V = vandermonde_submatrix(alpha, E, D, p)
        kern = left_kernel(V, p)
        assert len(kern) == c, f"Expected kernel dim {c}, got {len(kern)} for E={E}"
        kernels[E] = kern

    # Check all pairs
    total_pairs = 0
    independent_pairs = 0
    failed = []

    for i in range(num_subsets):
        for j in range(i + 1, num_subsets):
            E1, E2 = all_subsets[i], all_subsets[j]
            combined = kernels[E1] + kernels[E2]  # 2c vectors in F_p^D

            total_pairs += 1
            if check_independence(combined, p):
                independent_pairs += 1
            else:
                failed.append((E1, E2))

    return total_pairs, independent_pairs, failed


def verify_EM_formula(n, k, w, p):
    """
    Verify E[M] = C(n,w)/p^c by direct enumeration.
    Compute M(s) for all syndromes, check that the average matches.
    Only feasible for small parameters.
    """
    alpha = make_eval_points(n, p)
    D = n - k
    c = D - w

    print(f"  Verifying E[M] for RS[{n},{k}], w={w}, c={c}, p={p}, D={D}")
    print(f"  C(n,w) = {comb(n, w)}, predicted E[M] = {comb(n, w)}/{p}^{c} = {comb(n,w)/p**c:.6f}")

    all_subsets = list(combinations(range(n), w))

    # Precompute kernels
    kernels = {}
    for E in all_subsets:
        V = vandermonde_submatrix(alpha, E, D, p)
        kern = left_kernel(V, p)
        kernels[E] = kern

    # For each syndrome, count M(s)
    total_M = 0
    total_M2 = 0
    num_syndromes = p ** D

    # Only feasible for very small cases
    if num_syndromes > 500000:
        print(f"  Skipping exact E[M] verification: {num_syndromes} syndromes too many")
        return None

    count = 0
    for s_tuple in iter_syndromes(D, p):
        M_s = 0
        for E in all_subsets:
            # Check if s is compatible with E (all kernel vectors annihilate s)
            compatible = True
            for n_vec in kernels[E]:
                dot = sum(n_vec[j] * s_tuple[j] for j in range(D)) % p
                if dot != 0:
                    compatible = False
                    break
            if compatible:
                M_s += 1
        total_M += M_s
        total_M2 += M_s * M_s
        count += 1

    avg_M = total_M / count
    avg_M2 = total_M2 / count
    var_M = avg_M2 - avg_M * avg_M
    predicted_EM = comb(n, w) / p ** c
    predicted_var = predicted_EM * (1 - 1 / p ** c)

    print(f"  Computed E[M]   = {avg_M:.6f},  predicted = {predicted_EM:.6f},  match = {abs(avg_M - predicted_EM) < 1e-9}")
    print(f"  Computed Var[M] = {var_M:.6f},  predicted = {predicted_var:.6f},  match = {abs(var_M - predicted_var) < 1e-6}")

    return avg_M, var_M


def main():
    print("=" * 70)
    print("c ≥ 2 MOMENT BOUND VERIFICATION")
    print("=" * 70)

    # Test cases: (n, k, w, description)
    # c = n - k - w
    test_cases = [
        # c = 1 (baseline, should match existing theorem)
        (6, 3, 2, "RS[6,3] c=1 w=2"),
        (8, 4, 3, "RS[8,4] c=1 w=3"),

        # c = 2 (the target)
        (6, 3, 1, "RS[6,3] c=2 w=1"),
        (8, 4, 2, "RS[8,4] c=2 w=2"),
        (10, 5, 3, "RS[10,5] c=2 w=3"),
        (12, 6, 4, "RS[12,6] c=2 w=4"),

        # c = 3
        (8, 4, 1, "RS[8,4] c=3 w=1"),
        (10, 5, 2, "RS[10,5] c=3 w=2"),
        (12, 6, 3, "RS[12,6] c=3 w=3"),
    ]

    primes = [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]

    for n, k, w, desc in test_cases:
        D = n - k
        c = D - w
        print(f"\n{'=' * 70}")
        print(f"{desc}: n={n}, k={k}, w={w}, D={D}, c={c}, C(n,w)={comb(n,w)}")
        print(f"{'=' * 70}")

        for p in primes:
            if p < n:
                continue

            t0 = time.time()
            total, indep, failed = verify_pairwise_kernel_independence(n, k, w, p)
            dt = time.time() - t0

            status = "✓ ALL INDEPENDENT" if total == indep else f"✗ {len(failed)} FAILURES"
            print(f"  p={p:4d}: {total:6d} pairs, {indep:6d} independent, {status}  ({dt:.1f}s)")

            if failed:
                for E1, E2 in failed[:3]:
                    print(f"    FAILED: E1={E1}, E2={E2}")

            # For very small cases, also verify E[M] directly
            if p ** D <= 100000 and total == indep:
                verify_EM_formula(n, k, w, p)

            # Don't spend too long on large cases
            if dt > 30:
                print(f"  (skipping remaining primes for this case)")
                break

    # Large-scale independence check for c=2
    print(f"\n{'=' * 70}")
    print("LARGE-SCALE c=2 INDEPENDENCE CHECK")
    print(f"{'=' * 70}")

    large_cases = [
        (14, 7, 5, "RS[14,7] c=2 w=5"),
        (16, 8, 6, "RS[16,8] c=2 w=6"),
    ]

    for n, k, w, desc in large_cases:
        D = n - k
        c = D - w
        num_subsets = comb(n, w)
        num_pairs = num_subsets * (num_subsets - 1) // 2
        print(f"\n{desc}: {num_subsets} subsets, {num_pairs} pairs")

        for p in [17, 31, 61]:
            if p < n:
                continue
            t0 = time.time()
            total, indep, failed = verify_pairwise_kernel_independence(n, k, w, p)
            dt = time.time() - t0
            status = "✓" if total == indep else f"✗ {len(failed)} FAIL"
            print(f"  p={p:4d}: {total:6d} pairs  {status}  ({dt:.1f}s)")
            if failed:
                for E1, E2 in failed[:3]:
                    print(f"    FAILED: E1={E1}, E2={E2}")
            if dt > 120:
                break

    print(f"\n{'=' * 70}")
    print("DONE")


if __name__ == "__main__":
    main()
