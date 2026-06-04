"""
k-wise independence of error-locator normals for RS codes.

For RS[n,k] over F_p:
- Each w-subset E ⊂ [n] gives error-locator poly Λ_E(x) = ∏_{e∈E}(x - α_e)
- Normal vector n_E = coefficients of Λ_E
- Pairwise independence is PROVED (distinct monic polys are lin. indep.)
- Question: does k-wise independence hold for k ≥ 3?

k-wise dependence of {Λ_{E_1}, ..., Λ_{E_k}} means ∃ c_1,...,c_k not all zero
with Σ c_i Λ_{E_i} = 0.  Since all monic: Σ c_i = 0, so this reduces to
(k-1) differences Λ_{E_i} - Λ_{E_k} being linearly dependent.

These differences have degree ≤ w-1 (leading term cancels), living in a
w-dimensional space.  So (w+1)-wise dependence MUST occur.

For the OP2 application with codimension excess c:
- RS-compatible flat has codim c in syndrome space
- Need: no point on the flat satisfies the compatibility conditions
- k-wise independence for k ≤ c+1 would give concentration bounds

This script checks:
1. For which triples (E_1, E_2, E_3) are the normals 3-wise dependent?
2. What fraction of triples are 3-wise dependent?
3. Pattern as p grows?
"""

import itertools
import sys

def is_prime(n):
    if n < 2: return False
    for d in range(2, int(n**0.5)+1):
        if n % d == 0: return False
    return True

def primes_above(n, count=10):
    res = []
    p = n + 1
    while len(res) < count:
        if is_prime(p):
            res.append(p)
        p += 1
    return res

def poly_coeffs(roots, p):
    """Compute coefficients of ∏(x - r_i) mod p.  Returns [a_0, a_1, ..., a_w] where
    poly = a_0 + a_1 x + ... + a_w x^w (a_w = 1, monic)."""
    w = len(roots)
    c = [0] * (w + 1)
    c[0] = 1  # start with "1"
    for r in roots:
        # multiply by (x - r)
        new_c = [0] * (w + 1)
        for i in range(len(c)):
            if c[i] == 0: continue
            if i + 1 <= w:
                new_c[i + 1] = (new_c[i + 1] + c[i]) % p
            new_c[i] = (new_c[i] - r * c[i]) % p
        c = new_c
    return c  # c[w] = 1 (monic)

def check_3wise_dependence(n, k, p):
    """Check 3-wise dependence of error-locator normals for RS[n,k] over F_p.

    Returns: (total_triples, dependent_triples, examples)
    """
    # Evaluation domain: L = {1, g, g^2, ..., g^{n-1}} where g is primitive n-th root mod p
    # Need p ≡ 1 (mod n) for n-th roots of unity to exist

    # Find primitive n-th root of unity
    g = None
    for candidate in range(2, p):
        if pow(candidate, n, p) == 1:
            # Check it's primitive (order exactly n)
            is_prim = True
            for d in range(1, n):
                if n % d == 0 and d < n:
                    if pow(candidate, d, p) == 1:
                        is_prim = False
                        break
            if is_prim:
                g = candidate
                break

    if g is None:
        return None  # No n-th root of unity exists

    L = [pow(g, i, p) for i in range(n)]
    w = n - k - 1  # Johnson-like weight; for simplicity use this
    # Actually for the paper: w is the error weight at codimension excess c=1
    # w = n - k - c, so for c=1: w = n - k - 1

    if w < 2 or w > n - 1:
        return None

    # Generate all w-subsets of L
    all_subsets = list(itertools.combinations(range(n), w))
    N_subsets = len(all_subsets)

    if N_subsets > 500:
        # Too many, sample
        import random
        random.seed(42)
        sample = random.sample(all_subsets, min(200, N_subsets))
    else:
        sample = all_subsets

    # Compute normals (coefficients of error-locator poly)
    normals = {}
    for E in sample:
        roots = [L[i] for i in E]
        normals[E] = poly_coeffs(roots, p)

    # Check 3-wise dependence
    # Three normals n_1, n_2, n_3 are dependent iff det of any 3x(w+1) submatrix...
    # Since they're in F_p^{w+1}, dependence means rank({n_1, n_2, n_3}) < 3.
    # Since pairwise independent, rank is at least 2. So 3-wise dependent iff rank = 2.

    # Equivalent: n_3 = a*n_1 + b*n_2 for some a,b.
    # Since monic: 1 = a + b, so b = 1-a.
    # n_3 = a*n_1 + (1-a)*n_2
    # n_3 - n_2 = a*(n_1 - n_2)
    # So: 3-wise dependent iff (n_3 - n_2) is proportional to (n_1 - n_2).

    keys = list(normals.keys())
    total = 0
    dependent = 0
    examples = []

    max_check = min(len(keys), 100)
    for i in range(max_check):
        for j in range(i+1, max_check):
            for l in range(j+1, max_check):
                total += 1
                E1, E2, E3 = keys[i], keys[j], keys[l]
                n1, n2, n3 = normals[E1], normals[E2], normals[E3]

                # Compute diff1 = n1 - n2, diff2 = n3 - n2
                diff1 = [(n1[d] - n2[d]) % p for d in range(w+1)]
                diff2 = [(n3[d] - n2[d]) % p for d in range(w+1)]

                # Check proportionality: diff2 = λ * diff1
                # Find first nonzero in diff1
                lam = None
                is_prop = True
                for d in range(w+1):
                    if diff1[d] != 0:
                        if lam is None:
                            lam = (diff2[d] * pow(diff1[d], p-2, p)) % p
                        else:
                            if (lam * diff1[d]) % p != diff2[d]:
                                is_prop = False
                                break
                    else:
                        if diff2[d] != 0:
                            is_prop = False
                            break

                if is_prop and lam is not None:
                    dependent += 1
                    if len(examples) < 5:
                        examples.append((E1, E2, E3, lam))

    return total, dependent, examples, N_subsets, w, g

def main():
    print("=" * 70)
    print("k-wise independence of error-locator normals")
    print("=" * 70)

    # Test cases: RS[n, k] over F_p with p ≡ 1 (mod n)
    test_cases = [
        # (n, k, list_of_p)
        (6, 2, [7, 13, 31, 43]),
        (6, 3, [7, 13, 31, 43]),
        (8, 4, [17, 41, 73, 97]),
        (10, 5, [11, 31, 41, 61, 71, 101]),
        (12, 6, [13, 37, 61, 97]),
    ]

    for n, k, ps in test_cases:
        print(f"\n{'='*50}")
        print(f"RS[{n},{k}], w = {n-k-1} (c=1)")
        print(f"{'='*50}")

        for p in ps:
            if p <= n: continue
            if (p - 1) % n != 0:
                continue  # Skip if no n-th roots of unity

            result = check_3wise_dependence(n, k, p)
            if result is None:
                print(f"  p={p}: no n-th root of unity or bad params")
                continue

            total, dep, examples, N_sub, w, g = result
            print(f"  p={p}: C({n},{w})={N_sub}, checked {total} triples, "
                  f"3-wise dependent: {dep} ({dep/max(total,1)*100:.1f}%)")
            if examples:
                for E1, E2, E3, lam in examples[:2]:
                    print(f"    Example: E1={E1}, E2={E2}, E3={E3}, λ={lam}")

    # Now check HIGHER-ORDER dependence
    print(f"\n{'='*70}")
    print("Higher-order (4-wise, 5-wise) independence check")
    print("=" * 70)

    # For RS[8,4] over F_17: w=3, normals in F_17^4
    # Max independent set: 4 (dimension of space)
    # So 5-wise dependence MUST occur. But does 4-wise?
    n, k, p = 8, 4, 17
    if (p-1) % n == 0:
        g = None
        for candidate in range(2, p):
            if pow(candidate, n, p) == 1:
                is_prim = all(pow(candidate, d, p) != 1 for d in range(1, n) if n % d == 0 and d < n)
                if is_prim:
                    g = candidate
                    break

        if g:
            L = [pow(g, i, p) for i in range(n)]
            w = n - k - 1  # = 3
            all_subsets = list(itertools.combinations(range(n), w))

            normals = {}
            for E in all_subsets:
                roots = [L[i] for i in E]
                normals[E] = poly_coeffs(roots, p)

            keys = list(normals.keys())
            print(f"\nRS[{n},{k}] over F_{p}: w={w}, D={w+1}={w+1}")
            print(f"Total {w}-subsets: {len(keys)}")
            print(f"Normal vectors live in F_{p}^{w+1}")
            print(f"Max linearly independent: {w+1}")

            # Check 4-wise dependence
            dep4 = 0
            total4 = 0
            for combo in itertools.combinations(range(len(keys)), 4):
                total4 += 1
                vecs = [normals[keys[i]] for i in combo]
                # Build matrix and compute rank mod p
                mat = [list(v) for v in vecs]
                rank = gauss_rank(mat, p)
                if rank < 4:
                    dep4 += 1

            print(f"4-wise: checked {total4}, dependent: {dep4} ({dep4/max(total4,1)*100:.1f}%)")

            # Check if ANY (w+1)=4 normals are independent (should be yes)
            indep4 = total4 - dep4
            print(f"4-wise independent: {indep4}")

def gauss_rank(mat, p):
    """Compute rank of matrix over F_p."""
    m = len(mat)
    if m == 0: return 0
    n = len(mat[0])
    mat = [row[:] for row in mat]  # copy

    rank = 0
    for col in range(n):
        # Find pivot
        pivot = None
        for row in range(rank, m):
            if mat[row][col] % p != 0:
                pivot = row
                break
        if pivot is None:
            continue

        # Swap
        mat[rank], mat[pivot] = mat[pivot], mat[rank]

        # Scale
        inv = pow(mat[rank][col], p-2, p)
        mat[rank] = [(x * inv) % p for x in mat[rank]]

        # Eliminate
        for row in range(m):
            if row != rank and mat[row][col] != 0:
                factor = mat[row][col]
                mat[row] = [(mat[row][j] - factor * mat[rank][j]) % p for j in range(n)]

        rank += 1

    return rank

if __name__ == "__main__":
    main()
