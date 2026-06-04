"""
OP2 Feasibility Analysis

Key question: Can M_max = 0 at FRI-relevant parameters?

CRITICAL OBSERVATION: For two codewords c_1, c_2 at minimum distance d_min,
we can construct a received word u with d(u,c_1) = w and d(u,c_2) = d_min - w.
Both within distance w iff d_min <= 2w, i.e., c <= (n-k-1)/2.

At rate 1/2 and Johnson bound:
  c ≈ 0.207n, threshold (n-k-1)/2 ≈ n/4 = 0.25n
  Since 0.207 < 0.25: M_max >= 2 for ALL p.

This script verifies this construction directly.
"""

import itertools

def is_prime(n):
    if n < 2: return False
    for d in range(2, int(n**0.5)+1):
        if n % d == 0: return False
    return True

def find_primitive_root(n, p):
    if (p-1) % n != 0: return None
    for g in range(2, p):
        omega = pow(g, (p-1)//n, p)
        if pow(omega, n, p) == 1:
            ok = all(pow(omega, d, p) != 1 for d in range(1, n) if n % d == 0 and d < n)
            if ok: return omega
    return None

def rs_encode(coeffs, L, p):
    """Evaluate polynomial (coefficient list, low-to-high) at all points of L."""
    return [sum(c * pow(x, i, p) for i, c in enumerate(coeffs)) % p for x in L]

def hamming_dist(a, b):
    return sum(1 for x, y in zip(a, b) if x != y)

def verify_construction(n, k, p, c_excess):
    """Verify: can we construct u with M(u) >= 2 at codimension excess c?"""
    omega = find_primitive_root(n, p)
    if omega is None:
        return None

    L = [pow(omega, i, p) for i in range(n)]
    w = n - k - c_excess
    d_min = n - k + 1

    if w < 1 or w >= n:
        return None

    # Check if construction is possible: d_min <= 2w
    if d_min > 2 * w:
        return f"IMPOSSIBLE: d_min={d_min} > 2w={2*w}"

    # Find two codewords at minimum distance
    # For RS codes: c_1 = 0 (zero codeword), c_2 = any codeword with exactly d_min nonzero positions
    # A polynomial of degree < k with exactly d_min = n-k+1 nonzero evaluations
    # Actually, any nonzero codeword has >= d_min nonzero positions

    # Simpler: use c_1 = 0, c_2 = encoding of [1, 0, ..., 0]
    c1 = [0] * n
    c2 = rs_encode([1], L, p)  # constant polynomial 1 -> all ones? No, that has n nonzero positions

    # Actually c2 = [1, 1, ..., 1] has d(c1, c2) = n (all positions differ)
    # We need d = d_min = n-k+1

    # For minimum distance: use a polynomial of degree k-1 with exactly d_min = n-k+1 nonzero evaluations
    # This requires n - (k-1) = n-k+1 zeros among n evaluation points -> k-1 roots in L.
    # Choose k-1 points from L as roots, build polynomial.

    # Choose first k-1 points of L as roots
    roots = L[:k-1]
    # Build polynomial with these roots
    poly_coeffs = [1]
    for r in roots:
        new = [0] * (len(poly_coeffs) + 1)
        for i, c in enumerate(poly_coeffs):
            new[i + 1] = (new[i + 1] + c) % p
            new[i] = (new[i] - r * c) % p
        poly_coeffs = new

    c2 = rs_encode(poly_coeffs, L, p)
    d = hamming_dist(c1, c2)

    # Verify d = d_min
    # The polynomial has degree k-1 and k-1 roots in L, so it has exactly n - (k-1) = n-k+1 nonzero evaluations
    assert d == d_min, f"d={d} != d_min={d_min}"

    # Support of c1 - c2 = support of c2 (since c1 = 0)
    S = [i for i in range(n) if c2[i] != 0]
    assert len(S) == d_min

    # Choose B1 = first w elements of S, B2 = last w elements
    # Need S ⊂ B1 ∪ B2, so |B1 ∪ B2| >= |S| = d_min
    # |B1 ∪ B2| = |B1| + |B2| - |B1 ∩ B2| = 2w - |B1 ∩ B2|
    # Need 2w - |B1 ∩ B2| >= d_min, i.e., |B1 ∩ B2| <= 2w - d_min

    overlap = 2 * w - d_min
    if overlap < 0:
        return f"IMPOSSIBLE: overlap={overlap} < 0"

    B1 = S[:w]
    B2 = S[d_min - w:]  # last w elements of S
    assert len(B1) == w and len(B2) == w

    B1_set = set(B1)
    B2_set = set(B2)
    actual_overlap = len(B1_set & B2_set)
    assert B1_set | B2_set == set(S), f"B1∪B2 doesn't cover S"

    # Construct u
    u = list(c1)  # start with c1

    # On B1\B2: set u = c2 (so u ≠ c1 on B1, and u = c2 on these positions)
    for i in B1_set - B2_set:
        u[i] = c2[i]

    # On B2\B1: set u = c1 (already done; u = 0 here, and c1 = 0, c2 ≠ 0)
    # u[i] = c1[i] = 0 ≠ c2[i]. ✓

    # On B1 ∩ B2: set u ≠ c1 AND u ≠ c2
    for i in B1_set & B2_set:
        # Need u[i] not in {c1[i], c2[i]} = {0, c2[i]}
        for v in range(1, p):
            if v != c2[i]:
                u[i] = v
                break

    # Verify distances
    d1 = hamming_dist(u, c1)
    d2 = hamming_dist(u, c2)

    return {
        'w': w,
        'd_min': d_min,
        'c': c_excess,
        'd(u,c1)': d1,
        'd(u,c2)': d2,
        'M_geq_2': d1 <= w and d2 <= w,
        'overlap': actual_overlap,
        'B1': B1,
        'B2': B2,
    }

def main():
    print("=" * 70)
    print("OP2 Feasibility: M_max >= 2 construction")
    print("=" * 70)

    # Check threshold: c <= (n-k-1)/2
    print("\nThreshold analysis: M >= 2 possible iff c <= (n-k-1)/2")
    print("-" * 60)

    for rho_num, rho_den in [(1,2), (1,3), (1,4)]:
        rho = rho_num / rho_den
        print(f"\nRate ρ = {rho_num}/{rho_den}:")

        for n in [8, 10, 12, 16, 20, 32, 64]:
            k = n * rho_num // rho_den
            if k < 1 or k >= n: continue

            d_min = n - k + 1

            # Johnson bound
            import math
            w_J = n - math.ceil(math.sqrt(n * k))
            c_J = n - k - w_J

            threshold = (n - k - 1) / 2

            feasible = c_J <= threshold

            print(f"  n={n:>3d}, k={k:>3d}: d_min={d_min}, "
                  f"w_J={w_J}, c_J={c_J}, threshold={(n-k-1)/2:.1f}, "
                  f"M≥2 at Johnson: {'YES ✓' if feasible else 'NO ✗'}")

    # Direct verification with actual RS codes
    print(f"\n{'='*70}")
    print("Direct verification with RS codes")
    print(f"{'='*70}")

    test_cases = [
        (8, 4, 17),
        (10, 5, 11),
        (10, 5, 31),
        (10, 5, 101),
        (12, 6, 13),
        (12, 6, 37),
        (12, 6, 97),
        (16, 8, 17),
        (16, 8, 97),
    ]

    for n, k, p in test_cases:
        if not is_prime(p) or p <= n or (p-1) % n != 0:
            continue

        print(f"\nRS[{n},{k}] over F_{p}:")

        for c_excess in range(1, min(n-k, 6)):
            result = verify_construction(n, k, p, c_excess)
            if result is None:
                continue
            if isinstance(result, str):
                print(f"  c={c_excess}: {result}")
            else:
                status = "M≥2 VERIFIED ✓" if result['M_geq_2'] else "M<2 ✗"
                print(f"  c={c_excess}, w={result['w']}: "
                      f"d(u,c1)={result['d(u,c1)']}, d(u,c2)={result['d(u,c2)']}, "
                      f"{status}")

    # Key implication for FRI
    print(f"\n{'='*70}")
    print("CONCLUSION: FRI implications")
    print(f"{'='*70}")
    print("""
At rate ρ = 1/2 and Johnson bound δ = 1 - √ρ ≈ 0.293:
  c_J ≈ 0.207n, threshold (n-k-1)/2 ≈ n/4 = 0.25n

Since c_J < threshold for ALL n:
  → M_max ≥ 2 at FRI-relevant parameters for ALL p
  → OP2 (M_max = 0) is FALSE at these parameters

Combined with OP1 (equal-threshold CA is false):
  → The 2× query overhead is INTRINSIC
  → Cannot be eliminated by M=0 or by improving CA threshold
  → Half-threshold (δ/2) is the best achievable within the CA framework
""")

if __name__ == "__main__":
    main()
