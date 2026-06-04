"""
Direct computation of M_max vs p for RS codes.

For RS[n,k] over F_p with evaluation domain L (n-th roots of unity):
M(u) = number of codewords c in RS_k with d(u,c) ≤ w
where w = n - k - c (error weight at codimension excess c).

For the FRI proximity gap application, we care about c ≥ 1.

This script computes M via the syndrome hyperplane arrangement:
- For each w-subset E of [n], compute the error-locator polynomial Λ_E
- The syndrome compatibility condition defines a hyperplane H_E
- M(s) = |{E : s ∈ H_E}|

For c=1: D = w+1, each H_E is a hyperplane in F_p^D.
M_max = max over all s ∈ F_p^D of |{E : ⟨n_E, s⟩ = 0}|.

For c ≥ 2: not implemented yet; the flat structure is more complex.
"""

import itertools
import sys
from collections import Counter

def find_primitive_root_of_unity(n, p):
    """Find primitive n-th root of unity in F_p (requires n | p-1)."""
    if (p - 1) % n != 0:
        return None
    # Find a generator of F_p*, then raise to (p-1)/n
    for g in range(2, p):
        if pow(g, (p-1)//2, p) != 1:  # Quick check: g is not a QR
            omega = pow(g, (p-1)//n, p)
            if pow(omega, n, p) == 1:
                # Check primitive
                ok = True
                for d in range(1, n):
                    if n % d == 0 and d < n and pow(omega, d, p) == 1:
                        ok = False
                        break
                if ok:
                    return omega
    # Brute force
    for omega in range(2, p):
        if pow(omega, n, p) == 1:
            ok = True
            for d in range(1, n):
                if n % d == 0 and d < n and pow(omega, d, p) == 1:
                    ok = False
                    break
            if ok:
                return omega
    return None

def error_locator_normal(E_indices, L, p):
    """Compute normal vector (coefficients of error-locator poly) for subset E.
    Returns list of w+1 coefficients [a_0, ..., a_w] with a_w = 1."""
    roots = [L[i] for i in E_indices]
    w = len(roots)
    # Build polynomial (x - r_0)(x - r_1)...(x - r_{w-1})
    coeffs = [1]  # constant poly = 1
    for r in roots:
        new_coeffs = [0] * (len(coeffs) + 1)
        for i, c in enumerate(coeffs):
            new_coeffs[i + 1] = (new_coeffs[i + 1] + c) % p  # x * c
            new_coeffs[i] = (new_coeffs[i] - r * c) % p       # -r * c
        coeffs = new_coeffs
    return coeffs  # [a_0, a_1, ..., a_w] with a_w = 1

def compute_mmax_c1(n, k, p):
    """Compute M_max for RS[n,k] over F_p at codimension excess c=1."""
    omega = find_primitive_root_of_unity(n, p)
    if omega is None:
        return None

    L = [pow(omega, i, p) for i in range(n)]
    w = n - k - 1  # c=1
    D = w + 1      # syndrome dimension

    if w < 2 or w >= n:
        return None

    # Compute all normals
    all_E = list(itertools.combinations(range(n), w))
    N = len(all_E)

    # For each E, compute n_E = error-locator coefficients
    normals = []
    for E in all_E:
        normals.append(tuple(error_locator_normal(E, L, p)))

    # Method: for each pair of normals, compute their "intersection direction"
    # and find the syndrome that maximizes M.
    #
    # More directly: for each hyperplane H_E (defined by ⟨n_E, s⟩ = 0),
    # the syndrome s lies on H_E iff dot(n_E, s) = 0.
    #
    # M(s) = |{E : dot(n_E, s) = 0}|.
    #
    # To find M_max: for each s ∈ F_p^D, compute M(s). But |F_p^D| = p^D is huge.
    #
    # Better: M_max = max over all s of the number of hyperplanes through s.
    # This equals the maximum point multiplicity in the arrangement.
    #
    # For small cases, we can enumerate intersection points.
    # Key insight: M(s) > 0 only if s lies on some H_E.
    # On each H_E, M(s) ≥ 1. The maximum is achieved at points
    # where multiple hyperplanes intersect.

    # Strategy: for each PAIR (E1, E2), compute the codim-2 subspace H_{E1} ∩ H_{E2}.
    # Sample points from this subspace and count M.

    # Actually, for small enough parameters, we can just compute M for all
    # points on all hyperplanes. But that's still O(N * p^{D-1}).

    # Fastest approach for small p: just iterate over all s ∈ F_p^D and count.
    if p ** D > 5_000_000:
        # Too large, use sampling
        return compute_mmax_sampling(n, k, p, L, w, D, all_E, normals)

    # Full enumeration
    # M(s) = |{E : dot(n_E, s) ≡ 0 (mod p)}|
    # We iterate over all s and count.

    # Actually even smarter: precompute for each s, dot products.
    # But p^D can be up to 5M, and N can be up to ~1000. So N * p^D ~ 5G — too much.

    # Better: for each hyperplane H_E, enumerate its p^{D-1} points.
    # Maintain a counter for each point. Total work: N * p^{D-1}.

    if N * (p ** (D-1)) > 50_000_000:
        return compute_mmax_sampling(n, k, p, L, w, D, all_E, normals)

    # Create a counter: for each point s (as tuple), how many hyperplanes contain it
    counter = Counter()

    for idx, E in enumerate(all_E):
        n_E = normals[idx]
        # H_E = {s : sum(n_E[j] * s[j] for j in range(D)) ≡ 0 mod p}
        # Enumerate all s on this hyperplane.
        # Fix s[0], ..., s[D-2] freely, then s[D-1] is determined (if n_E[D-1] ≠ 0).
        # Since n_E is the error-locator poly and the leading coeff is 1 (monic),
        # n_E[D-1] = n_E[w] = 1. So s[w] = -sum(n_E[j]*s[j] for j in range(w)) mod p.

        # Iterate over s[0], ..., s[w-1] ∈ F_p^w
        for s_prefix in itertools.product(range(p), repeat=w):
            s_last = (-sum(n_E[j] * s_prefix[j] for j in range(w))) % p
            s = s_prefix + (s_last,)
            counter[s] += 1

    if counter:
        mmax = max(counter.values())
        # How many s have M ≥ 1, M ≥ 2, etc.
        m_dist = Counter(counter.values())
        return mmax, m_dist, N, w
    else:
        return 0, {}, N, w

def compute_mmax_sampling(n, k, p, L, w, D, all_E, normals):
    """Estimate M_max via sampling: check pairwise intersections."""
    import random
    random.seed(42)
    N = len(all_E)

    # For each pair of hyperplanes, find their intersection (codim-2)
    # and sample points on it to find the max M.
    #
    # But even C(N,2) pairs can be large. Sample random pairs.

    best_M = 0

    # First, check M at the zero vector
    M_zero = sum(1 for nE in normals if all(x == 0 for x in nE[:-1]) and nE[-1] == 0)

    # Check M at random points
    num_samples = min(100000, p**D)
    for _ in range(num_samples):
        s = tuple(random.randrange(p) for _ in range(D))
        M_s = sum(1 for nE in normals if sum(nE[j]*s[j] for j in range(D)) % p == 0)
        if M_s > best_M:
            best_M = M_s

    # Also check pairwise intersections
    num_pairs = min(2000, N*(N-1)//2)
    pairs = random.sample(list(itertools.combinations(range(N), 2)), num_pairs)

    for i, j in pairs:
        n1, n2 = normals[i], normals[j]
        # Find a point on H_{n1} ∩ H_{n2}
        # n1·s = 0, n2·s = 0
        # System: 2 equations in D unknowns
        # Set s[2], ..., s[D-1] randomly, solve for s[0], s[1]
        for _ in range(10):
            s_tail = [random.randrange(p) for _ in range(D-2)]
            # n1[0]*s0 + n1[1]*s1 = -sum(n1[j+2]*s_tail[j] for j) mod p
            # n2[0]*s0 + n2[1]*s1 = -sum(n2[j+2]*s_tail[j] for j) mod p
            rhs1 = (-sum(n1[j+2]*s_tail[j] for j in range(D-2))) % p
            rhs2 = (-sum(n2[j+2]*s_tail[j] for j in range(D-2))) % p
            det = (n1[0]*n2[1] - n1[1]*n2[0]) % p
            if det == 0:
                continue
            det_inv = pow(det, p-2, p)
            s0 = ((rhs1*n2[1] - rhs2*n1[1]) * det_inv) % p
            s1 = ((n1[0]*rhs2 - n2[0]*rhs1) * det_inv) % p
            s = (s0, s1) + tuple(s_tail)

            M_s = sum(1 for nE in normals if sum(nE[j]*s[j] for j in range(D)) % p == 0)
            if M_s > best_M:
                best_M = M_s

    return best_M, None, N, w

def main():
    print("=" * 70)
    print("M_max vs p for RS codes (c=1 codimension excess)")
    print("=" * 70)

    # Test parameters: (n, k) pairs with list of primes p ≡ 1 (mod n)
    test_cases = [
        (6, 2),   # w=3, D=4
        (6, 3),   # w=2, D=3
        (8, 4),   # w=3, D=4
        (10, 5),  # w=4, D=5
        (12, 6),  # w=5, D=6
    ]

    for n, k in test_cases:
        w = n - k - 1
        D = w + 1
        print(f"\n{'='*50}")
        print(f"RS[{n},{k}], w={w}, D={D}, C({n},{w})={len(list(itertools.combinations(range(n),w)))}")
        print(f"{'='*50}")

        # Find primes p ≡ 1 (mod n), p > n
        primes = []
        for p in range(n+1, 5000):
            if (p-1) % n == 0 and is_prime(p):
                primes.append(p)
            if len(primes) >= 10:
                break

        for p in primes:
            result = compute_mmax_c1(n, k, p)
            if result is None:
                print(f"  p={p}: skipped")
                continue

            mmax, m_dist, N, w_actual = result
            E_M = N / p  # Expected M
            if m_dist is not None:
                total_with_M_ge1 = sum(cnt for m, cnt in m_dist.items() if m >= 1)
                total_with_M_ge2 = sum(cnt for m, cnt in m_dist.items() if m >= 2)
                print(f"  p={p:>4d}: M_max={mmax}, E[M]={E_M:.2f}, "
                      f"|{{s:M≥1}}|={total_with_M_ge1}, |{{s:M≥2}}|={total_with_M_ge2}")
                if m_dist:
                    dist_str = ", ".join(f"M={m}:{cnt}" for m, cnt in sorted(m_dist.items()))
                    print(f"          Distribution: {dist_str}")
            else:
                print(f"  p={p:>4d}: M_max≥{mmax} (sampled), E[M]={E_M:.2f}")

def is_prime(n):
    if n < 2: return False
    for d in range(2, int(n**0.5)+1):
        if n % d == 0: return False
    return True

if __name__ == "__main__":
    main()
