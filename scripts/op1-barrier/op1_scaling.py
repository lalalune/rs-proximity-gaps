"""
OP1 scaling test: does ε_ca(C, δ, δ) stay Θ(1) or decay as q grows?

Key insight: For RS[n,k] MDS over F_q, w = n-k-1, each w-erasure pattern S ⊂ L
gives AT MOST one γ where u_γ = f₁+γf₂ is S-decodable (linear equation in γ).
So |{bad γ}| ≤ C(n,w) (number of w-subsets).

Prediction: ε_ca ≈ min(1, C(n,w)/q).

Test: RS[6,3] (C(6,2)=15) over F_q for q = 7,13,19,31,37,43,61,67,...
Transition should occur at q ≈ 15.
"""

from itertools import combinations
import random, sys

def find_prim_root(p, n):
    if (p - 1) % n != 0:
        return None
    for g in range(2, p):
        w = pow(g, (p - 1) // n, p)
        if pow(w, n, p) == 1:
            ok = True
            for d in range(1, n):
                if n % d == 0 and d < n and pow(w, d, p) == 1:
                    ok = False
                    break
            if ok:
                return w
    return None

def lagrange_eval(x_pts, y_pts, x_eval, p):
    k = len(x_pts)
    val = 0
    for i in range(k):
        num = y_pts[i]
        den = 1
        for m in range(k):
            if m != i:
                num = num * (x_eval - x_pts[m]) % p
                den = den * (x_pts[i] - x_pts[m]) % p
        val = (val + num * pow(den, p - 2, p)) % p
    return val

def is_S_consistent(f, S_indices, L, k, p, n):
    """Check if f restricted to L\\S is a degree-<k polynomial."""
    remaining = [i for i in range(n) if i not in S_indices]
    m = len(remaining)
    if m <= k:
        return True  # underdetermined or exactly determined
    x_pts = [L[i] for i in remaining[:k]]
    y_pts = [f[i] for i in remaining[:k]]
    for j in range(k, m):
        val = lagrange_eval(x_pts, y_pts, L[remaining[j]], p)
        if val != f[remaining[j]]:
            return False
    return True

def count_bad_gammas(f1, f2, w, L, k, p, n):
    """Count |{γ : d(f₁+γf₂, C) ≤ w}|."""
    count = 0
    for gamma in range(p):
        u = tuple((f1[j] + gamma * f2[j]) % p for j in range(n))
        # Check if u is within distance w of some codeword
        for s in range(w + 1):
            found = False
            for S in combinations(range(n), s):
                if is_S_consistent(u, set(S), L, k, p, n):
                    found = True
                    break
            if found:
                count += 1
                break
    return count

def joint_dist_gt_w(f1, f2, w, L, k, p, n):
    """Check if Δ_joint > w/n, i.e., no S with |S|≤w makes both consistent."""
    for s in range(w + 1):
        for S in combinations(range(n), s):
            S_set = set(S)
            if is_S_consistent(f1, S_set, L, k, p, n) and \
               is_S_consistent(f2, S_set, L, k, p, n):
                return False
    return True

def test_q(n, k, p, n_samples=5000):
    w = n - k - 1
    omega = find_prim_root(p, n)
    if omega is None:
        return None
    L = [pow(omega, i, p) for i in range(n)]

    max_bad = 0
    n_tested = 0
    total_bad = 0  # sum over tested pairs

    for _ in range(n_samples):
        f1 = tuple(random.randint(0, p-1) for _ in range(n))
        f2 = tuple(random.randint(0, p-1) for _ in range(n))

        if not joint_dist_gt_w(f1, f2, w, L, k, p, n):
            continue

        n_tested += 1
        bad = count_bad_gammas(f1, f2, w, L, k, p, n)
        total_bad += bad
        if bad > max_bad:
            max_bad = bad

    avg_bad = total_bad / n_tested if n_tested > 0 else 0
    return max_bad, n_tested, avg_bad

if __name__ == "__main__":
    from math import comb
    n, k = 6, 3
    w = n - k - 1  # = 2
    delta_J = 1 - (k/n)**0.5
    delta = w / n

    print(f"RS[{n},{k}], w={w}, δ={delta:.4f}, δ_J={delta_J:.4f}")
    print(f"C(n,w) = C({n},{w}) = {comb(n,w)}")
    print(f"Prediction: ε_ca ≈ min(1, {comb(n,w)}/q)")
    print()
    print(f"{'q':>6}  {'max_bad':>7}  {'max/q':>7}  {'avg_bad':>8}  {'avg/q':>7}  "
          f"{'C(n,w)/q':>8}  {'tested':>7}")
    print("-" * 70)

    # Primes q ≡ 1 (mod 6) so that F_q has a 6th root of unity
    primes = []
    for q in range(7, 500):
        if (q - 1) % n != 0:
            continue
        # Check prime
        if q < 2:
            continue
        is_prime = True
        for d in range(2, int(q**0.5) + 1):
            if q % d == 0:
                is_prime = False
                break
        if is_prime:
            primes.append(q)

    for q in primes:
        n_samples = min(20000, max(2000, 100000 // q))
        result = test_q(n, k, q, n_samples=n_samples)
        if result is None:
            continue
        max_bad, tested, avg_bad = result
        ratio = max_bad / q
        avg_ratio = avg_bad / q
        predicted = comb(n, w) / q
        print(f"{q:6d}  {max_bad:7d}  {ratio:7.4f}  {avg_bad:8.2f}  {avg_ratio:7.4f}  "
              f"{predicted:8.4f}  {tested:7d}", flush=True)
