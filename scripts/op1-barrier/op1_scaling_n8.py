"""
OP1 scaling test for RS[8,4]: w=3, C(8,3)=56.
Prediction: max_bad = min(q, 56).
"""
from itertools import combinations
import random
from math import comb

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
    remaining = [i for i in range(n) if i not in S_indices]
    m = len(remaining)
    if m <= k:
        return True
    x_pts = [L[i] for i in remaining[:k]]
    y_pts = [f[i] for i in remaining[:k]]
    for j in range(k, m):
        val = lagrange_eval(x_pts, y_pts, L[remaining[j]], p)
        if val != f[remaining[j]]:
            return False
    return True

def count_bad_gammas(f1, f2, w, L, k, p, n):
    count = 0
    for gamma in range(p):
        u = tuple((f1[j] + gamma * f2[j]) % p for j in range(n))
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
    for s in range(w + 1):
        for S in combinations(range(n), s):
            S_set = set(S)
            if is_S_consistent(f1, S_set, L, k, p, n) and \
               is_S_consistent(f2, S_set, L, k, p, n):
                return False
    return True

def test_q(n, k, p, n_samples=2000):
    w = n - k - 1
    omega = find_prim_root(p, n)
    if omega is None:
        return None
    L = [pow(omega, i, p) for i in range(n)]
    max_bad = 0
    n_tested = 0
    total_bad = 0
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
    n, k = 8, 4
    w = n - k - 1  # = 3
    cnw = comb(n, w)
    print(f"RS[{n},{k}], w={w}, C(n,w)={cnw}")
    print(f"{'q':>6}  {'max_bad':>7}  {'max/q':>7}  {'C(n,w)/q':>8}  {'tested':>7}")
    print("-" * 50)

    # Primes with n | (q-1)
    for q in range(n+1, 300):
        if (q - 1) % n != 0:
            continue
        is_prime = all(q % d != 0 for d in range(2, int(q**0.5) + 1))
        if not is_prime or q < 2:
            continue
        n_samples = min(3000, max(500, 50000 // q))
        result = test_q(n, k, q, n_samples=n_samples)
        if result is None:
            continue
        max_bad, tested, avg_bad = result
        print(f"{q:6d}  {max_bad:7d}  {max_bad/q:7.4f}  {cnw/q:8.4f}  {tested:7d}", flush=True)
