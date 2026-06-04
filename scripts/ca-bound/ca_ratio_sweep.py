"""
Sweep the CA threshold ratio: test ε_ca(C, δ/c, δ) for various c.

Key finding from v3: ε_ca(C, δ, δ) = Θ(1) for RS above Johnson (OP1 is FALSE).
Now test: what's the OPTIMAL ratio c? Is c=3 tight, or can we get c=2?

For each c in {1, 1.5, 2, 2.5, 3, 4}:
  Count #{γ : dist(f1+γf2, C) ≤ ⌊δn/c⌋} over (f1,f2) with Δ_joint > δ
"""
import random
from itertools import combinations

def find_prim_root(p, n):
    if (p - 1) % n != 0: return None
    for g in range(2, p):
        w = pow(g, (p - 1) // n, p)
        if pow(w, n, p) == 1:
            ok = True
            for d in range(1, n):
                if n % d == 0 and d < n and pow(w, d, p) == 1:
                    ok = False; break
            if ok: return w
    return None

def lagrange_eval(x_pts, y_pts, x_eval, p):
    k = len(x_pts)
    val = 0
    for i in range(k):
        num, den = y_pts[i], 1
        for m in range(k):
            if m != i:
                num = num * (x_eval - x_pts[m]) % p
                den = den * (x_pts[i] - x_pts[m]) % p
        val = (val + num * pow(den, p - 2, p)) % p
    return val

def is_consistent(f, S_set, L, k, p):
    remaining = [(L[i], f[i]) for i in range(len(L)) if i not in S_set]
    m = len(remaining)
    if m <= k: return True
    x_pts = [r[0] for r in remaining]
    y_pts = [r[1] for r in remaining]
    for j in range(k, m):
        val = lagrange_eval(x_pts[:k], y_pts[:k], x_pts[j], p)
        if val != y_pts[j]: return False
    return True

def joint_dist_leq_w(f1, f2, w, L, k, p, n):
    for s in range(w + 1):
        for S in combinations(range(n), s):
            S_set = set(S)
            if is_consistent(f1, S_set, L, k, p) and is_consistent(f2, S_set, L, k, p):
                return True
    return False

def dist_to_code(f, L, k, p, n):
    for d in range(n - k + 1):
        for S in combinations(range(n), d):
            if is_consistent(f, set(S), L, k, p):
                return d
    return n - k

def run_ratio_sweep(n, k, p, omega, w_nt, n_samples=30000):
    """Test ε_ca(C, w_hd/n, w_nt/n) for various w_hd ≤ w_nt."""
    delta_J = 1.0 - (k / n) ** 0.5
    rho = k / n
    L = [pow(omega, i, p) for i in range(n)]

    print(f"\n{'='*60}", flush=True)
    print(f"RS[{n},{k}]/F_{p}  ρ={rho:.3f}  δ_J={delta_J:.4f}  δ_nt={w_nt}/{n}={w_nt/n:.4f}", flush=True)
    print(f"Sweeping conclusion threshold w_hd from 0 to {w_nt}", flush=True)
    print(f"{'='*60}", flush=True)

    # For each sample pair with Δ_joint > w_nt:
    # compute dist(f1+γf2, C) for all γ, and record in which w_hd bins they fall

    # bins[w_hd] = max number of γ with dist ≤ w_hd
    max_bad = {w_hd: 0 for w_hd in range(w_nt + 1)}
    total_tested = 0

    for trial in range(n_samples):
        f1 = tuple(random.randint(0, p-1) for _ in range(n))
        f2 = tuple(random.randint(0, p-1) for _ in range(n))

        if joint_dist_leq_w(f1, f2, w_nt, L, k, p, n):
            continue

        total_tested += 1

        # Compute distance of f1+γf2 for all γ
        dists = []
        for gamma in range(p):
            fg = tuple((f1[j] + gamma * f2[j]) % p for j in range(n))
            d = dist_to_code(fg, L, k, p, n)
            dists.append(d)

        # For each threshold w_hd: count how many γ have dist ≤ w_hd
        for w_hd in range(w_nt + 1):
            bad = sum(1 for d in dists if d <= w_hd)
            if bad > max_bad[w_hd]:
                max_bad[w_hd] = bad

        if (trial + 1) % max(1, n_samples // 5) == 0:
            print(f"  [{100*(trial+1)//n_samples}%] tested={total_tested}", flush=True)

    print(f"\n  Tested {total_tested} pairs with Δ_joint > {w_nt}/{n}", flush=True)
    print(f"\n  {'w_hd':>4} | {'δ_hd':>8} | {'ratio':>6} | {'max_bad':>7} | {'ε_ca':>10} | {'status':>10}", flush=True)
    print(f"  {'-'*4}-+-{'-'*8}-+-{'-'*6}-+-{'-'*7}-+-{'-'*10}-+-{'-'*10}", flush=True)

    for w_hd in range(w_nt + 1):
        delta_hd = w_hd / n
        ratio = w_nt / max(w_hd, 0.01)
        eps = max_bad[w_hd] / p
        status = "O(1)/|F|" if max_bad[w_hd] <= 2 else f"{max_bad[w_hd]}/{p}"
        print(f"  {w_hd:>4} | {delta_hd:>8.4f} | {ratio:>6.1f} | {max_bad[w_hd]:>7} | {eps:>10.4f} | {status:>10}", flush=True)

    print(flush=True)
    return max_bad


if __name__ == "__main__":
    print("CA THRESHOLD RATIO SWEEP", flush=True)
    print("Finding the optimal ratio c in ε_ca(C, δ/c, δ)", flush=True)

    # RS[6,3]/F_7, δ=2/6
    w = find_prim_root(7, 6)
    if w: run_ratio_sweep(6, 3, 7, w, 2, n_samples=50000)

    # RS[6,3]/F_13, δ=2/6
    w = find_prim_root(13, 6)
    if w: run_ratio_sweep(6, 3, 13, w, 2, n_samples=30000)

    # RS[8,4]/F_17, δ=3/8
    w = find_prim_root(17, 8)
    if w: run_ratio_sweep(8, 4, 17, w, 3, n_samples=15000)

    # RS[10,5]/F_11, δ=4/10
    w = find_prim_root(11, 10)
    if w: run_ratio_sweep(10, 5, 11, w, 4, n_samples=10000)

    print("\n" + "=" * 60, flush=True)
    print("KEY QUESTION: At what w_hd does max_bad drop to ≤ 2?", flush=True)
    print("If w_hd = w_nt/c: the optimal ratio is c.", flush=True)
    print("Our theorem: c = 3. Can we do c = 2?", flush=True)
