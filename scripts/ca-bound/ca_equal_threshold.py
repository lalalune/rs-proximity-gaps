"""
Equal-threshold CA test v3: correct parameters + efficient joint distance.

KEY FIX: w must be < n-k (covering radius). With w = n-k, joint ≤ w always
(by MDS erasure correction), so CA premise is vacuously satisfied.

Correct choice: w = n-k-1 (first value below covering radius), and check δ > δ_J.

Efficient joint distance via subset enumeration:
  Δ_joint ≤ w  ⟺  ∃ S ⊂ L, |S| ≤ w, both f₁ and f₂ are "S-consistent"
  (i.e., their restrictions to L\S lie in RS_k(L\S))

For MDS RS: f is S-consistent iff the polynomial interpolating f on any k
points of L\S also matches the other |L\S|-k points.
"""

import sys
import random
from itertools import combinations

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
    """Evaluate Lagrange interpolant at x_eval, mod p."""
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

def is_consistent(f, S_set, L, k, p):
    """Check if f restricted to L\S is a degree-<k polynomial.
    S_set: set of indices to exclude."""
    remaining = [(L[i], f[i]) for i in range(len(L)) if i not in S_set]
    m = len(remaining)
    if m < k:
        return True  # underdetermined
    if m == k:
        return True  # exactly determined, always consistent

    x_pts = [r[0] for r in remaining]
    y_pts = [r[1] for r in remaining]

    # Interpolate through first k points, check remaining
    for j in range(k, m):
        val = lagrange_eval(x_pts[:k], y_pts[:k], x_pts[j], p)
        if val != y_pts[j]:
            return False
    return True

def joint_dist_leq_w(f1, f2, w, L, k, p, n):
    """Check if Δ_joint((f1,f2), C²) ≤ w/n.
    Equivalent: ∃ S ⊂ {0,...,n-1}, |S| ≤ w, both f1 and f2 are S-consistent."""
    for s in range(w + 1):
        for S in combinations(range(n), s):
            S_set = set(S)
            if is_consistent(f1, S_set, L, k, p) and is_consistent(f2, S_set, L, k, p):
                return True
    return False

def dist_to_code(f, L, k, p, n):
    """Compute Δ(f, RS_k) = min errors over all codewords.
    For MDS: try erasing positions one by one."""
    # Check if f itself is a codeword (0 errors)
    if is_consistent(f, set(), L, k, p):
        return 0
    # Check 1 erasure
    for i in range(n):
        if is_consistent(f, {i}, L, k, p):
            return 1
    # Check 2 erasures
    for S in combinations(range(n), 2):
        if is_consistent(f, set(S), L, k, p):
            return 2
    # Check 3 erasures
    for S in combinations(range(n), 3):
        if is_consistent(f, set(S), L, k, p):
            return 3
    # etc.
    for d in range(4, n - k + 1):
        for S in combinations(range(n), d):
            if is_consistent(f, set(S), L, k, p):
                return d
    return n - k  # covering radius

def find_closest_codeword(f, L, k, p, n):
    """Find closest codeword to f."""
    d = dist_to_code(f, L, k, p, n)
    if d == 0:
        return list(f), d
    for S in combinations(range(n), d):
        S_set = set(S)
        if is_consistent(f, S_set, L, k, p):
            # Interpolate on L\S
            remaining_idx = [i for i in range(n) if i not in S_set]
            x_pts = [L[i] for i in remaining_idx]
            y_pts = [f[i] for i in remaining_idx]
            # Build codeword
            cw = list(f)
            for i in S_set:
                cw[i] = lagrange_eval(x_pts[:k], y_pts[:k], L[i], p)
            return cw, d
    return list(f), n  # shouldn't reach here

def run_test(n, k, p, omega, w, mode="exhaustive", n_samples=50000):
    delta = w / n
    delta_J = 1.0 - (k / n) ** 0.5
    rho = k / n

    print(f"\n{'='*60}", flush=True)
    print(f"RS[{n},{k}] / F_{p},  ω={omega},  ρ={rho:.3f}", flush=True)
    print(f"d_min={n-k+1}, covering_radius={n-k}", flush=True)
    print(f"δ_J = {delta_J:.4f},  δ = {w}/{n} = {delta:.4f}", flush=True)

    if delta <= delta_J + 1e-9:
        print(f"SKIP: δ ≤ δ_J", flush=True)
        return None
    if w >= n - k:
        print(f"SKIP: w ≥ n-k (covering radius), CA premise vacuous", flush=True)
        return None

    L = [pow(omega, i, p) for i in range(n)]
    print(f"L = {L}", flush=True)

    total_words = p ** n
    print(f"|F_p^n| = {total_words}", flush=True)

    max_bad = 0
    max_info = None
    hist = {}
    n_tested = 0
    n_checked = 0

    if mode == "exhaustive" and total_words <= 50000:
        print(f"Exhaustive search over all {total_words}² = {total_words**2} pairs...", flush=True)
        for f1_int in range(total_words):
            f1 = []
            tmp = f1_int
            for _ in range(n):
                f1.append(tmp % p)
                tmp //= p
            f1 = tuple(f1)

            for f2_int in range(total_words):
                f2 = []
                tmp = f2_int
                for _ in range(n):
                    f2.append(tmp % p)
                    tmp //= p
                f2 = tuple(f2)
                n_checked += 1

                if joint_dist_leq_w(f1, f2, w, L, k, p, n):
                    continue

                n_tested += 1
                bad = 0
                for gamma in range(p):
                    fg = tuple((f1[j] + gamma * f2[j]) % p for j in range(n))
                    if dist_to_code(fg, L, k, p, n) <= w:
                        bad += 1

                hist[bad] = hist.get(bad, 0) + 1
                if bad > max_bad:
                    max_bad = bad
                    d1 = dist_to_code(f1, L, k, p, n)
                    d2 = dist_to_code(f2, L, k, p, n)
                    print(f"  ★ NEW MAX: {bad} bad γ", flush=True)
                    print(f"    f1={f1} (d={d1}), f2={f2} (d={d2})", flush=True)
                    # Show which gammas are bad
                    for gamma in range(p):
                        fg = tuple((f1[j] + gamma * f2[j]) % p for j in range(n))
                        d_fg = dist_to_code(fg, L, k, p, n)
                        if d_fg <= w:
                            cw, _ = find_closest_codeword(fg, L, k, p, n)
                            print(f"    γ={gamma}: d(f1+γf2,C)={d_fg}, closest={cw}", flush=True)

            if (f1_int + 1) % max(1, total_words // 10) == 0:
                pct = 100 * (f1_int + 1) / total_words
                print(f"  [{pct:.0f}%] checked={n_checked}, tested={n_tested}, max={max_bad}", flush=True)

    else:
        print(f"Sampling {n_samples} random pairs...", flush=True)
        for trial in range(n_samples):
            f1 = tuple(random.randint(0, p-1) for _ in range(n))
            f2 = tuple(random.randint(0, p-1) for _ in range(n))
            n_checked += 1

            if joint_dist_leq_w(f1, f2, w, L, k, p, n):
                continue

            n_tested += 1
            bad = 0
            for gamma in range(p):
                fg = tuple((f1[j] + gamma * f2[j]) % p for j in range(n))
                if dist_to_code(fg, L, k, p, n) <= w:
                    bad += 1

            hist[bad] = hist.get(bad, 0) + 1
            if bad > max_bad:
                max_bad = bad
                d1 = dist_to_code(f1, L, k, p, n)
                d2 = dist_to_code(f2, L, k, p, n)
                print(f"  ★ NEW MAX: {bad} bad γ", flush=True)
                print(f"    f1={f1} (d={d1}), f2={f2} (d={d2})", flush=True)
                for gamma in range(p):
                    fg = tuple((f1[j] + gamma * f2[j]) % p for j in range(n))
                    d_fg = dist_to_code(fg, L, k, p, n)
                    if d_fg <= w:
                        cw, _ = find_closest_codeword(fg, L, k, p, n)
                        print(f"    γ={gamma}: d(f1+γf2,C)={d_fg}, closest={cw}", flush=True)

            if (trial + 1) % max(1, n_samples // 10) == 0:
                pct = 100 * (trial + 1) / n_samples
                print(f"  [{pct:.0f}%] checked={n_checked}, tested={n_tested}, max={max_bad}", flush=True)

    print(f"\n  RESULT: max_bad_γ = {max_bad}", flush=True)
    print(f"  Pairs checked: {n_checked}, with Δ_joint > δ: {n_tested}", flush=True)
    print(f"  Histogram: {dict(sorted(hist.items()))}", flush=True)
    if max_bad <= 2:
        print(f"  ✓ ε_ca(C,δ,δ) ≤ {max_bad}/{p} = O(1)/|F|", flush=True)
    else:
        print(f"  ✗ max_bad = {max_bad}", flush=True)
    print(flush=True)
    return max_bad


if __name__ == "__main__":
    print("EQUAL-THRESHOLD CA: CORRECTED PARAMETER TEST", flush=True)
    print("w < n-k (strictly below covering radius)", flush=True)
    print("δ > δ_J (above Johnson bound)", flush=True)
    print(flush=True)

    results = []

    # RS[6,3]/F_7: n=6,k=3,d=4. w=2, δ=1/3≈0.333 > δ_J≈0.293 ✓. n-k=3, w<3 ✓
    w = find_prim_root(7, 6)
    if w:
        r = run_test(6, 3, 7, w, 2, mode="sample", n_samples=100000)
        results.append(("RS[6,3]/F_7,w=2", r))

    # RS[6,3]/F_13: same code, larger field
    w = find_prim_root(13, 6)
    if w:
        r = run_test(6, 3, 13, w, 2, mode="sample", n_samples=50000)
        results.append(("RS[6,3]/F_13,w=2", r))

    # RS[8,4]/F_17: n=8,k=4,d=5. w=3, δ=3/8=0.375 > δ_J≈0.293 ✓. n-k=4, w<4 ✓
    w = find_prim_root(17, 8)
    if w:
        r = run_test(8, 4, 17, w, 3, mode="sample", n_samples=30000)
        results.append(("RS[8,4]/F_17,w=3", r))

    # RS[10,5]/F_11: n=10,k=5,d=6. w=4, δ=0.4 > δ_J≈0.293 ✓. n-k=5, w<5 ✓
    w = find_prim_root(11, 10)
    if w:
        r = run_test(10, 5, 11, w, 4, mode="sample", n_samples=20000)
        results.append(("RS[10,5]/F_11,w=4", r))

    # RS[6,3]/F_31: larger field test
    w = find_prim_root(31, 6)
    if w:
        r = run_test(6, 3, 31, w, 2, mode="sample", n_samples=50000)
        results.append(("RS[6,3]/F_31,w=2", r))

    # RS[12,6]/F_13: n=12,k=6,d=7. w=5, δ=5/12≈0.417 > δ_J≈0.293 ✓. n-k=6, w<6 ✓
    w = find_prim_root(13, 12)
    if w:
        r = run_test(12, 6, 13, w, 5, mode="sample", n_samples=10000)
        results.append(("RS[12,6]/F_13,w=5", r))

    print("\n" + "=" * 60, flush=True)
    print("SUMMARY", flush=True)
    print("=" * 60, flush=True)
    for name, r in results:
        if r is None:
            print(f"  {name}: SKIPPED", flush=True)
        elif r <= 2:
            print(f"  {name}: max_bad={r}  ✓ O(1)/|F|", flush=True)
        else:
            print(f"  {name}: max_bad={r}  ✗", flush=True)
