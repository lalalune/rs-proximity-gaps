"""
FRI Folding — FIXED version.

BUG FIX: For odd k, the folded code is RS[n/2, ceil(k/2)], not RS[n/2, k//2].
f_even has ceil(k/2) coefficients, f_odd has floor(k/2) coefficients.
g_alpha = f_even + alpha * f_odd has ceil(k/2) coefficients.
"""
import math, random
from itertools import combinations
from collections import Counter

def find_params(n):
    p = n + 1
    while True:
        if p % n == 1:
            ok = True
            for i in range(2, int(p**0.5)+1):
                if p % i == 0: ok = False; break
            if ok:
                for g in range(2, p):
                    x, seen = 1, set()
                    for _ in range(p-1): seen.add(x); x = x*g%p
                    if len(seen) == p-1:
                        return p, pow(g, (p-1)//n, p)
        p += n

def johnson_w(n, k):
    if k <= 1: return 0
    return int(math.floor(n - math.sqrt(n * (k - 1))))

def poly_eval(coeffs, x, p):
    v, xi = 0, 1
    for c in coeffs:
        v = (v + c * xi) % p
        xi = xi * x % p
    return v

def lagrange_interp(pts, vals, x, p):
    n_pts = len(pts)
    r = 0
    for i in range(n_pts):
        num, den = vals[i], 1
        for j in range(n_pts):
            if i != j:
                num = num * (x - pts[j]) % p
                den = den * (pts[i] - pts[j]) % p
        r = (r + num * pow(den, p-2, p)) % p
    return r

def hdist(a, b, p):
    return sum(1 for x, y in zip(a, b) if (x-y)%p)


def fold_center(center, pw, n, p, alpha):
    """FRI fold of function values on L to L'."""
    n2 = n // 2
    inv2 = pow(2, p-2, p)
    gc = []
    for i in range(n2):
        fi, fi2 = center[i], center[i + n2]
        fe = (fi + fi2) * inv2 % p
        inv_oi = pow(pw[i], p-2, p)
        fo = (fi - fi2) * inv2 % p * inv_oi % p
        gc.append((fe + alpha * fo) % p)
    return gc


def fold_poly_fixed(co, alpha, cur_k, p):
    """Fold polynomial coefficients. FIXED for odd k.

    f(x) = sum_{j=0}^{k-1} co[j] x^j
    f_even(y) = sum_{l} co[2l] y^l  (l = 0, ..., ceil(k/2)-1)
    f_odd(y) = sum_{l} co[2l+1] y^l  (l = 0, ..., floor(k/2)-1)
    g_alpha(y) = f_even(y) + alpha * f_odd(y)
    """
    k2 = (cur_k + 1) // 2  # ceil(k/2) = number of even-index coefficients
    fc = []
    for j in range(k2):
        ce = co[2*j] if 2*j < cur_k else 0
        co_odd = co[2*j+1] if 2*j+1 < cur_k else 0
        fc.append((ce + alpha * co_odd) % p)
    return fc


def find_list(center, omega, pw, n, k, w, p):
    """Find distinct codewords within distance w of center."""
    codewords = {}
    inv_n = pow(n, p-2, p)

    for B_tuple in combinations(range(n), w):
        B = set(B_tuple)
        A = [i for i in range(n) if i not in B]

        if len(A) < k:
            continue

        x_pts = [pw[i] for i in A[:k]]
        y_pts = [center[i] for i in A[:k]]

        ok = True
        for ci in range(k, len(A)):
            y_check = lagrange_interp(x_pts, y_pts, pw[A[ci]], p)
            if y_check != center[A[ci]]:
                ok = False
                break

        if not ok:
            continue

        vals = [lagrange_interp(x_pts, y_pts, pw[i], p) for i in range(n)]

        # Extract monomial coefficients via DFT
        coeffs = []
        for j in range(k):
            cj = 0
            omega_neg_j = pow(omega, (n - j) % n, p) if j > 0 else 1
            x_power = 1
            for i in range(n):
                cj = (cj + vals[i] * x_power) % p
                x_power = x_power * omega_neg_j % p
            cj = cj * inv_n % p
            coeffs.append(cj)

        key = tuple(vals)
        if key not in codewords:
            d = hdist(vals, center, p)
            eset = frozenset(i for i in range(n) if (vals[i] - center[i]) % p)
            codewords[key] = (coeffs, vals, d, eset)

    return list(codewords.values())


def analyze(n, k, w, p_override=None):
    if p_override:
        p = p_override
        for g in range(2, p):
            x, seen = 1, set()
            for _ in range(p-1): seen.add(x); x = x*g%p
            if len(seen) == p-1:
                omega = pow(g, (p-1)//n, p); break
    else:
        p, omega = find_params(n)

    c = n - k - w
    n2 = n // 2
    k2 = (k + 1) // 2  # ceil(k/2) — correct for FRI folding!
    w2 = johnson_w(n2, k2)
    c2 = n2 - k2 - w2

    pw = [pow(omega, i, p) for i in range(n)]
    omega2 = pow(omega, 2, p)
    pw2 = [pow(omega, 2*i, p) for i in range(n2)]

    print(f"\n{'='*60}")
    print(f"n={n} k={k} p={p} w={w} c={c}")
    print(f"Folded: n'={n2} k'_fold=ceil(k/2)={k2} w'_J={w2} c'={c2}")
    print(f"Note: k//2={k//2} vs ceil(k/2)={k2} {'<-- DIFFERENT!' if k%2 else ''}")
    print(f"{'='*60}")

    random.seed(42)
    best_M, best_data = 0, None

    n_trials = 1000
    for trial in range(n_trials):
        center = [random.randrange(p) for _ in range(n)]
        cws = find_list(center, omega, pw, n, k, w, p)
        M = len(cws)
        if M > best_M:
            best_M = M
            best_data = (center, cws)
            print(f"  trial {trial}: M={M}", flush=True)

    print(f"\nBest M_actual = {best_M}")
    if best_M <= 1:
        print("  M too small.\n")
        return

    center, cws = best_data

    # Error structure
    print(f"\nError structure:")
    for idx, (co, va, d, eset) in enumerate(cws):
        E = set(eset)
        paired = sum(1 for i in E if (i + n//2) % n in E) // 2
        unp = len(E) - 2 * paired
        E_im = set(i % n2 for i in E)
        print(f"  cw{idx}: d={d} E={sorted(E)} p={paired} u={unp} |E'|={len(E_im)}")

    # Folding
    max_test = min(p-1, 100)
    print(f"\nFRI folding (k'={k2}, w'={w2}, {max_test} alphas):")

    survive_counts = []
    for alpha in range(1, max_test+1):
        gc = fold_center(center, pw, n, p, alpha)
        surv = 0
        for co, va, d, eset in cws:
            fc = fold_poly_fixed(co, alpha, k, p)
            fv = [poly_eval(fc, pw2[i], p) for i in range(n2)]
            df = hdist(fv, gc, p)
            if df <= w2:
                surv += 1
        survive_counts.append(surv)

    dist = Counter(survive_counts)
    print(f"  M' dist: {dict(sorted(dist.items()))}")
    print(f"  Mean={sum(survive_counts)/len(survive_counts):.3f} Max={max(survive_counts)}")

    # Per-codeword
    if best_M <= 15:
        print(f"\nPer-codeword:")
        for idx, (co, va, d, eset) in enumerate(cws):
            E = set(eset)
            paired = sum(1 for i in E if (i+n//2)%n in E) // 2
            unp = len(E) - 2*paired
            E_im = set(i%n2 for i in E)
            cnt = 0
            for alpha in range(1, max_test+1):
                gc = fold_center(center, pw, n, p, alpha)
                fc = fold_poly_fixed(co, alpha, k, p)
                fv = [poly_eval(fc, pw2[i], p) for i in range(n2)]
                df = hdist(fv, gc, p)
                if df <= w2:
                    cnt += 1
            need_c = max(0, len(E_im) - w2)
            print(f"  cw{idx}: d={d} |E'|={len(E_im)} w'={w2} "
                  f"need_cancel={need_c} survive={cnt}/{max_test}")

    # Multi-round
    print(f"\nMulti-round (20 trials):")
    random.seed(777)
    for trial in range(20):
        cur_c = center[:]
        cur_list = [(co[:], va[:], d) for co, va, d, _ in cws]
        cur_n, cur_k = n, k
        cur_om = omega
        chain = [len(cur_list)]

        while cur_n >= 4 and cur_k >= 2 and len(cur_list) > 0:
            al = random.randrange(1, p)
            nn = cur_n // 2
            nk = (cur_k + 1) // 2  # FIXED: ceil(k/2)
            nw = johnson_w(nn, nk)
            if nw < 0: break
            nom = pow(cur_om, 2, p)
            npw = [pow(nom, i, p) for i in range(nn)]

            nc = fold_center(cur_c, [pow(cur_om, i, p) for i in range(cur_n)],
                             cur_n, p, al)
            nl = []
            for co, va, d in cur_list:
                fc = fold_poly_fixed(co, al, cur_k, p)
                fv = [poly_eval(fc, npw[i], p) for i in range(nn)]
                df = hdist(fv, nc, p)
                if df <= nw:
                    nl.append((fc, fv, df))

            cur_c, cur_list = nc, nl
            cur_n, cur_k, cur_om = nn, nk, nom
            chain.append(len(cur_list))

        print(f"  trial {trial}: {chain}")


# Run
analyze(12, 6, 4, p_override=13)
analyze(14, 7, 5, p_override=29)
analyze(16, 8, 5, p_override=17)
