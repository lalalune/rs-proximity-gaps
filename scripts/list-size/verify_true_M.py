#!/usr/bin/env python3
"""
Compute the TRUE worst-case list size M_true(s) for s != 0.

M_true(s) counts w-subsets E where:
1. Syndrome compatibility: <Λ_E · x^r, s> = 0 for r = 0, ..., c-1
2. Non-zero error values: solving V_E · v = (s_0, ..., s_{w-1}) gives all v_i != 0

Compare with M_compat(s) which only checks condition 1.

Key hypothesis: evaluation syndromes s_α = (1, α, ..., α^{D-1}) have M_compat = C(n-1,w-1)
but M_true = 0 (the error is weight-1, not weight-w).
"""
import sys
from itertools import combinations
from math import comb

sys.stdout = open(sys.stdout.fileno(), mode='w', buffering=1)


def poly_coeffs(roots, p):
    """Compute coefficients of Λ_E = ∏(x - r) mod p."""
    coeffs = [1]
    for r in roots:
        new = [0] * (len(coeffs) + 1)
        for i, c in enumerate(coeffs):
            new[i] = (new[i] - c * r) % p
            new[i + 1] = (new[i + 1] + c) % p
        coeffs = new
    return coeffs


def poly_mult_xr(coeffs, r, max_deg, p):
    result = [0] * (max_deg + 1)
    for i, c in enumerate(coeffs):
        if i + r <= max_deg:
            result[i + r] = c % p
    return result


def solve_vandermonde(E, s_first_w, p):
    """Solve V_E · v = s_first_w over F_p. Returns list of error values, or None if no solution."""
    w = len(E)
    assert len(s_first_w) == w
    # Build Vandermonde matrix V[j][i] = E[i]^j
    V = []
    for j in range(w):
        row = [pow(e, j, p) for e in E]
        V.append(row)
    # Gaussian elimination to solve V · v = s
    # Augmented matrix [V | s]
    aug = [row[:] + [s_first_w[j]] for j, row in enumerate(V)]
    n = w
    for col in range(n):
        # Find pivot
        pivot = None
        for row in range(col, n):
            if aug[row][col] % p != 0:
                pivot = row
                break
        if pivot is None:
            return None  # Singular (shouldn't happen for distinct E elements)
        aug[col], aug[pivot] = aug[pivot], aug[col]
        inv = pow(aug[col][col], p - 2, p)
        for j in range(n + 1):
            aug[col][j] = (aug[col][j] * inv) % p
        for row in range(n):
            if row != col and aug[row][col] % p != 0:
                factor = aug[row][col]
                for j in range(n + 1):
                    aug[row][j] = (aug[row][j] - factor * aug[col][j]) % p
    return [aug[i][n] % p for i in range(n)]


def compute_true_M(n, w, c, p, verbose=True):
    """Compute true worst-case M for valid RS parameters."""
    L = list(range(n))
    D = w + c
    all_E = list(combinations(L, w))

    if verbose:
        print(f"\n{'='*70}")
        print(f"TRUE M: n={n}, w={w}, c={c}, D={D}, p={p}")
        print(f"C(n,w)={comb(n,w)}, C(n-1,w-1)={comb(n-1,w-1)}, E[M]={comb(n,w)/p**c:.4f}")
        print(f"{'='*70}")

    # Precompute normals for syndrome compatibility check
    E_normals = {}
    for E in all_E:
        lam = poly_coeffs(E, p)
        normals = []
        for r in range(c):
            row = poly_mult_xr(lam, r, D - 1, p)
            normals.append(row)
        E_normals[E] = normals

    total_s = p ** D
    if total_s > 300000:
        if verbose:
            print(f"p^D = {total_s} too large, skipping")
        return None, None

    max_M_compat = 0
    max_M_true = 0
    max_s_compat = None
    max_s_true = None
    compat_hist = {}
    true_hist = {}

    def iterate_s(D, p):
        if D == 0:
            yield []
            return
        for rest in iterate_s(D - 1, p):
            for v in range(p):
                yield rest + [v]

    for s in iterate_s(D, p):
        if all(v == 0 for v in s):
            continue

        M_compat = 0
        M_true = 0
        s_first_w = s[:w]

        for E in all_E:
            # Check syndrome compatibility
            in_WE = True
            for normal in E_normals[E]:
                dot = sum(normal[i] * s[i] for i in range(D)) % p
                if dot != 0:
                    in_WE = False
                    break
            if not in_WE:
                continue
            M_compat += 1

            # Solve for error values
            v = solve_vandermonde(list(E), s_first_w, p)
            if v is None:
                continue
            # Check all non-zero
            if all(vi != 0 for vi in v):
                M_true += 1

        compat_hist[M_compat] = compat_hist.get(M_compat, 0) + 1
        true_hist[M_true] = true_hist.get(M_true, 0) + 1

        if M_compat > max_M_compat:
            max_M_compat = M_compat
            max_s_compat = s[:]
        if M_true > max_M_true:
            max_M_true = M_true
            max_s_true = s[:]

    if verbose:
        print(f"\nM_compat histogram (syndrome-compatible supports):")
        for m in sorted(compat_hist.keys()):
            pct = compat_hist[m] / (total_s - 1) * 100
            bar = "#" * min(m * 2, 40)
            print(f"  M_compat={m:3d}: {compat_hist[m]:6d} ({pct:5.2f}%) {bar}")

        print(f"\nM_true histogram (valid weight-w errors, all values nonzero):")
        for m in sorted(true_hist.keys()):
            pct = true_hist[m] / (total_s - 1) * 100
            bar = "#" * min(m * 2, 40)
            print(f"  M_true  ={m:3d}: {true_hist[m]:6d} ({pct:5.2f}%) {bar}")

        print(f"\n*** max M_compat = {max_M_compat} at s = {max_s_compat}")
        print(f"*** max M_true   = {max_M_true} at s = {max_s_true}")
        print(f"*** C(n-1,w-1)   = {comb(n-1, w-1)}")

        # Check evaluation syndromes
        print(f"\nEvaluation syndrome check:")
        for alpha in range(min(n, 5)):
            s_eval = [pow(alpha, i, p) for i in range(D)]
            # Compute M_compat and M_true for this syndrome
            mc = 0
            mt = 0
            for E in all_E:
                in_WE = True
                for normal in E_normals[E]:
                    dot = sum(normal[i] * s_eval[i] for i in range(D)) % p
                    if dot != 0:
                        in_WE = False
                        break
                if not in_WE:
                    continue
                mc += 1
                v = solve_vandermonde(list(E), s_eval[:w], p)
                if v and all(vi != 0 for vi in v):
                    mt += 1
            print(f"  s_{alpha} = {s_eval[:4]}... : M_compat={mc}, M_true={mt}")

    return max_M_compat, max_M_true


# ============================================================
# SYSTEMATIC TESTS
# ============================================================
print("=" * 70)
print("COMPARING M_compat vs M_true (syndrome-compatible vs valid errors)")
print("=" * 70)

results = []

for n, w, c, p in [
    # c = 1 cases (most interesting)
    (5, 2, 1, 5),
    (5, 2, 1, 7),
    (5, 2, 1, 11),
    (5, 3, 1, 5),
    (5, 3, 1, 7),
    (6, 2, 1, 7),
    (6, 3, 1, 7),
    (6, 4, 1, 7),
    (7, 2, 1, 7),
    (7, 3, 1, 7),
    (7, 3, 1, 11),
    # c = 2 cases
    (5, 2, 2, 5),
    (5, 2, 2, 7),
    (6, 2, 2, 7),
    (6, 3, 2, 7),
    (7, 3, 2, 7),
    # c = 3 cases
    (6, 2, 3, 7),
    (7, 3, 3, 7),
]:
    D = w + c
    if D > n or n > p:
        continue
    if p ** D > 300000:
        continue
    mc, mt = compute_true_M(n, w, c, p)
    if mc is not None:
        results.append((n, w, c, p, D, mc, mt))

# Summary
print("\n\n" + "=" * 70)
print("SUMMARY: M_compat vs M_true")
print("=" * 70)
print(f"{'n':>3} {'w':>3} {'c':>3} {'p':>5} {'D':>3} {'C(n-1,w-1)':>12} {'M_compat':>9} {'M_true':>7} {'gap':>6}")
print("-" * 70)
for n, w, c, p, D, mc, mt in results:
    gap = mc - mt
    print(f"{n:3d} {w:3d} {c:3d} {p:5d} {D:3d} {comb(n-1,w-1):12d} {mc:9d} {mt:7d} {gap:6d}")
