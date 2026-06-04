"""
Test: does |R_w| depend on the syndrome c?

Hypothesis: |R_w| is approximately the same for all syndromes.
If true: the phase psi(-<xi,c>) averages out, and |R_w| depends only on (n,k,p,w).
"""
import cmath, math
from itertools import product as iter_product

def find_prim_root(p, n):
    assert (p-1) % n == 0
    for g in range(2, p):
        w = pow(g, (p-1)//n, p)
        if pow(w, n, p) == 1:
            ok = True; tmp = n; d = 2
            while d*d <= tmp:
                while tmp % d == 0:
                    if pow(w, n//d, p) == 1: ok = False
                    tmp //= d
                d += 1
            if tmp > 1 and pow(w, n//tmp, p) == 1: ok = False
            if ok: return w
    return None

def psi(a, p):
    return cmath.exp(2j * cmath.pi * (a % p) / p)

def compute_Rw_all_syndromes(n, k, p, w_target):
    """Compute |R_w| for ALL possible syndromes (p^{n-k} of them)."""
    omega = find_prim_root(p, n)
    dim = n - k
    omega_inv = pow(omega, p-2, p)

    # Precompute S_w(z)
    S_w = []
    for z in range(n+1):
        val = 0
        for j in range(min(w_target, z) + 1):
            val += math.comb(z, j) * math.comb(n-z, w_target-j) * (1-p)**j
        val *= (-1)**w_target
        S_w.append(val)

    # Precompute: for each xi != 0, store (z(xi), <xi,·> as function of syndrome)
    # Actually: for each xi, compute z and the "syndrome index" sum_r xi_r * c_r

    # For efficiency: precompute all xi data
    xi_data = []  # list of (z, phase_func) where phase_func maps syndrome to psi value

    for xi_tuple in iter_product(range(p), repeat=dim):
        if all(x == 0 for x in xi_tuple):
            continue

        # Compute Z(xi)
        z = 0
        for i in range(n):
            val = 0
            omi = pow(omega_inv, i, p)
            power = 1
            for r in range(dim):
                val = (val + xi_tuple[r] * power) % p
                power = power * omi % p
            if val == 0:
                z += 1

        xi_data.append((z, list(xi_tuple)))

    main = math.comb(n, w_target) * (p-1)**w_target / p**dim

    # For each syndrome c, compute R_w
    Rw_values = []

    # Sample syndromes (if too many, sample randomly)
    import random
    random.seed(42)

    if p**dim <= 10000:
        # Enumerate all syndromes
        for c_tuple in iter_product(range(p), repeat=dim):
            R = 0j
            for (z, xi) in xi_data:
                inner = sum(xi[r] * c_tuple[r] for r in range(dim)) % p
                R += S_w[z] * psi(-inner, p)
            R /= p**dim
            Rw_values.append(abs(R))
    else:
        # Sample
        for _ in range(500):
            c_tuple = tuple(random.randint(0, p-1) for _ in range(dim))
            R = 0j
            for (z, xi) in xi_data:
                inner = sum(xi[r] * c_tuple[r] for r in range(dim)) % p
                R += S_w[z] * psi(-inner, p)
            R /= p**dim
            Rw_values.append(abs(R))

    return Rw_values, main

# Test n=6, k=3, p=7
print("n=6, k=3, p=7, w=2:")
vals, main = compute_Rw_all_syndromes(6, 3, 7, 2)
print(f"  Main = {main:.4f}")
print(f"  |R_w| values: min={min(vals):.4f}, max={max(vals):.4f}, mean={sum(vals)/len(vals):.4f}")
print(f"  Unique values: {sorted(set(round(v, 4) for v in vals))}")
print(f"  #violations (|R|>=1): {sum(1 for v in vals if v >= 1)}/{len(vals)}")

# Test n=8, k=4, p=17
print("\nn=8, k=4, p=17, w=2:")
vals, main = compute_Rw_all_syndromes(8, 4, 17, 2)
print(f"  Main = {main:.6f}")
print(f"  |R_w| values: min={min(vals):.6f}, max={max(vals):.6f}")
uniq = sorted(set(round(v, 4) for v in vals))
print(f"  Unique values (rounded to 4dp): {uniq[:20]}{'...' if len(uniq)>20 else ''}")
print(f"  #violations: {sum(1 for v in vals if v >= 1)}/{len(vals)}")

# Test n=6, k=3, p=13
print("\nn=6, k=3, p=13, w=2:")
vals, main = compute_Rw_all_syndromes(6, 3, 13, 2)
print(f"  Main = {main:.6f}")
print(f"  |R_w| values: min={min(vals):.6f}, max={max(vals):.6f}")
uniq = sorted(set(round(v, 4) for v in vals))
print(f"  Unique values: {uniq[:20]}{'...' if len(uniq)>20 else ''}")
print(f"  #violations: {sum(1 for v in vals if v >= 1)}/{len(vals)}")
