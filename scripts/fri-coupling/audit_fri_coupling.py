"""
Audit FRI folding coupling: how does error structure (paired vs unpaired)
affect proximity of f_even and f_odd to RS_{k/2}?

Setup:
  - L = <omega> subset F_p^*, |L| = n = 2^K
  - f on L with Delta(f, RS_k) = delta  (nearest codeword g, error e = f - g)
  - f_even(y) = (f(sqrt_y) + f(-sqrt_y))/2    on L' = L^2, |L'| = n/2
  - f_odd(y)  = (f(sqrt_y) - f(-sqrt_y))/(2*sqrt_y) on L' = L^2

Two constructions:
  1. UNPAIRED errors: each error x has -x NOT in the error set
  2. PAIRED errors (symmetric): error set is {x,-x} pairs, e(x)=e(-x)
  3. PAIRED errors (antisymmetric): error set is {x,-x} pairs, e(x)=-e(-x)

For each: measure Delta(f_even, RS_{k/2}), Delta(f_odd, RS_{k/2}),
count alpha where f_even + alpha*f_odd is delta-close / (delta/2)-close to RS_{k/2}.

Key: g = sum_{j=0}^{k-1} a_j X^j.
  g_even(y) = sum_{j even, j<k} a_j y^{j/2}  => degree < k/2  => in RS_{k/2} on L'
  g_odd(y)  = sum_{j odd, j<k} a_j y^{(j-1)/2} => degree < k/2 => in RS_{k/2} on L'

So Delta(f_even, RS_{k/2}) <= wt(e_even)/(n/2) and similarly for odd.
The DFT projection distance equals the distance to g_even/g_odd respectively.
"""

import random
from math import gcd

random.seed(2026)

# ─── Arithmetic helpers ───

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    d = 5
    while d * d <= n:
        if n % d == 0 or n % (d + 2) == 0: return False
        d += 6
    return True

def prime_factors(n):
    out = set(); d = 2; nn = n
    while d * d <= nn:
        while nn % d == 0: out.add(d); nn //= d
        d += 1
    if nn > 1: out.add(nn)
    return list(out)

def find_generator(p):
    pf = prime_factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in pf):
            return g
    raise RuntimeError("no generator found")

def find_omega(p, n):
    g = find_generator(p)
    return pow(g, (p - 1) // n, p)

def modinv(a, p):
    return pow(a, p - 2, p)

def find_suitable_prime(n, min_p=100):
    p = min_p + n - (min_p % n) + 1
    while not is_prime(p):
        p += n
    return p

def poly_eval(coeffs, x, p):
    val = 0; xi = 1
    for c in coeffs:
        val = (val + c * xi) % p
        xi = xi * x % p
    return val

# ─── RS distance on ordered domain ───

def rs_distance_to_planted(f_vals, g_vals, n2):
    """Distance between f and planted codeword g on domain of size n2."""
    return sum(1 for i in range(n2) if f_vals[i] != g_vals[i]) / n2

def rs_min_distance_dft(f_vals, omega_prime, p, n_prime, k_prime):
    """
    Compute distance from f to RS_{k_prime} on domain L' = <omega_prime> of order n_prime.
    Uses DFT projection: nearest codeword has hat_g_j = hat_f_j for j < k_prime, 0 for j >= k_prime.

    DFT: hat_f_j = sum_{i=0}^{n'-1} f_vals[i] * omega'^{-ij}
    where f_vals[i] = f(omega'^i).
    """
    inv_omega = modinv(omega_prime, p)
    inv_n = modinv(n_prime, p)

    # Forward DFT
    hat_f = [0] * n_prime
    for j in range(n_prime):
        s = 0
        w = pow(inv_omega, j, p)
        wi = 1
        for i in range(n_prime):
            s = (s + f_vals[i] * wi) % p
            wi = wi * w % p
        hat_f[j] = s

    # Project: keep only [0, k_prime)
    hat_g = [hat_f[j] if j < k_prime else 0 for j in range(n_prime)]

    # Inverse DFT
    g_vals = [0] * n_prime
    for i in range(n_prime):
        s = 0
        wi = 1
        oi = pow(omega_prime, i, p)
        for j in range(n_prime):
            s = (s + hat_g[j] * wi) % p
            wi = wi * oi % p
        g_vals[i] = s * inv_n % p

    disagree = sum(1 for i in range(n_prime) if f_vals[i] != g_vals[i])
    return disagree / n_prime, g_vals

# ─── FRI folding ───

def fri_decompose(f_vals, L, p, n):
    """
    Decompose f on L into f_even and f_odd on L'.
    L[i] = omega^i. Pairing: (L[i], L[i + n/2]) = (x, -x).
    f_even(x^2) = (f(x) + f(-x)) / 2
    f_odd(x^2)  = (f(x) - f(-x)) / (2x)

    L' = {L[0]^2, L[1]^2, ..., L[n/2-1]^2} = {omega^0, omega^2, ..., omega^{n-2}}
    So L' = <omega^2> of order n/2, and L'[i] = omega^{2i}.
    """
    n2 = n // 2
    inv2 = modinv(2, p)
    f_even = []
    f_odd = []
    L_prime = []

    for i in range(n2):
        x = L[i]
        fx = f_vals[i]
        fnx = f_vals[i + n2]
        y = x * x % p

        fe = (fx + fnx) * inv2 % p
        fo = (fx - fnx) % p * modinv(2 * x % p, p) % p

        f_even.append(fe)
        f_odd.append(fo)
        L_prime.append(y)

    return f_even, f_odd, L_prime

def fri_fold(f_even, f_odd, alpha, p, n2):
    return [(f_even[i] + alpha * f_odd[i]) % p for i in range(n2)]

# ─── Construction helpers ───

def make_codeword(L, p, k):
    n = len(L)
    coeffs = [random.randint(0, p - 1) for _ in range(k)]
    return [poly_eval(coeffs, L[i], p) for i in range(n)], coeffs

def construct_unpaired_errors(n, num_errors):
    """Pick error positions from first half only (indices 0..n/2-1)."""
    n2 = n // 2
    available = list(range(n2))
    random.shuffle(available)
    if num_errors > n2:
        raise ValueError(f"Cannot have {num_errors} unpaired errors with n={n}")
    return sorted(available[:num_errors])

def construct_paired_errors(n, num_errors):
    """Pick {x, -x} pairs. num_errors must be even."""
    n2 = n // 2
    if num_errors % 2 != 0:
        raise ValueError("num_errors must be even for paired errors")
    num_pairs = num_errors // 2
    available = list(range(n2))
    random.shuffle(available)
    pair_indices = sorted(available[:num_pairs])
    positions = []
    for i in pair_indices:
        positions.append(i)
        positions.append(i + n2)
    return sorted(positions)

def add_errors(g_vals, p, error_positions, mode="random"):
    """
    mode = "random": independent random nonzero errors
    mode = "symmetric": e(x) = e(-x) for each pair
    mode = "antisymmetric": e(x) = -e(-x) for each pair
    """
    n = len(g_vals)
    n2 = n // 2
    f = list(g_vals)

    if mode == "random":
        for pos in error_positions:
            val = random.randint(1, p - 1)
            f[pos] = (g_vals[pos] + val) % p
    elif mode == "symmetric":
        done = set()
        for pos in error_positions:
            if pos in done: continue
            partner = (pos + n2) % n
            val = random.randint(1, p - 1)
            f[pos] = (g_vals[pos] + val) % p
            if partner in error_positions:
                f[partner] = (g_vals[partner] + val) % p
                done.add(partner)
            done.add(pos)
    elif mode == "antisymmetric":
        done = set()
        for pos in error_positions:
            if pos in done: continue
            partner = (pos + n2) % n
            val = random.randint(1, p - 1)
            f[pos] = (g_vals[pos] + val) % p
            if partner in error_positions:
                f[partner] = (g_vals[partner] + (p - val)) % p  # -val mod p
                done.add(partner)
            done.add(pos)

    return f

# ─── Main experiment ───

def run_experiment(n, K, k, num_errors, p=None):
    assert n == 2**K
    if p is None:
        p = find_suitable_prime(n, max(200, 4 * n))

    omega = find_omega(p, n)
    L = [pow(omega, i, p) for i in range(n)]
    n2 = n // 2
    k2 = k // 2
    omega_prime = omega * omega % p  # primitive (n/2)-th root of unity

    rho = k / n
    delta = num_errors / n

    print(f"{'='*70}")
    print(f"Parameters: n={n}, K={K}, p={p}, k={k}, k2={k2}, rho={rho:.4f}")
    print(f"  delta={delta:.4f}, num_errors={num_errors}")
    print(f"  Johnson bound = {1 - rho**0.5:.4f}")
    print(f"  Unique decoding = {(1-rho)/2:.4f}")
    print(f"  Capacity = {1 - rho:.4f}")
    print(f"  delta/2 = {delta/2:.4f}")
    print(f"{'='*70}")

    # Verify domain structure
    assert L[0] == 1
    assert pow(omega, n, p) == 1
    assert pow(omega, n2, p) == p - 1  # omega^{n/2} = -1
    assert pow(omega_prime, n2, p) == 1  # omega'^{n/2} = 1

    # Verify L' ordering: L_prime[i] = L[i]^2 = omega^{2i} = omega_prime^i
    Lp_check = [pow(omega_prime, i, p) for i in range(n2)]
    Lp_from_L = [L[i] * L[i] % p for i in range(n2)]
    assert Lp_check == Lp_from_L, "L' ordering mismatch"

    # Make a random RS_k codeword g(x) = sum a_j x^j, deg < k
    g_vals, g_coeffs = make_codeword(L, p, k)

    # Decompose g into g_even and g_odd
    # g(x) = sum_{j even} a_j x^j + x * sum_{j odd} a_j x^{j-1}
    #       = g_even(x^2) + x * g_odd(x^2)
    # g_even(y) = sum_{j=0,2,4,...} a_j y^{j/2},  degree < ceil(k/2) = k/2
    # g_odd(y)  = sum_{j=1,3,5,...} a_j y^{(j-1)/2}, degree < floor(k/2) = k/2 (when k even)
    ge_coeffs = [g_coeffs[j] if j < k else 0 for j in range(0, k, 2)]
    go_coeffs = [g_coeffs[j] if j < k else 0 for j in range(1, k, 2)]
    ge_from_coeffs = [poly_eval(ge_coeffs, pow(omega_prime, i, p), p) for i in range(n2)]
    go_from_coeffs = [poly_eval(go_coeffs, pow(omega_prime, i, p), p) for i in range(n2)]

    # Verify decomposition
    ge_from_fri, go_from_fri, Lp = fri_decompose(g_vals, L, p, n)
    assert ge_from_fri == ge_from_coeffs, "g_even decomposition mismatch"
    assert go_from_fri == go_from_coeffs, "g_odd decomposition mismatch"

    results = {}

    for label, err_pos, mode in [
        ("UNPAIRED", construct_unpaired_errors(n, num_errors), "random"),
        ("PAIRED(sym)", construct_paired_errors(n, num_errors), "symmetric"),
        ("PAIRED(anti)", construct_paired_errors(n, num_errors), "antisymmetric"),
    ]:
        print(f"\n--- Construction: {label} ---")
        f = add_errors(g_vals, p, err_pos, mode=mode)

        actual_err = sum(1 for i in range(n) if f[i] != g_vals[i])
        print(f"  actual errors: {actual_err}/{n}  (target {num_errors})")

        # Decompose f
        fe, fo, _ = fri_decompose(f, L, p, n)

        # Error components relative to planted codeword components
        ee = [(fe[i] - ge_from_coeffs[i]) % p for i in range(n2)]
        eo = [(fo[i] - go_from_coeffs[i]) % p for i in range(n2)]
        wt_ee = sum(1 for v in ee if v != 0)
        wt_eo = sum(1 for v in eo if v != 0)

        # Distance to planted codeword components
        delta_even_planted = wt_ee / n2
        delta_odd_planted = wt_eo / n2

        # Distance to nearest RS_{k/2} codeword (via DFT projection on L')
        delta_even_min, _ = rs_min_distance_dft(fe, omega_prime, p, n2, k2)
        delta_odd_min, _ = rs_min_distance_dft(fo, omega_prime, p, n2, k2)

        print(f"  wt(e_even) = {wt_ee}/{n2},  wt(e_odd) = {wt_eo}/{n2}")
        print(f"  Delta(f_even, g_even)  = {delta_even_planted:.4f}  [to planted]")
        print(f"  Delta(f_odd,  g_odd)   = {delta_odd_planted:.4f}  [to planted]")
        print(f"  Delta(f_even, RS_{k2}) = {delta_even_min:.4f}  [to nearest, DFT proj]")
        print(f"  Delta(f_odd,  RS_{k2}) = {delta_odd_min:.4f}  [to nearest, DFT proj]")
        print(f"  max(D_even_min, D_odd_min) = {max(delta_even_min, delta_odd_min):.4f}")
        print(f"  delta/2 = {delta/2:.4f}")
        print(f"  max > delta/2 ? {max(delta_even_min, delta_odd_min) > delta/2}")

        # Count alpha where f_even + alpha*f_odd is close to RS_{k/2}
        count_delta = 0
        count_half = 0
        min_folded_dist = 1.0
        for alpha in range(p):
            folded = fri_fold(fe, fo, alpha, p, n2)
            d_folded, _ = rs_min_distance_dft(folded, omega_prime, p, n2, k2)
            if d_folded < min_folded_dist:
                min_folded_dist = d_folded
            if d_folded <= delta + 1e-9:
                count_delta += 1
            if d_folded <= delta / 2 + 1e-9:
                count_half += 1

        print(f"  min_alpha Delta(fold, RS_{k2}) = {min_folded_dist:.4f}")
        print(f"  #alpha with Delta(fold, RS_{k2}) <= delta:   {count_delta}/{p}")
        print(f"  #alpha with Delta(fold, RS_{k2}) <= delta/2: {count_half}/{p}")

        results[label] = {
            'wt_ee': wt_ee, 'wt_eo': wt_eo,
            'delta_even_planted': delta_even_planted,
            'delta_odd_planted': delta_odd_planted,
            'delta_even_min': delta_even_min,
            'delta_odd_min': delta_odd_min,
            'count_delta': count_delta,
            'count_half': count_half,
            'min_folded_dist': min_folded_dist,
        }

    # t' for RS_{k/2} on L'
    t_prime = n2 * (1 - rho**0.5)
    prediction = n2 / t_prime if t_prime > 0 else float('inf')

    # ─── Summary ───
    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}")
    labels = ["UNPAIRED", "PAIRED(sym)", "PAIRED(anti)"]
    header = f"  {'':32s}" + "".join(f"{l:>14s}" for l in labels)
    print(header)
    for field, name in [
        ('wt_ee', 'wt(e_even)'),
        ('wt_eo', 'wt(e_odd)'),
        ('delta_even_planted', 'D(f_even, g_even)'),
        ('delta_odd_planted', 'D(f_odd, g_odd)'),
        ('delta_even_min', 'D(f_even, RS) min'),
        ('delta_odd_min', 'D(f_odd, RS) min'),
        ('min_folded_dist', 'min_a D(fold, RS)'),
        ('count_delta', '#a fold<=delta'),
        ('count_half', '#a fold<=delta/2'),
    ]:
        vals = []
        for l in labels:
            v = results[l][field]
            if isinstance(v, float):
                vals.append(f"{v:14.4f}")
            else:
                vals.append(f"{v:14d}")
        print(f"  {name:32s}" + "".join(vals))

    tp_label = "n/(2t') prediction"
    print(f"  {tp_label:32s} {prediction:14.2f}")
    print(f"  {'delta':32s} {delta:14.4f}")
    print(f"  {'delta/2':32s} {delta/2:14.4f}")
    print()

def main():
    print("=" * 70)
    print("FRI FOLDING COUPLING AUDIT")
    print("How error structure affects even/odd proximity after decomposition")
    print("=" * 70)

    # NOTE: unpaired errors need num_errors <= n/2 (one per {x,-x} pair)
    #       paired errors need num_errors even

    # ─── Experiment 1: n=32, k=8 ───
    # Johnson = 0.5, capacity = 0.75
    # Pick 16 errors (delta=0.5), at Johnson bound, max unpaired
    print("\n\n### EXPERIMENT 1: n=32, k=8, delta=0.5 (16 errors) ###")
    run_experiment(n=32, K=5, k=8, num_errors=16)

    # ─── Experiment 2: n=32, k=4 ───
    # Johnson ~= 0.646, capacity = 0.875
    # Pick 14 errors (delta=0.4375), unpaired ok (14<=16), paired ok (14 even)
    print("\n\n### EXPERIMENT 2: n=32, k=4, delta=0.4375 (14 errors) ###")
    run_experiment(n=32, K=5, k=4, num_errors=14)

    # ─── Experiment 3: n=64, k=8 ───
    # Johnson ~= 0.646, capacity = 0.875
    # Pick 32 errors (delta=0.5), max unpaired for n=64
    print("\n\n### EXPERIMENT 3: n=64, k=8, delta=0.5 (32 errors) ###")
    run_experiment(n=64, K=6, k=8, num_errors=32)

    # ─── Experiment 4: n=64, k=8, fewer errors ───
    # 20 errors (delta=0.3125)
    print("\n\n### EXPERIMENT 4: n=64, k=8, delta=0.3125 (20 errors) ###")
    run_experiment(n=64, K=6, k=8, num_errors=20)

    # ─── Key question summary ───
    print("\n" + "=" * 70)
    print("KEY QUESTION: When Delta(f, RS_k) = delta,")
    print("does max(Delta_even, Delta_odd) > delta/2 ALWAYS hold?")
    print()
    print("Theory prediction:")
    print("  UNPAIRED: errors spread to BOTH even and odd")
    print("    => both f_even and f_odd are far from RS_{k/2}")
    print("  PAIRED(sym): e(x)=e(-x) => e_even has full error, e_odd=0")
    print("    => f_even is far, f_odd is IN RS_{k/2} (worst case!)")
    print("  PAIRED(anti): e(x)=-e(-x) => e_even=0, e_odd has full error")
    print("    => f_even is IN RS_{k/2}, f_odd is far")
    print()
    print("For FRI soundness: PAIRED(sym) is the critical case.")
    print("When f_odd = g_odd (a codeword), the fold f_even + alpha*f_odd")
    print("only varies by alpha*(codeword), so proximity of fold to RS_{k/2}")
    print("equals proximity of f_even + alpha*g_odd to RS_{k/2}.")
    print("Since g_odd is in RS_{k/2}, this = proximity of f_even to RS_{k/2}.")
    print("So ALL alpha give the same distance! The fold gives no randomness.")
    print("=" * 70)

if __name__ == "__main__":
    main()
