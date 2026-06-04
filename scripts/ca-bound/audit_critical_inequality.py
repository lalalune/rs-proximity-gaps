"""
Rigorous test of Delta_joint >= Delta(f, RS_k).

Also test ADVERSARIAL case: paired errors designed to minimize Delta_joint.
"""
import random

def find_prim_root(p, n):
    assert (p - 1) % n == 0
    g = 2
    while True:
        w = pow(g, (p - 1) // n, p)
        if pow(w, n, p) == 1 and pow(w, n // 2, p) != 1:
            return w
        g += 1

def test_critical_inequality(n, p, num_trials=1000):
    omega = find_prim_root(p, n)
    L = [pow(omega, i, p) for i in range(n)]
    n_half = n // 2

    # Build coset map: for i in [0,n), pair i with the index of -omega^i
    neg_map = {}  # i -> j where L[j] = -L[i]
    for i in range(n):
        neg = (-L[i]) % p
        for j in range(n):
            if L[j] == neg:
                neg_map[i] = j
                break

    # For each y_idx in L': sqrt_map[y_idx] = (i, j) with L[i]^2 = L[j]^2 = L'[y_idx]
    # i and j = neg_map[i]
    sqrt_pairs = []
    used = set()
    for i in range(n):
        if i not in used:
            j = neg_map[i]
            sqrt_pairs.append((i, j))
            used.add(i)
            used.add(j)
    assert len(sqrt_pairs) == n_half

    min_ratio = float('inf')
    violations = 0

    for trial in range(num_trials):
        # Random error pattern
        err_weight = random.randint(1, n - 1)
        err_positions = set(random.sample(range(n), err_weight))
        e_f = [0] * n
        for pos in err_positions:
            e_f[pos] = random.randint(1, p - 1)

        # Count Delta(f, g) = err_weight / n
        delta_f = err_weight / n

        # Count joint errors
        joint_errors = 0
        for (i, j) in sqrt_pairs:
            if e_f[i] != 0 or e_f[j] != 0:
                joint_errors += 1

        delta_joint = joint_errors / n_half

        ratio = delta_joint / delta_f if delta_f > 0 else float('inf')
        min_ratio = min(min_ratio, ratio)

        if delta_joint < delta_f - 1e-10:
            violations += 1

    print(f"n={n}, p={p}: {num_trials} random trials")
    print(f"  min(Delta_joint / Delta_f) = {min_ratio:.4f}")
    print(f"  violations (Delta_joint < Delta_f): {violations}")
    print()

    # ADVERSARIAL TEST: maximize err_weight while minimizing joint_errors
    # Strategy: pair all errors (e_f(x) = e_f(-x) for all x in error set)
    print("  ADVERSARIAL TEST (fully paired errors):")
    for err_frac in [0.2, 0.3, 0.4, 0.5]:
        num_pairs = int(err_frac * n_half)
        if num_pairs > n_half:
            num_pairs = n_half

        # Select num_pairs of the sqrt_pairs
        selected = random.sample(range(n_half), num_pairs)

        e_f = [0] * n
        for idx in selected:
            i, j = sqrt_pairs[idx]
            val = random.randint(1, p - 1)
            e_f[i] = val
            e_f[j] = val  # paired: same value -> e_odd = 0

        err_weight_actual = sum(1 for x in e_f if x != 0)
        delta_f = err_weight_actual / n

        joint_errors = 0
        for (i, j) in sqrt_pairs:
            if e_f[i] != 0 or e_f[j] != 0:
                joint_errors += 1

        delta_joint = joint_errors / n_half

        print(f"    err_frac={err_frac:.1f}: Delta_f={delta_f:.4f}, Delta_joint={delta_joint:.4f}, "
              f"ratio={delta_joint/delta_f:.4f}, {'OK' if delta_joint >= delta_f - 1e-10 else '*** VIOLATION ***'}")

    # ADVERSARIAL: paired with DIFFERENT values (e_f(x) != e_f(-x))
    print("  ADVERSARIAL (paired, different values):")
    for err_frac in [0.2, 0.3, 0.4, 0.5]:
        num_pairs = int(err_frac * n_half)
        if num_pairs > n_half:
            num_pairs = n_half

        selected = random.sample(range(n_half), num_pairs)

        e_f = [0] * n
        for idx in selected:
            i, j = sqrt_pairs[idx]
            e_f[i] = random.randint(1, p - 1)
            e_f[j] = random.randint(1, p - 1)
            while e_f[j] == e_f[i]:  # ensure different
                e_f[j] = random.randint(1, p - 1)

        err_weight_actual = sum(1 for x in e_f if x != 0)
        delta_f = err_weight_actual / n

        joint_errors = sum(1 for (i, j) in sqrt_pairs if e_f[i] != 0 or e_f[j] != 0)
        delta_joint = joint_errors / n_half

        print(f"    err_frac={err_frac:.1f}: Delta_f={delta_f:.4f}, Delta_joint={delta_joint:.4f}, "
              f"ratio={delta_joint/delta_f:.4f}, {'OK' if delta_joint >= delta_f - 1e-10 else '*** VIOLATION ***'}")

    # ADVERSARIAL: all UNPAIRED (one from each pair)
    print("  ADVERSARIAL (all unpaired):")
    for err_frac in [0.1, 0.2, 0.3, 0.4]:
        num_errs = int(err_frac * n)
        if num_errs > n_half:
            num_errs = n_half

        selected = random.sample(range(n_half), num_errs)
        e_f = [0] * n
        for idx in selected:
            i, j = sqrt_pairs[idx]
            e_f[i] = random.randint(1, p - 1)
            # e_f[j] = 0 (unpaired)

        err_weight_actual = sum(1 for x in e_f if x != 0)
        delta_f = err_weight_actual / n

        joint_errors = sum(1 for (i, j) in sqrt_pairs if e_f[i] != 0 or e_f[j] != 0)
        delta_joint = joint_errors / n_half

        print(f"    err_frac={err_frac:.1f}: Delta_f={delta_f:.4f}, Delta_joint={delta_joint:.4f}, "
              f"ratio={delta_joint/delta_f:.4f}, {'OK' if delta_joint >= delta_f - 1e-10 else '*** VIOLATION ***'}")

    print()

random.seed(123)
test_critical_inequality(32, 97, num_trials=5000)
test_critical_inequality(64, 193, num_trials=5000)
test_critical_inequality(128, 257, num_trials=2000)

print("="*60)
print("PROOF of Delta_joint >= Delta(f):")
print()
print("For each y in L', the coset {sqrt(y), -sqrt(y)} has 2 elements of L.")
print("If e_f(sqrt(y)) != 0 OR e_f(-sqrt(y)) != 0: y contributes to joint errors.")
print("This is the SAME condition as: at least one coset element has error.")
print()
print("Delta(f,g) = |{x in L : e_f(x) != 0}| / n")
print("           = (sum over y in L' of |{x in coset_y : e_f(x) != 0}|) / n")
print("           = (sum over y of c_y) / n   where c_y in {0, 1, 2}")
print()
print("Delta_joint = |{y : c_y >= 1}| / (n/2)")
print()
print("Now: sum c_y = wt(e_f). And sum 1[c_y >= 1] = joint_errors.")
print("Since c_y <= 2: sum c_y <= 2 * sum 1[c_y >= 1].")
print("So: wt(e_f) <= 2 * joint_errors.")
print("Dividing: wt(e_f)/n <= 2 * joint_errors/n = joint_errors / (n/2) = Delta_joint.")
print("Therefore: Delta(f,g) <= Delta_joint.  QED")
print()
print("Also: sum c_y >= sum 1[c_y >= 1] (since c_y >= 1 implies c_y >= 1).")
print("So: wt(e_f) >= joint_errors.")
print("Dividing: Delta(f,g) = wt(e_f)/n >= joint_errors/n = Delta_joint * (n/2)/n = Delta_joint/2.")
print("Therefore: Delta_joint/2 <= Delta(f,g) <= Delta_joint.")
print()
print("KEY: Delta_joint >= Delta(f,g) >= Delta(f, RS_k) since g minimizes Delta(f,g).")
print("WRONG - Delta_joint uses SPECIFIC (g_even, g_odd), not the minimizer.")
print()
print("CORRECTION: Delta_joint = min over (g_even, g_odd) of joint distance.")
print("For any specific g = g_even(x^2) + x*g_odd(x^2) in RS_k:")
print("  Delta(f,g) <= Delta_joint((f_even,f_odd), (g_even,g_odd))")
print("So: Delta(f, RS_k) = min_g Delta(f,g) <= min_{g_even,g_odd} Delta_joint = Delta_joint")
print("Since every g in RS_k decomposes as (g_even, g_odd) in RS_{k/2}^2.")
print("QED (for real this time)")
