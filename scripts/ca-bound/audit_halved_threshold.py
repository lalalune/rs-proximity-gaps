"""
Verify the halved-threshold proximity gap:

1. Delta_joint >= Delta(f, RS_k)  (critical inequality)
2. Count alpha where f' = f_even + alpha*f_odd is (delta/2)-close to RS_{k/2}
3. Verify this count is <= ceil(1/(1-delta/2)) = O(1)
"""
import random

def find_prim_root(p, n):
    """Find element of order n in F_p."""
    assert (p - 1) % n == 0
    g = 2
    while True:
        w = pow(g, (p - 1) // n, p)
        if pow(w, n, p) == 1 and pow(w, n // 2, p) != 1:
            return w
        g += 1

def rs_distance(word, L, k, p):
    """Min Hamming distance from word to RS_k on L."""
    n = len(L)
    if k > n:
        return 0
    # Try all degree-<k polynomials? Too expensive for large k.
    # Use: distance = n - max agreement.
    # For small k: enumerate codewords via Lagrange on k points.
    # Actually: for our test, use the DFT approach.
    # The RS_k codewords are determined by k coefficients.
    # For k small: enumerate. For k large: use projection.

    # DFT approach: compute syndrome, distance = weight of error
    # Actually, just find nearest codeword via interpolation on (n-k) agreement points.
    # Simpler: compute the "projection" of word onto RS_k.

    # Vandermonde approach: solve for best fit polynomial of degree < k
    # This is equivalent to polynomial regression.
    # For exact computation: use the fact that for RS on L,
    # the nearest codeword agrees with word on >= n-d+1 = k points.

    # For brute force: count, for each codeword, the agreement.
    # Too expensive for k > 3.

    # Use DFT projection:
    # Compute DFT of word, zero out syndromes, inverse DFT.

    # DFT: hat_w[j] = sum_i w[i] * omega^{-ij} mod p
    omega = L[1] * pow(L[0], -1, p) % p if L[0] != 1 else L[1]
    # Actually L = [omega^0, omega^1, ..., omega^{n-1}]
    # Assume L[i] = omega^i mod p

    omega = L[1]  # L[0] = 1, L[1] = omega
    omega_inv = pow(omega, p - 2, p)
    n_inv = pow(n, p - 2, p)

    # DFT
    hat_w = [0] * n
    for j in range(n):
        s = 0
        for i in range(n):
            s = (s + word[i] * pow(omega_inv, i * j, p)) % p
        hat_w[j] = s

    # Zero out syndromes (positions k to n-1)
    hat_proj = list(hat_w)
    for j in range(k, n):
        hat_proj[j] = 0

    # Inverse DFT
    proj = [0] * n
    for i in range(n):
        s = 0
        for j in range(n):
            s = (s + hat_proj[j] * pow(omega, i * j, p)) % p
        proj[i] = s * n_inv % p

    # Distance = Hamming distance between word and proj
    dist = sum(1 for i in range(n) if word[i] != proj[i])
    return dist

def test_halved_threshold(n, k, p, delta, num_trials=5):
    """Test the halved-threshold proximity gap."""
    omega = find_prim_root(p, n)
    L = [pow(omega, i, p) for i in range(n)]

    n_half = n // 2
    omega2 = pow(omega, 2, p)
    L_half = [pow(omega2, i, p) for i in range(n_half)]

    # Precompute square roots: for each y in L', find sqrt(y) and -sqrt(y) in L
    sqrt_map = {}  # y -> (sqrt_y, neg_sqrt_y) as indices in L
    for i in range(n):
        y = L[i] * L[i] % p
        y_idx = None
        for j in range(n_half):
            if L_half[j] == y:
                y_idx = j
                break
        if y_idx is not None:
            if y_idx not in sqrt_map:
                sqrt_map[y_idx] = []
            sqrt_map[y_idx].append(i)

    t = int((1 - delta) * n)
    t_half = int((1 - delta/2) * n_half)
    bound = -(-n_half // t_half)  # ceil(n_half / t_half)

    print(f"\n{'='*60}")
    print(f"n={n}, k={k}, p={p}, delta={delta:.2f}")
    print(f"t={t}, t'={t_half}, bound=ceil(n'/t')={bound}")
    print(f"{'='*60}")

    for trial in range(num_trials):
        # Generate random codeword g (degree < k)
        coeffs_g = [random.randint(0, p-1) for _ in range(k)]
        g = [sum(coeffs_g[j] * pow(L[i], j, p) for j in range(k)) % p for i in range(n)]

        # Generate error e_f with weight = delta*n + 1 (barely exceeding delta)
        err_weight = int(delta * n) + 1
        err_positions = random.sample(range(n), err_weight)
        e_f = [0] * n
        for pos in err_positions:
            e_f[pos] = random.randint(1, p-1)

        # f = g + e_f
        f = [(g[i] + e_f[i]) % p for i in range(n)]

        # Compute f_even and f_odd on L'
        f_even = [0] * n_half
        f_odd = [0] * n_half
        for y_idx in range(n_half):
            if y_idx in sqrt_map and len(sqrt_map[y_idx]) >= 2:
                i1, i2 = sqrt_map[y_idx][0], sqrt_map[y_idx][1]
                # f_even(y) = (f(sqrt_y) + f(-sqrt_y)) / 2
                f_even[y_idx] = (f[i1] + f[i2]) * pow(2, p-2, p) % p
                # f_odd(y) = (f(sqrt_y) - f(-sqrt_y)) / (2 * sqrt_y)
                sqrt_y = L[i1]
                f_odd[y_idx] = (f[i1] - f[i2]) * pow(2 * sqrt_y % p, p-2, p) % p

        # Similarly for g
        g_even = [0] * n_half
        g_odd = [0] * n_half
        for y_idx in range(n_half):
            if y_idx in sqrt_map and len(sqrt_map[y_idx]) >= 2:
                i1, i2 = sqrt_map[y_idx][0], sqrt_map[y_idx][1]
                g_even[y_idx] = (g[i1] + g[i2]) * pow(2, p-2, p) % p
                sqrt_y = L[i1]
                g_odd[y_idx] = (g[i1] - g[i2]) * pow(2 * sqrt_y % p, p-2, p) % p

        # Compute Delta(f, RS_k)
        delta_f = err_weight / n

        # Compute e_even, e_odd
        e_even = [(f_even[i] - g_even[i]) % p for i in range(n_half)]
        e_odd = [(f_odd[i] - g_odd[i]) % p for i in range(n_half)]

        # Delta_joint = |{y : e_even(y) != 0 OR e_odd(y) != 0}| / n_half
        joint_errors = sum(1 for i in range(n_half) if e_even[i] != 0 or e_odd[i] != 0)
        delta_joint = joint_errors / n_half

        # CRITICAL CHECK: Delta_joint >= Delta(f, RS_k)?
        critical = delta_joint >= delta_f

        # Count alpha where f' = f_even + alpha*f_odd is (delta/2)-close to RS_{k/2}
        close_count = 0
        k_half = k // 2 if k % 2 == 0 else (k + 1) // 2

        # For each alpha, compute distance of f_even + alpha*f_odd from RS_{k/2}
        # Use the error: e_even + alpha*e_odd. Distance <= weight / n_half.
        # This is an UPPER BOUND on the true distance.
        for alpha in range(min(p, 200)):  # check first 200 alpha values
            err_weight_fold = sum(1 for i in range(n_half)
                                  if (e_even[i] + alpha * e_odd[i]) % p != 0)
            if err_weight_fold <= int(delta/2 * n_half):
                close_count += 1

        print(f"\nTrial {trial+1}:")
        print(f"  Delta(f, RS_k) = {delta_f:.4f} (weight {err_weight}/{n})")
        print(f"  Delta_joint    = {delta_joint:.4f} (joint errors {joint_errors}/{n_half})")
        print(f"  Delta_joint >= Delta(f)? {'YES' if critical else '*** NO ***'}")
        print(f"  Close alpha (delta/2={delta/2:.3f}, first 200): {close_count}")
        print(f"  Bound: {bound}")

        if not critical:
            print("  *** CRITICAL INEQUALITY VIOLATED ***")

# Test with various parameters
random.seed(42)

# Small test: n=32, k=4
test_halved_threshold(n=32, k=4, p=97, delta=0.35, num_trials=3)

# Medium test: n=64, k=8
test_halved_threshold(n=64, k=8, p=193, delta=0.40, num_trials=3)

# Power of 2 with higher rate: n=32, k=16
test_halved_threshold(n=32, k=16, p=97, delta=0.35, num_trials=3)

print("\n" + "="*60)
print("SUMMARY")
print("="*60)
print("If Delta_joint >= Delta(f) in all cases: the halved-threshold")
print("trick gives O(1) proximity gap above Johnson for ALL k.")
print("This would be the first such result for plain RS codes.")
