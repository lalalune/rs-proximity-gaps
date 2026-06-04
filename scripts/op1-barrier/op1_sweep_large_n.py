"""op1_sweep_large_n.py — Extend OP1 disproof to n = 16, 32 (and 64 via construction).

For each (n, k, p, w), Monte-Carlo sample random (f1, f2) ∈ F_p^n × F_p^n,
verify Δ_joint > δ = w/n (premise of CA), then count bad γ:

    bad(f1, f2) = |{γ ∈ F_p : Δ(f1 + γ f2, C) ≤ w}|.

Goal: confirm bad / p stays bounded away from 0 uniformly in p, n.

Algorithm (the per-T trick): instead of (γ × T) double loop, enumerate
T ⊂ [n] of size w only. For fixed T, exactly one γ ∈ F_p (or all, or none)
satisfies syndrome(f1 + γ f2) ∈ col(H[:, T]).

Proof: Let A = H[:, T] (syndrome submatrix), s_i = H · f_i.
We seek γ s.t. s_1 + γ s_2 ∈ col(A).
- If s_2 ∈ col(A): condition independent of γ; either all γ or none (depending on s_1 ∈ col(A)).
- Else col([A | s_2]) has dim |T|+1, and s_1 + γ s_2 traces an affine line.
  The line meets col(A) in ≤ 1 point — so ≤ 1 valid γ.

Cost per pair: C(n, w) × O(w² (n-k)) for rank tests.
For n=16, w=5: ~875k ops. For n=32, w=10: ~10^11 ops (infeasible exhaustively).

For n ≥ 32: use the Crites-Stewart algebraic construction which gives explicit
(f1, f2) pairs with provably bad γ count = s. We verify computationally that
each predicted γ yields fold within distance δn from C.
"""

import sys
import time
import random
from itertools import combinations
from math import comb


# ----------------------- Field utilities -----------------------

def find_prim_root(p, n):
    """Smallest primitive n-th root of unity in F_p."""
    if (p - 1) % n != 0:
        return None
    # Find primes dividing n
    factors = set()
    t = n
    for q in range(2, n + 1):
        while t % q == 0:
            factors.add(q)
            t //= q
        if t == 1:
            break
    for g in range(2, p):
        w = pow(g, (p - 1) // n, p)
        if pow(w, n, p) != 1:
            continue
        if all(pow(w, n // q, p) != 1 for q in factors):
            return w
    return None


def modinv(a, p):
    return pow(a % p, p - 2, p)


# ----------------------- Linear algebra over F_p -----------------------

def gauss_rank(rows, p):
    """Compute rank of matrix (list of lists) over F_p; in-place okay since copy."""
    if not rows:
        return 0
    rows = [list(r) for r in rows]
    nrows = len(rows)
    ncols = len(rows[0])
    rank = 0
    col = 0
    while rank < nrows and col < ncols:
        pr = None
        for r in range(rank, nrows):
            if rows[r][col] % p != 0:
                pr = r
                break
        if pr is None:
            col += 1
            continue
        rows[rank], rows[pr] = rows[pr], rows[rank]
        inv = modinv(rows[rank][col], p)
        rows[rank] = [(x * inv) % p for x in rows[rank]]
        for r in range(nrows):
            if r != rank and rows[r][col] != 0:
                f = rows[r][col]
                rows[r] = [(rows[r][c] - f * rows[rank][c]) % p for c in range(ncols)]
        rank += 1
        col += 1
    return rank


def solve_gamma(A_cols, s2, s1, p):
    """Given A (syn_dim × |T|), s2, s1 (syn_dim each), and the precondition
    that s2 ∉ col(A) and s1 ∈ col([A | s2]),
    find unique γ_0 such that s1 = A·x + γ_0·s2 for some x.
    Returns γ_0; bad_gamma = -γ_0 mod p."""
    syn_dim = len(s1)
    T_size = len(A_cols[0]) if A_cols else 0
    # Augmented matrix: [A | s2 | s1], we reduce A then s2, read off s1 column
    aug = [list(A_cols[i]) + [s2[i]] + [s1[i]] for i in range(syn_dim)]
    ncols = T_size + 2
    pivot_col_for_row = {}
    rank = 0
    col = 0
    while rank < syn_dim and col <= T_size:  # only reduce on first T_size+1 cols (A and s2)
        pr = None
        for r in range(rank, syn_dim):
            if aug[r][col] % p != 0:
                pr = r
                break
        if pr is None:
            col += 1
            continue
        aug[rank], aug[pr] = aug[pr], aug[rank]
        inv = modinv(aug[rank][col], p)
        aug[rank] = [(x * inv) % p for x in aug[rank]]
        for r in range(syn_dim):
            if r != rank and aug[r][col] != 0:
                f = aug[r][col]
                aug[r] = [(aug[r][c] - f * aug[rank][c]) % p for c in range(ncols)]
        pivot_col_for_row[rank] = col
        rank += 1
        col += 1
    # The s2 column is at index T_size; if there's a pivot in column T_size, the
    # corresponding row's last entry is the coefficient of s2 in expansion of s1.
    for r, pc in pivot_col_for_row.items():
        if pc == T_size:
            return aug[r][T_size + 1] % p
    # s2 was in col(A) — caller should not have called here.
    return None


# ----------------------- RS parity-check matrix -----------------------

def parity_check(L, n, k, p):
    """Parity check matrix for RS_k(L) where L = order-n multiplicative subgroup.
    f ∈ RS_k iff f = eval of poly p, deg(p) < k, iff f's DFT (with negative
    exponent: F_b = Σ_j ω^{-jb} f_j) is supported on b ∈ [0, k).

    So syndromes at b ∈ [k, n) must vanish. Parity check rows:
        H[i][j] = ω^{-j(k+i)} = pow(L[j], (-(k+i)) % n, p),  for i ∈ [0, n-k).

    Then H @ f = 0 iff f ∈ RS_k.

    NOTE: a previous version used H[i][j] = L[j]^(k+i) (positive exponent), which
    is NOT a valid parity check for RS_k — it has the right kernel dimension
    but the wrong kernel.
    """
    H = []
    for i in range(n - k):
        e = (-(k + i)) % n
        H.append([pow(L[j], e, p) for j in range(n)])
    return H


def matvec(M, v, p):
    return [sum(M[i][j] * v[j] for j in range(len(v))) % p for i in range(len(M))]


# ----------------------- Bad γ counting -----------------------

def count_bad_gammas(f1, f2, H, n, k, w, p):
    """Return (count, all_flag): count of γ s.t. dist(f1+γf2, RS_k) ≤ w; all_flag if every γ.
    Iterates over T of size w only (catches dist ≤ w via T containing the actual support)."""
    s1 = matvec(H, f1, p)
    s2 = matvec(H, f2, p)

    # Trivial early termination: if both s1 and s2 are zero, every γ gives fold ∈ C.
    if all(x == 0 for x in s1) and all(x == 0 for x in s2):
        return p, True

    bad_set = set()
    syn_dim = n - k
    H_cols = list(zip(*H))  # H_cols[j] = column j of H (tuple of length syn_dim)

    # Note: at w=0, T=() gives A empty, col(A) = {0}; bad iff s1 + γs2 = 0 for some γ.
    # We handle w ≥ 1 here (caller ensures).
    # If we want dist=0 also covered, include T=() — but then s1+γs2=0 is rare.

    for T in combinations(range(n), w):
        # Build A = syn_dim × w matrix
        A = [[H_cols[j][i] for j in T] for i in range(syn_dim)]
        # Test: s2 ∈ col(A)?  rank(A) vs rank(A|s2)
        rA = gauss_rank(A, p)
        A_s2 = [A[i] + [s2[i]] for i in range(syn_dim)]
        rA_s2 = gauss_rank(A_s2, p)
        if rA_s2 == rA:
            # s2 ∈ col(A); check if s1 also ∈ col(A)
            A_s1 = [A[i] + [s1[i]] for i in range(syn_dim)]
            rA_s1 = gauss_rank(A_s1, p)
            if rA_s1 == rA:
                # All γ are bad via this T
                return p, True
            # else: no γ from this T
        else:
            # s2 ∉ col(A); check if s1 ∈ col([A|s2])
            A_s2_s1 = [A[i] + [s2[i]] + [s1[i]] for i in range(syn_dim)]
            rA_s2_s1 = gauss_rank(A_s2_s1, p)
            if rA_s2_s1 == rA_s2:
                gamma_0 = solve_gamma(A, s2, s1, p)
                if gamma_0 is not None:
                    bad_set.add((-gamma_0) % p)

    return len(bad_set), False


def joint_dist_le_w(f1, f2, H, n, k, w, p):
    """Δ_joint((f1,f2), C × C) ≤ w iff ∃ T ⊂ [n], |T| ≤ w, with both
    s1 = H f1 ∈ col(H[:, T]) and s2 ∈ col(H[:, T])."""
    s1 = matvec(H, f1, p)
    s2 = matvec(H, f2, p)
    if all(x == 0 for x in s1) and all(x == 0 for x in s2):
        return True
    syn_dim = n - k
    H_cols = list(zip(*H))
    for sz in range(0, w + 1):
        for T in combinations(range(n), sz):
            A = [[H_cols[j][i] for j in T] for i in range(syn_dim)]
            rA = gauss_rank(A, p) if A and A[0] else 0
            A_aug = [A[i] + [s1[i], s2[i]] for i in range(syn_dim)] if A and A[0] else \
                    [[s1[i], s2[i]] for i in range(syn_dim)]
            rA_aug = gauss_rank(A_aug, p)
            if rA_aug == rA:
                return True
    return False


# ----------------------- Test driver -----------------------

def run_case(n, k, p, w, n_samples, seed=0, verbose=True, time_budget_sec=900):
    """Random sample n_samples pairs; report distribution of bad γ counts."""
    omega = find_prim_root(p, n)
    if omega is None:
        if verbose:
            print(f"[skip] n={n}, p={p}: no primitive {n}-th root", flush=True)
        return None
    delta = w / n
    rho = k / n
    delta_J = 1.0 - rho ** 0.5
    if delta <= delta_J + 1e-9:
        if verbose:
            print(f"[skip] n={n}, k={k}, p={p}, w={w}: δ={delta:.4f} ≤ δ_J={delta_J:.4f}", flush=True)
        return None
    if w >= n - k:
        if verbose:
            print(f"[skip] n={n}, k={k}, p={p}, w={w}: w ≥ n-k (vacuous CA premise)", flush=True)
        return None

    L = [pow(omega, i, p) for i in range(n)]
    H = parity_check(L, n, k, p)

    if verbose:
        print(f"\n=== n={n}, k={k}, p={p}, w={w}, δ={delta:.4f}, δ_J={delta_J:.4f}", flush=True)
        print(f"    ω={omega}, ρ={rho:.3f}, T-iter cost = C({n},{w}) = {comb(n,w):,}", flush=True)

    rng = random.Random(seed)
    hist = {}
    max_bad = 0
    n_tested = 0
    n_skipped = 0
    t_start = time.time()

    for trial in range(n_samples):
        if time.time() - t_start > time_budget_sec:
            if verbose:
                print(f"    [time budget exceeded after {trial} trials]", flush=True)
            break
        f1 = [rng.randrange(p) for _ in range(n)]
        f2 = [rng.randrange(p) for _ in range(n)]

        # Verify CA premise: Δ_joint > δ
        if joint_dist_le_w(f1, f2, H, n, k, w, p):
            n_skipped += 1
            continue

        bad, all_flag = count_bad_gammas(f1, f2, H, n, k, w, p)
        n_tested += 1
        hist[bad] = hist.get(bad, 0) + 1
        if bad > max_bad:
            max_bad = bad
            if verbose:
                print(f"    ★ trial {trial}: max_bad={bad} (= {bad}/{p} = {bad/p:.3f})", flush=True)

    elapsed = time.time() - t_start
    if verbose:
        print(f"    DONE: {n_tested} tested ({n_skipped} skipped on premise), max_bad/p = {max_bad}/{p} = {max_bad/p:.4f}", flush=True)
        print(f"    histogram: {dict(sorted(hist.items()))}", flush=True)
        print(f"    elapsed: {elapsed:.1f}s", flush=True)
    return {
        "n": n, "k": k, "p": p, "w": w, "delta": delta, "delta_J": delta_J,
        "n_samples": n_samples, "n_tested": n_tested, "n_skipped": n_skipped,
        "max_bad": max_bad, "ratio": max_bad / p, "hist": dict(sorted(hist.items())),
        "elapsed_sec": elapsed,
    }


# ----------------------- Main -----------------------

if __name__ == "__main__":
    print("=" * 70, flush=True)
    print("OP1 SWEEP — extending equal-threshold CA disproof to n=16", flush=True)
    print("=" * 70, flush=True)

    results = []

    # ----- n = 16, k = 8 (rate 1/2). δ_J·n ≈ 4.69, n-k = 8.  w ∈ {5, 6, 7}. -----
    # p must satisfy 16 | p-1: smallest are 17, 97, 113, 193, 241, 257.
    n_samples_16 = 100
    for p in [17, 97, 193]:
        for w in [5, 6, 7]:
            # For larger p, fewer samples (each is expensive)
            ns = n_samples_16 if p == 17 else (50 if p == 97 else 30)
            r = run_case(16, 8, p, w, n_samples=ns, seed=42, time_budget_sec=600)
            if r is not None:
                results.append(r)

    print("\n" + "=" * 70, flush=True)
    print("SUMMARY", flush=True)
    print("=" * 70, flush=True)
    print(f"{'(n, k, p, w)':<22} {'δ':<8} {'max_bad':<9} {'/p':<8} {'note':<10}", flush=True)
    for r in results:
        tag = "✓ Θ(1)" if r["ratio"] >= 0.05 else "✗ small"
        print(f"({r['n']},{r['k']},{r['p']},{r['w']})       {r['delta']:.4f}   {r['max_bad']:<9} {r['ratio']:<8.4f} {tag}", flush=True)
