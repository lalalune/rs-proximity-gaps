#!/usr/bin/env python3
"""
M_fast.py — Fast exact list-size computation for small RS codes.

Focus: intermediate zone [Johnson, capacity) for n=2^K, rate 1/2.
Key question: is M = O(1) or even M = 0?
"""

import numpy as np
from math import sqrt, ceil, floor, comb, log, lgamma
import time

def eval_poly_vec(coeffs_matrix, L, p):
    """Evaluate all polynomials at all points. coeffs_matrix: (num_polys, k), L: list of eval points.
    Returns (num_polys, n) array of evaluations mod p."""
    k = coeffs_matrix.shape[1]
    n = len(L)
    # Horner's method vectorized
    result = np.zeros((coeffs_matrix.shape[0], n), dtype=np.int64)
    for j in range(k - 1, -1, -1):
        for i, x in enumerate(L):
            result[:, i] = (result[:, i] * x + coeffs_matrix[:, j]) % p
    return result

def generate_codewords_chunked(n, k, p, L, chunk_size=50000):
    """Generate codewords in chunks to avoid memory issues. Returns full array."""
    total = p ** k
    all_cw = np.zeros((total, n), dtype=np.int16)

    for start in range(0, total, chunk_size):
        end = min(start + chunk_size, total)
        size = end - start

        # Decode indices to polynomial coefficients
        coeffs = np.zeros((size, k), dtype=np.int64)
        for j in range(k):
            coeffs[:, j] = (np.arange(start, end) // (p ** j)) % p

        # Evaluate
        for ci in range(n):
            x = L[ci]
            val = np.zeros(size, dtype=np.int64)
            for j in range(k - 1, -1, -1):
                val = (val * x + coeffs[:, j]) % p
            all_cw[start:end, ci] = val

    return all_cw


def exact_M(n, k, p, max_cw_centers=500, num_rand=500):
    """Compute exact M_max(w) for RS[n,k] over F_p."""
    L = list(range(1, n + 1))
    total = p ** k
    rho = k / n
    wJ = n * (1 - sqrt(rho))
    cap = n - k

    print(f"\n{'='*60}")
    print(f"RS[{n},{k}] over F_{p}  (p^k={total}, ρ={rho:.2f})")
    print(f"  Johnson wJ={wJ:.2f}, capacity={cap}")
    print(f"  Intermediate zone: w ∈ [{ceil(wJ)}, {cap})")

    t0 = time.time()
    cw = generate_codewords_chunked(n, k, p, L)
    print(f"  Generated {total} codewords in {time.time()-t0:.1f}s")

    M_max = np.zeros(n + 1, dtype=np.int32)

    # --- Codeword-centered list sizes ---
    t0 = time.time()
    nc = min(max_cw_centers, total)
    if total <= max_cw_centers:
        indices = np.arange(total)
    else:
        np.random.seed(123)
        indices = np.random.choice(total, nc, replace=False)

    for idx in indices:
        dists = np.sum(cw[idx].astype(np.int16) != cw, axis=1)
        hist = np.bincount(dists.astype(np.int32), minlength=n + 1)
        cum = np.cumsum(hist)
        for w in range(n + 1):
            if cum[w] > M_max[w]:
                M_max[w] = cum[w]

    print(f"  {nc} codeword centers: {time.time()-t0:.1f}s")

    # --- Random non-codeword centers ---
    t0 = time.time()
    np.random.seed(42)
    for _ in range(num_rand):
        u = np.random.randint(0, p, size=n, dtype=np.int16)
        dists = np.sum(u != cw, axis=1)
        hist = np.bincount(dists.astype(np.int32), minlength=n + 1)
        cum = np.cumsum(hist)
        for w in range(n + 1):
            if cum[w] > M_max[w]:
                M_max[w] = cum[w]

    print(f"  {num_rand} random centers: {time.time()-t0:.1f}s")

    # --- Report ---
    print(f"\n  {'w':>3} | {'M_max':>7} | zone")
    print(f"  {'---':>3} | {'---':>7} | ---")
    for w in range(n + 1):
        mm = int(M_max[w])
        if w < ceil(wJ):
            zone = "< Johnson"
        elif w < cap:
            zone = "INTERMEDIATE"
        elif w == cap:
            zone = "= capacity"
        else:
            zone = "> capacity"

        show = (zone == "INTERMEDIATE") or mm > 1 or w == ceil(wJ)-1 or w == cap
        if show:
            flag = ""
            if zone == "INTERMEDIATE" and mm <= 1:
                flag = "  ** M≤1! **"
            elif zone == "INTERMEDIATE" and mm > 1:
                flag = f"  (M={mm})"
            print(f"  {w:3d} | {mm:7d} | {zone}{flag}")

    return M_max


def analytic_bounds():
    """Evaluate analytic bound for large FRI parameters."""
    print(f"\n{'='*60}")
    print(f"ANALYTIC BOUND: M formula in intermediate zone")
    print(f"{'='*60}")

    configs = [
        (2**4, 2**3, 17, "n=16"),
        (2**5, 2**4, 37, "n=32"),
        (2**6, 2**5, 67, "n=64"),
        (2**10, 2**9, 2**31-1, "n=1024, FRI-like"),
        (2**15, 2**14, 2**31-1, "n=32768"),
        (2**20, 2**19, 2**31-1, "n=1M, FRI actual"),
    ]

    for n, k, p, label in configs:
        rho = k / n
        wJ = n * (1 - sqrt(rho))
        cap = n - k
        log2p = log(p) / log(2)

        print(f"\n  {label}: RS[{n},{k}] over F_{p}")
        print(f"  wJ={wJ:.1f}, cap={cap}, log2(p)={log2p:.1f}")

        # Sample a few w values in intermediate zone
        w_samples = []
        zone_size = cap - ceil(wJ)
        if zone_size <= 0:
            print(f"  Intermediate zone empty!")
            continue

        for frac in [0.0, 0.25, 0.5, 0.75, 1.0]:
            w = ceil(wJ) + int(frac * (zone_size - 1))
            w_samples.append(w)

        print(f"  {'w':>8} | {'t=n-w':>8} | {'t|n':>4} | {'(t-1)|n':>7} | {'log2(spor)':>12} | result")
        print(f"  {'---':>8} | {'---':>8} | {'---':>4} | {'---':>7} | {'---':>12} | ---")

        for w in w_samples:
            t = n - w
            if t <= 1:
                continue

            t_div = (n % t == 0)
            tm1_div = (n % (t - 1) == 0) if t > 1 else False

            # For k=2 bound: sporadic = n^2/(t*(t-1))
            sporadic_k2 = n * n / (t * (t - 1)) if t > 1 else float('inf')

            # For general density: log2(C(n,t)/p^{t-2})
            log2_spor = (lgamma(n+1) - lgamma(t+1) - lgamma(n-t+1))/log(2) - (t-2)*log2p

            ind = ""
            if t_div:
                ind += f"n/t={n//t} "
            if tm1_div:
                ind += f"n/(t-1)={n//(t-1)} "
            if not ind:
                ind = "both=0"

            result = f"M≤{sporadic_k2:.1f} (k=2)" if not t_div and not tm1_div else f"ind: {ind.strip()}, +{sporadic_k2:.1f}"

            print(f"  {w:8d} | {t:8d} | {'Y' if t_div else '.':>4} | {'Y' if tm1_div else '.':>7} | {log2_spor:12.1f} | {result}")


def smooth_indicators():
    """For n=2^K, how many t in intermediate zone have nonzero indicators?"""
    print(f"\n{'='*60}")
    print(f"SMOOTH DOMAIN: indicator term analysis")
    print(f"{'='*60}")

    for K in [3, 4, 5, 6, 8, 10, 15, 20]:
        n = 2 ** K
        k = n // 2
        wJ = n * (1 - sqrt(0.5))
        t_lo = k + 1
        t_hi = n - ceil(wJ)
        total = t_hi - t_lo + 1

        if total <= 0:
            continue

        # Divisors of n = 2^K in range [t_lo, t_hi]
        # Divisors of 2^K are 1, 2, 4, ..., 2^K
        t_div = [d for d in range(t_lo, t_hi + 1) if n % d == 0]
        tm1_div = [d for d in range(t_lo, t_hi + 1) if d > 1 and n % (d - 1) == 0]
        either = set(t_div) | set(tm1_div)
        clean = total - len(either)

        print(f"\n  n=2^{K}={n}, k={k}, zone size={total}")
        print(f"    t|n:     {len(t_div):>4}  {t_div[:5]}")
        print(f"    (t-1)|n: {len(tm1_div):>4}  {tm1_div[:5]}")
        print(f"    CLEAN:   {clean:>4} / {total}  ({100*clean/total:.1f}%)")


# ═══════════════════════════════════════════
if __name__ == '__main__':
    print("=" * 60)
    print("LIST SIZE M IN INTERMEDIATE ZONE — FAST VERSION")
    print("=" * 60)

    # Part 1: Tiny cases — FAST
    print("\n### EXACT COMPUTATION ###")

    # k=2 cases (very fast, p^k tiny)
    for p in [11, 17, 31, 43, 67, 97]:
        if p > 8:
            exact_M(8, 2, p, max_cw_centers=500, num_rand=500)

    # k=3 (moderate)
    for p in [11, 17, 31]:
        if p > 8:
            exact_M(8, 3, p, max_cw_centers=500, num_rand=500)

    # k=4, rate 1/2 (the key case)
    for p in [11, 17, 31]:
        if p > 8:
            exact_M(8, 4, p, max_cw_centers=500, num_rand=500)

    # n=12, k=6 (rate 1/2)
    exact_M(12, 6, 13, max_cw_centers=200, num_rand=300)

    # Part 2: Analytic bounds
    analytic_bounds()

    # Part 3: Smooth domain
    smooth_indicators()

    print(f"\n{'='*60}")
    print("DONE")
