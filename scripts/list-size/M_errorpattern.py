#!/usr/bin/env python3
"""
M_errorpattern.py — Exact M via error-pattern enumeration.

Key insight: in intermediate zone, n-w > k, so each (n-w)-agreement-set
uniquely determines the codeword. Enumerate C(n,w) error patterns, not p^k codewords.

Complexity: O(num_samples · C(n,w) · n) — independent of p!
"""

import numpy as np
from itertools import combinations
from math import sqrt, ceil, comb
import time
import sys

def mod_inv(a, p):
    return pow(a, p - 2, p)

def interpolate_lagrange(xs, ys, p):
    """Lagrange interpolation over F_p. Returns [a0, a1, ..., a_{k-1}]."""
    k = len(xs)
    coeffs = [0] * k
    for i in range(k):
        # Basis polynomial L_i: product of (x - x_j)/(x_i - x_j) for j != i
        basis = [0] * k
        basis[0] = 1  # start with 1
        deg = 0
        denom = 1
        for j in range(k):
            if j == i:
                continue
            denom = (denom * ((xs[i] - xs[j]) % p)) % p
            # Multiply current basis by (x - x_j)
            new_basis = [0] * k
            for d in range(deg + 1):
                new_basis[d] = (new_basis[d] + basis[d] * ((-xs[j]) % p)) % p
                new_basis[d + 1] = (new_basis[d + 1] + basis[d]) % p
            basis = new_basis
            deg += 1

        inv_denom = mod_inv(denom % p, p)
        scale = (ys[i] * inv_denom) % p
        for d in range(k):
            coeffs[d] = (coeffs[d] + basis[d] * scale) % p

    return coeffs

def eval_poly(coeffs, x, p):
    val = 0
    for c in reversed(coeffs):
        val = (val * x + c) % p
    return val

def list_size_for_u(u, n, k, p, L, w):
    """Count codewords within Hamming distance w from u."""
    t = n - w  # agreement count
    if t < k:
        return -1  # underdetermined

    found = set()

    # Enumerate all w-subsets of error positions
    for err_pos in combinations(range(n), w):
        err_set = set(err_pos)
        agr_pos = [j for j in range(n) if j not in err_set]

        # Take first k agreement points for interpolation
        xs = [L[j] for j in agr_pos[:k]]
        ys = [u[j] for j in agr_pos[:k]]

        # Interpolate degree < k polynomial
        coeffs = interpolate_lagrange(xs, ys, p)

        # Verify on remaining agreement positions
        valid = True
        for j in agr_pos[k:]:
            if eval_poly(coeffs, L[j], p) != u[j]:
                valid = False
                break

        if valid:
            # Compute full codeword and actual distance
            codeword = tuple(eval_poly(coeffs, x, p) for x in L)
            d = sum(1 for a, b in zip(u, codeword) if a != b)
            if d <= w:
                found.add(codeword)

    return len(found)


def M_max_errorpattern(n, k, p, w, num_cw_centers=200, num_rand_centers=300):
    """Compute M_max at distance w using error-pattern enumeration."""
    L = list(range(1, n + 1))
    enum_size = comb(n, w)

    rng = np.random.RandomState(42)

    M_max = 0
    best_u = None

    t0 = time.time()

    # Codeword centers: generate random degree-<k polynomials
    for ci in range(num_cw_centers):
        coeffs = [rng.randint(0, p) for _ in range(k)]
        u = tuple(eval_poly(coeffs, x, p) for x in L)

        m = list_size_for_u(u, n, k, p, L, w)
        if m > M_max:
            M_max = m
            best_u = ("codeword", ci)

    cw_time = time.time() - t0

    # Random non-codeword centers
    t1 = time.time()
    for ri in range(num_rand_centers):
        u = tuple(rng.randint(0, p) for _ in range(n))

        m = list_size_for_u(u, n, k, p, L, w)
        if m > M_max:
            M_max = m
            best_u = ("random", ri)

    rand_time = time.time() - t1

    return M_max, best_u, cw_time, rand_time


def run_config(n, k, primes, w_range=None):
    """Run M computation for RS[n,k] across primes."""
    rho = k / n
    wJ = n * (1 - sqrt(rho))
    cap = n - k
    d_min = n - k + 1

    if w_range is None:
        w_range = list(range(ceil(wJ), cap))

    print(f"\n{'='*70}", flush=True)
    print(f"RS[{n},{k}] over F_p, ρ={rho:.2f}", flush=True)
    print(f"  wJ={wJ:.2f}, cap={cap}, d_min={d_min}", flush=True)
    print(f"  Intermediate zone: w ∈ [{ceil(wJ)}, {cap})", flush=True)

    for w in w_range:
        if w >= n or w < 0:
            continue
        t = n - w
        if t < k:
            print(f"  w={w}: skip (t={t} < k={k})", flush=True)
            continue

        c = n - k - w  # companion matrix codimension
        d = w - c       # companion matrix dimension
        enum_size = comb(n, w)

        print(f"\n  w={w}: c={c}, d={d}, C(n,w)={enum_size}", flush=True)
        print(f"  {'p':>6} | {'M_max':>6} | {'best_from':>12} | time", flush=True)

        for p in primes:
            if p <= n:
                continue

            # Adjust sample sizes based on enum_size
            if enum_size > 100000:
                nc, nr = 50, 50
            elif enum_size > 10000:
                nc, nr = 100, 100
            else:
                nc, nr = 200, 300

            M, best, ct, rt = M_max_errorpattern(n, k, p, w, nc, nr)
            total_t = ct + rt
            print(f"  {p:6d} | {M:6d} | {str(best):>12} | {total_t:.1f}s", flush=True)


if __name__ == '__main__':
    print("=" * 70, flush=True)
    print("M_max via ERROR-PATTERN ENUMERATION", flush=True)
    print("Independent of p^k — scales with C(n,w)", flush=True)
    print("=" * 70, flush=True)

    # --- RS[8,4] rate 1/2: baseline (matches density_mini) ---
    run_config(8, 4,
               [11, 17, 31, 61, 97, 127, 251, 509, 1021],
               w_range=[3])

    # --- RS[12,6] rate 1/2: the key test ---
    run_config(12, 6,
               [13, 17, 23, 31, 43, 61, 97, 127, 251, 509],
               w_range=[4, 5])

    # --- RS[16,8] rate 1/2: NEW! ---
    # C(16,5)=4368, C(16,6)=8008, C(16,7)=11440
    run_config(16, 8,
               [17, 31, 61, 97, 127, 251, 509, 1021],
               w_range=[5, 6, 7])

    # --- RS[20,10] rate 1/2: push further ---
    # C(20,6)=38760, C(20,7)=77520, C(20,8)=125970, C(20,9)=167960
    run_config(20, 10,
               [23, 31, 61, 127, 251],
               w_range=[6, 7, 8, 9])

    # --- RS[24,12] rate 1/2: if fast enough ---
    # C(24,8)=735471 — might be slow
    # Only do w=8 (c=4) which should have small M
    run_config(24, 12,
               [29, 31, 61, 127],
               w_range=[8])

    print(f"\n{'='*70}", flush=True)
    print("DONE", flush=True)
