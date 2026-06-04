#!/usr/bin/env python3
"""
Since M is INDEPENDENT of p, use the SMALLEST possible p for exact computation.
This allows us to reach larger n.

For n | p-1: the smallest prime p is roughly n+1 (if n+1 is prime).

Strategy: use the FFT approach with the smallest p.
Feasibility: p^{n-k} must fit in memory (syndrome space size).

Rate 1/2:
n=4, k=2: smallest p=5. p^2 = 25. ✓
n=6, k=3: smallest p=7. p^3 = 343. ✓
n=8, k=4: smallest p=17. p^4 = 83521. ✓
n=10, k=5: smallest p=11. p^5 = 161051. ✓
n=12, k=6: smallest p=13. p^6 = 4826809. ✓ (tight)
n=14, k=7: smallest p=29. p^7 = 17,249,876,309. ✗ (too large)
n=16, k=8: smallest p=17. p^8 = 6,975,757,441. ✗

For n=14: need p^7 ≤ ~10M. p ≤ 10^{6/7} ≈ 4.6. No prime that small.
So n=14 is NOT feasible with FFT at rate 1/2.

Alternative approach for larger n: use LOWER rates where p^{n-k} is manageable.
E.g., n=14, k=3: p=29, p^{11} way too large. ✗

Or: use the codeword-enumeration approach. p^k codewords.
n=14, k=7: p=29, p^7 ≈ 17B. ✗
n=14, k=7: p=29 is too large. Need p=15? Not prime.

Hmm. For n=14: the smallest prime with 14|p-1 is p=29 (since 28/14=2).
p^7 = 17B. Way too large.

What about non-rate-1/2? For n=14, k=2: p=29, p^2=841 codewords. VERY manageable!
But then d = 13, Johnson w = ceil(0.143*14) = 3, 2w-d = 6-13 = -7. Way below Johnson.

For n=14, k=4: d=11, Johnson w = ceil((1-sqrt(4/14))*14) = ceil(6.51) = 7.
p=29, p^4 = 707281 codewords. Manageable!
2w-d = 14-11 = 3. Overlap ≤ 3.

For n=16, k=4: d=13, Johnson w = ceil((1-sqrt(4/16))*16) = ceil(8) = 8.
p=17, p^4 = 83521 codewords. Easy!
2w-d = 16-13 = 3. Overlap ≤ 3.

Let me compute M for these cases using codeword enumeration + GPU.
"""

import torch
import numpy as np
import time
from math import comb, ceil, sqrt

DEVICE = torch.device('mps' if torch.backends.mps.is_available() else 'cpu')

def find_primitive_root(p):
    for g in range(2, p):
        factors = set()
        temp = p - 1
        d = 2
        while d * d <= temp:
            while temp % d == 0:
                factors.add(d)
                temp //= d
            d += 1
        if temp > 1:
            factors.add(temp)
        if all(pow(g, (p-1)//q, p) != 1 for q in factors):
            return g

def find_omega(n, p):
    g = find_primitive_root(p)
    return pow(g, (p - 1) // n, p)

def compute_M_gpu(n, k, p, w_list, n_test=50000):
    """Enumerate all p^k codewords, then GPU-accelerated distance computation."""
    omega = find_omega(n, p)
    L = [pow(omega, i, p) for i in range(n)]

    L_eval = np.zeros((n, k), dtype=np.int64)
    for i in range(n):
        L_eval[i, 0] = 1
        for j in range(1, k):
            L_eval[i, j] = L_eval[i, j-1] * L[i] % p

    num_cw = p ** k
    coeff = np.zeros((num_cw, k), dtype=np.int64)
    idx = np.arange(num_cw)
    for dim in range(k):
        coeff[:, dim] = (idx // (p ** dim)) % p

    cw = coeff @ L_eval.T % p
    cw_gpu = torch.tensor(cw, dtype=torch.int16, device=DEVICE)

    max_M = {w: 0 for w in w_list}
    rng = np.random.default_rng(42)

    batch_size = min(5000, n_test)
    for batch_start in range(0, n_test, batch_size):
        actual = min(batch_size, n_test - batch_start)
        test = np.zeros((actual, n), dtype=np.int64)
        s1 = actual // 3
        test[:s1] = rng.integers(0, p, size=(s1, n))
        for i in range(s1, 2*s1):
            base = cw[rng.integers(0, num_cw)]
            test[i] = base.copy()
            ew = rng.integers(1, max(w_list)+1)
            ep = rng.choice(n, min(ew, n), replace=False)
            for pos in ep:
                test[i, pos] = (test[i, pos] + rng.integers(1, p)) % p
        for i in range(2*s1, actual):
            base = cw[rng.integers(0, num_cw)]
            test[i] = base.copy()
            p1, p2 = rng.choice(n, 2, replace=False)
            test[i, p1] = (test[i, p1] + rng.integers(1, p)) % p
            test[i, p2] = (test[i, p2] + rng.integers(1, p)) % p

        test_gpu = torch.tensor(test, dtype=torch.int16, device=DEVICE)

        cw_batch = 200000
        for cw_start in range(0, num_cw, cw_batch):
            cw_end = min(cw_start + cw_batch, num_cw)
            cw_sub = cw_gpu[cw_start:cw_end]
            agree = (test_gpu.unsqueeze(1) == cw_sub.unsqueeze(0)).sum(dim=2)
            dist = n - agree
            for w in w_list:
                counts = (dist <= w).sum(dim=1)
                bm = counts.max().item()
                if bm > max_M[w]:
                    max_M[w] = int(bm)

    return max_M

# ================================================================
# Comprehensive table: M at Johnson radius for various (n, k)
# ================================================================
print("=" * 80)
print("M at the Johnson radius: comprehensive table")
print("=" * 80)

MAX_CW = 5_000_000

cases = []
# Rate 1/2
for n in range(4, 22, 2):
    k = n // 2
    cases.append((n, k))

# Rate 1/3
for n in [6, 9, 12, 15, 18, 21]:
    k = n // 3
    if k >= 2:
        cases.append((n, k))

# Rate 1/4
for n in [8, 12, 16, 20, 24]:
    k = n // 4
    if k >= 2:
        cases.append((n, k))

# Rate 2/3
for n in [6, 9, 12, 15]:
    k = 2 * n // 3
    if k >= 2:
        cases.append((n, k))

# Deduplicate
cases = sorted(set(cases))

print(f"{'n':>4} {'k':>3} {'ρ':>5} {'d':>3} {'δ_J':>6} {'w_J':>3} {'2w-d':>5} {'p':>5} {'p^k':>10} {'M':>5} {'⌊n/w⌋':>6}")

for n, k in cases:
    d = n - k + 1
    rho = k / n
    delta_J = 1 - sqrt(rho)
    w_J = ceil(delta_J * n)

    if w_J >= d:  # above minimum distance, trivial
        continue
    if w_J < 1:
        continue

    overlap = 2 * w_J - d

    # Find smallest prime
    for p in range(n + 1, 10000):
        if (p - 1) % n != 0:
            continue
        is_prime = all(p % dd != 0 for dd in range(2, int(p**0.5)+1))
        if is_prime:
            break
    else:
        continue

    if p ** k > MAX_CW:
        print(f"{n:4d} {k:3d} {rho:5.2f} {d:3d} {delta_J:6.3f} {w_J:3d} {overlap:5d} {p:5d} {p**k:10d} {'SKIP':>5} {n//w_J:6d}")
        continue

    t0 = time.time()
    M_dict = compute_M_gpu(n, k, p, [w_J], n_test=30000)
    M = M_dict[w_J]
    elapsed = time.time() - t0

    floor_nw = n // w_J

    print(f"{n:4d} {k:3d} {rho:5.2f} {d:3d} {delta_J:6.3f} {w_J:3d} {overlap:5d} {p:5d} {p**k:10d} {M:5d} {floor_nw:6d}  ({elapsed:.1f}s)", flush=True)
