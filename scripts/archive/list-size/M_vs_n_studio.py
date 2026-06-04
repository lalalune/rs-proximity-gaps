#!/usr/bin/env python3
"""
M_vs_n_studio.py — M_max at minimum valid p for n=6..24, rate 1/2, c=1.
THIS IS THE KEY TEST FOR POLYNOMIAL BOUND.

Uses error-pattern enumeration + syndrome method for speed.
"""
import numpy as np
from itertools import combinations
from math import comb
import time
import sys

def next_prime(n):
    """Smallest prime > n."""
    if n < 2: return 2
    candidate = n + 1 if n % 2 == 0 else n + 2
    if candidate == 3: return 3
    while True:
        is_prime = True
        for d in range(2, int(candidate**0.5) + 1):
            if candidate % d == 0:
                is_prime = False
                break
        if is_prime:
            return candidate
        candidate += 2 if candidate > 2 else 1

def precompute_normals(n, k, L, p, w):
    D = n - k
    normals = []
    for E in combinations(range(n), w):
        poly = [1]
        for e in E:
            new_poly = [0] * (len(poly) + 1)
            for i, c in enumerate(poly):
                new_poly[i] = (new_poly[i] + (-L[e]) * c) % p
                new_poly[i+1] = (new_poly[i+1] + c) % p
            poly = new_poly
        normals.append(tuple(c % p for c in poly[:D]))
    return normals

def measure_M_max(n, k, p, num_random=2000, num_cw=500):
    D = n - k
    w = n - k - 1
    L = list(range(1, n + 1))
    N_E = comb(n, w)
    
    t0 = time.time()
    normals = precompute_normals(n, k, L, p, w)
    normal_arr = np.array(normals, dtype=np.int64)
    
    rng = np.random.RandomState(42)
    M_max = 0
    
    # Random centers
    for _ in range(num_random):
        u = rng.randint(0, p, size=n).astype(np.int64)
        s = np.zeros(D, dtype=np.int64)
        for l in range(D):
            pows = np.array([pow(int(L[j]), l, p) for j in range(n)], dtype=np.int64)
            s[l] = int(np.sum(u * pows) % p)
        dots = np.sum(normal_arr * s, axis=1) % p
        M = int(np.sum(dots == 0))
        if M > M_max:
            M_max = M
    
    # Codeword + perturbation centers
    for _ in range(num_cw):
        coeffs = rng.randint(0, p, size=k).astype(np.int64)
        u = np.zeros(n, dtype=np.int64)
        for j in range(n):
            val = 0
            for c_idx in range(k):
                val = (val + int(coeffs[c_idx]) * pow(int(L[j]), c_idx, p)) % p
            u[j] = val
        # Add random errors
        err_pos = rng.choice(n, size=min(w, n), replace=False)
        for j in err_pos:
            u[j] = (u[j] + rng.randint(1, p)) % p
        
        s = np.zeros(D, dtype=np.int64)
        for l in range(D):
            pows = np.array([pow(int(L[j]), l, p) for j in range(n)], dtype=np.int64)
            s[l] = int(np.sum(u * pows) % p)
        dots = np.sum(normal_arr * s, axis=1) % p
        M = int(np.sum(dots == 0))
        if M > M_max:
            M_max = M
    
    elapsed = time.time() - t0
    return M_max, elapsed

def main():
    print("=" * 80)
    print("M_max vs n at MINIMUM VALID p — KEY POLY BOUND TEST")
    print("=" * 80)
    print(flush=True)
    
    results = []
    
    # Rate 1/2, c=1
    configs = [(2*k, k) for k in range(3, 13)]  # n=6..24
    
    for n, k in configs:
        w = n - k - 1
        N_E = comb(n, w)
        
        if N_E > 200000:
            print(f"RS[{n},{k}] w={w}: C(n,w)={N_E} — TOO LARGE, skipping")
            sys.stdout.flush()
            continue
        
        # Test at min valid p and a few more
        p_min = next_prime(n)
        primes_to_test = [p_min]
        # Add a couple more
        p2 = next_prime(p_min)
        p3 = next_prime(p2)
        primes_to_test.extend([p2, p3])
        # Also test larger primes
        for p_extra in [31, 47, 67, 97, 127]:
            if p_extra > n and p_extra not in primes_to_test:
                primes_to_test.append(p_extra)
        primes_to_test.sort()
        
        print(f"\nRS[{n},{k}] w={w}, C(n,w)={N_E}")
        print(f"  {'p':>5} | {'M_max':>6} | {'C(n,w)/p':>10} | {'M/avg':>7} | {'M·p^α':>10} (α={w/(n-k+1):.3f}) | {'time':>8}")
        print(f"  " + "-" * 70)
        
        for p in primes_to_test:
            if p <= n:
                continue
            
            # Adjust sample size
            num_r = min(3000, max(500, 50 * p))
            num_c = min(1000, max(100, 10 * p))
            
            M_max, elapsed = measure_M_max(n, k, p, num_random=num_r, num_cw=num_c)
            avg = N_E / p
            alpha = (w - 0) / (n - k)  # d/(n-k) with d=w-c+1=w for c=1? No...
            # Actually α = d/(n-k) where d = n-k-1 - (c-1) = w - 0 = w? No.
            # From session: α = d/(n-k) where d = w - c + 1 = w (since c=1).
            # Wait: d = distance-related. Let me use the confirmed formula:
            # For c=1: α = (w-1+1)/(n-k) = w/(n-k)... no.
            # From the data: RS[16,8] w=7: α = 3/4 = 6/8 = (w-1)/(n-k)
            # RS[14,7] w=6: α = 5/7 ≈ 0.714 = (w-1)/(n-k)
            # RS[12,6] w=5: α = 4/6 = 2/3 = (w-1)/(n-k)
            # So α = (w-1)/(n-k) = (n-k-2)/(n-k) = 1 - 2/(n-k)
            alpha = (w - 1) / (n - k)
            M_palpha = M_max * (p ** alpha) if alpha > 0 else M_max
            
            print(f"  {p:5d} | {M_max:6d} | {avg:10.1f} | {M_max/max(avg,0.01):7.2f} | {M_palpha:10.1f} | {elapsed:7.1f}s")
            sys.stdout.flush()
            
            results.append((n, k, p, M_max, avg, alpha, M_palpha, elapsed))
    
    # Summary
    print(f"\n\n{'='*80}")
    print("SUMMARY: M_max at p_min vs n")
    print(f"{'='*80}")
    print(f"{'n':>4} {'k':>4} {'w':>4} | {'p_min':>5} | {'M_max':>6} | {'C(n,w)':>8} | {'log2(M)':>8} | {'log2(n)':>8} | {'M/n²':>8} | {'M/n³':>8}")
    print("-" * 90)
    
    ns = []
    Ms = []
    for n, k in configs:
        p_min = next_prime(n)
        w = n - k - 1
        for nn, kk, pp, mm, aa, al, mp, el in results:
            if nn == n and kk == k and pp == p_min:
                import math
                logM = math.log2(max(mm, 1))
                logn = math.log2(n)
                print(f"{n:4d} {k:4d} {w:4d} | {p_min:5d} | {mm:6d} | {comb(n,w):8d} | {logM:8.2f} | {logn:8.2f} | {mm/n**2:8.2f} | {mm/n**3:8.4f}")
                ns.append(n)
                Ms.append(mm)
                break
    
    if len(ns) >= 3:
        ns_arr = np.array(ns, dtype=float)
        Ms_arr = np.array([max(m, 1) for m in Ms], dtype=float)
        
        # Fit M ~ n^a (polynomial)
        log_n = np.log(ns_arr)
        log_M = np.log(Ms_arr)
        coeffs_poly = np.polyfit(log_n, log_M, 1)
        print(f"\nPolynomial fit: M_max ~ n^{coeffs_poly[0]:.2f}")
        
        # Fit M ~ b^n (exponential)
        coeffs_exp = np.polyfit(ns_arr, log_M, 1)
        print(f"Exponential fit: M_max ~ {np.exp(coeffs_exp[0]):.4f}^n")
        
        # R² comparison
        M_mean = np.mean(log_M)
        SS_tot = np.sum((log_M - M_mean)**2)
        
        pred_poly = np.polyval(coeffs_poly, log_n)
        R2_poly = 1 - np.sum((log_M - pred_poly)**2) / max(SS_tot, 1e-10)
        
        pred_exp = np.polyval(coeffs_exp, ns_arr)
        R2_exp = 1 - np.sum((log_M - pred_exp)**2) / max(SS_tot, 1e-10)
        
        print(f"R² polynomial: {R2_poly:.6f}")
        print(f"R² exponential: {R2_exp:.6f}")
        
        if R2_poly > R2_exp:
            print(f"\n*** POLYNOMIAL GROWTH IS BETTER FIT! M_max ~ n^{coeffs_poly[0]:.2f} ***")
        else:
            print(f"\n*** Exponential growth is better fit: M_max ~ {np.exp(coeffs_exp[0]):.4f}^n ***")

if __name__ == "__main__":
    main()
