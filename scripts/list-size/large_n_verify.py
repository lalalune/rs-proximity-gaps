"""Large-n verification: sweep t values on power-of-2 domains.
Uses 28 cores for parallel lambda sweep."""
from multiprocessing import Pool
from math import gcd, comb
import random, sys

def is_prime(n):
    if n<2: return False
    if n<4: return True
    if n%2==0 or n%3==0: return False
    d=5
    while d*d<=n:
        if n%d==0 or n%(d+2)==0: return False
        d+=6
    return True

def prime_factors(n):
    out=set(); d=2; nn=n
    while d*d<=nn:
        while nn%d==0: out.add(d); nn//=d
        d+=1
    if nn>1: out.add(nn)
    return list(out)

def find_omega(p,n):
    pf=prime_factors(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in pf):
            return pow(g,(p-1)//n,p)

def modinv(a,p): return pow(a,p-2,p)

def find_proper_prime(n, min_ratio=3):
    p=n*min_ratio+1
    while True:
        if p%n==1 and is_prime(p): return p
        p+=1

def sweep_one(args):
    lam, L, n, p, t = args
    a, b = t, t-1
    c=[(pow(L[i],a,p)+lam*pow(L[i],b,p))%p for i in range(n)]
    seen=set(); M=0; max_ag=0
    for i in range(n):
        for j in range(i+1,n):
            dx=(L[j]-L[i])%p; dy=(c[j]-c[i])%p
            h1=(dy*modinv(dx,p))%p; h0=(c[i]-h1*L[i])%p
            key=(h0,h1)
            if key in seen: continue
            seen.add(key)
            ag=sum(1 for idx in range(n) if (h0+h1*L[idx])%p==c[idx])
            if ag>=t: M+=1; max_ag=max(max_ag,ag)
    return (M, max_ag)

if __name__=="__main__":
    random.seed(42)
    ncpu = 24

    # Test matrix: power-of-2 domains × even t values
    test_cases = [
        # (n, t_values)
        (128, [6, 8, 10]),
        (256, [6, 8, 10]),
        (512, [6, 8, 10]),
        (1024, [6, 8]),
    ]

    print(f"Large-n verification (power-of-2 domains, worst-case binomial)")
    print(f"Cores: {ncpu}")
    print(f"{'n':>6} {'t':>3} {'p':>8} {'gcd':>4} {'samples':>8} {'max_M':>6} {'max_ag':>7} "
          f"{'n/(t-1)':>8} {'spor_est':>9} {'predict':>8}")
    print("-"*80)

    for n, t_list in test_cases:
        p = find_proper_prime(n, 3)
        omega = find_omega(p, n)
        L = [pow(omega, i, p) for i in range(n)]

        for t in t_list:
            g = gcd(t-1, n)
            coset_M = n // (t-1) if g == t-1 else 0
            spor = comb(n, t) / (p ** (t-2))

            samp = min(100, p)
            lams = random.sample(range(p), samp)
            tasks = [(l, L, n, p, t) for l in lams]

            with Pool(ncpu) as pool:
                results = pool.map(sweep_one, tasks, chunksize=max(1,samp//48))

            mx_M = max(r[0] for r in results)
            mx_ag = max(r[1] for r in results)

            if g == 1:
                pred = "O(1)"
            elif g == t-1:
                pred = f"≤{coset_M}"
            else:
                pred = f"≤{n//g}"

            print(f"{n:>6} {t:>3} {p:>8} {g:>4} {samp:>8} {mx_M:>6} {mx_ag:>7} "
                  f"{n/(t-1):>8.1f} {spor:>9.1e} {pred:>8}", flush=True)

    # Also test non-power-of-2 (divisible by 5) for comparison
    print(f"\nComparison: domains divisible by 5")
    for n in [160, 320, 640]:
        p = find_proper_prime(n, 3)
        omega = find_omega(p, n)
        L = [pow(omega, i, p) for i in range(n)]
        t = 6
        g = gcd(5, n)

        samp = min(100, p)
        lams = random.sample(range(p), samp)
        tasks = [(l, L, n, p, t) for l in lams]
        with Pool(ncpu) as pool:
            results = pool.map(sweep_one, tasks, chunksize=max(1,samp//48))
        mx_M = max(r[0] for r in results)
        spor = comb(n,t)/(p**(t-2))
        print(f"{n:>6} {t:>3} {p:>8} {g:>4} {samp:>8} {mx_M:>6} {'':>7} "
              f"{n/(t-1):>8.1f} {spor:>9.1e} {'≤'+str(n//5):>8}", flush=True)
