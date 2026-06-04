"""
Faster, focused sweep — only small cases, streaming output.
Drops the huge k=5,6 cases that take hours.
"""
import sys
from itertools import product

def find_omega(p, n, n_factors):
    for cand in range(2, p):
        if pow(cand, n, p) != 1:
            continue
        if all(pow(cand, n // q, p) != 1 for q in n_factors):
            return cand
    raise RuntimeError("no primitive root")

def prime_factors(n):
    out = set(); d = 2; nn = n
    while d * d <= nn:
        while nn % d == 0: out.add(d); nn //= d
        d += 1
    if nn > 1: out.add(nn)
    return list(out)

def divisors(n):
    return [d for d in range(1, n+1) if n % d == 0]

def cosets_of_index_subgroup(n, d):
    H = [(i * (n // d)) % n for i in range(d)]
    seen = set(); out = []
    for t in range(n // d):
        c = tuple(sorted((t + h) % n for h in H))
        if c not in seen: seen.add(c); out.append(c)
    return out

def is_subgroup_aligned(S_set, n):
    for d in divisors(n):
        if d == 1 or d == n: continue
        if len(S_set) % d != 0: continue
        cs = cosets_of_index_subgroup(n, d)
        covered = [c for c in cs if set(c).issubset(S_set)]
        if covered and sum(len(c) for c in covered) == len(S_set):
            return d
    return None

def smallest_p(n):
    cand = n + 1
    while True:
        if all(cand % i != 0 for i in range(2, int(cand**0.5) + 1)):
            return cand
        cand += n

def run_case(n, m, s, r):
    assert n == s * m
    k = (r - 2) * m
    if k < 1: return
    delta = 1 - r / s
    if delta <= 0: return
    threshold = r * m
    p = smallest_p(n)
    omega = find_omega(p, n, prime_factors(n))
    L = [pow(omega, i, p) for i in range(n)]
    f_vals = [pow(x, r * m, p) for x in L]
    g_vals = [pow(x, (r - 1) * m, p) for x in L]

    bad = []
    for lam in range(p):
        target = [(f_vals[i] + lam * g_vals[i]) % p for i in range(n)]
        for hc in product(range(p), repeat=k):
            agree = []
            for i in range(n):
                hv = 0; xpw = 1
                for j in range(k):
                    hv = (hv + hc[j] * xpw) % p
                    xpw = (xpw * L[i]) % p
                if hv == target[i]:
                    agree.append(i)
            if len(agree) >= threshold:
                bad.append((lam, hc, tuple(agree)))

    aligned = sum(1 for _, _, S in bad if is_subgroup_aligned(set(S), n) is not None)
    not_aligned = [(lam, hc, S) for lam, hc, S in bad if is_subgroup_aligned(set(S), n) is None]
    n_lam = len(set(w[0] for w in bad))
    print(f"({n:>2},{m:>2},{s:>2},{r:>2}) p={p:<3} k={k} d={delta:.3f} | "
          f"#lam={n_lam:<3} #wits={len(bad):<5} #aligned={aligned:<5} #NOT={len(not_aligned)}",
          flush=True)
    if not_aligned:
        for lam, hc, S in not_aligned[:3]:
            print(f"     NON-ALIGNED: lam={lam} h={hc} S={S}", flush=True)
    return bad, not_aligned

# Only small cases — keep total under ~5 min
cases = [
    (12, 2, 6, 3),    # k=2, p=13 → 13*169 = 2200 ops/lam
    (12, 2, 6, 4),    # k=4, p=13 → 13*28k = 360k
    (12, 3, 4, 3),    # k=3, p=13 → 13*2200 = 30k
    (24, 2, 12, 3),   # k=2, p=73 → 73*5300 = 390k
    (24, 2, 12, 4),   # k=4, p=73 → 73*28M = 2B  -- skip if slow
    (24, 3, 8, 3),    # k=3, p=73 → 73*390k = 28M
    (30, 2, 15, 3),   # k=2, p=31 → 31*960 = 30k
    (30, 3, 10, 3),   # k=3, p=31 → 31*30k = 930k
    (36, 2, 18, 3),   # k=2, p=37 → 37*1370 = 51k
    (36, 3, 12, 3),   # k=3, p=37 → 37*51k = 1.9M
    (36, 4, 9, 3),    # k=4, p=37 → 37*1.9M = 70M  borderline
    (42, 2, 21, 3),   # k=2, p=43
    (42, 3, 14, 3),   # k=3, p=43
    (60, 2, 30, 3),   # k=2, p=61
]

print(f"{'(n,m,s,r)':<14} {'p':<5} {'k':<3} {'delta':<6} | results", flush=True)
print("-" * 90, flush=True)

total_wits = 0; total_aligned = 0; total_not = 0
for case in cases:
    n, m, s, r = case
    k = (r - 2) * m
    p = smallest_p(n)
    # Estimate cost: p * p^k * n. Skip if > 3e8.
    cost = p * (p ** k) * n
    if cost > 3e8:
        print(f"  skip {case}: cost~{cost:.1e}", flush=True)
        continue
    try:
        result = run_case(*case)
        if result is not None:
            bad, not_aligned = result
            total_wits += len(bad)
            total_aligned += len(bad) - len(not_aligned)
            total_not += len(not_aligned)
    except Exception as e:
        print(f"  error in {case}: {e}", flush=True)

print("-" * 90, flush=True)
print(f"TOTAL across sweep: {total_wits} witnesses, {total_aligned} aligned, {total_not} NOT", flush=True)
