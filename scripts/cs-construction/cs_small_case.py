"""
Small-case verification of Crites-Stewart counterexample structure.

Setup: F_p, p = 73, n = 24, m = 2, s = 12, r = 3.
  k = (r-2)m = 2,  delta = 1 - r/s = 3/4,  agreement threshold = (1-delta)n = 6.

Test: For f = X^{rm} = X^6, g = X^{(r-1)m} = X^4, find every lambda in F_p such that
f + lambda*g is delta-close to RS_k on L = <omega>. For each bad lambda, extract the
agreement sets S = {x in L : f(x) + lambda g(x) = h(x)} for the witnessing h's, and
check whether S aligns with multiplicative-coset structure of subgroups of L.

Expected (if Conjecture in Note 0002 is right): bad agreement sets are unions of
multiplicative cosets of subgroups of L.
"""

from itertools import combinations

p = 73
n = 24
m = 2
s = 12
r = 3
k = (r - 2) * m  # 2
delta_n = n - r * m  # support size of error = 24 - 6 = 18
threshold = r * m   # agreement size = 6

assert (p - 1) % n == 0, "need n | p-1"

# Find primitive n-th root of 1 in F_p
def find_omega(p, n):
    for cand in range(2, p):
        if pow(cand, n, p) != 1:
            continue
        # check it's primitive
        primitive = True
        for d in [2, 3]:  # n = 24 = 2^3 * 3, so primes dividing n are 2,3
            if pow(cand, n // d, p) == 1:
                primitive = False
                break
        if primitive:
            return cand
    raise RuntimeError("no primitive n-th root found")

omega = find_omega(p, n)
print(f"p = {p}, n = {n}, omega = {omega}")
L = [pow(omega, i, p) for i in range(n)]
print(f"L = {L}")

# Subgroups of L = Z/24Z (additive index group) correspond to divisors of 24.
# A subgroup of order d in L has index set {0, n/d, 2n/d, ...}.
divisors = [d for d in range(1, n+1) if n % d == 0]
print(f"Divisors of n: {divisors}")
subgroups_idx = {d: [(i * (n // d)) % n for i in range(d)] for d in divisors}
# Each coset of subgroup of order d has form {t + j*(n/d) mod n : j=0..d-1}
def cosets_of_subgroup(d):
    """Return list of cosets, each as a sorted index tuple."""
    h = subgroups_idx[d]
    seen = set()
    out = []
    for t in range(n // d):
        coset = tuple(sorted((t + i) % n for i in h))
        if coset not in seen:
            seen.add(coset)
            out.append(coset)
    return out

# Precompute f, g values on L
f_vals = [pow(x, r * m, p) for x in L]            # X^6
g_vals = [pow(x, (r - 1) * m, p) for x in L]     # X^4

# For each lambda, find ALL polynomials h(x) = h0 + h1*x of degree < k = 2 with
# at least `threshold` agreement points with (f + lambda*g)|_L.
def all_witnesses(lam):
    target = [(f_vals[i] + lam * g_vals[i]) % p for i in range(n)]
    witnesses = []
    for h0 in range(p):
        for h1 in range(p):
            agree_idx = []
            for i in range(n):
                hv = (h0 + h1 * L[i]) % p
                if hv == target[i]:
                    agree_idx.append(i)
                    # No early-abort: collect full agreement set for alignment analysis
            if len(agree_idx) >= threshold:
                witnesses.append((h0, h1, tuple(agree_idx)))
    return witnesses

# Sweep lambdas
print(f"\nSweeping lambda in F_{p} for max agreement >= {threshold} ...")
bad = {}
for lam in range(p):
    ws = all_witnesses(lam)
    if ws:
        bad[lam] = ws

print(f"\nFound {len(bad)} bad lambdas (out of {p}).")
for lam, ws in bad.items():
    print(f"\n  lambda = {lam}: {len(ws)} witness(es)")
    for h0, h1, S in ws:
        # S is index tuple in L; check if it's a union of cosets of any subgroup
        S_set = set(S)
        aligned_with = []
        for d in divisors:
            if r * m % d != 0:
                continue
            for coset in cosets_of_subgroup(d):
                if set(coset).issubset(S_set):
                    aligned_with.append((d, coset))
        # Try to express S as a disjoint union of cosets of a single subgroup
        union_decomps = {}
        for d in divisors:
            cs = cosets_of_subgroup(d)
            covered = []
            for c in cs:
                if set(c).issubset(S_set):
                    covered.append(c)
            if covered and sum(len(c) for c in covered) == len(S):
                union_decomps[d] = covered
        print(f"    h = {h0} + {h1}*x, S indices = {S}")
        if union_decomps:
            for d, decomp in union_decomps.items():
                print(f"      ✓ S = union of {len(decomp)} cosets of subgroup of order {d}: {decomp}")
        else:
            print(f"      ✗ S is NOT a clean union of cosets of any subgroup")

# Summary
print("\n=== SUMMARY ===")
print(f"Number of bad lambdas: {len(bad)}")
print(f"Total witnesses: {sum(len(w) for w in bad.values())}")
n_subgroup_aligned = 0
n_total = 0
for ws in bad.values():
    for _, _, S in ws:
        n_total += 1
        S_set = set(S)
        for d in divisors:
            cs = cosets_of_subgroup(d)
            covered = [c for c in cs if set(c).issubset(S_set)]
            if covered and sum(len(c) for c in covered) == len(S):
                n_subgroup_aligned += 1
                break
print(f"Of {n_total} witness agreement sets, {n_subgroup_aligned} align with a subgroup-coset decomposition.")
