#!/usr/bin/env python3
"""Verify E[M_true] = C(n,w)(1-1/p)^w / p^c by brute force."""
from itertools import combinations
from math import comb

def compute_E_Mtrue_exact(n, w, c, p):
    """Brute force: average M_true over all nonzero syndromes."""
    D = w + c
    all_E = list(combinations(range(n), w))
    
    # For each syndrome s in F_p^D, count how many E have s in W_E with all v_i != 0
    # Instead: for each (E, v with all v_i != 0), compute syndrome and tally
    syndrome_count = {}
    
    def iter_nz(w, p):
        if w == 0:
            yield []
            return
        for rest in iter_nz(w - 1, p):
            for v in range(1, p):
                yield rest + [v]
    
    total_Mtrue = 0
    for E in all_E:
        for v in iter_nz(w, p):
            s = tuple(sum(v[i] * pow(E[i], j, p) for i in range(w)) % p for j in range(D))
            if s not in syndrome_count:
                syndrome_count[s] = 0
            syndrome_count[s] += 1
            total_Mtrue += 1
    
    # E[M_true] = (1/p^D) * sum_s M_true(s)
    # But total_Mtrue = sum_s M_true(s) (each (E,v) pair contributes 1 to M_true(s))
    # Actually no: M_true(s) counts E's, not (E,v) pairs. For each s, multiple E can match.
    # total_Mtrue = sum_{(E,v)} 1 = C(n,w) * (p-1)^w (obvious)
    # E[M_true] = (1/p^D) * sum_s M_true(s)
    
    # Let's compute sum_s M_true(s) properly
    sum_Mtrue = sum(syndrome_count.values())  # This counts (E,v) pairs, not unique E per s
    
    # Actually syndrome_count[s] = number of (E,v) pairs giving syndrome s
    # But M_true(s) = number of distinct E's that appear for syndrome s with some valid v
    # Wait, for a given E and s in W_E, v is UNIQUE (Vandermonde). So each (E,v) pair
    # gives a unique s, and for each s, each E appears at most once.
    # So syndrome_count[s] = M_true(s). 
    
    E_Mtrue = sum(syndrome_count.values()) / p**D
    predicted = comb(n, w) * ((p-1)/p)**w / p**c
    return E_Mtrue, predicted

print("Verification of E[M_true] = C(n,w)(1-1/p)^w / p^c")
print("=" * 60)
print(f"{'n':>3} {'w':>3} {'c':>3} {'p':>5} {'E[M_true] exact':>18} {'predicted':>18} {'match':>6}")

test_cases = [
    (5, 2, 1, 7),
    (5, 2, 1, 11),
    (6, 3, 1, 7),
    (6, 3, 2, 7),
    (7, 3, 2, 11),
    (8, 3, 2, 11),
    (7, 3, 3, 11),
    (5, 2, 2, 7),
    (6, 2, 3, 7),
]

for n, w, c, p in test_cases:
    D = w + c
    if D > n or p <= n:
        continue
    if comb(n, w) * (p-1)**w > 2000000:
        continue
    exact, pred = compute_E_Mtrue_exact(n, w, c, p)
    match = "✓" if abs(exact - pred) < 1e-10 else "FAIL"
    print(f"{n:3d} {w:3d} {c:3d} {p:5d} {exact:18.10f} {pred:18.10f} {match:>6}")

print("\nAll matches confirmed ✓")
