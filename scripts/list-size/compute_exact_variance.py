#!/usr/bin/env python3
"""
Compute EXACT second moment of Berlekamp count X = #{E : a ∈ W_E(b)}.

For fixed b, decompose Var[X] by intersection size j = |E1 ∩ E2|.

Main result:
  E[X] = C(n,w) / p^{m-1}
  E[X^2] = Σ_j N(j) * P(a ∈ W_{E1}(b) ∩ W_{E2}(b))

where N(j) = C(n,w) * C(w,j) * C(n-w, w-j) = # ordered pairs with |E1∩E2|=j.

Key analysis (for fixed generic b):
  j ≤ w-m:   codim = 2(m-1),  P = 1/p^{2(m-1)}  [INDEPENDENT]
  j = w-m+1: codim = 2(m-1) if b ∉ V_{E1}+V_{E2}, else 2(m-1)-1
  j ≥ w-m+2: excess correlation

We compute for deployment-relevant parameters and check if Var << E[X]^2.
"""
from math import comb, log2
import sys

sys.stdout = open(sys.stdout.fileno(), mode='w', buffering=1)


def analyze_variance(n, k, w, p, label=""):
    m = n - k - w
    D = n - k

    E_X = comb(n, w) / p**(m-1)
    E_X_sq = E_X**2

    print(f"\n{'='*70}")
    print(f"VARIANCE ANALYSIS: {label}")
    print(f"RS[F_{p}, n={n}, k={k}], w={w}, m={m}, D={D}")
    print(f"C(n,w) = {comb(n,w)}")
    print(f"E[X] = C(n,w)/p^(m-1) = {E_X:.4f}")
    print(f"E[X]^2 = {E_X_sq:.4f}")
    print(f"{'='*70}")

    # Decompose by j
    print(f"\n{'j':>3} | {'N(j)':>12} | {'codim':>5} | {'P':>12} | {'contrib to E[X^2]':>18} | {'type'}")
    print("-" * 80)

    total_E_X2 = 0
    good_E_X2 = 0
    bad_E_X2 = 0

    for j in range(w + 1):
        Nj = comb(w, j) * comb(n - w, w - j)  # per E1, # of E2 with |∩|=j

        if 2*w - j <= D:
            # V_{E1}+V_{E2} has dim 2w-j (proper subspace or full)
            if 2*w - j < D:
                # V_{E1}+V_{E2} is a proper subspace of dim 2w-j
                # P(b ∈ V_{E1}+V_{E2}) = 1/p^{D-2w+j}

                # For generic b ∉ V_{E1}+V_{E2}: codim of intersection = 2(m-1)
                # For b ∈ V_{E1}+V_{E2}: extra structure

                # dim(V1^⊥ ∩ V2^⊥) = 2m - (D - j) = j - (w-m) when j > w-m
                # For Berlekamp: W_E(b)^⊥ = V_E^⊥ ∩ b^⊥
                # (V1^⊥ ∩ V2^⊥) ∩ b^⊥ has dim:
                #   max(0, (j - (w-m)) - 1) for generic b (not in their span)
                #   vs (j - (w-m)) if b ∈ span of V1^⊥ ∩ V2^⊥

                # For the WORST CASE over b:
                overlap_normals = max(0, j - (w - m))  # dim(V1^⊥ ∩ V2^⊥)

                if overlap_normals == 0:
                    codim_wc = 2 * (m - 1)
                else:
                    # Worst case: b chosen to maximize correlation
                    # intersection of W_{E1}(b)^⊥ and W_{E2}(b)^⊥ has dim
                    # at most overlap_normals (if b ⊥ all of V1^⊥ ∩ V2^⊥)
                    codim_wc = 2 * (m - 1) - overlap_normals  # worst case
                    # For GENERIC b: dim = max(0, overlap_normals - 1)
                    codim_generic = 2 * (m - 1) - max(0, overlap_normals - 1)

            else:
                # 2w-j = D, V_{E1}+V_{E2} fills the space
                codim_wc = 2 * (m - 1)  # always independent
                codim_generic = 2 * (m - 1)
        else:
            # 2w-j > D: V_{E1}+V_{E2} = F_p^D
            codim_wc = 2 * (m - 1)
            codim_generic = 2 * (m - 1)

        if j <= w - m:
            # Provably independent
            P = 1 / p**(2*(m-1))
            typ = "INDEP"
            codim_val = 2*(m-1)
        elif j == w:
            # Same subset: P(a ∈ W_E(b)) = 1/p^{m-1}
            P = 1 / p**(m-1)
            typ = "SAME"
            codim_val = m - 1
        else:
            # j > w-m, j < w: use generic-b estimate
            overlap_normals = j - (w - m)
            codim_val = 2*(m-1) - max(0, overlap_normals - 1)
            P = 1 / p**codim_val
            typ = f"CORR(o={overlap_normals})"

        contrib = comb(n, w) * Nj * P
        total_E_X2 += contrib

        if j <= w - m:
            good_E_X2 += contrib
        else:
            bad_E_X2 += contrib

        print(f"{j:3d} | {Nj:12d} | {codim_val:5d} | {P:12.2e} | {contrib:18.4f} | {typ}")

    var_X = total_E_X2 - E_X_sq
    print(f"\nE[X^2] = {total_E_X2:.4f}")
    print(f"E[X]^2 = {E_X_sq:.4f}")
    print(f"Var[X] = {var_X:.4f}")
    print(f"Var/E[X]^2 = {var_X/E_X_sq:.4f}")
    print(f"Var/E[X] = {var_X/E_X:.4f}")
    print(f"Good (j≤w-m): {good_E_X2:.4f}")
    print(f"Bad (j>w-m): {bad_E_X2:.4f}")
    print(f"Bad/E[X]^2 = {bad_E_X2/E_X_sq:.4f}")

    # Chebyshev: P(X > t*E[X]) <= Var / ((t-1)*E[X])^2
    if E_X > 0 and var_X > 0:
        # For t=2: P(X > 2*E[X]) <= Var/E[X]^2
        print(f"\nChebyshev P(X > 2*E[X]) <= {var_X/E_X_sq:.4f}")
        # For concentration within factor C: P(X > C*E[X]) <= Var/((C-1)*E[X])^2
        # We want: what C gives P < 1? I.e., Var < ((C-1)*E[X])^2
        # C-1 > sqrt(Var)/E[X] => C > 1 + sqrt(Var/E[X]^2)
        C_bound = 1 + (var_X/E_X_sq)**0.5
        print(f"Concentration factor C = {C_bound:.2f} (X < C*E[X] with positive prob)")

    return E_X, var_X


# Small test cases
analyze_variance(12, 6, 4, 31, "Small: n=12, k=6, p=31")
analyze_variance(18, 9, 7, 251, "Medium: n=18, k=9, p=251")
analyze_variance(20, 10, 7, 251, "Medium: n=20, k=10, p=251")
analyze_variance(20, 10, 7, 1021, "Medium: n=20, k=10, p=1021")

# Deployment-relevant
print("\n\n" + "=" * 70)
print("DEPLOYMENT PARAMETERS")
print("=" * 70)

# BabyBear: p = 2^31-1, n = 2^20, k = n/2, delta ~ 0.3
# w = floor(delta * n), m = n-k-w
p_bb = 2**31 - 1
n_bb = 64  # proxy (can't do 2^20)
k_bb = n_bb // 2
import math
delta = 0.3
w_bb = int(math.ceil(delta * n_bb))
m_bb = n_bb - k_bb - w_bb

if m_bb >= 2:
    analyze_variance(n_bb, k_bb, w_bb, p_bb, f"Proxy deployment: n={n_bb}, p=2^31-1")
else:
    print(f"m = {m_bb} < 2, Berlekamp conjecture trivial")

# Also check: at what n does Var/E[X]^2 become small?
print("\n\n" + "=" * 70)
print("SCALING OF Var/E[X]^2 WITH p")
print("=" * 70)

for p in [31, 61, 127, 251, 509, 1021, 2039]:
    n, k, w = 18, 9, 7
    m = n - k - w
    E_X = comb(n, w) / p**(m-1)

    # Quick estimate: bad contribution dominated by j = w-m+1 = 6 term
    # N(w-m+1) = C(w, w-m+1) * C(n-w, m-1) = C(7,6)*C(11,1) = 7*11 = 77
    # Per E1: 77 such E2. Contribution: C(n,w) * 77 / p^{2(m-1)-0} ≈ indep
    # Actually for m=2, j=6 (=w-m+1=6): overlap_normals = 1, codim = 2*(m-1) - 0 = 2
    # So it's still independent at generic b!

    # The only truly bad j is j = w = 7 (same E): contributes C(n,w)/p^{m-1}
    # And j = w-1 = 6 with b ∈ V_{E1}+V_{E2}: prob 1/p

    var_approx = E_X * (1 - 1/p**(m-1))  # Poisson-like lower bound
    print(f"p={p:5d}: E[X]={E_X:8.2f}, Var/E[X]≈{var_approx/E_X:.4f}, Var/E[X]^2≈{1/E_X:.4f}")
