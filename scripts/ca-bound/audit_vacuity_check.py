"""
Audit: Is the CA-with-loss bound vacuous in the intermediate zone?

Thm 3.1 says: eps_ca(C, delta, 2*delta) <= ceil(n/t) / |F|

The CA violation requires:
  (A) Delta(f1+gamma*f2, C) <= delta  AND
  (B) Delta((f1,f2), C^{=2}) > 2*delta

Using infinity-norm for pair distance:
  Delta_inf = min_{g1,g2} max(Delta(f1,g1), Delta(f2,g2))

Max possible Delta(f, C) = covering_radius/n = (n-k)/n = 1 - rho

So Delta_inf <= 1 - rho.

For (B) to be satisfiable: need 2*delta < 1 - rho,  i.e. delta < (1-rho)/2.

But the intermediate zone has delta > delta_J = 1 - sqrt(rho).

Question: Is (1-rho)/2 >= 1 - sqrt(rho) for any rho?

Answer: (1-rho)/2 >= 1-sqrt(rho)
  iff  1-rho >= 2-2*sqrt(rho)
  iff  2*sqrt(rho) - 1 >= rho
  iff  -(rho - 2*sqrt(rho) + 1) >= 0
  iff  -(sqrt(rho) - 1)^2 >= 0

This is FALSE for all rho != 1.

So (1-rho)/2 < delta_J for ALL rho in (0,1).

Conclusion: For ALL delta in the intermediate zone and ALL rates rho:
  2*delta > 2*delta_J > 1-rho = max possible Delta_inf
  => condition (B) is NEVER satisfied
  => eps_ca(C, delta, 2*delta) = 0 trivially
  => Thm 3.1 bound is correct but VACUOUS

Let's verify numerically for standard parameters.
"""

import math

print("=" * 70)
print("VACUITY CHECK: Is 2*delta_J > 1-rho for all rates?")
print("=" * 70)
print(f"{'rho':>8} {'delta_J':>10} {'2*delta_J':>10} {'1-rho':>10} {'vacuous?':>10}")
print("-" * 70)

for rho_num, rho_den in [(1,2), (1,3), (1,4), (1,8), (1,16), (3,4), (2,3)]:
    rho = rho_num / rho_den
    delta_J = 1 - math.sqrt(rho)
    two_delta_J = 2 * delta_J
    capacity = 1 - rho
    vacuous = two_delta_J > capacity
    tag = 'YES' if vacuous else 'NO'
    print(f"{rho:8.4f} {delta_J:10.4f} {two_delta_J:10.4f} {capacity:10.4f} {tag:>10}")

print()
print("Algebraic proof: 2(1-sqrt(rho)) > 1-rho")
print("  iff  2-2u > 1-u^2   where u=sqrt(rho)")
print("  iff  (u-1)^2 > 0")
print("  TRUE for all rho != 1.")
print()

# Now check: what about the UNION definition?
# Delta_union = min_{g1,g2} |{x: f1!=g1 OR f2!=g2}|/n
# Delta_union <= Delta1 + Delta2 <= (1-rho) + (1-rho) = 2(1-rho)
# For (B): need Delta_union > 2*delta
# Is 2*delta < 2*(1-rho)?  iff delta < 1-rho.  YES in intermediate zone.
# So with UNION definition: (B) CAN be satisfied!

print("=" * 70)
print("WHAT IF ABF uses UNION definition for pair distance?")
print("=" * 70)
print()
print("Delta_union <= Delta1 + Delta2 <= 2*(1-rho)")
print("For (B): need 2*delta < 2*(1-rho), i.e., delta < 1-rho")
print("This IS true in the intermediate zone!")
print()
print("But Thm 3.1 Case 2 gives Delta1 <= 2*delta, Delta2 <= delta")
print("=> Delta_union <= 3*delta")
print("=> NOT necessarily <= 2*delta")
print()

print("Paper claims: (f1,f2) is NOT a CA violation at threshold 2*delta")
print("This requires: Delta_pair <= 2*delta")
print()
print(f"{'rho':>8} {'delta_J':>10} {'3*delta_J':>10} {'2*(1-rho)':>10} {'3dJ<2cap?':>10}")
print("-" * 70)
for rho_num, rho_den in [(1,2), (1,3), (1,4), (1,8), (1,16)]:
    rho = rho_num / rho_den
    delta_J = 1 - math.sqrt(rho)
    three_dJ = 3 * delta_J
    two_cap = 2 * (1 - rho)
    tag2 = 'YES' if three_dJ < two_cap else 'NO'
    print(f"{rho:8.4f} {delta_J:10.4f} {three_dJ:10.4f} {two_cap:10.4f} {tag2:>10}")

print()
print("KEY QUESTION: Which definition does ABF use?")
print("- Infinity-norm (max): Thm 3.1 is CORRECT but VACUOUS")
print("- Union-norm (sum): Thm 3.1 Case 2 has a GAP (3*delta, not 2*delta)")
print()

# Check what the paper's proof actually needs
print("=" * 70)
print("RESOLUTION: Check paper's Case 2 logic")
print("=" * 70)
print()
print("Case 2: Delta(f2, C) <= delta")
print("  => f2 = g2 + e, wt(e) <= delta*n")
print("  => f1+gamma*f2 = (f1+gamma*g2) + gamma*e")
print("  => Delta(f1+gamma*f2, h) <= delta  (given)")
print("  => Delta(f1+gamma*g2, h) <= delta + delta = 2*delta  (triangle)")
print("  => Delta(f1, C) <= 2*delta  (since gamma*g2 in C)")
print()
print("With INFINITY-NORM definition:")
print("  Delta_inf((f1,f2), C^2) <= max(2*delta, delta) = 2*delta")
print("  So (B) requires Delta_inf > 2*delta => NOT satisfied")
print("  Thm 3.1 is CORRECT: no CA violation in this case")
print()
print("But: Delta_inf <= 1-rho < 2*delta (for ALL intermediate zone)")
print("So (B) is NEVER satisfied, even in Case 1!")
print("Wait - Case 1 has Delta(f2,C) > delta, so max >= delta.")
print("Can max > 2*delta?  Need Delta(f1,C) > 2*delta or Delta(f2,C) > 2*delta.")
print("Delta(f_i, C) <= 1-rho.  Need 2*delta < 1-rho. FALSE in intermediate zone.")
print()
print("CONCLUSION: With infinity-norm, the ENTIRE Thm 3.1 is vacuous.")
print("The bound eps_ca = 0 trivially for ALL delta > delta_J.")
print()
print("The USEFUL content of the paper is NOT the CA bound, but the")
print("PACKING bound (Case 1): when f2 is far, <= ceil(n/t) bad gamma.")
print("This is a DIRECT proximity statement, independent of the CA framework.")
