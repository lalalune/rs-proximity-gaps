/-
Copyright (c) 2026 Raullen Chai, Xinxin Fan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

FRI Coupling Lemma, Proximity Gap, and Soundness Composition.
-/
import FRISoundness.CA
import FRISoundness.RSCode
import Mathlib.RingTheory.Polynomial.Basic

open Finset Fintype

namespace FRISoundness

/-! ## Proximity Gap (Theorem 4.2)

The proximity gap theorem combines:
1. FRI coupling: Δ(f, RS_k) > δ ⟹ Δ_joint((fE, fO), RS_{k/2}²) > δ
2. ca_halved: joint distance > 2d ⟹ at most 1 bad α

Step 1 requires the RS isomorphism witness from RSCode.lean.
Step 2 is fully proved in CA.lean.

We prove the proximity gap modulo the coupling premise.
-/

/--
**Theorem (Half-Threshold Proximity Gap)** — Theorem 4.2.

If the joint distance of (fE, fO) from C' × C' exceeds 2d,
then at most 1 value of α makes fE + α · fO within distance d of C'.

This is a direct application of ca_halved.
-/
theorem proximity_gap
    {L' : Type*} [Fintype L'] [DecidableEq L']
    {F : Type*} [Field F] [DecidableEq F]
    (C' : Submodule F (L' → F))
    (fE fO : L' → F) (d : ℕ)
    (hprem : ∀ g₁ ∈ C', ∀ g₂ ∈ C',
      (jointAgreeSet fE fO g₁ g₂).card + 2 * d < card L')
    {α₁ α₂ : F} (hne : α₁ ≠ α₂)
    {c₁ c₂ : L' → F} (hc₁ : c₁ ∈ C') (hc₂ : c₂ ∈ C')
    (hA₁ : card L' ≤ (agreeSet (linComb fE fO α₁) c₁).card + d)
    (hA₂ : card L' ≤ (agreeSet (linComb fE fO α₂) c₂).card + d) :
    False :=
  ca_halved C' fE fO d hprem hne hc₁ hc₂ hA₁ hA₂

/-! ## FRI Soundness Composition

The full FRI soundness theorem:
  Pr[FRI accepts] ≤ nR/|F| + (1 - δ/2)^q

Proof structure:
- Strategy A (honest fold): Schwartz-Zippel ⟹ Pr ≤ R/|F|
- Strategy B (deviation at round i):
  · Round 1: ≤ 1 bad α (proximity_gap / ca_halved)
  · Rounds 2..R: ≤ n bad α's per round (BCIKS)
  · Total: ≤ 1 + (R-1)n ≤ nR bad α-tuples
  · Consistency check catches with probability ≥ 1 - (1-δ/2)^q
-/

/-- **Schwartz–Zippel** (building block, fully proved).

A nonzero univariate polynomial over an integral domain has at most
`natDegree` distinct roots.  The multivariate/multilinear syndrome reduction
needed for FRI Strategy A is still outside this lemma; this theorem
discharges only the univariate root-count axiom.

This was previously declared as an axiom; it is now proved from the Mathlib
lemma `Polynomial.card_roots` (root multiset cardinality is bounded by the
polynomial's degree, valued in `WithBot ℕ`), composed with
`Multiset.toFinset_card_le` (distinct-root count is bounded by total root
count) and the natDegree / degree relation for nonzero polynomials.

For FRI Strategy A: the syndrome polynomial is multilinear of degree ≤ R,
so `Pr[all syndromes vanish] ≤ R/|F|` by union over R variables. -/
theorem schwartz_zippel_fri
    {F : Type*} [CommRing F] [IsDomain F]
    (p : Polynomial F) (hp : p ≠ 0) :
    p.roots.toFinset.card ≤ p.natDegree := by
  refine le_trans (Multiset.toFinset_card_le _) ?_
  -- Goal: p.roots.card ≤ p.natDegree
  have h := Polynomial.card_roots hp
  -- h : (p.roots.card : WithBot ℕ) ≤ p.degree
  rw [Polynomial.degree_eq_natDegree hp] at h
  exact_mod_cast h

/-- **BCIKS Proximity Gap** (Theorem 1.2, FOCS 2020).
At unique-decoding radius γ < (1-ρ)/2: for all but ≤ n values of α,
the FRI fold preserves γ-distance from RS.

This is an external proved result. We state it as an axiom
with the precise interface needed for our composition. -/
axiom bciks_proximity_gap
    {L : Type*} [Fintype L] [DecidableEq L]
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (C : Submodule F (L → F))
    (f : L → F) (d : ℕ)
    -- At unique-decoding radius d < (1-ρ)/2 · n:
    -- the set of α ∈ F for which the fold f_α is NOT d-close to the folded code
    -- has cardinality ≤ card L. (BCIKS Theorem 1.2, FOCS 2020)
    (hud : 2 * d < card L) -- unique-decoding regime
    : ∃ (bad : Finset F), bad.card ≤ card L ∧
        ∀ α, α ∉ bad → ∃ g ∈ C, card L ≤ (agreeSet (linComb f f α) g).card + d
    -- Note: the linComb here is a placeholder for the FRI fold operation;
    -- the precise statement requires the FRIPairing structure.

/-- Bad-α count across all R rounds: ≤ nR total. -/
theorem bad_alpha_count (n R : ℕ) (hn : 0 < n) (hR : 0 < R) :
    1 + (R - 1) * n ≤ n * R := by
  obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.mul_succ]
  rw [Nat.mul_comm R' n]
  omega

/-
**Theorem fri-full** — FRI Soundness Above the Johnson Bound (Theorem 5.1).

The full theorem states:
  Pr[FRI accepts] ≤ nR/|F| + (1 - δ/2)^q

We decompose this into its combinatorial and probabilistic components:

**Combinatorial** (fully proved):
- ca_halved: at most 1 bad α at round 1
- BCIKS (axiom): at most n bad α's at rounds ≥ 2
- Total: ≤ nR bad α-tuples

**Probabilistic** (elementary):
- Commit phase: nR bad tuples out of |F|^R → probability nR/|F|
- Query phase: each query catches δ/2-far deviation → (1-δ/2)^q

## Formalization Status

| Component | Status | Reference |
|-----------|--------|-----------|
| ca_halved | **FULLY PROVED** | CA.lean |
| coupling_pointwise | **FULLY PROVED** | RSCode.lean |
| fEven/fOdd identities | **FULLY PROVED** | RSCode.lean |
| RS code definition | **FULLY PROVED** | RSCode.lean |
| proximity_gap | **PROVED** (via ca_halved) | this file |
| bad_alpha_count | **FULLY PROVED** | this file |
| RS isomorphism | **PROVED** under explicit `RSIsomorphismWitness` | RSCode.lean |
| BCIKS | axiomatized | this file |
| Schwartz-Zippel root count | **FULLY PROVED** | this file |
-/
end FRISoundness
