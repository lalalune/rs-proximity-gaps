/-
Copyright (c) 2026 Raullen Chai, Xinxin Fan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Berlekamp / V_bad codim formalization — Core definitions.

This namespace formalizes the combinatorial cores of the four load-bearing
lemmas behind the rigorous unconditional bound `codim V_bad = 2(c-1)` for
all `c ≥ 2`, all deployment `D` (paper 3, §3–§5).

The four cores are split into four files:

  * `PreimageCounting.lean`   ← paper 3, Lemma 5.1   (Note 0119, Sub-case A1)
  * `SupportSubstitution.lean` ← paper 3, Lemma 5.2  (Note 0122)
  * `VSInclusion.lean`        ← paper 3, Theorem 4.1 (Note 0117)
  * `CrossRatioCount.lean`    ← paper 3, Lemma 5.3   (Note 0123)

with the final composition assembled in `Main.lean`.

This file collects only the basic definitions that every other Berlekamp
file uses: `preimageSize`, distinctness predicates, and the canonical
"Vandermonde slot" coordinate type used to write algebraic conditions on
`(α, β)` pairs combinatorially.
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

open Finset Fintype

namespace FRISoundness.Berlekamp

variable {ι : Type*} [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Preimage counting

The combinatorial heart of paper 3, §5 is a counting argument on
`f : ι → F` restricted to a finite subset `V ⊆ ι`. We use
`Finset.filter` directly rather than introducing a separate quotient
type. -/

/-- `preimageOn V f γ` — the fibre of `f` over `γ` inside `V`. -/
def preimageOn (V : Finset ι) (f : ι → F) (γ : F) : Finset ι :=
  V.filter (fun v => f v = γ)

@[simp] lemma mem_preimageOn {V : Finset ι} {f : ι → F} {γ : F} {v : ι} :
    v ∈ preimageOn V f γ ↔ v ∈ V ∧ f v = γ := by
  simp [preimageOn]

lemma preimageOn_subset (V : Finset ι) (f : ι → F) (γ : F) :
    preimageOn V f γ ⊆ V := by
  intro v hv; exact (mem_preimageOn.mp hv).1

/-- Distinct fibres are disjoint. -/
lemma preimageOn_disjoint
    {V : Finset ι} {f : ι → F} {γ₁ γ₂ : F} (hne : γ₁ ≠ γ₂) :
    Disjoint (preimageOn V f γ₁) (preimageOn V f γ₂) := by
  rw [Finset.disjoint_left]
  intro v h₁ h₂
  rcases mem_preimageOn.mp h₁ with ⟨_, hv₁⟩
  rcases mem_preimageOn.mp h₂ with ⟨_, hv₂⟩
  exact hne (hv₁.symm.trans hv₂)

/-- Sum of fibre sizes over a `Finset` of distinct `γ` values is bounded by
`V.card`. This is the "preimages partition `V`" inequality used in the
Note 0119 counting bound. -/
lemma sum_card_preimageOn_le
    (V : Finset ι) (f : ι → F) (Γ : Finset F) :
    (Γ.sum fun γ => (preimageOn V f γ).card) ≤ V.card := by
  classical
  -- The disjoint union of fibres over `Γ` is a subset of `V`.
  have hdisj : ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ ≠ γ₂ →
      Disjoint (preimageOn V f γ₁) (preimageOn V f γ₂) := by
    intro γ₁ _ γ₂ _ hne; exact preimageOn_disjoint hne
  have hsub : (Γ.disjiUnion (fun γ => preimageOn V f γ) hdisj) ⊆ V := by
    intro v hv
    rcases Finset.mem_disjiUnion.mp hv with ⟨_, _, hvfib⟩
    exact preimageOn_subset _ _ _ hvfib
  have hcardEq : (Γ.disjiUnion (fun γ => preimageOn V f γ) hdisj).card =
      Γ.sum fun γ => (preimageOn V f γ).card :=
    Finset.card_disjiUnion _ _ _
  calc Γ.sum (fun γ => (preimageOn V f γ).card)
      = (Γ.disjiUnion (fun γ => preimageOn V f γ) hdisj).card := hcardEq.symm
    _ ≤ V.card := Finset.card_le_card hsub

/-! ## "Realizer-data" abstract view

Throughout `Berlekamp/`, we work with the following abstract counting
witness. A `RealizerData V f γs w` says:

  * `V`     — the joint Vandermonde support `S*` (a finite subset of `ι`),
  * `f`     — the ratio function `f(v) = -α_v/β_v` defined on `V`,
  * `γs`    — a `Finset F` of distinct realizer parameters (size = `T+1`),
  * `w`     — the "support size" parameter,
  * each `γ ∈ γs` has fibre of size at least `V.card - w` inside `V`.

The "fibre ≥ |V| - w" condition is exactly the algebraic content
extracted by the Note 0122 substitution: every realizer admits a case-A
representative `E_A ⊂ S*` of size `w`, forcing `(α + γβ)|_v = 0` on
`V \ E_A`, i.e., `f(v) = γ` for at least `|V| - w` values of `v`.

`RealizerData` packages this combinatorial core so that
`PreimageCounting.lean` can prove the size bound `|V| ≤ w + ⌊w/T⌋`
without ever mentioning Reed–Solomon codes, Vandermonde matrices, or
linear algebra. -/

/-- Combinatorial witness for a tuple of `T+1` realizers in `V_bad`,
    after the Note 0122 case-B → case-A substitution. -/
structure RealizerData (V : Finset ι) (f : ι → F) (γs : Finset F) (w : ℕ) : Prop where
  fibre_lb : ∀ γ ∈ γs, V.card - w ≤ (preimageOn V f γ).card

end FRISoundness.Berlekamp
