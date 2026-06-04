/-
Copyright (c) 2026 Raullen Chai, Xinxin Fan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

**Theorem 7** (paper §4): Equal-threshold correlated agreement upper bound.

For any linear code `C` over a field `F` with domain `L` (`|L| = n`):
if `(f₁, f₂)` has joint distance `> w` from `C × C`, then the number of
`γ ∈ F` that make `f₁ + γ · f₂` within distance `w` of `C` is at most
`Nat.choose n w` (= `C(n, w)`).

The proof mirrors `ca_halved` (CA.lean): two distinct "bad" `γ`'s that
witness agreement on the **same** `(n−w)`-subset `A` of `L` would yield a
codeword pair `(g₁, g₂) ∈ C × C` matching `(f₁, f₂)` on `A`, contradicting
the joint-distance premise. The map `γ ↦ A_γ` is therefore injective into
the `(n − w)`-subsets of `L`, giving the `C(n, n−w) = C(n, w)` bound.

Both the two-`γ` core lemma and the aggregate count bound are fully proved
(zero `sorry`). The aggregate bound packages the codeword witness and its
agreement subset into a single sigma-type so that `Classical.choose`
preserves the codeword's membership in `C`.
-/
import FRISoundness.Defs

open Finset Fintype

namespace FRISoundness

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Two-γ core lemma

Two distinct `γ`'s that share the **same** `(n − w)`-subset of agreement
contradict the joint-distance premise. This is the equal-threshold analogue
of `ca_halved`: the bookkeeping is identical except that the agreement set
`A` is a fixed parameter rather than derived from the inclusion-exclusion
of two `(n − d)`-subsets. -/

/--
**Equal-threshold CA, two-γ core lemma.**

If
- `C` is a linear code,
- `(f₁, f₂)` has joint distance `> w` from `C × C` (premise `hprem`),
- `γ₁ ≠ γ₂` both lie in the "bad" set
  (`f₁ + γᵢ · f₂` agrees with some `hᵢ ∈ C` on a common subset `A`),
- `|A| + w = |L|`,

then we derive `False`. The contradicting codeword pair is
`g₂ := (h₁ − h₂)/(γ₁ − γ₂) ∈ C` and `g₁ := h₁ − γ₁ · g₂ ∈ C`,
which agree with `(f₁, f₂)` on all of `A`.
-/
theorem ca_equal_threshold_pair
    (C : Submodule F (L → F))
    (f₁ f₂ : L → F) (w : ℕ)
    (hprem : ∀ g₁ ∈ C, ∀ g₂ ∈ C,
      (jointAgreeSet f₁ f₂ g₁ g₂).card + w < card L)
    {γ₁ γ₂ : F} (hne : γ₁ ≠ γ₂)
    {h₁ h₂ : L → F} (hh₁ : h₁ ∈ C) (hh₂ : h₂ ∈ C)
    {A : Finset L} (hAcard : A.card + w = card L)
    (hAgree₁ : A ⊆ agreeSet (linComb f₁ f₂ γ₁) h₁)
    (hAgree₂ : A ⊆ agreeSet (linComb f₁ f₂ γ₂) h₂) :
    False := by
  -- Build g₂ := (h₁ - h₂)/(γ₁ - γ₂), g₁ := h₁ - γ₁·g₂.
  have hγ : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne
  set g₂ : L → F := (γ₁ - γ₂)⁻¹ • (h₁ - h₂) with hg₂_def
  set g₁ : L → F := h₁ - γ₁ • g₂ with hg₁_def
  have hg₂C : g₂ ∈ C := C.smul_mem _ (C.sub_mem hh₁ hh₂)
  have hg₁C : g₁ ∈ C := C.sub_mem hh₁ (C.smul_mem _ hg₂C)
  -- Show A ⊆ jointAgreeSet f₁ f₂ g₁ g₂.
  have hsub : A ⊆ jointAgreeSet f₁ f₂ g₁ g₂ := by
    intro x hxA
    have h1 : f₁ x + γ₁ * f₂ x = h₁ x := by
      have := hAgree₁ hxA
      simp only [agreeSet, linComb, Finset.mem_filter, mem_univ, true_and] at this
      exact this
    have h2 : f₁ x + γ₂ * f₂ x = h₂ x := by
      have := hAgree₂ hxA
      simp only [agreeSet, linComb, Finset.mem_filter, mem_univ, true_and] at this
      exact this
    -- f₂ x = g₂ x
    have hf₂ : f₂ x = g₂ x := by
      simp only [hg₂_def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [eq_comm, inv_mul_eq_div, div_eq_iff hγ]
      rw [eq_comm, mul_comm]
      linear_combination h1 - h2
    -- f₁ x = g₁ x
    have hf₁ : f₁ x = g₁ x := by
      simp only [hg₁_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hf₂]
      linear_combination h1
    simp only [jointAgreeSet, Finset.mem_filter, mem_univ, true_and]
    exact ⟨hf₁, hf₂⟩
  -- |jointAgreeSet| ≥ |A| = n - w, but premise says |jointAgreeSet| + w < n
  have hcard : A.card ≤ (jointAgreeSet f₁ f₂ g₁ g₂).card :=
    Finset.card_le_card hsub
  have hcontra := hprem g₁ hg₁C g₂ hg₂C
  omega

/-! ## Aggregate count bound

For each bad `γ`, the agreement set has size `≥ n − w`, so we can pick a
`(n − w)`-subset `A_γ ⊆ L`. The two-`γ` lemma above shows the assignment
`γ ↦ A_γ` is injective into `Finset.univ.powersetCard (n − w)`, which has
cardinality `C(n, n − w) = C(n, w)`. -/

/-- A single packaged "witness" for a bad γ: a codeword `h ∈ C` together with
    a `(n − w)`-subset `A ⊆ L` on which `f₁ + γ · f₂ = h`. Packaging both
    into one existential ensures `Classical.choose` preserves both pieces. -/
private def IsBadWitness
    (C : Submodule F (L → F))
    (f₁ f₂ : L → F) (w : ℕ) (γ : F)
    (h : L → F) (A : Finset L) : Prop :=
  h ∈ C ∧ A.card = card L - w ∧ A ⊆ agreeSet (linComb f₁ f₂ γ) h

private lemma exists_witness
    (C : Submodule F (L → F))
    (f₁ f₂ : L → F) (w : ℕ) (hw : w ≤ card L) (γ : F)
    (hbad : ∃ h ∈ C, card L ≤ (agreeSet (linComb f₁ f₂ γ) h).card + w) :
    ∃ (h : L → F) (A : Finset L), IsBadWitness C f₁ f₂ w γ h A := by
  obtain ⟨h, hC, hcard⟩ := hbad
  have hagree_card : card L - w ≤ (agreeSet (linComb f₁ f₂ γ) h).card := by omega
  obtain ⟨A, hAsub, hAcard⟩ :=
    Finset.exists_subset_card_eq hagree_card
  exact ⟨h, A, hC, hAcard, hAsub⟩

/--
**Equal-threshold CA upper bound** (paper Theorem 7).

If `(f₁, f₂)` has joint distance `> w` from `C × C` and `w ≤ |L|`, then the
set of "bad" γ's — those for which `f₁ + γ · f₂` is within distance `w` of
`C` — has cardinality at most `Nat.choose |L| w`.

For RS[F, L, k] with `w = n − k − 1`, this gives the `C(n, w)/|F|` bound of
the paper's Theorem 7.
-/
theorem ca_equal_threshold
    (C : Submodule F (L → F))
    (f₁ f₂ : L → F) (w : ℕ) (hw : w ≤ card L)
    (hprem : ∀ g₁ ∈ C, ∀ g₂ ∈ C,
      (jointAgreeSet f₁ f₂ g₁ g₂).card + w < card L)
    (Γ : Finset F)
    (hbad : ∀ γ ∈ Γ,
      ∃ h ∈ C, card L ≤ (agreeSet (linComb f₁ f₂ γ) h).card + w) :
    Γ.card ≤ Nat.choose (card L) w := by
  classical
  -- For every γ ∈ Γ, package its codeword + (n−w)-witness subset.
  let pickH : ∀ γ ∈ Γ, L → F := fun γ hγ =>
    Classical.choose (exists_witness C f₁ f₂ w hw γ (hbad γ hγ))
  let pickA : ∀ γ ∈ Γ, Finset L := fun γ hγ =>
    Classical.choose
      (Classical.choose_spec (exists_witness C f₁ f₂ w hw γ (hbad γ hγ)))
  have pickSpec : ∀ γ (hγ : γ ∈ Γ),
      IsBadWitness C f₁ f₂ w γ (pickH γ hγ) (pickA γ hγ) := fun γ hγ =>
    Classical.choose_spec
      (Classical.choose_spec (exists_witness C f₁ f₂ w hw γ (hbad γ hγ)))
  -- Each pickA γ is in the powersetCard (card L - w) of L.
  have hmem : ∀ γ (hγ : γ ∈ Γ),
      pickA γ hγ ∈ (Finset.univ : Finset L).powersetCard (card L - w) := by
    intro γ hγ
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, (pickSpec γ hγ).2.1⟩
  -- The map γ ↦ pickA γ is injective (two-γ core lemma).
  have hinj : Set.InjOn (fun γ => if hγ : γ ∈ Γ then pickA γ hγ else ∅) Γ := by
    intro γ₁ hmem₁ γ₂ hmem₂ hAeq
    -- Set.InjOn introduces membership in the Set coercion of Γ; bridge to Finset.
    have hγ₁ : γ₁ ∈ Γ := hmem₁
    have hγ₂ : γ₂ ∈ Γ := hmem₂
    by_contra hne
    -- Unfold the if-then-else under the membership hypothesis.
    rw [dif_pos hγ₁, dif_pos hγ₂] at hAeq
    -- Now hAeq : pickA γ₁ hγ₁ = pickA γ₂ hγ₂. Use ca_equal_threshold_pair
    -- on the SHARED subset A := pickA γ₁ hγ₁.
    set A := pickA γ₁ hγ₁ with hA_def
    have hA_card : A.card + w = card L := by
      have : A.card = card L - w := (pickSpec γ₁ hγ₁).2.1
      omega
    obtain ⟨hC₁, _, hsub₁⟩ := pickSpec γ₁ hγ₁
    obtain ⟨hC₂, _, hsub₂_raw⟩ := pickSpec γ₂ hγ₂
    have hsub₂ : A ⊆ agreeSet (linComb f₁ f₂ γ₂) (pickH γ₂ hγ₂) := by
      rw [hAeq]; exact hsub₂_raw
    exact ca_equal_threshold_pair C f₁ f₂ w hprem hne hC₁ hC₂ hA_card hsub₁ hsub₂
  -- Conclude via card_le_card_of_injOn into the powersetCard target.
  calc Γ.card
      ≤ ((Finset.univ : Finset L).powersetCard (card L - w)).card := by
        refine Finset.card_le_card_of_injOn
          (fun γ => if hγ : γ ∈ Γ then pickA γ hγ else ∅) ?_ hinj
        intro γ hγ
        rw [dif_pos hγ]
        exact hmem γ hγ
    _ = Nat.choose (card L) (card L - w) := by
        rw [Finset.card_powersetCard, Finset.card_univ]
    _ = Nat.choose (card L) w := Nat.choose_symm hw

end FRISoundness
