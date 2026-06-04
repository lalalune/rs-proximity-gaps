/-
Copyright (c) 2026 Raullen Chai, Xinxin Fan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

FRI Soundness Above the Johnson Bound via Threshold Halving — Core Definitions.
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic

open Finset Fintype

namespace FRISoundness

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Agreement and error sets -/

/-- The agreement set of two functions: {x ∈ L : f(x) = g(x)} -/
def agreeSet (f g : L → F) : Finset L :=
  Finset.univ.filter (fun x => f x = g x)

/-- The error set: {x ∈ L : f(x) ≠ g(x)} -/
def errorSet (f g : L → F) : Finset L :=
  Finset.univ.filter (fun x => f x ≠ g x)

/-- Joint agreement set: positions where both pairs agree -/
def jointAgreeSet (f₁ f₂ g₁ g₂ : L → F) : Finset L :=
  Finset.univ.filter (fun x => f₁ x = g₁ x ∧ f₂ x = g₂ x)

/-- The linear combination f₁ + γ · f₂ -/
def linComb (f₁ f₂ : L → F) (γ : F) : L → F :=
  fun x => f₁ x + γ * f₂ x

/-! ## Cardinality lemmas -/

theorem agreeSet_card_add_errorSet_card (f g : L → F) :
    (agreeSet f g).card + (errorSet f g).card = card L := by
  have hunion : agreeSet f g ∪ errorSet f g = Finset.univ := by
    ext x; simp [agreeSet, errorSet, Finset.mem_union, Finset.mem_filter, eq_or_ne]
  have hdisj : Disjoint (agreeSet f g) (errorSet f g) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [agreeSet, errorSet, Finset.mem_filter, mem_univ, true_and] at hx1 hx2
    exact hx2 hx1
  rw [← card_union_of_disjoint hdisj, hunion, card_univ]

/-- The joint agreement set equals the intersection of individual agreement sets -/
theorem jointAgreeSet_eq_inter (f₁ f₂ g₁ g₂ : L → F) :
    jointAgreeSet f₁ f₂ g₁ g₂ = agreeSet f₁ g₁ ∩ agreeSet f₂ g₂ := by
  ext x; simp [jointAgreeSet, agreeSet, Finset.mem_inter, Finset.mem_filter]

/-- Inclusion-exclusion: |A ∩ B| + n ≥ |A| + |B| for subsets of a finite type -/
theorem card_inter_add_card_univ_ge {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) :
    (A ∩ B).card + card α ≥ A.card + B.card := by
  have h := (card_union_add_card_inter A B).symm
  have hle : (A ∪ B).card ≤ card α := card_le_univ _
  omega

end FRISoundness
