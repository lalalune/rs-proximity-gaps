/-
Copyright (c) 2026 Raullen Chai, Xinxin Fan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

**Theorem ca-halved** (RVW13, STOC 2013).
Half-Threshold Correlated Agreement Bound.

For any linear code C over a field F with domain L (|L| = n):
  If (f₁, f₂) has joint error weight > 2d from C × C,
  then at most one γ ∈ F satisfies Δ(f₁ + γf₂, C) ≤ d.

This is Theorem 3.1 in the paper. Setting d = ⌊δn/2⌋ gives ε_ca(C, δ/2, δ) ≤ 1/|F|.
The proof uses only linearity of C — no polynomial structure, no restriction on k or δ.
-/
import FRISoundness.Defs

open Finset Fintype

namespace FRISoundness

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The main theorem -/

/--
**Theorem ca-halved** (RVW13).

Given:
- C : a linear code (submodule of L → F)
- f₁, f₂ : received words
- d : conclusion threshold (in absolute terms)
- Premise: for all (g₁, g₂) ∈ C × C, the joint agreement of (f₁,f₂) with (g₁,g₂)
  satisfies |agree| + 2d < n. (Equivalently: joint distance > 2d.)

Then: there cannot exist two DISTINCT γ₁ ≠ γ₂ in F with codewords h₁, h₂ ∈ C
such that both f₁ + γᵢf₂ agree with hᵢ on ≥ n - d positions.
(Equivalently: at most one γ has Δ(f₁ + γf₂, C) ≤ d.)
-/
theorem ca_halved
    (C : Submodule F (L → F))
    (f₁ f₂ : L → F) (d : ℕ)
    -- Premise: joint distance > 2d
    (hprem : ∀ g₁ ∈ C, ∀ g₂ ∈ C,
      (jointAgreeSet f₁ f₂ g₁ g₂).card + 2 * d < card L)
    -- Two distinct bad γ's
    {γ₁ γ₂ : F} (hne : γ₁ ≠ γ₂)
    {h₁ h₂ : L → F} (hh₁ : h₁ ∈ C) (hh₂ : h₂ ∈ C)
    -- Each has agreement ≥ n - d
    (hS₁ : card L ≤ (agreeSet (linComb f₁ f₂ γ₁) h₁).card + d)
    (hS₂ : card L ≤ (agreeSet (linComb f₁ f₂ γ₂) h₂).card + d)
    : False := by
  -- Let S₁, S₂ be the agreement sets.
  set S₁ := agreeSet (linComb f₁ f₂ γ₁) h₁ with hS₁_def
  set S₂ := agreeSet (linComb f₁ f₂ γ₂) h₂ with hS₂_def
  set n := card L with hn

  -- Step 1: By inclusion-exclusion, |S₁ ∩ S₂| + n ≥ |S₁| + |S₂| ≥ 2(n - d)
  have hie := card_inter_add_card_univ_ge S₁ S₂

  -- Step 2: Construct g₁, g₂ ∈ C as linear combinations of h₁, h₂.
  -- g₂ := (h₁ - h₂) / (γ₁ - γ₂), g₁ := h₁ - γ₁ · g₂
  have hγ : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne
  set g₂ : L → F := (γ₁ - γ₂)⁻¹ • (h₁ - h₂) with hg₂_def
  set g₁ : L → F := h₁ - γ₁ • g₂ with hg₁_def
  have hg₂C : g₂ ∈ C := C.smul_mem _ (C.sub_mem hh₁ hh₂)
  have hg₁C : g₁ ∈ C := C.sub_mem hh₁ (C.smul_mem _ hg₂C)

  -- Step 3: Show S₁ ∩ S₂ ⊆ jointAgreeSet f₁ f₂ g₁ g₂.
  -- On S₁ ∩ S₂: f₁(x) + γ₁·f₂(x) = h₁(x) AND f₁(x) + γ₂·f₂(x) = h₂(x).
  -- Solving: f₂(x) = (h₁(x) - h₂(x))/(γ₁ - γ₂) = g₂(x),
  --          f₁(x) = h₁(x) - γ₁·f₂(x) = h₁(x) - γ₁·g₂(x) = g₁(x).
  have hsub : S₁ ∩ S₂ ⊆ jointAgreeSet f₁ f₂ g₁ g₂ := by
    intro x hx
    rw [Finset.mem_inter] at hx
    simp only [S₁, S₂, agreeSet, linComb, Finset.mem_filter, mem_univ, true_and] at hx
    obtain ⟨eq1, eq2⟩ := hx
    -- eq1 : f₁ x + γ₁ * f₂ x = h₁ x
    -- eq2 : f₁ x + γ₂ * f₂ x = h₂ x
    -- First: f₂ x = g₂ x
    have hf₂ : f₂ x = g₂ x := by
      simp only [hg₂_def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      -- Goal: f₂ x = (γ₁ - γ₂)⁻¹ * (h₁ x - h₂ x)
      rw [eq_comm, inv_mul_eq_div, div_eq_iff hγ]
      -- Goal: h₁ x - h₂ x = f₂ x * (γ₁ - γ₂)
      rw [eq_comm, mul_comm]
      -- Goal: (γ₁ - γ₂) * f₂ x = h₁ x - h₂ x
      linear_combination eq1 - eq2
    -- Second: f₁ x = g₁ x
    have hf₁ : f₁ x = g₁ x := by
      simp only [hg₁_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      -- Goal: f₁ x = h₁ x - γ₁ * g₂ x
      rw [← hf₂]
      -- Goal: f₁ x = h₁ x - γ₁ * f₂ x
      linear_combination eq1
    simp only [jointAgreeSet, Finset.mem_filter, mem_univ, true_and]
    exact ⟨hf₁, hf₂⟩
  have hcard : (S₁ ∩ S₂).card ≤ (jointAgreeSet f₁ f₂ g₁ g₂).card :=
    Finset.card_le_card hsub

  -- Step 4: Apply the premise to g₁, g₂.
  have hcontra := hprem g₁ hg₁C g₂ hg₂C
  -- hcontra : (jointAgreeSet f₁ f₂ g₁ g₂).card + 2 * d < n

  -- Step 5: Contradiction.
  -- From Steps 1,3: (jointAgreeSet ...).card ≥ (S₁ ∩ S₂).card ≥ n - 2d
  -- From Step 4: (jointAgreeSet ...).card + 2d < n, i.e., (jointAgreeSet ...).card < n - 2d
  omega

end FRISoundness
