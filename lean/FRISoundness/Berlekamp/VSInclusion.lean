/-
Copyright (c) 2026 Raullen Chai, Xinxin Fan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Berlekamp / V_bad codim — V_S × V_S inclusion (upper bound).

This is paper 3, Theorem 4.1 (Note 0117): for any `S ⊆ [n]` with
`|S| = w + 1`, the locus `V_S × V_S` lies in `V_bad`. The headline
codim consequence is `codim V_bad ≤ 2(c − 1)`.

The proof in the paper has two ingredients:

  (i)  *Combinatorial:* removing any `u ∈ S` from `S` produces a valid
       size-`w` support `E_u := S \ {u}`. As `u` ranges over `S`, this
       produces `|S| = w + 1` distinct supports, paired with `w + 1`
       distinct ratio values `γ_u := −α_u / β_u`.

  (ii) *Algebraic:* the projection `(s_1 + γ_u s_2)` of a generic
       `(s_1, s_2) ∈ V_S × V_S` lies in `V_{E_u}` because the `u`-th
       Vandermonde coefficient cancels.

Ingredient (ii) is encoded once in `Defs.lean` via `RealizerData`; the
file you are reading provides the *combinatorial* counting half (i):
the family `(γ, E)` constructed from a generic `(α, β)` on `S` has
`|S| = w + 1` distinct realisers. Since `|S| = w + 1 > T` whenever
`w ≥ T`, the witness count exceeds the Berlekamp threshold and we land
in `V_bad`. -/
import FRISoundness.Berlekamp.Defs

open Finset Fintype

namespace FRISoundness.Berlekamp

variable {ι : Type*} [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The realiser family from a `V_S × V_S` witness -/

/-- Combinatorial realiser family on a `(w + 1)`-element support.

Given `S` of size `w + 1`, and an *injective* ratio map
`γ : ι → F` on `S` (i.e., `γ_v ≠ γ_v'` for distinct `v, v' ∈ S`), the
assignment `v ↦ (γ v, S \ {v})` produces `w + 1` distinct pairs in
`F × Finset ι`. Both projections are injections when restricted to `S`:
the second because `S \ {v} = S \ {v'}` forces `v = v'` whenever `v ∈ S`,
and the first by the injectivity hypothesis on `γ`.

This is paper 3, §4 (immediate corollary of injectivity). -/
theorem v_S_realizer_family_card
    {S : Finset ι} {w : ℕ} (hS : S.card = w + 1)
    (γ : ι → F) (hγ : Set.InjOn γ S) :
    (S.image fun v => (γ v, S \ {v})).card = w + 1 := by
  rw [Finset.card_image_of_injOn (f := fun v => (γ v, S \ {v}))]
  · exact hS
  · intro v₁ hv₁ v₂ hv₂ heq
    -- The first coordinate is `γ v₁ = γ v₂`, hence v₁ = v₂ by injectivity.
    have : γ v₁ = γ v₂ := (Prod.mk.inj heq).1
    exact hγ hv₁ hv₂ this

/-- Specialisation: the *first* projection of the realiser family is the
set of distinct ratio values, of size `w + 1`. This corresponds to the
"`w + 1` distinct realisers" count cited in the paper's `M ≥ w + 1 > T`
inequality. -/
theorem v_S_distinct_gammas_card
    {S : Finset ι} {w : ℕ} (hS : S.card = w + 1)
    (γ : ι → F) (hγ : Set.InjOn γ S) :
    (S.image γ).card = w + 1 := by
  rw [Finset.card_image_of_injOn hγ, hS]

/-! ## Threshold step: `w + 1 > T`

The realiser-family count above produces `w + 1` distinct realisers.
The Berlekamp threshold is `T`, and the deployment regime always
satisfies `w ≥ T` (paper 3, §2.1). Hence `w + 1 > T`, so any
`(s_1, s_2)` admitting this realiser family is inside `V_bad`. -/

theorem realizer_count_exceeds_threshold
    {w T : ℕ} (hwT : T ≤ w) :
    T < w + 1 := by
  omega

end FRISoundness.Berlekamp
