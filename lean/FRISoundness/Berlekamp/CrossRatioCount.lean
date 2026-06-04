/-
Copyright (c) 2026 Raullen Chai, Xinxin Fan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Berlekamp / V_bad codim — sub-leading cross-ratio codim count.

This is paper 3, Lemma 5.3 (Note 0123): every sub-leading stratum of
`V_bad` has codimension *strictly greater* than the leading `2(c − 1)`.
The headline consequence is that `dim V_bad = 2(w + 1)` exactly, hence
`codim V_bad = 2(c − 1)` *universally* for all `c ≥ 2`, all `D`.

The argument has two parts:

  *Cross-ratio fibre count* (paper 3, Lemma 5.3 step 4): a "ratio
  coincidence" preimage `f^{-1}(γ) ⊆ V_1` of size `r ≥ 1` cuts out a
  variety of size `(|F| − 1)^r` inside `(F × F^*)^r`, contributing
  codim `r − 1` to `V_{S^*}^2` (encoded combinatorially as a
  cardinality bound).

  *Sub-leading arithmetic*: the total codim of the
  `|S^*| = w + δ'` stratum is `2(c − δ') + (T + 1)(δ' − 1)`, which equals
  `2(c − 1) + (T − 1)(δ' − 1)`. For `δ' ≥ 2` and `T ≥ 2`, this is
  *strictly greater* than `2(c − 1)`.

The cross-ratio fibre count is established here as a per-`γ` cardinality
identity. The sub-leading arithmetic identity, lower bound, and strict
gap are proved as separate `Nat` inequalities. -/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Units
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Tactic

open Finset Fintype

namespace FRISoundness.Berlekamp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Cross-ratio variety cardinality

The fibre `{(α_1, β_1, …, α_r, β_r) : β_i ≠ 0, α_1/β_1 = … = α_r/β_r}`
has cardinality exactly `(|F| − 1)^r` per fixed `γ`: once `γ := α_1/β_1`
is chosen and the `β_i ≠ 0` are chosen, the `α_i = γ β_i` are determined.

Summed over `γ ∈ F`, the total cardinality is `≤ |F| · (|F| − 1)^r`,
i.e., codim `r − 1` in the ambient `(F × F^*)^r`. -/

/--
**Paper 3, Lemma 5.3, cross-ratio fibre count** (Note 0123 step 4).

For every `γ ∈ F` and every `r ≥ 0`, the cross-ratio fibre

  `{β : Fin r → F^× ↦ (i ↦ (γ · β i, β i))}`

has cardinality exactly `(|F| − 1)^r` — once `γ` is fixed, every
non-zero `β`-tuple yields a distinct point of the fibre.

We give the count of the *image* under the injection
`β ↦ (i ↦ (γ · β i, β i))`; the codim consequence inside `(F × F^*)^r`
follows by comparing this count with the ambient `|F^*|^r · |F|^r`.

The lemma is stated in terms of `Finset.image` and `Finset.univ`
explicitly to avoid `noncomputable def` / `Classical.decEq` instance
gaps that prevent `rw` from matching when wrapped through a definition. -/
theorem crossRatioFibre_card_eq (r : ℕ) (γ : F) :
    ((Finset.univ : Finset (Fin r → Fˣ)).image
        (fun (β : Fin r → Fˣ) (i : Fin r) => (γ * (β i : F), β i))).card =
      (Fintype.card F - 1) ^ r := by
  classical
  have hinj :
      Set.InjOn (fun (β : Fin r → Fˣ) (i : Fin r) =>
        (γ * (β i : F), β i)) ↑(Finset.univ : Finset (Fin r → Fˣ)) := by
    intro β₁ _ β₂ _ heq
    funext i
    have hi : (γ * (β₁ i : F), β₁ i) = (γ * (β₂ i : F), β₂ i) :=
      congrFun heq i
    exact (Prod.mk.inj hi).2
  rw [Finset.card_image_of_injOn hinj, Finset.card_univ,
      Fintype.card_pi]
  simp [Fintype.card_units]

/-- The non-zero coordinate count `(|F| − 1)^r` is bounded by `|F|^r`. -/
private lemma units_pow_le (r : ℕ) :
    (Fintype.card F - 1) ^ r ≤ (Fintype.card F) ^ r :=
  Nat.pow_le_pow_left (Nat.sub_le _ _) r

/-- **Paper 3, Lemma 5.3, fibre cardinality bound.**

Per-`γ` cardinality is `≤ |F|^r`, the multiplicative form of "fibre has
codim ≥ 0 in `(F × F^*)^r`". -/
theorem crossRatioFibre_card_le (r : ℕ) (γ : F) :
    ((Finset.univ : Finset (Fin r → Fˣ)).image
        (fun (β : Fin r → Fˣ) (i : Fin r) => (γ * (β i : F), β i))).card ≤
      (Fintype.card F) ^ r := by
  rw [crossRatioFibre_card_eq]
  exact units_pow_le r

/-- Total cardinality summed over `γ ∈ F`: bounded by `|F|^{r + 1}`,
i.e., codim ≥ `r − 1` in the ambient `(F × F^*)^r ≃ F^{2r}`. -/
theorem crossRatioFibre_total_card_le (r : ℕ) :
    (Finset.univ.sum fun γ : F =>
      ((Finset.univ : Finset (Fin r → Fˣ)).image
        (fun (β : Fin r → Fˣ) (i : Fin r) => (γ * (β i : F), β i))).card) ≤
      (Fintype.card F) ^ (r + 1) := by
  calc (Finset.univ.sum fun γ : F =>
        ((Finset.univ : Finset (Fin r → Fˣ)).image
          (fun (β : Fin r → Fˣ) (i : Fin r) => (γ * (β i : F), β i))).card)
      = (Finset.univ.sum fun _ : F => (Fintype.card F - 1) ^ r) := by
        refine Finset.sum_congr rfl ?_
        intro γ _
        exact crossRatioFibre_card_eq r γ
    _ = (Fintype.card F) * ((Fintype.card F - 1) ^ r) := by
        simp [Finset.sum_const, Finset.card_univ]
    _ ≤ (Fintype.card F) * ((Fintype.card F) ^ r) :=
        Nat.mul_le_mul_left _ (units_pow_le r)
    _ = (Fintype.card F) ^ (r + 1) := by ring

/-! ## Sub-leading codim arithmetic

For a sub-leading stratum `V_bad^{(δ')}` with `|S^*| = w + δ'` and
`δ' ≥ 1`, the total codim in `F^{2D}` is bounded below by
`2(c − δ') + (T + 1)(δ' − 1)`. The key arithmetic facts are:

  *Identity (rearrangement):*
    `2(c − δ') + (T + 1)(δ' − 1) = 2(c − 1) + (T − 1)(δ' − 1)`.

  *Lower bound:*
    The expression is `≥ 2(c − 1)`, with equality iff `δ' = 1` or
    `T = 1`.

  *Strict positivity:*
    For `δ' ≥ 2` and `T ≥ 2`, the gap `(T − 1)(δ' − 1) ≥ 1`.

We work in `ℕ` with truncated subtraction; the `δ' ≤ c`, `1 ≤ δ'`,
`1 ≤ T` hypotheses ensure subtractions do not under-flow. -/

/-- **Sub-leading codim identity** (paper 3, Lemma 5.3, line `codim_total`).

`2(c − δ') + (T + 1)(δ' − 1) = 2(c − 1) + (T − 1)(δ' − 1)`,
provided `1 ≤ δ' ≤ c` and `1 ≤ T`. -/
theorem subleading_codim_identity
    {c δ' T : ℕ} (hδ_pos : 1 ≤ δ') (hδc : δ' ≤ c) (hT_pos : 1 ≤ T) :
    2 * (c - δ') + (T + 1) * (δ' - 1) = 2 * (c - 1) + (T - 1) * (δ' - 1) := by
  have hδ_succ : δ' - 1 + 1 = δ' := Nat.succ_pred_eq_of_pos hδ_pos
  have hT_succ : T - 1 + 1 = T := Nat.succ_pred_eq_of_pos hT_pos
  have hcδ : (c - δ') + δ' = c := Nat.sub_add_cancel hδc
  have hc_pos : 1 ≤ c := le_trans hδ_pos hδc
  have hc_succ : c - 1 + 1 = c := Nat.succ_pred_eq_of_pos hc_pos
  nlinarith [Nat.zero_le (δ' - 1), Nat.zero_le (T - 1), Nat.zero_le (c - δ')]

/-- **Sub-leading codim lower bound.**

`2(c − δ') + (T + 1)(δ' − 1) ≥ 2(c − 1)`, provided `1 ≤ δ' ≤ c`
and `1 ≤ T`.

This is the codim guarantee for every sub-leading stratum:
`codim V_bad^{(δ')} ≥ 2(c − 1)` (matching the leading codim from
`V_S × V_S`). -/
theorem subleading_codim_lower_bound
    {c δ' T : ℕ} (hδ_pos : 1 ≤ δ') (hδc : δ' ≤ c) (hT_pos : 1 ≤ T) :
    2 * (c - 1) ≤ 2 * (c - δ') + (T + 1) * (δ' - 1) := by
  rw [subleading_codim_identity hδ_pos hδc hT_pos]
  exact Nat.le_add_right _ _

/-- **Sub-leading codim strict gap** (paper 3, Lemma 5.3 conclusion).

For `δ' ≥ 2` and `T ≥ 2`, the sub-leading codim is *strictly greater*
than the leading `2(c − 1)`:
`2(c − δ') + (T + 1)(δ' − 1) ≥ 2(c − 1) + 1`. -/
theorem subleading_codim_strict
    {c δ' T : ℕ} (hδ : 2 ≤ δ') (hδc : δ' ≤ c) (hT : 2 ≤ T) :
    2 * (c - 1) + 1 ≤ 2 * (c - δ') + (T + 1) * (δ' - 1) := by
  rw [subleading_codim_identity (le_trans (by norm_num) hδ) hδc
    (le_trans (by norm_num) hT)]
  have h₁ : 1 ≤ δ' - 1 := by omega
  have h₂ : 1 ≤ T - 1 := by omega
  have hgap : 1 ≤ (T - 1) * (δ' - 1) := by
    have := Nat.mul_le_mul h₂ h₁
    simpa using this
  omega

end FRISoundness.Berlekamp
