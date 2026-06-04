/-
Copyright (c) 2026 Raullen Chai, Xinxin Fan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Berlekamp / V_bad codim — preimage counting bound.

This is paper 3, Lemma 5.1 (Note 0119, Sub-case A1):

  RealizerData V f γs w  ⟹  γs.card * (V.card - w) ≤ V.card.

Specialised to `γs.card = T + 1` with `T ≥ 1` and `V.card > w`, this
forces `V.card ≤ w + w / T`. Both forms are needed downstream: the raw
multiplicative inequality drives the case-B → case-A reduction in
`SupportSubstitution.lean`, while the divided form is the headline
"|S*| ≤ w + ⌊w/T⌋" bound used in the codim composition.

Sub-case A2 (some `β_v = 0`) follows from Sub-case A1 applied to
`V_1 := {v ∈ S* : β_v ≠ 0}` with effective `w' := w - |V_0|`, plus the
straightforward observation `|S*| = |V_0| + |V_1|`. The reduction is
combinatorially trivial and is recorded as `realizer_bound_with_zero_part`.
-/
import FRISoundness.Berlekamp.Defs

open Finset Fintype

namespace FRISoundness.Berlekamp

variable {ι : Type*} [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Multiplicative form of the bound -/

/--
**Paper 3, Lemma 5.1, multiplicative form.**

If every `γ ∈ γs` has `(V.card - w) ≤ |preimageOn V f γ|`, then summing
over the (disjoint) fibres of distinct `γ`'s gives
`γs.card * (V.card - w) ≤ V.card`.

This is the raw output of the Note 0119 / Note 0122 substitution before
any algebraic rearrangement. -/
theorem RealizerData.card_mul_diff_le
    {V : Finset ι} {f : ι → F} {γs : Finset F} {w : ℕ}
    (R : RealizerData V f γs w) :
    γs.card * (V.card - w) ≤ V.card := by
  classical
  -- Sum of fibre sizes is ≥ γs.card * (V.card - w) by R.fibre_lb,
  -- and ≤ V.card by sum_card_preimageOn_le.
  have hsum_const :
      γs.sum (fun _ : F => V.card - w) = γs.card * (V.card - w) := by
    simp [Finset.sum_const]
  have hsum_lb :
      γs.card * (V.card - w) ≤ γs.sum (fun γ => (preimageOn V f γ).card) := by
    rw [← hsum_const]
    exact Finset.sum_le_sum (fun γ hγ => R.fibre_lb γ hγ)
  exact hsum_lb.trans (sum_card_preimageOn_le V f γs)

/-! ## Divided form: `|V| ≤ w + ⌊w/T⌋`

The next theorem extracts the `|S*|`-bound used in the deployment table.
We work entirely in `ℕ` (using natural subtraction): the hypothesis
`V.card > w` ensures `V.card - w` is genuinely positive, the hypothesis
`T ≥ 1` ensures we can divide. -/

/-- Algebraic kernel: `(T + 1)·(N − w) ≤ N` and `N > w` and `T ≥ 1`
imply `N ≤ w + w / T`. -/
private lemma S_star_size_kernel
    {N w T : ℕ} (hT : 1 ≤ T) (hgt : w < N)
    (hineq : (T + 1) * (N - w) ≤ N) :
    N ≤ w + w / T := by
  -- Set δ := N - w > 0.
  set δ := N - w with hδ
  have hN : N = w + δ := by simp [hδ, Nat.add_sub_of_le hgt.le]
  -- (T+1)·δ ≤ w + δ ⟹ T·δ ≤ w
  have hTδ : T * δ ≤ w := by
    have hh : (T + 1) * δ ≤ w + δ := by rw [← hN]; exact hineq
    -- (T + 1) * δ = T * δ + δ
    have : T * δ + δ ≤ w + δ := by rw [Nat.add_mul, one_mul] at hh; exact hh
    omega
  -- δ ≤ w / T (integer division), since T·δ ≤ w
  have hδ_le : δ ≤ w / T := by
    rcases Nat.lt_or_ge δ (w / T + 1) with hlt | hge
    · omega
    · -- if δ ≥ w/T + 1, then T·δ ≥ T·(w/T + 1) > w, contradicting hTδ
      have hmul : T * (w / T + 1) ≤ T * δ := Nat.mul_le_mul_left T hge
      have hT_div_lt : w < T * (w / T + 1) := by
        have hwrec : w = T * (w / T) + w % T := (Nat.div_add_mod w T).symm
        have hmod_lt : w % T < T := Nat.mod_lt _ hT
        have htmul : T * (w / T + 1) = T * (w / T) + T := by ring
        omega
      linarith
  rw [hN]
  omega

/--
**Paper 3, Lemma 5.1, divided form** (Note 0119 Sub-case A1 headline).

Given a `RealizerData` witness with `γs.card = T + 1`, `T ≥ 1`, and
`V.card > w`, we have `V.card ≤ w + w / T`.

This is the bound `|S*| ≤ w + ⌊w/T⌋` reported in the paper — the
specialisation `T = 1` (which holds for `c ∈ {3, 4}` at all deployment
`D`) gives `|S*| ≤ w + 1`, matching the `V_S × V_S` upper-bound
construction in `VSInclusion.lean`. -/
theorem RealizerData.S_star_size_bound
    {V : Finset ι} {f : ι → F} {γs : Finset F} {w T : ℕ}
    (R : RealizerData V f γs w)
    (hT : 1 ≤ T) (hγs_card : γs.card = T + 1) (hgt : w < V.card) :
    V.card ≤ w + w / T := by
  have hineq : (T + 1) * (V.card - w) ≤ V.card := by
    have := R.card_mul_diff_le
    rw [hγs_card] at this
    exact this
  exact S_star_size_kernel hT hgt hineq

/-! ## Sub-case A2: some `β_v = 0`

In the Berlekamp realiser setup, the variables `(α_v, β_v) ∈ F²` for
`v ∈ S*` are nonzero (by minimality of `S*`), but the `β_v` may
individually vanish. Note 0119's Sub-case A2 splits `S*` as the disjoint
union `V₀ ∪ V₁` of zero / nonzero `β`-positions and reduces to the
Sub-case A1 analysis on `V₁` with effective `w' := w - |V₀|`.

Combinatorially, the reduction is just additivity of cardinality and
nat-subtraction bookkeeping: `|S*| = |V₀| + |V₁|` and `|V₁| ≤ w' + w'/T`
gives `|S*| ≤ w + ⌊(w − |V₀|)/T⌋ ≤ w + ⌊w/T⌋`. -/

/-- Sub-case A2 reduction packaging: combine a Sub-case A1 bound on `V₁`
with the disjoint-union split `S* = V₀ ⊔ V₁` to obtain the Note 0119
universal `|S*| ≤ w + ⌊w/T⌋` bound. -/
theorem realizer_bound_with_zero_part
    {V₀ V₁ : Finset ι} (hdisj : Disjoint V₀ V₁) {w T : ℕ}
    (hbound : V₁.card ≤ (w - V₀.card) + (w - V₀.card) / T)
    (hV₀ : V₀.card ≤ w) :
    (V₀ ∪ V₁).card ≤ w + w / T := by
  rw [Finset.card_union_of_disjoint hdisj]
  -- |V₀| + |V₁| ≤ |V₀| + (w - |V₀|) + (w - |V₀|)/T
  --              = w + (w - |V₀|)/T
  --              ≤ w + w/T
  have h₁ : (w - V₀.card) / T ≤ w / T := Nat.div_le_div_right (Nat.sub_le _ _)
  calc V₀.card + V₁.card
      ≤ V₀.card + ((w - V₀.card) + (w - V₀.card) / T) := by
        exact Nat.add_le_add_left hbound _
    _ = w + (w - V₀.card) / T := by
        have : V₀.card + (w - V₀.card) = w := Nat.add_sub_of_le hV₀
        omega
    _ ≤ w + w / T := Nat.add_le_add_left h₁ _

end FRISoundness.Berlekamp
