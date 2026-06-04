/-
Copyright (c) 2026 Raullen Chai, Xinxin Fan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Berlekamp / V_bad codim — composition of the four load-bearing lemmas.

This file collects the four combinatorial cores into the headline
statement of paper 3:

  **codim V_bad = 2(c − 1)** for all `c ≥ 2`, all deployment `D`.

The result is the composition of:

  * `RealizerData.S_star_size_bound`   ← Lemma 5.1 (Note 0119)
  * `support_substitution`             ← Lemma 5.2 (Note 0122)
  * `v_S_realizer_family_card`         ← Theorem 4.1 (Note 0117)
  * `subleading_codim_strict`          ← Lemma 5.3 (Note 0123)

The algebraic-geometric content (`V_S` is a sub-module spanned by `ev_v`,
`V_bad` is Zariski-closed, codim/dim accounting for affine varieties) is
*not* formalised here — the existing FRISoundness Mathlib stack does not
yet host the relevant API. Instead, we expose an explicit interface
`VbadCodimWitness`, modelled on the `RSIsomorphismWitness` pattern in
`RSCode.lean`, that records exactly the algebraic facts the paper uses
to bridge the combinatorial cores to the codim count. Once that
interface is supplied (by a downstream algebraic-geometric formalisation
of `V_S` and `V_bad`), the combinatorial theorems below give the codim
value as the corresponding combinatorial witness count. -/
import FRISoundness.Berlekamp.Defs
import FRISoundness.Berlekamp.PreimageCounting
import FRISoundness.Berlekamp.SupportSubstitution
import FRISoundness.Berlekamp.VSInclusion
import FRISoundness.Berlekamp.CrossRatioCount

open Finset Fintype

namespace FRISoundness.Berlekamp

variable {ι : Type*} [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Headline arithmetic identity

The "core arithmetic" of paper 3, §5 reads:

  *Sub-leading codim ≥ leading codim* iff `(T − 1)(δ' − 1) ≥ 0`,
  *strictly* iff `T ≥ 2` and `δ' ≥ 2`.

Two regimes arise. For `T = 1` (which holds for `c ∈ {3, 4}` at all
deployment `D`), Note 0119's `|S^*| ≤ w + ⌊w/T⌋ = 2w` does *not*
collapse the sub-leading strata, but the codim accounting still gives
`codim V_bad^{(δ')} ≥ 2(c − 1)` (with equality, not strict): every
sub-leading stratum has the *same* dim `2(w + 1)` as the leading one,
so `dim V_bad = 2(w + 1)` and the codim equality is preserved. For
`T ≥ 2` (which holds for `c ≥ 5`), Note 0123's strict gap
`(δ' − 1)(T − 1) ≥ 1` forces every sub-leading stratum to be *strictly*
lower-dim than the leading, so only leading saturates `dim V_bad`. -/

/-- **Paper 3, §5 universal codim equality** (combinatorial form).

The sub-leading codim contribution `2(c − δ') + (T + 1)(δ' − 1)` is
always at least the leading `2(c − 1)`, and is *strictly* greater
whenever `T ≥ 2` and `δ' ≥ 2`. -/
theorem subleading_dominates
    {c δ' T : ℕ} (hδ : 1 ≤ δ') (hδc : δ' ≤ c) (hT : 1 ≤ T) :
    2 * (c - 1) ≤ 2 * (c - δ') + (T + 1) * (δ' - 1) :=
  subleading_codim_lower_bound hδ hδc hT

/-- **Combinatorial-codim composition.**

Suppose:

  * `(s_1, s_2)` lives in `V_bad` with realiser data `R : RealizerData V f γs w`,
    `γs.card = T + 1`, and `T ≥ 2`.
  * The substitution `support_substitution` produces case-A
    representatives (`E_A ⊆ V`).

Then any sub-leading stratum (`V.card > w + 1`, i.e., `δ' = V.card - w ≥ 2`)
is *strictly* deeper than `2(c − 1)`. -/
theorem RealizerData.subleading_strict
    {V : Finset ι} {f : ι → F} {γs : Finset F} {w T : ℕ}
    (_R : RealizerData V f γs w)
    (hT : 2 ≤ T) (_hγs_card : γs.card = T + 1)
    (hgt : w + 1 < V.card)
    {c : ℕ} (hδc : V.card - w ≤ c) :
    2 * (c - 1) + 1 ≤ 2 * (c - (V.card - w)) + (T + 1) * (V.card - w - 1) := by
  set δ' := V.card - w with hδdef
  have hδ_pos : 2 ≤ δ' := by
    rw [hδdef]; omega
  exact subleading_codim_strict hδ_pos hδc hT

/-! ## Headline statements

The final paper 3 §3 theorem reads:

  *codim V_bad = 2(c − 1)*  RIGOROUSLY for all `c ≥ 2`, all deployment
  parameters `(n, k)` with `w ≥ T ≥ 1`.

This statement is naturally split into two halves:

  * Upper bound `codim V_bad ≤ 2(c − 1)`: from the V_S × V_S inclusion
    (Theorem 4.1 / Note 0117). Combinatorial witness:
    `v_S_realizer_family_card`.

  * Lower bound `codim V_bad ≥ 2(c − 1)`: from the |S^*|-bound
    (Lemma 5.1 / Note 0119) lifted by the case-B → case-A substitution
    (Lemma 5.2 / Note 0122) and tightened by sub-leading
    cross-ratio codim (Lemma 5.3 / Note 0123). Combinatorial witnesses:
    `RealizerData.S_star_size_bound`, `support_substitution`,
    `subleading_codim_strict`.

Both halves are stated below in their final combinatorial form; their
algebraic-geometric closure is left to the downstream
`VbadCodimWitness` interface. -/

/-- **Upper bound, combinatorial form** (paper 3, Theorem 4.1, restated).

For every `(w + 1)`-element support `S` and every injective ratio map
`γ : ι → F` on `S`, the realiser family has exactly `w + 1` distinct
pairs. This is the combinatorial heart of `V_S × V_S ⊆ V_bad`: as
`(s_1, s_2)` ranges over `V_S × V_S`, each generic point produces
`w + 1 > T` distinct realisers. -/
theorem v_bad_upper_bound_witness_count
    {S : Finset ι} {w : ℕ} (hS : S.card = w + 1)
    (γ : ι → F) (hγ : Set.InjOn γ S) :
    (S.image fun v => (γ v, S \ {v})).card = w + 1 :=
  v_S_realizer_family_card hS γ hγ

/-- **Lower bound, combinatorial form** (paper 3, Lemmas 5.1+5.2 unified).

Given a `RealizerData V f γs w` with `γs.card = T + 1` and `T ≥ 1`:
either `V.card ≤ w` (degenerate, no contribution to codim) or
`V.card ≤ w + w / T` (Note 0119 + Note 0122 universal bound). For
`δ' := V.card - w ≥ 2` and `T ≥ 2`, the additional
`subleading_codim_strict` guarantees the stratum is sub-leading. -/
theorem v_bad_lower_bound_witness
    {V : Finset ι} {f : ι → F} {γs : Finset F} {w T : ℕ}
    (R : RealizerData V f γs w)
    (hT : 1 ≤ T) (hγs_card : γs.card = T + 1) :
    V.card ≤ w ∨ V.card ≤ w + w / T := by
  by_cases h : V.card ≤ w
  · exact Or.inl h
  · refine Or.inr (R.S_star_size_bound hT hγs_card ?_)
    omega

/-! ## Algebraic-geometric interface

The final composition step — translating the combinatorial witness
counts above into the codim equality `codim V_bad = 2(c − 1)` — requires
the following algebraic facts about the affine variety `V_bad ⊆ F^{2D}`:

  * (S1) `V_S × V_S ⊆ V_bad` for every `S` of size `w + 1` (consequence of
    `v_S_realizer_family_card` once realiser-validity is established).
  * (S2) `dim (V_S × V_S) = 2(w + 1)` (linear independence of
    `{ev_v : v ∈ S}` for `|S| ≤ D`).
  * (S3) `V_bad ⊆ ⋃_{|S| ≤ w + ⌊w/T⌋} V_S × V_S` (combinatorial output of
    `RealizerData.S_star_size_bound`).
  * (S4) For `δ' ≥ 2`, `dim V_bad^{(δ')} ≤ 2(w + 1) − (δ' − 1)(T − 1)`
    (combinatorial output of `subleading_codim_strict`).

Items (S2)–(S4) are the algebraic-geometric content not formalised in
this file. We package them as a single `VbadCodimWitness` interface so a
downstream formalisation of affine varieties can supply them and obtain
the headline `codim V_bad = 2(c − 1)` as a Lean theorem. -/

/-- Interface witness for the algebraic-geometric content needed to
translate the combinatorial witness counts of `Berlekamp/` into the
codim equality `codim V_bad = 2(c − 1)`.

Concrete domains satisfying (S2)–(S4) above can supply this structure;
all fields are stated abstractly (in terms of opaque `ℕ`-valued `dim`,
`codim` functions on a placeholder type) so that any downstream
affine-variety formalisation can plug in.

The fields encode:

  * `dim_top_eq_leading`: the top variety realises *exactly* the leading
    dimension `2(w + 1)` (saturated by the V_S × V_S leading stratum, no
    higher-dimensional component exists by Note 0123).
  * `codim_dim_dual`: codim/dim duality in the ambient `F^{2D}` with
    `D = w + c`. -/
structure VbadCodimWitness
    (Vbad : Type*) (dim codim : Vbad → ℕ) (top : Vbad)
    (c w : ℕ) : Prop where
  /-- Top stratum has dim `2(w + 1)` (leading saturates, sub-leading
      strictly lower by Note 0123). -/
  dim_top_eq_leading : dim top = 2 * (w + 1)
  /-- Codim/dim duality in the ambient `F^{2D}` (`D = w + c`). -/
  codim_dim_dual : dim top + codim top = 2 * (w + c)

/-- **Paper 3, Theorem 3.1** (combinatorial composition under the
algebraic-geometric interface).

If `VbadCodimWitness Vbad dim codim top c w` holds with `c ≥ 1`, then
the top variety has codim *exactly* `2(c − 1)`. -/
theorem v_bad_codim_eq
    {Vbad : Type*} {dim codim : Vbad → ℕ} {top : Vbad} {c w : ℕ}
    (hc : 1 ≤ c)
    (W : VbadCodimWitness Vbad dim codim top c w) :
    codim top = 2 * (c - 1) := by
  have hdim := W.dim_top_eq_leading
  have hcd := W.codim_dim_dual
  -- dim top = 2(w+1), dim top + codim top = 2(w+c)  ⟹  codim top = 2(c-1).
  omega

/-- Cancellation form of `v_bad_codim_eq` (no `c ≥ 1` hypothesis needed):
`codim top + 2(w + 1) = 2(w + c)`. Useful when chaining through the
`codim_dim_dual` equation without committing to the truncated `2(c - 1)`
shape. -/
theorem v_bad_codim_dim_sum
    {Vbad : Type*} {dim codim : Vbad → ℕ} {top : Vbad} {c w : ℕ}
    (W : VbadCodimWitness Vbad dim codim top c w) :
    codim top + 2 * (w + 1) = 2 * (w + c) := by
  have hdim := W.dim_top_eq_leading
  have hcd := W.codim_dim_dual
  omega

end FRISoundness.Berlekamp
