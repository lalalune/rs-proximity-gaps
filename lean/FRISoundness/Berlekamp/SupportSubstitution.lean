/-
Copyright (c) 2026 Raullen Chai, Xinxin Fan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Berlekamp / V_bad codim — case-B → case-A support substitution.

This is paper 3, Lemma 5.2 (Note 0122). The algebraic statement reads:

  *Every realiser `(γ, E)` of an `(s_1, s_2) ∈ V_bad` admits a case-A
  representative `(γ, E_A)` with `E_A ⊂ S*` and `|E_A| = w`, at the same
  `γ`.*

The combinatorial heart of the substitution is the padding lemma:

> Given finite sets `T ⊆ S` with `|T| ≤ w ≤ |S|`, there exists
> `E ⊆ S` with `T ⊆ E` and `|E| = w`.

The algebraic content of Note 0122 — that `x_γ ∈ V_{T_γ} ⊆ V_{E_A}`
whenever `T_γ ⊆ E_A` and `|E_A| ≤ D` — is encoded once and for all in
the abstract `RealizerData` interface (`Defs.lean`); this file
provides the *combinatorial* half of the reduction.

The substitution is purely set-theoretic — no field structure is used.
We therefore parameterise by a generic decidable-equality type `α`. -/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic

open Finset

namespace FRISoundness.Berlekamp

/--
**Paper 3, Lemma 5.2, combinatorial core** (Note 0122).

Given `T ⊆ S` with `|T| ≤ w ≤ |S|`, there exists `E ⊆ S` with `T ⊆ E`
and `|E| = w`.

In the Berlekamp application, `S = S*` (the joint Vandermonde support),
`T = T_γ ⊆ S*` (the intrinsic Vandermonde support of the realiser
`x_γ`), and `w` is the realiser support size; the resulting `E` is the
case-A representative `E_A`. The "padding" is the `S* ∖ T_γ` extras of
size `w − |T_γ|`. -/
theorem support_substitution
    {α : Type*} [DecidableEq α]
    {S T : Finset α} (hTS : T ⊆ S)
    {w : ℕ} (hT : T.card ≤ w) (hSw : w ≤ S.card) :
    ∃ E : Finset α, T ⊆ E ∧ E ⊆ S ∧ E.card = w := by
  have hsdiff : (S \ T).card = S.card - T.card :=
    Finset.card_sdiff_of_subset hTS
  have hpad : w - T.card ≤ (S \ T).card := by
    rw [hsdiff]; omega
  obtain ⟨P, hP_sub, hP_card⟩ := Finset.exists_subset_card_eq hpad
  refine ⟨T ∪ P, Finset.subset_union_left, ?_, ?_⟩
  · -- E = T ∪ P ⊆ S: T ⊆ S by hypothesis, P ⊆ S \ T ⊆ S.
    intro x hx
    rcases Finset.mem_union.mp hx with hxT | hxP
    · exact hTS hxT
    · exact (Finset.mem_sdiff.mp (hP_sub hxP)).1
  · -- |E| = w: T and P are disjoint, |T| + |P| = T.card + (w - T.card) = w.
    have hdisj : Disjoint T P := by
      rw [Finset.disjoint_right]
      intro x hxP hxT
      exact (Finset.mem_sdiff.mp (hP_sub hxP)).2 hxT
    rw [Finset.card_union_of_disjoint hdisj, hP_card]
    omega

end FRISoundness.Berlekamp
