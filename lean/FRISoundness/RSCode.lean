/-
Copyright (c) 2026 Raullen Chai, Xinxin Fan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Reed-Solomon codes, FRI fold, and coupling lemma.
-/
import FRISoundness.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs

open Finset Fintype Polynomial

namespace FRISoundness

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Reed-Solomon code

RS[α, k] = {f : L → F | ∃ p : F[X], p.degree < k ∧ ∀ x, f x = p.eval (α x)}

We use `degree` (valued in `WithBot ℕ`) to handle the zero polynomial cleanly:
degree 0 = ⊥ < ↑k for all k, so the zero function is always in the code. -/

/-- The RS code: evaluations of degree < k polynomials on evaluation points α. -/
def RSCode {L : Type*} [Fintype L] (α : L → F) (k : ℕ) : Submodule F (L → F) where
  carrier := {f | ∃ p : F[X], p.degree < (k : WithBot ℕ) ∧ ∀ x : L, f x = p.eval (α x)}
  add_mem' := by
    intro f g ⟨pf, hpf, hf⟩ ⟨pg, hpg, hg⟩
    refine ⟨pf + pg, ?_, fun x => ?_⟩
    · exact (degree_add_le pf pg).trans_lt (max_lt hpf hpg)
    · simp [hf x, hg x, eval_add]
  zero_mem' := ⟨0, by simp [degree_zero, WithBot.bot_lt_coe], fun x => by simp [eval_zero]⟩
  smul_mem' := by
    intro c f ⟨p, hp, hf⟩
    refine ⟨Polynomial.C c * p, ?_, fun x => ?_⟩
    · calc (Polynomial.C c * p).degree ≤ (Polynomial.C c).degree + p.degree := degree_mul_le _ _
        _ ≤ 0 + p.degree := by gcongr; exact degree_C_le
        _ = p.degree := by ring
        _ < _ := hp
    · simp [hf x, eval_mul, eval_C, Pi.smul_apply, smul_eq_mul]

/-! ## FRI fold structure

Model: L has a pairing into L' (each pair indexed by y ∈ L').
The even/odd decomposition is defined via the pair structure.

Key property: if f_even(y) = g_even(y) and f_odd(y) = g_odd(y),
then f = g at both elements of the pair. -/

/-- Abstract FRI domain pairing: L is partitioned into pairs indexed by L'. -/
structure FRIPairing (L L' : Type*) (F : Type*) [Field F] where
  /-- First element of each pair -/
  fst : L' → L
  /-- Second element of each pair -/
  snd : L' → L
  /-- Elements in a pair are distinct -/
  fst_ne_snd : ∀ y, fst y ≠ snd y
  /-- fst is injective -/
  fst_injective : Function.Injective fst
  /-- snd is injective -/
  snd_injective : Function.Injective snd
  /-- Images are disjoint: no fst-image element equals a snd-image element -/
  disjoint_images : ∀ y₁ y₂, fst y₁ ≠ snd y₂
  /-- The separation factor (= 2√y in multiplicative FRI) -/
  sep : L' → F
  sep_ne_zero : ∀ y, sep y ≠ 0

/-- Even part: (f(fst y) + f(snd y)) / 2 -/
noncomputable def fEven {L L' : Type*} [Field F]
    (P : FRIPairing L L' F) (f : L → F) : L' → F :=
  fun y => (f (P.fst y) + f (P.snd y)) / 2

/-- Odd part: (f(fst y) - f(snd y)) / sep(y) -/
noncomputable def fOdd {L L' : Type*} [Field F]
    (P : FRIPairing L L' F) (f : L → F) : L' → F :=
  fun y => (f (P.fst y) - f (P.snd y)) / P.sep y

/-- Identity: f(fst y) = f_even(y) + (sep y / 2) · f_odd(y) -/
theorem recover_fst {L L' : Type*} [Field F] [NeZero (2 : F)]
    (P : FRIPairing L L' F) (f : L → F) (y : L') :
    fEven P f y + (P.sep y / 2) * fOdd P f y = f (P.fst y) := by
  simp only [fEven, fOdd]
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hs : P.sep y ≠ 0 := P.sep_ne_zero y
  field_simp
  ring

/-- Identity: f(snd y) = f_even(y) - (sep y / 2) · f_odd(y) -/
theorem recover_snd {L L' : Type*} [Field F] [NeZero (2 : F)]
    (P : FRIPairing L L' F) (f : L → F) (y : L') :
    fEven P f y - (P.sep y / 2) * fOdd P f y = f (P.snd y) := by
  simp only [fEven, fOdd]
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hs : P.sep y ≠ 0 := P.sep_ne_zero y
  field_simp
  ring

/-- **Coupling key step** (FULLY PROVED): if even and odd parts agree,
    then both original values agree. -/
theorem coupling_pointwise {L L' : Type*} [Field F] [NeZero (2 : F)]
    (P : FRIPairing L L' F) (f g : L → F) (y : L')
    (heven : fEven P f y = fEven P g y)
    (hodd : fOdd P f y = fOdd P g y) :
    f (P.fst y) = g (P.fst y) ∧ f (P.snd y) = g (P.snd y) := by
  constructor
  · calc f (P.fst y)
        = fEven P f y + (P.sep y / 2) * fOdd P f y := (recover_fst P f y).symm
      _ = fEven P g y + (P.sep y / 2) * fOdd P g y := by rw [heven, hodd]
      _ = g (P.fst y) := recover_fst P g y
  · calc f (P.snd y)
        = fEven P f y - (P.sep y / 2) * fOdd P f y := (recover_snd P f y).symm
      _ = fEven P g y - (P.sep y / 2) * fOdd P g y := by rw [heven, hodd]
      _ = g (P.snd y) := recover_snd P g y

/-! ## Coupling counting lemma

The key quantitative step: joint agreement on L' gives ≥ 2× agreement on L.
Combined with the far hypothesis, this establishes the ca_halved premise. -/

/-- Each joint-agree position y ∈ L' produces two agree positions on L
    (at fst y and snd y). Since fst and snd have disjoint images,
    |agree on L| ≥ 2 · |jointAgree on L'|.

    Stated contrapositively: jointAgree on L' ≤ agree on L / 2.
    In the ℕ form used by ca_halved: 2 · jointAgree ≤ agree. -/
theorem coupling_counting
    {L L' : Type*} [Fintype L] [Fintype L'] [DecidableEq L] [DecidableEq L']
    [Field F] [DecidableEq F] [NeZero (2 : F)]
    (P : FRIPairing L L' F) (f g : L → F) :
    2 * (Finset.univ.filter fun y =>
      fEven P f y = fEven P g y ∧ fOdd P f y = fOdd P g y).card ≤
    (agreeSet f g).card := by
  -- Let A = {y ∈ L' : fEven f y = fEven g y ∧ fOdd f y = fOdd g y}
  set A := Finset.univ.filter fun y =>
    fEven P f y = fEven P g y ∧ fOdd P f y = fOdd P g y
  -- Map A to L via fst: each y ↦ fst(y) ∈ agreeSet(f,g)
  -- Map A to L via snd: each y ↦ snd(y) ∈ agreeSet(f,g)
  -- These two images are disjoint (by P.disjoint_images)
  -- Each image has |A| elements (by injectivity)
  -- So |agreeSet| ≥ 2|A|
  have hfst_mem : ∀ y ∈ A, P.fst y ∈ agreeSet f g := by
    intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    obtain ⟨hev, hod⟩ := hy'
    obtain ⟨h1, _⟩ := coupling_pointwise P f g y hev hod
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
  have hsnd_mem : ∀ y ∈ A, P.snd y ∈ agreeSet f g := by
    intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    obtain ⟨hev, hod⟩ := hy'
    obtain ⟨_, h2⟩ := coupling_pointwise P f g y hev hod
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩
  set imgF := A.image P.fst
  set imgS := A.image P.snd
  have himgF : imgF ⊆ agreeSet f g := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hfst_mem y hy
  have himgS : imgS ⊆ agreeSet f g := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hsnd_mem y hy
  have hdisj : Disjoint imgF imgS := by
    rw [Finset.disjoint_left]
    intro x hxF hxS
    obtain ⟨y₁, _, rfl⟩ := Finset.mem_image.mp hxF
    obtain ⟨y₂, _, h⟩ := Finset.mem_image.mp hxS
    exact P.disjoint_images y₁ y₂ h.symm
  -- Cardinalities
  have hcardF : imgF.card = A.card :=
    Finset.card_image_of_injective _ P.fst_injective
  have hcardS : imgS.card = A.card :=
    Finset.card_image_of_injective _ P.snd_injective
  -- Union bound
  have hunion : (imgF ∪ imgS).card = imgF.card + imgS.card :=
    Finset.card_union_of_disjoint hdisj
  have hsub : imgF ∪ imgS ⊆ agreeSet f g :=
    Finset.union_subset himgF himgS
  have hle : (imgF ∪ imgS).card ≤ (agreeSet f g).card :=
    Finset.card_le_card hsub
  rw [hunion, hcardF, hcardS] at hle
  linarith

/-! ## RS isomorphism interface

For even k: g ∈ RS_k implies (fEven g, fOdd g) ∈ RS_{k/2}², and conversely.
This requires algebraic facts about the concrete FRI domain pairing, not just
the abstract pairing/counting data above.  The witness below makes those facts
explicit: the concrete domain must supply the polynomial even/odd degree
preservation identities, after which the RS isomorphism statements are ordinary
Lean theorems rather than global axioms. -/

/--
Algebraic RS-isomorphism witness for a concrete FRI pairing.

`FRIPairing` only records the combinatorial pair partition and separation
factor.  To prove that RS codewords decompose into two half-rate RS codewords,
we also need the concrete polynomial identities relating `α (fst y)`,
`α (snd y)`, `sep y`, and `α' y`.  For the usual multiplicative FRI domain,
these are the even/odd coefficient extraction identities under the squaring
map.  This structure isolates exactly that remaining concrete-domain proof.
-/
structure RSIsomorphismWitness
    {L L' : Type*} [Fintype L] [Fintype L']
    {F : Type*} [Field F]
    (P : FRIPairing L L' F) (α : L → F) (α' : L' → F) (k : ℕ) where
  forward :
    ∀ p : F[X], p.degree < (k : WithBot ℕ) →
      ∃ pE pO : F[X],
        pE.degree < ((k / 2 : ℕ) : WithBot ℕ) ∧
        pO.degree < ((k / 2 : ℕ) : WithBot ℕ) ∧
        ∀ y : L',
          (p.eval (α (P.fst y)) + p.eval (α (P.snd y))) / 2 =
            pE.eval (α' y) ∧
          (p.eval (α (P.fst y)) - p.eval (α (P.snd y))) / P.sep y =
            pO.eval (α' y)
  surj :
    ∀ pE pO : F[X],
      pE.degree < ((k / 2 : ℕ) : WithBot ℕ) →
      pO.degree < ((k / 2 : ℕ) : WithBot ℕ) →
      ∃ p : F[X],
        p.degree < (k : WithBot ℕ) ∧
        ∀ y : L',
          (p.eval (α (P.fst y)) + p.eval (α (P.snd y))) / 2 =
            pE.eval (α' y) ∧
          (p.eval (α (P.fst y)) - p.eval (α (P.snd y))) / P.sep y =
            pO.eval (α' y)

theorem rs_iso_forward
    {L L' : Type*} [Fintype L] [Fintype L']
    {F : Type*} [Field F]
    (P : FRIPairing L L' F) (α : L → F) (α' : L' → F) (k : ℕ)
    (H : RSIsomorphismWitness P α α' k)
    (g : L → F) (hg : g ∈ RSCode α k) :
    fEven P g ∈ RSCode α' (k / 2) ∧ fOdd P g ∈ RSCode α' (k / 2) := by
  rcases hg with ⟨p, hpdeg, hp_eval⟩
  rcases H.forward p hpdeg with ⟨pE, pO, hpE, hpO, hvals⟩
  constructor
  · refine ⟨pE, hpE, ?_⟩
    intro y
    rw [fEven, hp_eval (P.fst y), hp_eval (P.snd y)]
    exact (hvals y).1
  · refine ⟨pO, hpO, ?_⟩
    intro y
    rw [fOdd, hp_eval (P.fst y), hp_eval (P.snd y)]
    exact (hvals y).2

theorem rs_iso_surj
    {L L' : Type*} [Fintype L] [Fintype L']
    {F : Type*} [Field F]
    (P : FRIPairing L L' F) (α : L → F) (α' : L' → F) (k : ℕ)
    (H : RSIsomorphismWitness P α α' k)
    (g₁ g₂ : L' → F) (hg₁ : g₁ ∈ RSCode α' (k / 2)) (hg₂ : g₂ ∈ RSCode α' (k / 2)) :
    ∃ g ∈ RSCode α k, fEven P g = g₁ ∧ fOdd P g = g₂ := by
  rcases hg₁ with ⟨pE, hpEdeg, hpE_eval⟩
  rcases hg₂ with ⟨pO, hpOdeg, hpO_eval⟩
  rcases H.surj pE pO hpEdeg hpOdeg with ⟨p, hpdeg, hvals⟩
  let g : L → F := fun x => p.eval (α x)
  refine ⟨g, ?_, ?_, ?_⟩
  · exact ⟨p, hpdeg, fun x => rfl⟩
  · funext y
    rw [fEven]
    calc
      (g (P.fst y) + g (P.snd y)) / 2
          = (p.eval (α (P.fst y)) + p.eval (α (P.snd y))) / 2 := rfl
      _ = pE.eval (α' y) := (hvals y).1
      _ = g₁ y := (hpE_eval y).symm
  · funext y
    rw [fOdd]
    calc
      (g (P.fst y) - g (P.snd y)) / P.sep y
          = (p.eval (α (P.fst y)) - p.eval (α (P.snd y))) / P.sep y := rfl
      _ = pO.eval (α' y) := (hvals y).2
      _ = g₂ y := (hpO_eval y).symm

end FRISoundness
