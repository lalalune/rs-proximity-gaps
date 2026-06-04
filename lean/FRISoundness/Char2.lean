/-
Copyright (c) 2026 Raullen Chai, Xinxin Fan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

**Generalized FRI Coupling for arbitrary characteristic** (including char 2).

In characteristic ≠ 2 (multiplicative FRI), the even/odd decomposition uses ±√y:
  fEven(y) = (f(x) + f(-x)) / 2,   fOdd(y) = (f(x) - f(-x)) / (2x).

In characteristic 2 (additive FRI), division by 2 is impossible. Instead, the
fold map s(x) = x² + βx gives fibers {x, x+β}, and the decomposition is:
  f(x) = p(s(x)) + x · q(s(x))
where p = fEven, q = fOdd are recovered via Lagrange interpolation on the fiber.

Both cases are unified by a **generalized FRI pairing** where:
  genFOdd(y) = (f(fst y) - f(snd y)) / (eval(fst y) - eval(snd y))   [Lagrange slope]
  genFEven(y) = f(fst y) - eval(fst y) · genFOdd(y)                    [intercept]

Recovery:
  f(fst y) = genFEven(y) + eval(fst y) · genFOdd(y)     [by definition]
  f(snd y) = genFEven(y) + eval(snd y) · genFOdd(y)     [field_simp + ring]

No NeZero(2 : F) hypothesis anywhere — works in ALL characteristics.
-/
import FRISoundness.Defs

open Finset Fintype

namespace FRISoundness

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Generalized FRI pairing

The key abstraction: each pair in L is equipped with distinct evaluation points.
Recovery uses Lagrange interpolation on the 2-element fiber, avoiding division by 2. -/

/-- Generalized FRI domain pairing that works in any characteristic.
    Each pair (fst y, snd y) has distinct evaluation points eval(fst y) ≠ eval(snd y).
    This subsumes multiplicative FRI (char ≠ 2) and additive FRI (char 2). -/
structure GenFRIPairing (L L' : Type*) (F : Type*) [Field F] where
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
  /-- Evaluation map embedding L into F -/
  eval : L → F
  /-- Evaluation points are distinct on each pair -/
  eval_ne : ∀ y, eval (fst y) ≠ eval (snd y)

variable {L L' : Type*}

/-- Generalized odd part (Lagrange slope on the 2-element fiber):
    (f(fst y) - f(snd y)) / (eval(fst y) - eval(snd y))

    - Multiplicative FRI: eval(x) = x, fiber = {√y, -√y}, gives standard fOdd
    - Additive FRI (char 2): eval(x) = x, fiber = {x, x+β}, gives q(s(x)) -/
noncomputable def genFOdd [Field F]
    (P : GenFRIPairing L L' F) (f : L → F) : L' → F :=
  fun y => (f (P.fst y) - f (P.snd y)) / (P.eval (P.fst y) - P.eval (P.snd y))

/-- Generalized even part (Lagrange intercept):
    f(fst y) - eval(fst y) · genFOdd(y)

    - Multiplicative FRI: gives fEven(y) = p(y) where f(x) = p(x²) + x·q(x²)
    - Additive FRI: gives p(s(x)) where f(x) = p(s(x)) + x·q(s(x)) -/
noncomputable def genFEven [Field F]
    (P : GenFRIPairing L L' F) (f : L → F) : L' → F :=
  fun y => f (P.fst y) - P.eval (P.fst y) * genFOdd P f y

/-! ## Recovery identities -/

/-- Recovery at fst: f(fst y) = genFEven(y) + eval(fst y) · genFOdd(y).
    This is immediate from the definition of genFEven. -/
theorem gen_recover_fst [Field F]
    (P : GenFRIPairing L L' F) (f : L → F) (y : L') :
    genFEven P f y + P.eval (P.fst y) * genFOdd P f y = f (P.fst y) := by
  simp only [genFEven]
  ring

/-- Recovery at snd: f(snd y) = genFEven(y) + eval(snd y) · genFOdd(y).
    This requires field arithmetic: the eval difference cancels. -/
theorem gen_recover_snd [Field F]
    (P : GenFRIPairing L L' F) (f : L → F) (y : L') :
    genFEven P f y + P.eval (P.snd y) * genFOdd P f y = f (P.snd y) := by
  simp only [genFEven, genFOdd]
  have hne : P.eval (P.fst y) - P.eval (P.snd y) ≠ 0 := sub_ne_zero.mpr (P.eval_ne y)
  field_simp
  ring

/-! ## Generalized coupling pointwise

The coupling lemma: if genFEven and genFOdd agree, both fiber points agree.
Identical proof structure to the char ≠ 2 version, but no NeZero(2:F) needed. -/

/-- **Generalized Coupling** (any characteristic): if even and odd parts agree,
    then both original values agree.

    Works in char 2 (additive FRI) and char ≠ 2 (multiplicative FRI). -/
theorem gen_coupling_pointwise
    (P : GenFRIPairing L L' F) (f g : L → F) (y : L')
    (heven : genFEven P f y = genFEven P g y)
    (hodd : genFOdd P f y = genFOdd P g y) :
    f (P.fst y) = g (P.fst y) ∧ f (P.snd y) = g (P.snd y) := by
  constructor
  · calc f (P.fst y)
        = genFEven P f y + P.eval (P.fst y) * genFOdd P f y := (gen_recover_fst P f y).symm
      _ = genFEven P g y + P.eval (P.fst y) * genFOdd P g y := by rw [heven, hodd]
      _ = g (P.fst y) := gen_recover_fst P g y
  · calc f (P.snd y)
        = genFEven P f y + P.eval (P.snd y) * genFOdd P f y := (gen_recover_snd P f y).symm
      _ = genFEven P g y + P.eval (P.snd y) * genFOdd P g y := by rw [heven, hodd]
      _ = g (P.snd y) := gen_recover_snd P g y

/-! ## Generalized coupling counting

Same quantitative step: 2·|jointAgree| ≤ |agree|, using GenFRIPairing. -/

/-- **Generalized Coupling Counting** (any characteristic):
    2 · |{y : genFEven agrees ∧ genFOdd agrees}| ≤ |agreeSet(f, g)|

    The proof is identical to coupling_counting in RSCode.lean,
    using GenFRIPairing's injectivity and disjointness. -/
theorem gen_coupling_counting
    [Fintype L] [Fintype L'] [DecidableEq L]
    (P : GenFRIPairing L L' F) (f g : L → F) :
    2 * (Finset.univ.filter fun y =>
      genFEven P f y = genFEven P g y ∧ genFOdd P f y = genFOdd P g y).card ≤
    (agreeSet f g).card := by
  set A := Finset.univ.filter fun y =>
    genFEven P f y = genFEven P g y ∧ genFOdd P f y = genFOdd P g y
  -- Each y ∈ A produces two agree positions: fst y and snd y
  have hfst_mem : ∀ y ∈ A, P.fst y ∈ agreeSet f g := by
    intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    obtain ⟨hev, hod⟩ := hy'
    obtain ⟨h1, _⟩ := gen_coupling_pointwise P f g y hev hod
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
  have hsnd_mem : ∀ y ∈ A, P.snd y ∈ agreeSet f g := by
    intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    obtain ⟨hev, hod⟩ := hy'
    obtain ⟨_, h2⟩ := gen_coupling_pointwise P f g y hev hod
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
  have hcardF : imgF.card = A.card :=
    Finset.card_image_of_injective _ P.fst_injective
  have hcardS : imgS.card = A.card :=
    Finset.card_image_of_injective _ P.snd_injective
  have hunion : (imgF ∪ imgS).card = imgF.card + imgS.card :=
    Finset.card_union_of_disjoint hdisj
  have hsub : imgF ∪ imgS ⊆ agreeSet f g :=
    Finset.union_subset himgF himgS
  have hle : (imgF ∪ imgS).card ≤ (agreeSet f g).card :=
    Finset.card_le_card hsub
  rw [hunion, hcardF, hcardS] at hle
  linarith

end FRISoundness
