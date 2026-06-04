/-
Copyright (c) 2026 Raullen Chai, Xinxin Fan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

**Theorem batch-ca** (Appendix A.1).
Batch Correlated Agreement: conditioning + union bound.

For STIR/WHIR batched proximity testing: given m received words f₁, ..., fₘ,
the random linear combination ∑ αᵢfᵢ is δ-close to C for at most m bad
coefficient tuples out of |F|^m (probability ≤ m/|F|).

The proof decomposes into:
1. **Conditioning**: if fᵢ is 2d-far from C, then for any "rest" function,
   the pair (rest, fᵢ) satisfies the ca_halved premise.
2. **Per-coordinate CA**: apply ca_halved to get at most 1 bad αᵢ per coordinate.
3. **Union bound**: m coordinates × 1 bad each ≤ m total bad tuples.
-/
import FRISoundness.CA
import Mathlib.Order.Defs.PartialOrder

open Finset Fintype

namespace FRISoundness

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Conditioning lemma

The joint agreement set of (rest, fᵢ) with any (g₁, g₂) ∈ C × C is contained
in the individual agreement set of fᵢ with g₂. Therefore, if fᵢ is far from C,
the joint distance is also large — regardless of what "rest" is. -/

/-- The joint agreement set is a subset of the second component's agreement set. -/
theorem jointAgreeSet_subset_agreeSet_snd (f₁ f₂ g₁ g₂ : L → F) :
    jointAgreeSet f₁ f₂ g₁ g₂ ⊆ agreeSet f₂ g₂ := by
  intro x hx
  simp only [jointAgreeSet, agreeSet, Finset.mem_filter, mem_univ, true_and] at hx ⊢
  exact hx.2

/-- The joint agreement set is a subset of the first component's agreement set. -/
theorem jointAgreeSet_subset_agreeSet_fst (f₁ f₂ g₁ g₂ : L → F) :
    jointAgreeSet f₁ f₂ g₁ g₂ ⊆ agreeSet f₁ g₁ := by
  intro x hx
  simp only [jointAgreeSet, agreeSet, Finset.mem_filter, mem_univ, true_and] at hx ⊢
  exact hx.1

/-- **Conditioning step**: if fᵢ is 2d-far from every codeword in C,
    then for any rest function, the pair (rest, fᵢ) satisfies the ca_halved premise.

    This is the key step that connects individual distance to joint distance. -/
theorem far_implies_joint_far
    (C : Submodule F (L → F))
    (rest fᵢ : L → F) (d : ℕ)
    (hfar : ∀ g ∈ C, (agreeSet fᵢ g).card + 2 * d < card L) :
    ∀ g₁ ∈ C, ∀ g₂ ∈ C,
      (jointAgreeSet rest fᵢ g₁ g₂).card + 2 * d < card L := by
  intro g₁ _ g₂ hg₂
  have hsub := jointAgreeSet_subset_agreeSet_snd rest fᵢ g₁ g₂
  have hcard := Finset.card_le_card hsub
  have hg := hfar g₂ hg₂
  omega

/-! ## Per-coordinate Batch CA

By combining the conditioning lemma with ca_halved, we get:
if fᵢ is far from C, then for any fixed "rest" (= ∑_{j≠i} αⱼfⱼ),
at most one value of αᵢ makes rest + αᵢ·fᵢ close to C. -/

/-- **Per-coordinate Batch CA**: at most one αᵢ is bad.
    Combines conditioning (far_implies_joint_far) with ca_halved. -/
theorem batch_ca_per_coord
    (C : Submodule F (L → F))
    (rest fᵢ : L → F) (d : ℕ)
    (hfar : ∀ g ∈ C, (agreeSet fᵢ g).card + 2 * d < card L)
    {α₁ α₂ : F} (hne : α₁ ≠ α₂)
    {c₁ c₂ : L → F} (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C)
    (hA₁ : card L ≤ (agreeSet (linComb rest fᵢ α₁) c₁).card + d)
    (hA₂ : card L ≤ (agreeSet (linComb rest fᵢ α₂) c₂).card + d) :
    False :=
  ca_halved C rest fᵢ d (far_implies_joint_far C rest fᵢ d hfar) hne hc₁ hc₂ hA₁ hA₂

/-- **Contrapositive form**: any two bad coefficients must be equal.
    Useful for the union bound counting argument. -/
theorem batch_ca_at_most_one
    (C : Submodule F (L → F))
    (rest fᵢ : L → F) (d : ℕ)
    (hfar : ∀ g ∈ C, (agreeSet fᵢ g).card + 2 * d < card L)
    {α₁ α₂ : F}
    (hα₁ : ∃ c ∈ C, card L ≤ (agreeSet (linComb rest fᵢ α₁) c).card + d)
    (hα₂ : ∃ c ∈ C, card L ≤ (agreeSet (linComb rest fᵢ α₂) c).card + d) :
    α₁ = α₂ := by
  by_contra hne
  obtain ⟨c₁, hc₁, hA₁⟩ := hα₁
  obtain ⟨c₂, hc₂, hA₂⟩ := hα₂
  exact batch_ca_per_coord C rest fᵢ d hfar hne hc₁ hc₂ hA₁ hA₂

/-! ## Union bound

With m functions, each contributing at most 1 bad coefficient,
the total number of bad coefficient tuples is at most m.
In probability terms: Pr[batch fails] ≤ m/|F|. -/

/-- **Batch CA union bound** (generic): a union of `m` singletons has cardinality
    ≤ `m`. The mathematical content is that each coordinate contributes at most
    1 bad coefficient value (by `batch_ca_at_most_one`), so the total number of
    bad coefficient tuples is at most `m`, giving probability `m/|F|`. -/
theorem batch_ca_bad_count {ι : Type*} [DecidableEq ι] [Fintype ι]
    {F : Type*} [DecidableEq F]
    (bad : ι → Finset F) (hbad : ∀ i, (bad i).card ≤ 1) :
    (Finset.univ.biUnion bad).card ≤ Fintype.card ι := by
  calc (Finset.univ.biUnion bad).card
      ≤ Finset.univ.sum (fun i => (bad i).card) := Finset.card_biUnion_le
    _ ≤ Finset.univ.sum (fun _ => 1) := Finset.sum_le_sum fun i _ => hbad i
    _ = Fintype.card ι := by simp [Finset.card_univ]

/-! ## Per-coordinate bad-set cardinality (≤ 1)

Specializes `batch_ca_at_most_one` to the cardinality of the entire bad set
of α-values: if `fᵢ` is `2d`-far from `C`, then the set
`{α ∈ F : ∃ c ∈ C, agreement ≥ n − d}` has cardinality `≤ 1`. -/

/-- **Per-coordinate bad set is at most a singleton.** Combines
    `batch_ca_at_most_one` with `Finset.card_le_one` to give a direct
    cardinality bound. -/
theorem batch_ca_per_coord_bad_card
    [Fintype F]
    (C : Submodule F (L → F))
    (rest fᵢ : L → F) (d : ℕ)
    (hfar : ∀ g ∈ C, (agreeSet fᵢ g).card + 2 * d < card L) :
    ((Finset.univ : Finset F).filter
      (fun α => ∃ c ∈ C, card L ≤ (agreeSet (linComb rest fᵢ α) c).card + d)).card
    ≤ 1 := by
  rw [Finset.card_le_one]
  intro α₁ hα₁ α₂ hα₂
  rw [Finset.mem_filter] at hα₁ hα₂
  exact batch_ca_at_most_one C rest fᵢ d hfar hα₁.2 hα₂.2

/-! ## Aggregate batch-CA bound

The full quantitative statement: across `m` "varying coordinates" (one per
`i ∈ ι`), the union of the per-coordinate bad sets has cardinality at most
`m`. In probability terms (over uniform `(α₁, …, αₘ) ∈ F^m`), the soundness
error is `m/|F|` — recovering the standard batch-CA bound used by
STIR/WHIR proofs. -/

/-- **Aggregate batch-CA bound** (paper Appendix A, Theorem batch-ca).

For each `i ∈ ι`, suppose `fᵢ` is `2d`-far from the codeword space `C` and
that for each `i` we are given a fixed "rest" function `restᵢ : L → F`. Then
the union of the per-coordinate bad sets

  `Bᵢ := {α ∈ F : ∃ c ∈ C, |agreeSet (restᵢ + α · fᵢ) c| ≥ n − d}`

has cardinality at most `|ι|`. Each `Bᵢ` is a singleton (or empty) by
`batch_ca_per_coord_bad_card`; `batch_ca_bad_count` then applies the
elementary union-bound on `|ι|` singletons. -/
theorem batch_ca_aggregate
    [Fintype F]
    (C : Submodule F (L → F))
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (rest : ι → L → F) (f : ι → L → F) (d : ℕ)
    (hfar : ∀ i, ∀ g ∈ C, (agreeSet (f i) g).card + 2 * d < card L) :
    (Finset.univ.biUnion (fun i =>
      (Finset.univ : Finset F).filter
        (fun α => ∃ c ∈ C,
          card L ≤ (agreeSet (linComb (rest i) (f i) α) c).card + d))).card
    ≤ Fintype.card ι :=
  batch_ca_bad_count
    (fun i => (Finset.univ : Finset F).filter
      (fun α => ∃ c ∈ C,
        card L ≤ (agreeSet (linComb (rest i) (f i) α) c).card + d))
    (fun i => batch_ca_per_coord_bad_card C (rest i) (f i) d (hfar i))

end FRISoundness
