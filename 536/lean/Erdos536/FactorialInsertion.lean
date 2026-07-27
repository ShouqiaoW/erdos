import Erdos536.FiniteProbability

/-!
# Exact factorial deletion and insertion

The identities here are finite reindexings.  They are the formal version of
deleting canonical pivot points and then summing over all legal insertions.
-/

open scoped BigOperators
open Finset

namespace Erdos536

/-- Exact one-point deletion/insertion, before rewriting the inserted mass
using Bernoulli odds. -/
theorem factorialInsertion_one {α : Type*} [DecidableEq α]
    (P : Finset α) (r : α → ℝ) (F : Finset α → α → ℝ) :
    ∑ S ∈ P.powerset, ∑ p ∈ S, subsetWeight P r S * F S p =
      ∑ A ∈ P.powerset, ∑ p ∈ P \ A,
        subsetWeight P r (insert p A) * F (insert p A) p := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij'
      (fun z _ => ⟨z.1.erase z.2, z.2⟩)
      (fun z _ => ⟨insert z.2 z.1, z.2⟩) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rw [mem_sigma] at hz ⊢
    refine ⟨mem_powerset.mpr ((erase_subset _ _).trans
      (mem_powerset.mp hz.1)), ?_⟩
    exact mem_sdiff.mpr
      ⟨(mem_powerset.mp hz.1) hz.2, by simp⟩
  · intro z hz
    rw [mem_sigma] at hz ⊢
    refine ⟨mem_powerset.mpr ?_, mem_insert_self _ _⟩
    exact insert_subset (mem_sdiff.mp hz.2).1 (mem_powerset.mp hz.1)
  · intro z hz
    rw [mem_sigma] at hz
    change
      (⟨insert z.2 (z.1.erase z.2), z.2⟩ :
        Sigma fun _ : Finset α => α) = z
    apply Sigma.ext
    · exact insert_erase hz.2
    · rfl
  · intro z hz
    rw [mem_sigma] at hz
    change
      (⟨(insert z.2 z.1).erase z.2, z.2⟩ :
        Sigma fun _ : Finset α => α) = z
    apply Sigma.ext
    · exact erase_insert (mem_sdiff.mp hz.2).2
    · rfl
  · intro z hz
    rw [mem_sigma] at hz
    simp only [insert_erase hz.2]

/-- One-point deletion/insertion with the inserted Bernoulli odds exposed. -/
theorem factorialInsertion_one_odds {α : Type*} [DecidableEq α]
    (P : Finset α) (r : α → ℝ) (F : Finset α → α → ℝ)
    (hr : ∀ p ∈ P, r p ≠ 1) :
    ∑ S ∈ P.powerset, ∑ p ∈ S, subsetWeight P r S * F S p =
      ∑ A ∈ P.powerset, ∑ p ∈ P \ A,
        subsetWeight P r A * (r p / (1 - r p)) * F (insert p A) p := by
  rw [factorialInsertion_one P r F]
  apply sum_congr rfl
  intro A hA
  apply sum_congr rfl
  intro p hp
  rw [subsetWeight_insert_odds (mem_sdiff.mp hp).1
    (mem_sdiff.mp hp).2 (hr p (mem_sdiff.mp hp).1)]

/-- Ordered pairs of distinct elements of a finite set. -/
def orderedDistinctPairs {α : Type*} [DecidableEq α]
    (S : Finset α) : Finset (α × α) :=
  (S ×ˢ S).filter fun pq => pq.1 ≠ pq.2

@[simp]
theorem mem_orderedDistinctPairs {α : Type*} [DecidableEq α]
    {S : Finset α} {p q : α} :
    (p, q) ∈ orderedDistinctPairs S ↔ p ∈ S ∧ q ∈ S ∧ p ≠ q := by
  simp [orderedDistinctPairs, and_assoc]

/-- Exact ordered two-point deletion/insertion, before rewriting masses by
odds. -/
theorem factorialInsertion_two {α : Type*} [DecidableEq α]
    (P : Finset α) (r : α → ℝ)
    (F : Finset α → α → α → ℝ) :
    ∑ S ∈ P.powerset, ∑ pq ∈ orderedDistinctPairs S,
        subsetWeight P r S * F S pq.1 pq.2 =
      ∑ A ∈ P.powerset, ∑ pq ∈ orderedDistinctPairs (P \ A),
        subsetWeight P r (insert pq.1 (insert pq.2 A)) *
          F (insert pq.1 (insert pq.2 A)) pq.1 pq.2 := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij'
      (fun z _ =>
        ⟨(z.1.erase z.2.1).erase z.2.2, z.2⟩)
      (fun z _ =>
        ⟨insert z.2.1 (insert z.2.2 z.1), z.2⟩) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rw [mem_sigma] at hz ⊢
    have hpS := (mem_orderedDistinctPairs.mp hz.2).1
    have hqS := (mem_orderedDistinctPairs.mp hz.2).2.1
    have hpq := (mem_orderedDistinctPairs.mp hz.2).2.2
    have hSP := mem_powerset.mp hz.1
    refine ⟨mem_powerset.mpr ((erase_subset _ _).trans
      ((erase_subset _ _).trans hSP)), ?_⟩
    apply mem_orderedDistinctPairs.mpr
    refine ⟨mem_sdiff.mpr ⟨hSP hpS, ?_⟩,
      mem_sdiff.mpr ⟨hSP hqS, ?_⟩, hpq⟩
    · simp
    · simp
  · intro z hz
    rw [mem_sigma] at hz ⊢
    have hp := (mem_orderedDistinctPairs.mp hz.2).1
    have hq := (mem_orderedDistinctPairs.mp hz.2).2.1
    have hpq := (mem_orderedDistinctPairs.mp hz.2).2.2
    have hAP := mem_powerset.mp hz.1
    refine ⟨mem_powerset.mpr
      (insert_subset (mem_sdiff.mp hp).1
        (insert_subset (mem_sdiff.mp hq).1 hAP)), ?_⟩
    exact mem_orderedDistinctPairs.mpr
      ⟨mem_insert_self _ _, mem_insert_of_mem (mem_insert_self _ _), hpq⟩
  · intro z hz
    rw [mem_sigma] at hz
    have hpS := (mem_orderedDistinctPairs.mp hz.2).1
    have hqS := (mem_orderedDistinctPairs.mp hz.2).2.1
    have hpq := (mem_orderedDistinctPairs.mp hz.2).2.2
    have hqErase : z.2.2 ∈ z.1.erase z.2.1 :=
      mem_erase.mpr ⟨hpq.symm, hqS⟩
    change
      (⟨insert z.2.1
          (insert z.2.2 ((z.1.erase z.2.1).erase z.2.2)), z.2⟩ :
        Sigma fun _ : Finset α => α × α) = z
    apply Sigma.ext
    · rw [insert_erase hqErase, insert_erase hpS]
    · rfl
  · intro z hz
    rw [mem_sigma] at hz
    have hp := (mem_orderedDistinctPairs.mp hz.2).1
    have hq := (mem_orderedDistinctPairs.mp hz.2).2.1
    have hpq := (mem_orderedDistinctPairs.mp hz.2).2.2
    have hpA := (mem_sdiff.mp hp).2
    have hqA := (mem_sdiff.mp hq).2
    have hpInsert : z.2.1 ∉ insert z.2.2 z.1 := by
      simp [hpA, hpq]
    change
      (⟨(insert z.2.1 (insert z.2.2 z.1)).erase z.2.1 |>.erase z.2.2,
          z.2⟩ : Sigma fun _ : Finset α => α × α) = z
    apply Sigma.ext
    · rw [erase_insert hpInsert, erase_insert hqA]
    · rfl
  · intro z hz
    rw [mem_sigma] at hz
    have hpS := (mem_orderedDistinctPairs.mp hz.2).1
    have hqS := (mem_orderedDistinctPairs.mp hz.2).2.1
    have hpq := (mem_orderedDistinctPairs.mp hz.2).2.2
    have hqErase : z.2.2 ∈ z.1.erase z.2.1 :=
      mem_erase.mpr ⟨hpq.symm, hqS⟩
    simp only [insert_erase hqErase, insert_erase hpS]

/-- Ordered two-point insertion with both Bernoulli odds exposed. -/
theorem factorialInsertion_two_odds {α : Type*} [DecidableEq α]
    (P : Finset α) (r : α → ℝ)
    (F : Finset α → α → α → ℝ)
    (hr : ∀ p ∈ P, r p ≠ 1) :
    ∑ S ∈ P.powerset, ∑ pq ∈ orderedDistinctPairs S,
        subsetWeight P r S * F S pq.1 pq.2 =
      ∑ A ∈ P.powerset, ∑ pq ∈ orderedDistinctPairs (P \ A),
        subsetWeight P r A *
          (r pq.1 / (1 - r pq.1)) *
          (r pq.2 / (1 - r pq.2)) *
          F (insert pq.1 (insert pq.2 A)) pq.1 pq.2 := by
  rw [factorialInsertion_two P r F]
  apply sum_congr rfl
  intro A hA
  apply sum_congr rfl
  intro pq hpq
  have hp := (mem_orderedDistinctPairs.mp hpq).1
  have hq := (mem_orderedDistinctPairs.mp hpq).2.1
  have hpNeq := (mem_orderedDistinctPairs.mp hpq).2.2
  have hpA := (mem_sdiff.mp hp).2
  have hqA := (mem_sdiff.mp hq).2
  have hpInsert : pq.1 ∉ insert pq.2 A := by simp [hpA, hpNeq]
  rw [subsetWeight_insert_odds (mem_sdiff.mp hp).1 hpInsert
      (hr pq.1 (mem_sdiff.mp hp).1),
    subsetWeight_insert_odds (mem_sdiff.mp hq).1 hqA
      (hr pq.2 (mem_sdiff.mp hq).1)]
  ring

end Erdos536
