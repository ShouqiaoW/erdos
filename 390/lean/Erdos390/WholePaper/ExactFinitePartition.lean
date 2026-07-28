import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Real.Archimedean

/-!
# Exact finite partitions with prescribed part sizes

This module is independent of the asymptotic allocation argument. It turns
finite target counts into actual disjoint Finset parts and an explicit
remainder.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- An exact partition of the source into indexed parts and a remainder. -/
structure ExactFinitePartition {α ι : Type*} [DecidableEq α]
    (source : Finset α) (indices : Finset ι) (count : ι → ℕ) where
  parts : ι → Finset α
  remainder : Finset α
  parts_subset : ∀ i ∈ indices, parts i ⊆ source
  parts_card : ∀ i ∈ indices, (parts i).card = count i
  parts_pairwiseDisjoint : (indices : Set ι).PairwiseDisjoint parts
  remainder_subset : remainder ⊆ source
  part_remainder_disjoint : ∀ i ∈ indices, Disjoint (parts i) remainder
  union_remainder : indices.biUnion parts ∪ remainder = source
  union_card : (indices.biUnion parts).card = ∑ i ∈ indices, count i
  remainder_card :
    remainder.card = source.card - ∑ i ∈ indices, count i

/-- Core finite allocation: prescribed counts whose sum fits in the source
can be realized by pairwise disjoint subsets. -/
theorem exists_pairwiseDisjoint_finset_parts
    {α ι : Type*} [DecidableEq α]
    (source : Finset α) (indices : Finset ι) (count : ι → ℕ)
    (hcount : ∑ i ∈ indices, count i ≤ source.card) :
    ∃ parts : ι → Finset α,
      (∀ i ∈ indices, parts i ⊆ source) ∧
      (indices : Set ι).PairwiseDisjoint parts ∧
      (∀ i ∈ indices, (parts i).card = count i) := by
  classical
  induction indices using Finset.induction_on generalizing source with
  | empty =>
      refine ⟨fun _ => ∅, ?_, ?_, ?_⟩
      · simp
      · intro i hi
        simp at hi
      · simp
  | @insert a indices ha ih =>
      have haCount : count a ≤ source.card := by
        calc
          count a ≤ count a + ∑ i ∈ indices, count i := Nat.le_add_right _ _
          _ = ∑ i ∈ insert a indices, count i := by simp [ha]
          _ ≤ source.card := hcount
      obtain ⟨part, hpartSource, hpartCard⟩ :=
        Finset.exists_subset_card_eq haCount
      have hrestCount :
          ∑ i ∈ indices, count i ≤ (source \ part).card := by
        rw [Finset.card_sdiff_of_subset hpartSource, hpartCard]
        rw [Finset.sum_insert ha] at hcount
        omega
      obtain ⟨parts, hpartsSubset, hpartsDisjoint, hpartsCard⟩ :=
        ih (source := source \ part) hrestCount
      let newParts : ι → Finset α := Function.update parts a part
      refine ⟨newParts, ?_, ?_, ?_⟩
      · intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · simpa [newParts] using hpartSource
        · have hiSubset := hpartsSubset i hi
          have hine : i ≠ a := ne_of_mem_of_not_mem hi ha
          simpa [newParts, hine] using
            (hiSubset.trans (Finset.sdiff_subset : source \ part ⊆ source))
      · intro i hi j hj hij
        simp only [Finset.mem_coe, Finset.mem_insert] at hi hj
        by_cases hia : i = a
        · subst i
          have hjne : j ≠ a := hij.symm
          have hjIndices : j ∈ indices := hj.resolve_left hjne
          change Disjoint (newParts a) (newParts j)
          rw [show newParts a = part by simp [newParts],
            show newParts j = parts j by simp [newParts, hjne]]
          rw [Finset.disjoint_left]
          intro x hxpart hxj
          have hxrest := hpartsSubset j hjIndices hxj
          exact (Finset.mem_sdiff.mp hxrest).2 hxpart
        · by_cases hja : j = a
          · subst j
            have hiIndices : i ∈ indices := hi.resolve_left hia
            change Disjoint (newParts i) (newParts a)
            rw [show newParts i = parts i by simp [newParts, hia],
              show newParts a = part by simp [newParts]]
            rw [Finset.disjoint_left]
            intro x hxi hxpart
            have hxrest := hpartsSubset i hiIndices hxi
            exact (Finset.mem_sdiff.mp hxrest).2 hxpart
          · have hiIndices : i ∈ indices := hi.resolve_left hia
            have hjIndices : j ∈ indices := hj.resolve_left hja
            change Disjoint (newParts i) (newParts j)
            rw [show newParts i = parts i by simp [newParts, hia],
              show newParts j = parts j by simp [newParts, hja]]
            exact hpartsDisjoint hiIndices hjIndices hij
      · intro i hi
        simp only [Finset.mem_insert] at hi
        by_cases hia : i = a
        · subst i
          simpa [newParts] using hpartCard
        · have hiIndices : i ∈ indices := hi.resolve_left hia
          simpa [newParts, hia] using
            hpartsCard i hiIndices

/-- Terminal finite partition theorem, including the explicit remainder and
all union/cardinality identities used by later anchor constructions. -/
theorem exists_exactFinitePartition
    {α ι : Type*} [DecidableEq α]
    (source : Finset α) (indices : Finset ι) (count : ι → ℕ)
    (hcount : ∑ i ∈ indices, count i ≤ source.card) :
    Nonempty (ExactFinitePartition source indices count) := by
  classical
  obtain ⟨parts, hpartsSubset, hpartsDisjoint, hpartsCard⟩ :=
    exists_pairwiseDisjoint_finset_parts source indices count hcount
  let union : Finset α := indices.biUnion parts
  let remainder : Finset α := source \ union
  have hunionSubset : union ⊆ source := by
    intro x hx
    simp only [union, Finset.mem_biUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    exact hpartsSubset i hi hxi
  have hunionCard :
      union.card = ∑ i ∈ indices, count i := by
    calc
      union.card = ∑ i ∈ indices, (parts i).card := by
        exact Finset.card_biUnion hpartsDisjoint
      _ = ∑ i ∈ indices, count i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hpartsCard i hi
  refine ⟨{
    parts := parts
    remainder := remainder
    parts_subset := hpartsSubset
    parts_card := hpartsCard
    parts_pairwiseDisjoint := hpartsDisjoint
    remainder_subset := Finset.sdiff_subset
    part_remainder_disjoint := ?_
    union_remainder := ?_
    union_card := hunionCard
    remainder_card := ?_
  }⟩
  · intro i hi
    apply Finset.disjoint_left.mpr
    intro x hxi hxremainder
    have hxiUnion : x ∈ union := by
      simp only [union, Finset.mem_biUnion]
      exact ⟨i, hi, hxi⟩
    exact (Finset.mem_sdiff.mp hxremainder).2 hxiUnion
  · exact Finset.union_sdiff_of_subset hunionSubset
  · change (source \ union).card =
      source.card - ∑ i ∈ indices, count i
    rw [Finset.card_sdiff_of_subset hunionSubset, hunionCard]

/-- Counts obtained by assigning all non-distinguished targets first and
giving the distinguished coordinate the remaining cardinality. -/
def distinguishedRemainderCount {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (distinguished : ι) (rawCount : ι → ℕ)
    (total : ℕ) (i : ι) : ℕ :=
  if i = distinguished then
    total - ∑ j ∈ indices.erase distinguished, rawCount j
  else rawCount i

theorem sum_distinguishedRemainderCount
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (distinguished : ι) (rawCount : ι → ℕ)
    (total : ℕ) (hdistinguished : distinguished ∈ indices)
    (hraw : ∑ j ∈ indices.erase distinguished, rawCount j ≤ total) :
    ∑ i ∈ indices,
        distinguishedRemainderCount indices distinguished rawCount total i =
      total := by
  classical
  have herase :
      ∑ i ∈ indices.erase distinguished,
          distinguishedRemainderCount indices distinguished rawCount total i =
        ∑ i ∈ indices.erase distinguished, rawCount i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [distinguishedRemainderCount]
    rw [if_neg]
    exact Finset.ne_of_mem_erase hi
  calc
    ∑ i ∈ indices,
        distinguishedRemainderCount indices distinguished rawCount total i =
        (∑ i ∈ indices.erase distinguished,
            distinguishedRemainderCount indices distinguished rawCount total i) +
          distinguishedRemainderCount indices distinguished rawCount total
            distinguished :=
      (Finset.sum_erase_add indices _ hdistinguished).symm
    _ = (∑ i ∈ indices.erase distinguished, rawCount i) +
        (total - ∑ i ∈ indices.erase distinguished, rawCount i) := by
      rw [herase]
      simp [distinguishedRemainderCount]
    _ = total := Nat.add_sub_of_le hraw

/-- Distinguished-coordinate form of the terminal partition theorem. -/
theorem exists_exactFinitePartition_distinguishedRemainder
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (source : Finset α) (indices : Finset ι) (distinguished : ι)
    (rawCount : ι → ℕ) (hdistinguished : distinguished ∈ indices)
    (hraw :
      ∑ j ∈ indices.erase distinguished, rawCount j ≤ source.card) :
    Nonempty (ExactFinitePartition source indices
      (distinguishedRemainderCount indices distinguished rawCount
        source.card)) := by
  apply exists_exactFinitePartition
  rw [sum_distinguishedRemainderCount indices distinguished rawCount
    source.card hdistinguished hraw]

/-- The natural floor of a real scale times a target weight. -/
def scaledFloorCount {ι : Type*}
    (scale : ℝ) (weight : ι → ℝ) (i : ι) : ℕ :=
  ⌊scale * weight i⌋₊

/-- Floor every non-distinguished coordinate, and give the distinguished
coordinate every source point left over. -/
def distinguishedScaledFloorCount {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (distinguished : ι) (scale : ℝ)
    (weight : ι → ℝ) (total : ℕ) : ι → ℕ :=
  distinguishedRemainderCount indices distinguished
    (scaledFloorCount scale weight) total

/-- A real budget inequality implies that all scaled floor counts fit in
the corresponding natural-number budget. -/
theorem sum_scaledFloorCount_le
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (scale : ℝ) (weight : ι → ℝ) (total : ℕ)
    (hscale : 0 ≤ scale)
    (hweight : ∀ i ∈ indices, 0 ≤ weight i)
    (hbudget :
      scale * ∑ i ∈ indices, weight i ≤ (total : ℝ)) :
    ∑ i ∈ indices, scaledFloorCount scale weight i ≤ total := by
  have hreal :
      ((∑ i ∈ indices, scaledFloorCount scale weight i : ℕ) : ℝ) ≤
        (total : ℝ) := by
    calc
      ((∑ i ∈ indices, scaledFloorCount scale weight i : ℕ) : ℝ) =
          ∑ i ∈ indices, (scaledFloorCount scale weight i : ℝ) := by
        simp
      _ ≤ ∑ i ∈ indices, scale * weight i := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.floor_le (mul_nonneg hscale (hweight i hi))
      _ = scale * ∑ i ∈ indices, weight i := by
        rw [Finset.mul_sum]
      _ ≤ (total : ℝ) := hbudget
  exact_mod_cast hreal

/-- Terminal floor-all-but-one realization.  Positivity of the
distinguished weight records the coordinate that will absorb the rounding
remainder in asymptotic applications. -/
theorem exists_exactFinitePartition_distinguishedScaledFloor
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (source : Finset α) (indices : Finset ι) (distinguished : ι)
    (scale : ℝ) (weight : ι → ℝ)
    (hdistinguished : distinguished ∈ indices)
    (_hdistinguishedPositive : 0 < weight distinguished)
    (hscale : 0 ≤ scale)
    (hweight :
      ∀ i ∈ indices.erase distinguished, 0 ≤ weight i)
    (hbudget :
      scale * ∑ i ∈ indices.erase distinguished, weight i ≤
        (source.card : ℝ)) :
    Nonempty (ExactFinitePartition source indices
      (distinguishedScaledFloorCount indices distinguished scale weight
        source.card)) := by
  apply exists_exactFinitePartition_distinguishedRemainder
    source indices distinguished (scaledFloorCount scale weight)
    hdistinguished
  exact sum_scaledFloorCount_le (indices.erase distinguished) scale weight
    source.card hscale hweight hbudget

end

end Erdos390.WholePaper
