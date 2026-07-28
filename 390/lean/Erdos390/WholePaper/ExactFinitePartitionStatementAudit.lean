import Erdos390.WholePaper.ExactFinitePartition

/-! # Expanded statement audit for exact finite partitions -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example {α ι : Type*} [DecidableEq α]
    (source : Finset α) (indices : Finset ι) (count : ι → ℕ)
    (hcount : ∑ i ∈ indices, count i ≤ source.card) :
    ∃ parts : ι → Finset α, ∃ remainder : Finset α,
      (∀ i ∈ indices, parts i ⊆ source) ∧
      (∀ i ∈ indices, (parts i).card = count i) ∧
      (indices : Set ι).PairwiseDisjoint parts ∧
      remainder ⊆ source ∧
      (∀ i ∈ indices, Disjoint (parts i) remainder) ∧
      indices.biUnion parts ∪ remainder = source ∧
      (indices.biUnion parts).card = ∑ i ∈ indices, count i ∧
      remainder.card = source.card - ∑ i ∈ indices, count i := by
  obtain ⟨partition⟩ :=
    exists_exactFinitePartition source indices count hcount
  exact ⟨partition.parts, partition.remainder,
    partition.parts_subset, partition.parts_card,
    partition.parts_pairwiseDisjoint, partition.remainder_subset,
    partition.part_remainder_disjoint, partition.union_remainder,
    partition.union_card, partition.remainder_card⟩

example {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (source : Finset α) (indices : Finset ι) (distinguished : ι)
    (scale : ℝ) (weight : ι → ℝ)
    (hdistinguished : distinguished ∈ indices)
    (hdistinguishedPositive : 0 < weight distinguished)
    (hscale : 0 ≤ scale)
    (hweight :
      ∀ i ∈ indices.erase distinguished, 0 ≤ weight i)
    (hbudget :
      scale * ∑ i ∈ indices.erase distinguished, weight i ≤
        (source.card : ℝ)) :
    Nonempty (ExactFinitePartition source indices
      (fun i ↦
        if i = distinguished then
          source.card -
            ∑ j ∈ indices.erase distinguished,
              ⌊scale * weight j⌋₊
        else
          ⌊scale * weight i⌋₊)) := by
  simpa only [distinguishedScaledFloorCount,
    distinguishedRemainderCount, scaledFloorCount] using
    exists_exactFinitePartition_distinguishedScaledFloor
      source indices distinguished scale weight hdistinguished
      hdistinguishedPositive hscale hweight hbudget

end

end Erdos390.WholePaper
