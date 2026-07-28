import Erdos390.WholePaper.StationaryPrefixAnchors

/-! # Expanded statement audit for simultaneous prefix anchors -/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example (R : ℕ) (distinguished : ℕ → ℕ)
    (hdistinguished :
      ∀ r ∈ Finset.Icc 1 R,
        distinguished r ∈ infiniteAllocationPositiveSupport r) :
    ∃ parts :
        ℕ → {r // r ∈ Finset.Icc 1 R} → ℕ → Finset ℕ,
      (∀ᶠ n : ℕ in atTop,
        ∀ r : {r // r ∈ Finset.Icc 1 R},
          (∀ q ∈ infiniteAllocationPositiveSupport r.1,
            parts n r q ⊆ stationaryPrimeLayer n r.1) ∧
          (∀ q ∈ infiniteAllocationPositiveSupport r.1,
            (parts n r q).card =
              stationaryPrefixCount n r.1 (distinguished r.1) q) ∧
          (infiniteAllocationPositiveSupport r.1 :
            Set ℕ).PairwiseDisjoint (parts n r) ∧
          (infiniteAllocationPositiveSupport r.1).biUnion
              (parts n r) =
            stationaryPrimeLayer n r.1) ∧
      ∀ r : {r // r ∈ Finset.Icc 1 R},
        ∀ q ∈ infiniteAllocationPositiveSupport r.1,
          Tendsto
            (fun n : ℕ ↦
              ((parts n r q).card : ℝ) / secondOrderScale n)
            atTop (nhds (infiniteAllocation r.1 q : ℝ)) := by
  apply exists_stationaryPrefixParts_on_finset
    (Finset.Icc 1 R) (fun r hr ↦ (Finset.mem_Icc.mp hr).1)
    distinguished hdistinguished

example {n r distinguished : ℕ}
    (partition : StationaryPrefixPartition n r distinguished)
    (hn : (2 * r + 1) * (r + 1) ≤ n) :
    (((infiniteAllocationPositiveSupport r).sigma
        partition.parts).image
          (fun x : Σ _q : ℕ, ℕ ↦ x.2 * x.1)).prod id =
      (((infiniteAllocationPositiveSupport r).sigma
        partition.parts).prod fun x ↦ x.2) *
      (((infiniteAllocationPositiveSupport r).sigma
        partition.parts).prod fun x ↦ x.1) := by
  simpa only [stationaryPrefixAnchors, stationaryPrefixMarkedPairs,
    stationaryPrefixAnchor, stationaryPrefixMarkerProduct,
    stationaryPrefixCofactorProduct] using
    stationaryPrefixAnchors_prod hn partition.parts_subset

end

end Erdos390.WholePaper
