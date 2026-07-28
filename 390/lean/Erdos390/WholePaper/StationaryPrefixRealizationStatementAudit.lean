import Erdos390.WholePaper.StationaryPrefixRealization

/-! # Expanded statement audit for fixed stationary-prefix realization -/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example (r : ℕ) (hr : 1 ≤ r) :
    (∑ q ∈
      (Finset.Icc (r + 1) (2 * r + 1)).filter
        (fun q ↦ 0 < infiniteAllocation r q),
      infiniteAllocation r q) = alpha r := by
  simpa only [infiniteAllocationPositiveSupport] using
    infiniteAllocationPositiveSupport_sum r hr

example (r distinguished : ℕ) (hr : 1 ≤ r)
    (hdistinguished :
      distinguished ∈
        (Finset.Icc (r + 1) (2 * r + 1)).filter
          (fun q ↦ 0 < infiniteAllocation r q)) :
    ∃ parts : ℕ → ℕ → Finset ℕ,
      (∀ᶠ n : ℕ in atTop,
        (∀ q ∈
          (Finset.Icc (r + 1) (2 * r + 1)).filter
            (fun q ↦ 0 < infiniteAllocation r q),
          parts n q ⊆ stationaryPrimeLayer n r) ∧
        (∀ q ∈
          (Finset.Icc (r + 1) (2 * r + 1)).filter
            (fun q ↦ 0 < infiniteAllocation r q),
          (parts n q).card =
            if q = distinguished then
              (stationaryPrimeLayer n r).card -
                ∑ j ∈
                  ((Finset.Icc (r + 1) (2 * r + 1)).filter
                    (fun q ↦ 0 < infiniteAllocation r q)).erase
                      distinguished,
                  ⌊secondOrderScale n *
                    (infiniteAllocation r j : ℝ)⌋₊
            else
              ⌊secondOrderScale n *
                (infiniteAllocation r q : ℝ)⌋₊) ∧
        ((Finset.Icc (r + 1) (2 * r + 1)).filter
          (fun q ↦ 0 < infiniteAllocation r q) : Set ℕ).PairwiseDisjoint
            (parts n) ∧
        ((Finset.Icc (r + 1) (2 * r + 1)).filter
          (fun q ↦ 0 < infiniteAllocation r q)).biUnion (parts n) =
            stationaryPrimeLayer n r) ∧
      ∀ q ∈
        (Finset.Icc (r + 1) (2 * r + 1)).filter
          (fun q ↦ 0 < infiniteAllocation r q),
        Tendsto
          (fun n : ℕ ↦
            ((parts n q).card : ℝ) / secondOrderScale n)
          atTop (nhds (infiniteAllocation r q : ℝ)) := by
  simpa only [infiniteAllocationPositiveSupport, stationaryPrefixCount,
    stationaryPrefixRawCount, scaledFloorCount,
    distinguishedRemainderCount] using
    exists_stationaryPrefixParts r distinguished hr hdistinguished

end

end Erdos390.WholePaper
