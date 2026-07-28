import Erdos390.WholePaper.InfiniteAllocationCore

/-! # Expanded statement audit for the finite/tail allocation splice -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example (r q : ℕ) :
    0 ≤ finiteAllocation r q +
      (if 201 ≤ r ∧ q = leastPrimeAbove r then
        1 / (((r : ℚ) + 1) * (2 * (r : ℚ) + 1)) else 0) := by
  simpa only [infiniteAllocation, tailAllocation, alpha] using
    infiniteAllocation_nonneg r q

example {r : ℕ} (hr : 1 ≤ r) :
    (∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
      (finiteAllocation r q +
        (if 201 ≤ r ∧ q = leastPrimeAbove r then
          1 / (((r : ℚ) + 1) * (2 * (r : ℚ) + 1)) else 0))) =
      1 / (((r : ℚ) + 1) * (2 * (r : ℚ) + 1)) := by
  simpa only [infiniteAllocation, tailAllocation, alpha] using
    infiniteAllocation_row_identity hr

example (ℓ : ℕ) :
    (∑' r : ℕ,
      ∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
        (q.factorization ℓ : ℚ) *
          (finiteAllocation r q +
            (if 201 ≤ r ∧ q = leastPrimeAbove r then
              1 / (((r : ℚ) + 1) * (2 * (r : ℚ) + 1)) else 0))) =
      finitePrimeLoad ℓ +
        ∑' r : ℕ,
          ∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
            (q.factorization ℓ : ℚ) *
              (if 201 ≤ r ∧ q = leastPrimeAbove r then
                1 / (((r : ℚ) + 1) * (2 * (r : ℚ) + 1)) else 0) := by
  simpa only [allocationPrimeLoad, allocationPrimeRowLoad,
    infiniteAllocation, tailPrimeRowLoad, tailAllocation, alpha] using
    allocationPrimeLoad_infiniteAllocation_eq ℓ

end

end Erdos390.WholePaper
