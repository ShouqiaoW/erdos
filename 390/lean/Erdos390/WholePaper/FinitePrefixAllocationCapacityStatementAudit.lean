import Erdos390.WholePaper.FinitePrefixAllocationCapacity

/-! # Expanded statement audit for finite-prefix allocation capacity -/

open scoped BigOperators

namespace Erdos390.WholePaper

example (R : ℕ) {ℓ : ℕ} (hℓPrime : ℓ.Prime) :
    (∑ r ∈ Finset.Icc 1 R,
      ∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
        (q.factorization ℓ : ℚ) *
          (finiteAllocation r q +
            if 201 ≤ r ∧ q = leastPrimeAbove r then alpha r else 0)) ≤
      C0Rat / (((ℓ - 1 : ℕ) : ℚ)) := by
  simpa only [prefixAllocationPrimeLoad, infiniteAllocation,
    tailAllocation] using prefixAllocationPrimeLoad_le_capacity R hℓPrime

end Erdos390.WholePaper
