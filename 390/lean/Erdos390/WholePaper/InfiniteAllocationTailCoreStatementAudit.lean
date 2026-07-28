import Erdos390.WholePaper.InfiniteAllocationTailCore

/-! # Expanded statement audit for the least-prime allocation tail -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example (r q : ℕ) :
    0 ≤ (if 201 ≤ r ∧ q = leastPrimeAbove r then
      1 / (((r : ℚ) + 1) * (2 * (r : ℚ) + 1)) else 0) := by
  simpa only [tailAllocation, alpha] using tailAllocation_nonneg r q

example (ℓ r : ℕ) :
    (∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
        (q.factorization ℓ : ℚ) *
          (if 201 ≤ r ∧ q = leastPrimeAbove r then
            1 / (((r : ℚ) + 1) * (2 * (r : ℚ) + 1)) else 0)) =
      if 201 ≤ r ∧ leastPrimeAbove r = ℓ then
        1 / (((r : ℚ) + 1) * (2 * (r : ℚ) + 1)) else 0 := by
  simpa only [tailPrimeRowLoad, allocationPrimeRowLoad, tailAllocation,
    alpha] using tailPrimeRowLoad_eq ℓ r

example (ℓ : ℕ) :
    (∑' r : ℕ,
      ∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
        (q.factorization ℓ : ℚ) *
          (if 201 ≤ r ∧ q = leastPrimeAbove r then
            1 / (((r : ℚ) + 1) * (2 * (r : ℚ) + 1)) else 0)) =
      ∑ r ∈ Finset.Icc 201 (ℓ - 1),
        if leastPrimeAbove r = ℓ then
          1 / (((r : ℚ) + 1) * (2 * (r : ℚ) + 1)) else 0 := by
  simpa only [tailPrimeRowLoad, allocationPrimeRowLoad, tailAllocation,
    alpha] using tsum_tailPrimeRowLoad_eq ℓ

example {pPrev p : ℕ} (hpPrev : pPrev.Prime) (hp : p.Prime)
    (hPrevP : pPrev < p)
    (hNoBetween : ∀ q : ℕ, q.Prime → pPrev < q → q < p → False) :
    (∑' r : ℕ,
      ∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
        (q.factorization p : ℚ) *
          (if 201 ≤ r ∧ q = leastPrimeAbove r then
            1 / (((r : ℚ) + 1) * (2 * (r : ℚ) + 1)) else 0)) =
      ∑ r ∈ Finset.Icc (max 201 pPrev) (p - 1),
        1 / (((r : ℚ) + 1) * (2 * (r : ℚ) + 1)) := by
  simpa only [tailPrimeRowLoad, allocationPrimeRowLoad, tailAllocation,
    alpha] using tsum_tailPrimeRowLoad_eq_consecutiveBlock
      hpPrev hp hPrevP hNoBetween

end

end Erdos390.WholePaper
