import Erdos390.WholePaper.InfiniteAllocation

/-!
# Capacity of every fixed prefix of the infinite allocation

The stationary-anchor construction realizes finitely many rows of the exact
infinite allocation.  This file proves that their literal weighted load is
bounded by the already certified full load.  No limiting argument occurs
here; it is finite-sum and summability algebra over the concrete allocation.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The valuation load in rows `1,...,R` of the concrete allocation. -/
def prefixAllocationPrimeLoad (R ℓ : ℕ) : ℚ :=
  ∑ r ∈ Finset.Icc 1 R,
    ∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
      (q.factorization ℓ : ℚ) * infiniteAllocation r q

theorem allocationPrimeRowLoad_infiniteAllocation_nonneg (ℓ r : ℕ) :
    0 ≤ allocationPrimeRowLoad infiniteAllocation ℓ r := by
  apply Finset.sum_nonneg
  intro q _hq
  exact mul_nonneg (Nat.cast_nonneg _) (infiniteAllocation_nonneg r q)

theorem summable_allocationPrimeRowLoad_infiniteAllocation (ℓ : ℕ) :
    Summable (allocationPrimeRowLoad infiniteAllocation ℓ) := by
  have hadd := (summable_finitePrimeRowLoad ℓ).add
    (summable_tailPrimeRowLoad ℓ)
  exact hadd.congr fun r ↦ (infinitePrimeRowLoad_eq_add ℓ r).symm

/-- A fixed prefix cannot use more of a prime coordinate than the full
nonnegative infinite allocation. -/
theorem prefixAllocationPrimeLoad_le_full (R ℓ : ℕ) :
    prefixAllocationPrimeLoad R ℓ ≤
      allocationPrimeLoad infiniteAllocation ℓ := by
  rw [prefixAllocationPrimeLoad, allocationPrimeLoad]
  exact (summable_allocationPrimeRowLoad_infiniteAllocation ℓ).sum_le_tsum
    (Finset.Icc 1 R)
    (fun r _hr ↦ allocationPrimeRowLoad_infiniteAllocation_nonneg ℓ r)

theorem prefixAllocationPrimeLoad_nonneg (R ℓ : ℕ) :
    0 ≤ prefixAllocationPrimeLoad R ℓ := by
  apply Finset.sum_nonneg
  intro r _hr
  exact allocationPrimeRowLoad_infiniteAllocation_nonneg ℓ r

/-- Every finite prefix inherits the paper's exact certified capacity. -/
theorem prefixAllocationPrimeLoad_le_capacity
    (R : ℕ) {ℓ : ℕ} (hℓPrime : ℓ.Prime) :
    prefixAllocationPrimeLoad R ℓ ≤
      C0Rat / (((ℓ - 1 : ℕ) : ℚ)) := by
  exact (prefixAllocationPrimeLoad_le_full R ℓ).trans
    (infiniteAllocation_prime_capacity hℓPrime)

end

end Erdos390.WholePaper
