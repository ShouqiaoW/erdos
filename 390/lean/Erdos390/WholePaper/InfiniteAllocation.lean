import Erdos390.WholePaper.InfiniteAllocationCore
import Erdos390.WholePaper.AllocationTailCapacity
import Erdos390.WholePaper.NaguraLeastPrimeCorollary

/-!
# The exact infinite cofactor allocation

This file instantiates the finite certificate plus least-prime tail and
proves every prime-capacity inequality in Lemma 4.2.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

theorem tsum_tailPrimeRowLoad_eq_zero_of_le_two_hundred
    {ℓ : ℕ} (hℓ : ℓ ≤ 200) :
    (∑' r : ℕ, tailPrimeRowLoad ℓ r) = 0 := by
  rw [tsum_tailPrimeRowLoad_eq]
  apply Finset.sum_eq_zero
  intro r hr
  have hrange := Finset.mem_Icc.mp hr
  omega

/-- Every prime receives at most its exact paper capacity. -/
theorem infiniteAllocation_prime_capacity {ℓ : ℕ} (hℓPrime : ℓ.Prime) :
    allocationPrimeLoad infiniteAllocation ℓ ≤
      C0Rat / (((ℓ - 1 : ℕ) : ℚ)) := by
  by_cases hℓ200 : ℓ ≤ 200
  · rw [allocationPrimeLoad_infiniteAllocation_eq,
      tsum_tailPrimeRowLoad_eq_zero_of_le_two_hundred hℓ200, add_zero]
    exact finiteAllocation_prime_capacity hℓPrime (by omega)
  by_cases hℓ401 : ℓ ≤ 401
  · have hℓ201 : 201 < ℓ := by
      by_contra hnot
      have hEq : ℓ = 201 := by omega
      subst ℓ
      norm_num at hℓPrime
    obtain ⟨hPrevPrime, hPrevℓ, hNoBetween⟩ :=
      previousPrime_spec (by omega : 2 < ℓ)
    rw [allocationPrimeLoad_infiniteAllocation_eq,
      tsum_tailPrimeRowLoad_eq_consecutiveBlock hPrevPrime hℓPrime
        hPrevℓ hNoBetween]
    exact finiteAllocation_prime_overlap hℓPrime hℓ201 hℓ401
  · have hℓGt : 401 < ℓ := by omega
    obtain ⟨hPrevPrime, hPrevℓ, hNoBetween⟩ :=
      previousPrime_spec (by omega : 2 < ℓ)
    have hPrev401 : 401 ≤ previousPrime ℓ := by
      by_contra hnot
      exact hNoBetween 401 (by norm_num) (by omega) (by omega)
    have hRatio : 5 * ℓ < 6 * previousPrime ℓ :=
      consecutivePrimes_ratio
        ⟨hPrevPrime, hℓPrime, hPrevℓ, hNoBetween⟩ (by omega)
    have hBlock := allocationTail_block_capacity_lt_C0Rat
      hPrevPrime.pos hPrevℓ hRatio
    rw [allocationPrimeLoad_infiniteAllocation_eq,
      finitePrimeLoad_eq_zero_of_gt_401 hℓGt, zero_add,
      tsum_tailPrimeRowLoad_eq_consecutiveBlock hPrevPrime hℓPrime
        hPrevℓ hNoBetween,
      max_eq_right (by omega : 201 ≤ previousPrime ℓ)]
    apply le_of_lt
    have hDenom : (0 : ℚ) < ((ℓ - 1 : ℕ) : ℚ) := by
      exact_mod_cast (by omega : 0 < ℓ - 1)
    apply (lt_div_iff₀ hDenom).2
    simpa only [mul_comm] using hBlock

/-- Lemma 4.2 (`Infinite cofactor allocation`) in a total-function form.
The second conjunct says that the total function is zero outside the
paper's permitted cofactor indices. -/
theorem infinite_cofactor_allocation :
    ∃ x : ℕ → ℕ → ℚ,
      (∀ r q : ℕ, 0 ≤ x r q) ∧
      (∀ r : ℕ, 1 ≤ r → ∀ q : ℕ,
        q ∉ Finset.Icc (r + 1) (2 * r + 1) → x r q = 0) ∧
      (∀ r : ℕ, 1 ≤ r →
        (∑ q ∈ Finset.Icc (r + 1) (2 * r + 1), x r q) = alpha r) ∧
      (∀ ℓ : ℕ, ℓ.Prime →
        allocationPrimeLoad x ℓ ≤ C0Rat / (((ℓ - 1 : ℕ) : ℚ))) := by
  refine ⟨infiniteAllocation, infiniteAllocation_nonneg, ?_, ?_, ?_⟩
  · intro r hr q hq
    exact infiniteAllocation_eq_zero_of_not_mem_allocationRange hr hq
  · intro r hr
    exact infiniteAllocation_row_identity hr
  · intro ℓ hℓPrime
    exact infiniteAllocation_prime_capacity hℓPrime

end

end Erdos390.WholePaper
