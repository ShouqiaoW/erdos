import Erdos390.WholePaper.Definitions

/-!
# Exact constants for Sections 3 and 4

This file records the thirteen lower-bound row masses, the nine small
primes, and the exact rational value of the paper's constant.  The same row
mass is used by the cofactor allocation in Section 4.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The mass of allocation/lower-bound row `r`:
`alpha_r = 1 / ((r+1)(2r+1))`. -/
def alpha (r : ℕ) : ℚ :=
  1 / (((r : ℚ) + 1) * (2 * (r : ℚ) + 1))

/-- The small-prime set used by the first thirteen lower-bound layers. -/
def smallPrimes : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23}

/-- The total mass in the first thirteen rows. -/
def A13 : ℚ :=
  ∑ r ∈ Finset.Icc 1 13, alpha r

/-- The total valuation capacity of the small-prime set. -/
def S23 : ℚ :=
  ∑ ℓ ∈ smallPrimes, 1 / (((ℓ - 1 : ℕ) : ℚ))

/-- The exact rational form of the paper's second-order constant. -/
def C0Rat : ℚ :=
  A13 / S23

/-- The row mass is the exact difference of the two layer endpoints. -/
theorem two_div_sub_one_div_eq_alpha (r : ℕ) :
    (2 : ℚ) / (2 * (r : ℚ) + 1) - 1 / ((r : ℚ) + 1) = alpha r := by
  have hr1 : (r : ℚ) + 1 ≠ 0 := by positivity
  have hr2 : 2 * (r : ℚ) + 1 ≠ 0 := by positivity
  rw [alpha]
  field_simp
  ring

/-- Exact evaluation of the first thirteen row masses. -/
theorem A13_eq :
    A13 = 2014819799 / 5736673800 := by
  norm_num [A13, alpha, Finset.sum_Icc_succ_top]

/-- Exact evaluation of the nine small-prime capacities. -/
theorem S23_eq :
    S23 = 17927 / 7920 := by
  norm_num [S23, smallPrimes]

/-- Exact rational evaluation of `C0`. -/
theorem C0Rat_eq :
    C0Rat = 4029639598 / 25970038185 := by
  rw [C0Rat, A13_eq, S23_eq]
  norm_num

/-- The quotient definition in multiplication form. -/
theorem A13_eq_C0Rat_mul_S23 :
    A13 = C0Rat * S23 := by
  rw [A13_eq, C0Rat_eq, S23_eq]
  norm_num

/-- The rational constant in this file is exactly the real constant fixed in
`Definitions.lean`. -/
theorem C0_eq_ratCast_C0Rat :
    C0 = (C0Rat : ℝ) := by
  rw [C0Rat_eq]
  norm_num [C0]

theorem C0Rat_lt_one : C0Rat < 1 := by
  rw [C0Rat_eq]
  norm_num

theorem three_div_twenty_five_lt_C0Rat :
    (3 : ℚ) / 25 < C0Rat := by
  rw [C0Rat_eq]
  norm_num

theorem C0_lt_one : C0 < 1 := by
  norm_num [C0]

theorem three_div_twenty_five_lt_C0 :
    (3 : ℝ) / 25 < C0 := by
  norm_num [C0]

/-- Every possible cofactor in the first thirteen layers has a prime divisor
in `smallPrimes`: those cofactors lie in the literal interval `[2,27]`. -/
theorem exists_smallPrime_dvd_of_mem_Icc {q : ℕ}
    (hq : q ∈ Finset.Icc 2 27) :
    ∃ ℓ ∈ smallPrimes, Nat.Prime ℓ ∧ ℓ ∣ q := by
  simp only [Finset.mem_Icc] at hq
  obtain ⟨ℓ, hℓPrime, hℓDvd⟩ :=
    Nat.exists_prime_and_dvd (ne_of_gt (lt_of_lt_of_le Nat.one_lt_two hq.1))
  have hℓLower : 2 ≤ ℓ := hℓPrime.two_le
  have hℓUpper : ℓ ≤ 27 :=
    (Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_two hq.1) hℓDvd).trans hq.2
  have hℓMem : ℓ ∈ smallPrimes := by
    interval_cases ℓ <;> norm_num at hℓPrime <;> norm_num [smallPrimes]
  exact ⟨ℓ, hℓMem, hℓPrime, hℓDvd⟩

end

end Erdos390.WholePaper
