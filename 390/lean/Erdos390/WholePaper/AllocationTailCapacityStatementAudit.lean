import Erdos390.WholePaper.AllocationTailCapacity

/-! # Expanded statement audit for one tail-allocation capacity block -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example {a r : ℕ} (ha : 0 < a) (har : a ≤ r) :
    1 / (((r : ℚ) + 1) * (2 * (r : ℚ) + 1)) <
      1 / (2 * (a : ℚ) ^ 2) := by
  exact alpha_lt_one_div_two_mul_sq ha har

example {a p : ℕ} (ha : 0 < a) (hap : a < p) :
    (∑ r ∈ Finset.Icc a (p - 1),
        1 / (((r : ℚ) + 1) * (2 * (r : ℚ) + 1))) <
      ((p - a : ℕ) : ℚ) / (2 * (a : ℚ) ^ 2) := by
  exact allocationTail_alpha_block_sum_lt ha hap

example {a p : ℕ} (ha : 0 < a) (hap : a < p)
    (hNagura : 5 * p < 6 * a) :
    (p : ℚ) * ((p - a : ℕ) : ℚ) /
        (2 * (a : ℚ) ^ 2) < (3 : ℚ) / 25 := by
  exact nagura_gap_fraction_lt_three_div_twenty_five ha hap hNagura

example {pPrev p : ℕ} (hpPrevPos : 0 < pPrev) (hPrevP : pPrev < p)
    (hNagura : 5 * p < 6 * pPrev) :
    (((p - 1 : ℕ) : ℚ)) *
        (∑ r ∈ Finset.Icc pPrev (p - 1),
          1 / (((r : ℚ) + 1) * (2 * (r : ℚ) + 1))) <
      4029639598 / 25970038185 := by
  simpa only [alpha, C0Rat_eq] using
    allocationTail_block_capacity_lt_C0Rat hpPrevPos hPrevP hNagura

end

end Erdos390.WholePaper
