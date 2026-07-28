import Erdos390.WholePaper.NaguraLeastPrimeCorollary

/-! # Expanded statement audit for the universal Nagura API -/

namespace Erdos390.WholePaper

example {n : ℕ} (hn : 25 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ 5 * p < 6 * n := by
  simpa only [HasNaguraPrime] using exists_prime_nagura hn

example {n : ℕ} (hn : 25 ≤ n) :
    5 * leastPrimeAbove n < 6 * n := by
  exact leastPrimeAbove_nagura_ratio hn

example {pPrev p : ℕ}
    (hConsecutive : pPrev.Prime ∧ p.Prime ∧ pPrev < p ∧
      ∀ q : ℕ, q.Prime → pPrev < q → q < p → False)
    (hpPrevLower : 25 ≤ pPrev) :
    5 * p < 6 * pPrev := by
  exact consecutivePrimes_ratio hConsecutive hpPrevLower

example {n : ℕ} (hn : 16000000 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ 5 * p < 6 * n := by
  simpa only [HasNaguraPrime] using exists_prime_nagura_analytic_tail hn

example {n : ℕ} (hn : 1000000 ≤ n) :
    Chebyshev.psi (n : ℝ) < (543 : ℝ) / 500 * (n : ℝ) := by
  exact psi_nat_lt_1_086_mul hn

example {n : ℕ} (hn : 20000 ≤ n) :
    (229 : ℝ) / 250 * (n : ℝ) < Chebyshev.psi (n : ℝ) := by
  exact psi_nat_gt_0_916_mul hn

end Erdos390.WholePaper
