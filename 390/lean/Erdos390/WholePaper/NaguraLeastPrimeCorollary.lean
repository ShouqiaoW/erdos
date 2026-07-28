import Erdos390.WholePaper.NaguraUniversal
import Erdos390.WholePaper.LeastPrimeTail

/-! # Least-prime consequences of the universal Nagura theorem -/

namespace Erdos390.WholePaper

/-- The least prime above `n` lies strictly below `6n/5`. -/
theorem leastPrimeAbove_nagura_ratio {n : ℕ} (hn : 25 ≤ n) :
    5 * leastPrimeAbove n < 6 * n := by
  apply consecutivePrime_ratio_of_naguraWitness
  · intro q hqPrime hnq
    exact leastPrimeAbove_le hqPrime hnq
  · exact exists_prime_nagura hn

/-- Consecutive primes above the Nagura cutoff have ratio below `6/5`. -/
theorem consecutivePrimes_ratio {pPrev p : ℕ}
    (hConsecutive : pPrev.Prime ∧ p.Prime ∧ pPrev < p ∧
      ∀ q : ℕ, q.Prime → pPrev < q → q < p → False)
    (hpPrevLower : 25 ≤ pPrev) :
    5 * p < 6 * pPrev := by
  obtain ⟨_hPrevPrime, _hpPrime, hPrevLt, hNoBetween⟩ := hConsecutive
  have hLeast : ∀ q : ℕ, q.Prime → pPrev < q → p ≤ q := by
    intro q hqPrime hPrevQ
    by_contra hqp
    exact hNoBetween q hqPrime hPrevQ (by omega)
  exact consecutivePrime_ratio_of_naguraWitness hLeast
    (exists_prime_nagura hpPrevLower)

end Erdos390.WholePaper
