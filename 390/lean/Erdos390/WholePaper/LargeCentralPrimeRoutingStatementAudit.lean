import Erdos390.WholePaper.LargeCentralPrimeRouting

/-! # Expanded statement audit for large-central-prime routing -/

namespace Erdos390.WholePaper

example {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hpExponent : 0 < (Nat.choose (2 * n) n).factorization p)
    (hpSq : 2 * n < p ^ 2) :
    (Nat.choose (2 * n) n).factorization p = 1 ∧
      (2 * n) / p = 2 * (n / p) + 1 := by
  exact centralChoose_largePrime_carry hn hp hpExponent hpSq

example {n X p : ℕ} (hXsq : 2 * n < X ^ 2) (hXp : X < p) :
    2 * n < p ^ 2 := by
  exact two_mul_lt_prime_sq_of_cutoff hXsq hXp

example {n X p : ℕ} (hn : 0 < n) (hXsq : 2 * n < X ^ 2)
    (hpMem : p ∈
      (Nat.choose (2 * n) n).primeFactors.filter (fun q ↦ X < q)) :
    (Nat.choose (2 * n) n).factorization p = 1 ∧
      ((n < p ∧ p ≤ 2 * n) ∨
        ∃ r : ℕ, 1 ≤ r ∧ r = n / p ∧
          p.Prime ∧ n < p * (r + 1) ∧
            p * (2 * r + 1) ≤ 2 * n) := by
  simpa only [largeCentralPrimes, mem_stationaryPrimeLayer] using
    largeCentralPrime_rowZero_or_stationary hn hXsq hpMem

end Erdos390.WholePaper
