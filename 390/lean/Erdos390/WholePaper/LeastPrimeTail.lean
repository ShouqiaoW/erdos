import Erdos390.WholePaper.Nagura

/-! # Least-prime routing for the infinite allocation tail -/

namespace Erdos390.WholePaper

noncomputable section

private theorem exists_prime_strictly_above (n : ℕ) :
    ∃ p : ℕ, p.Prime ∧ n < p := by
  obtain ⟨p, hpLower, hpPrime⟩ := Nat.exists_infinite_primes (n + 1)
  exact ⟨p, hpPrime, by omega⟩

/-- The least prime strictly larger than `n`. -/
def leastPrimeAbove (n : ℕ) : ℕ :=
  Nat.find (exists_prime_strictly_above n)

theorem leastPrimeAbove_prime (n : ℕ) : (leastPrimeAbove n).Prime :=
  (Nat.find_spec (exists_prime_strictly_above n)).1

theorem lt_leastPrimeAbove (n : ℕ) : n < leastPrimeAbove n :=
  (Nat.find_spec (exists_prime_strictly_above n)).2

theorem leastPrimeAbove_le {n p : ℕ} (hp : p.Prime) (hnp : n < p) :
    leastPrimeAbove n ≤ p := by
  exact Nat.find_min' (exists_prime_strictly_above n) ⟨hp, hnp⟩

/-- Bertrand places the least prime in the allocation range. -/
theorem leastPrimeAbove_le_two_mul {n : ℕ} (hn : 0 < n) :
    leastPrimeAbove n ≤ 2 * n := by
  obtain ⟨p, hpPrime, hnp, hpUpper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul n hn.ne'
  exact (leastPrimeAbove_le hpPrime hnp).trans hpUpper

theorem leastPrimeAbove_mem_allocationRange {r : ℕ} (hr : 1 ≤ r) :
    leastPrimeAbove r ∈ Finset.Icc (r + 1) (2 * r + 1) := by
  exact Finset.mem_Icc.mpr
    ⟨Nat.succ_le_iff.mpr (lt_leastPrimeAbove r),
      (leastPrimeAbove_le_two_mul (by omega)).trans (by omega)⟩

/-- For consecutive primes `pPrev < p`, least-prime routing sends exactly
the integer block `pPrev ≤ r ≤ p-1` to `p`. -/
theorem leastPrimeAbove_eq_of_consecutivePrimes
    {pPrev p r : ℕ} (hpPrev : pPrev.Prime) (hp : p.Prime)
    (hPrevP : pPrev < p)
    (hNoBetween : ∀ q : ℕ, q.Prime → pPrev < q → q < p → False) :
    leastPrimeAbove r = p ↔ pPrev ≤ r ∧ r < p := by
  constructor
  · intro hleast
    constructor
    · by_contra hPrevR
      have hrPrev : r < pPrev := by omega
      have hle : leastPrimeAbove r ≤ pPrev :=
        leastPrimeAbove_le hpPrev hrPrev
      omega
    · simpa only [hleast] using lt_leastPrimeAbove r
  · rintro ⟨hPrevR, hrP⟩
    apply Nat.le_antisymm (leastPrimeAbove_le hp hrP)
    by_contra hnot
    have hleastLt : leastPrimeAbove r < p := by omega
    exact hNoBetween (leastPrimeAbove r) (leastPrimeAbove_prime r)
      (hPrevR.trans_lt (lt_leastPrimeAbove r)) hleastLt

end

end Erdos390.WholePaper
