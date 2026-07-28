import Erdos390.WholePaper.LeastPrimeTail

/-! # Expanded statement audit for least-prime tail routing -/

namespace Erdos390.WholePaper

noncomputable section

example (n : ℕ) :
    (leastPrimeAbove n).Prime ∧ n < leastPrimeAbove n :=
  ⟨leastPrimeAbove_prime n, lt_leastPrimeAbove n⟩

example {n : ℕ} (hn : 0 < n) :
    n < leastPrimeAbove n ∧ leastPrimeAbove n ≤ 2 * n :=
  ⟨lt_leastPrimeAbove n, leastPrimeAbove_le_two_mul hn⟩

example {r : ℕ} (hr : 1 ≤ r) :
    r + 1 ≤ leastPrimeAbove r ∧ leastPrimeAbove r ≤ 2 * r + 1 := by
  simpa only [Finset.mem_Icc] using leastPrimeAbove_mem_allocationRange hr

example {pPrev p r : ℕ} (hpPrev : pPrev.Prime) (hp : p.Prime)
    (hPrevP : pPrev < p)
    (hNoBetween : ∀ q : ℕ, q.Prime → pPrev < q → q < p → False) :
    leastPrimeAbove r = p ↔ pPrev ≤ r ∧ r < p := by
  exact leastPrimeAbove_eq_of_consecutivePrimes
    hpPrev hp hPrevP hNoBetween

end

end Erdos390.WholePaper
