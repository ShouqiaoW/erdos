import Erdos390.WholePaper.TailValuationCore

/-!
# Fixed-small-prime tail valuation capacity

The factorial quotient over `(a,a+h]` is decomposed as a binomial
coefficient times `h!`.  This gives the paper's coefficient `1/(p-1)` with
only a logarithmic carry term, and summing over the nine fixed primes gives
the exact coefficient `S23`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Summed natural-valued capacity over the paper's nine small primes. -/
theorem smallPrimeFactorialValuationSum_le
    (n h : ℕ) :
    (∑ ℓ ∈ smallPrimes,
        ((2 * n + h).factorial.factorization ℓ -
          2 * n.factorial.factorization ℓ)) ≤
      centralSmallPrimeValuationSum n +
        (∑ ℓ ∈ smallPrimes, h / (ℓ - 1)) +
          9 * Nat.log2 (2 * n + h) := by
  calc
    (∑ ℓ ∈ smallPrimes,
        ((2 * n + h).factorial.factorization ℓ -
          2 * n.factorial.factorization ℓ)) ≤
        ∑ ℓ ∈ smallPrimes,
          ((Nat.choose (2 * n) n).factorization ℓ +
            (h / (ℓ - 1) + Nat.log2 (2 * n + h))) := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      apply fullFactorialValuationSub_le_central_add_tailCapacity
      simp only [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at hℓ
      rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num
    _ = centralSmallPrimeValuationSum n +
          (∑ ℓ ∈ smallPrimes, h / (ℓ - 1)) +
            9 * Nat.log2 (2 * n + h) := by
      simp only [Finset.sum_add_distrib]
      rw [centralSmallPrimeValuationSum]
      simp [smallPrimes, Nat.add_assoc]

/-- After casting, the exact geometric coefficient in the nine tail
capacities is `S23`. -/
theorem smallPrimeNatDivSum_cast_le (h : ℕ) :
    ((∑ ℓ ∈ smallPrimes, h / (ℓ - 1) : ℕ) : ℝ) ≤
      (h : ℝ) * (S23 : ℝ) := by
  simp only [Nat.cast_sum]
  calc
    ∑ ℓ ∈ smallPrimes, ((h / (ℓ - 1) : ℕ) : ℝ) ≤
        ∑ ℓ ∈ smallPrimes, (h : ℝ) / ((ℓ - 1 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro ℓ _hℓ
      exact Nat.cast_div_le
    _ = (h : ℝ) * (S23 : ℝ) := by
      norm_num [S23, smallPrimes]
      ring

/-- Real-valued nine-prime capacity, with a uniform logarithmic remainder
when `h ≤ n`. -/
theorem smallPrimeFactorialValuationSum_cast_le
    {n h : ℕ} (hh : h ≤ n) :
    ((∑ ℓ ∈ smallPrimes,
        ((2 * n + h).factorial.factorization ℓ -
          2 * n.factorial.factorization ℓ) : ℕ) : ℝ) ≤
      (h : ℝ) * (S23 : ℝ) +
        (centralSmallPrimeValuationSum n : ℝ) +
          9 * (Nat.log2 (3 * n) : ℝ) := by
  have hlog : Nat.log2 (2 * n + h) ≤ Nat.log2 (3 * n) := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right (by omega)
  have hnatural := smallPrimeFactorialValuationSum_le n h
  have hcast :
      ((∑ ℓ ∈ smallPrimes,
          ((2 * n + h).factorial.factorization ℓ -
            2 * n.factorial.factorization ℓ) : ℕ) : ℝ) ≤
        (centralSmallPrimeValuationSum n : ℝ) +
          ((∑ ℓ ∈ smallPrimes, h / (ℓ - 1) : ℕ) : ℝ) +
            9 * (Nat.log2 (2 * n + h) : ℝ) := by
    exact_mod_cast hnatural
  have hdiv := smallPrimeNatDivSum_cast_le h
  have hlogCast :
      (Nat.log2 (2 * n + h) : ℝ) ≤ (Nat.log2 (3 * n) : ℝ) := by
    exact_mod_cast hlog
  calc
    ((∑ ℓ ∈ smallPrimes,
        ((2 * n + h).factorial.factorization ℓ -
          2 * n.factorial.factorization ℓ) : ℕ) : ℝ) ≤
        (centralSmallPrimeValuationSum n : ℝ) +
          ((∑ ℓ ∈ smallPrimes, h / (ℓ - 1) : ℕ) : ℝ) +
            9 * (Nat.log2 (2 * n + h) : ℝ) := hcast
    _ ≤ (centralSmallPrimeValuationSum n : ℝ) +
          (h : ℝ) * (S23 : ℝ) +
            9 * (Nat.log2 (3 * n) : ℝ) := by
      gcongr
    _ = (h : ℝ) * (S23 : ℝ) +
          (centralSmallPrimeValuationSum n : ℝ) +
            9 * (Nat.log2 (3 * n) : ℝ) := by ring

end

end Erdos390.WholePaper
