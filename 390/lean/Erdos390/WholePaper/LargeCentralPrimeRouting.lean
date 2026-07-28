import Erdos390.WholePaper.CentralPrimeBlockDecomposition
import Erdos390.WholePaper.CentralCarryAnchors

/-!
# Routing every large central prime to a carry row or row zero

Above a square-root cutoff, Legendre's formula has only its first term.
Thus every large prime divisor of the central binomial coefficient occurs
once, and its quotient row `n / p` determines its unique anchor family.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- If a prime occurs in the central binomial coefficient and `p^2 > 2n`,
then its valuation is one and the two floor quotients differ by one carry. -/
theorem centralChoose_largePrime_carry
    {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hpExponent : 0 < (Nat.choose (2 * n) n).factorization p)
    (hpSq : 2 * n < p ^ 2) :
    (Nat.choose (2 * n) n).factorization p = 1 ∧
      (2 * n) / p = 2 * (n / p) + 1 := by
  let r := n / p
  have hnSq : n < p ^ 2 := by omega
  have hnFac : n.factorial.factorization p = r := by
    simpa only [r] using
      factorial_factorization_eq_div_of_lt_sq hp hn hnSq
  have htwoFac : (2 * n).factorial.factorization p = (2 * n) / p := by
    exact factorial_factorization_eq_div_of_lt_sq hp (by omega) hpSq
  have hnUpper : n < p * (r + 1) := by
    simpa only [r] using Nat.lt_mul_div_succ n hp.pos
  have htwoUpper : 2 * n < (2 * r + 2) * p := by
    calc
      2 * n < 2 * (p * (r + 1)) :=
        (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hnUpper
      _ = (2 * r + 2) * p := by ring
  have hdivUpper : (2 * n) / p ≤ 2 * r + 1 := by
    have hlt : (2 * n) / p < 2 * r + 2 :=
      (Nat.div_lt_iff_lt_mul hp.pos).2 htwoUpper
    omega
  have hcentral := centralFactorialValuation_eq_choose_add
    (n := n) (p := p)
  rw [hnFac, htwoFac] at hcentral
  constructor <;> omega

/-- A cutoff strictly below `p` transfers its square bound to `p`. -/
theorem two_mul_lt_prime_sq_of_cutoff
    {n X p : ℕ} (hXsq : 2 * n < X ^ 2) (hXp : X < p) :
    2 * n < p ^ 2 := by
  have hPow : X ^ 2 < p ^ 2 := by
    rw [pow_two, pow_two]
    exact (Nat.mul_le_mul_left X hXp.le).trans_lt
      ((Nat.mul_lt_mul_right (by omega : 0 < p)).2 hXp)
  exact hXsq.trans hPow

/-- Every large central prime is routed exactly either to the row-zero
interval `(n,2n]` or to its positive stationary carry row. -/
theorem largeCentralPrime_rowZero_or_stationary
    {n X p : ℕ} (hn : 0 < n) (hXsq : 2 * n < X ^ 2)
    (hpMem : p ∈ largeCentralPrimes n X) :
    (Nat.choose (2 * n) n).factorization p = 1 ∧
      ((n < p ∧ p ≤ 2 * n) ∨
        ∃ r : ℕ, 1 ≤ r ∧ r = n / p ∧
          p ∈ stationaryPrimeLayer n r) := by
  have hpPrime := largeCentralPrimes_prime hpMem
  have hpFactors : p ∈ (Nat.choose (2 * n) n).primeFactors :=
    (Finset.mem_filter.mp hpMem).1
  have hpExponent : 0 < (Nat.choose (2 * n) n).factorization p := by
    exact hpPrime.factorization_pos_of_dvd
      (Nat.choose_pos (by omega)).ne'
      (Nat.dvd_of_mem_primeFactors hpFactors)
  have hpSq := two_mul_lt_prime_sq_of_cutoff hXsq
    (largeCentralPrimes_gt hpMem)
  obtain ⟨hpOne, hfloor⟩ :=
    centralChoose_largePrime_carry hn hpPrime hpExponent hpSq
  refine ⟨hpOne, ?_⟩
  let r := n / p
  have hnUpper : n < p * (r + 1) := by
    simpa only [r] using Nat.lt_mul_div_succ n hpPrime.pos
  by_cases hrZero : r = 0
  · left
    constructor
    · simpa only [hrZero, zero_add, mul_one] using hnUpper
    · have hOneLe : 1 ≤ (2 * n) / p := by
        rw [hfloor]
        omega
      have hpLe := (Nat.le_div_iff_mul_le hpPrime.pos).1 hOneLe
      simpa only [one_mul] using hpLe
  · right
    refine ⟨r, Nat.one_le_iff_ne_zero.mpr hrZero, rfl, ?_⟩
    rw [mem_stationaryPrimeLayer]
    refine ⟨hpPrime, hnUpper, ?_⟩
    have hrowLe : 2 * r + 1 ≤ (2 * n) / p := by omega
    have hmul := (Nat.le_div_iff_mul_le hpPrime.pos).1 hrowLe
    simpa only [Nat.mul_comm] using hmul

end

end Erdos390.WholePaper
