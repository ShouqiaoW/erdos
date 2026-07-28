import Erdos390.WholePaper.CentralAnchorDivisorSupport
import Erdos390.WholePaper.UpperTailValuationAsymptotic
import Erdos390.WholePaper.UpperProductAssembly

/-!
# From central-anchor valuation reserve to literal tail divisibility

The analytic part of the central-anchor argument produces inequalities at a
fixed finite set of primes.  This file supplies the exact arithmetic bridge:
the factorial-tail valuation is the valuation of the literal tail product,
and bounds on the finite support of the anchor divisor imply actual natural-
number divisibility.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- The literal tail product is positive, including when the tail is empty. -/
theorem centralTailProduct_pos (n h : ℕ) : 0 < centralTailProduct n h := by
  exact Finset.prod_pos fun a ha ↦ by
    have haMem : a ∈ Finset.Ioc (2 * n) (2 * n + h) := ha
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp haMem).1

/-- Exact valuation of the literal product over `(2n,2n+h]`. -/
theorem centralTailProduct_factorization (n h p : ℕ) :
    (centralTailProduct n h).factorization p =
      (2 * n + h).factorial.factorization p -
        (2 * n).factorial.factorization p := by
  have hproduct := congrArg (fun m : ℕ ↦ m.factorization p)
    (centralTailProduct_mul_centralFactorial n h)
  have htailNe : centralTailProduct n h ≠ 0 :=
    (centralTailProduct_pos n h).ne'
  have hfactorialNe : (2 * n).factorial ≠ 0 := Nat.factorial_ne_zero _
  change
    (centralTailProduct n h * (2 * n).factorial).factorization p =
      (2 * n + h).factorial.factorization p at hproduct
  rw [Nat.factorization_mul htailNe hfactorialNe] at hproduct
  simp only [Finsupp.add_apply] at hproduct
  omega

/-- The asymptotic module's tail valuation is literally the valuation of the
corresponding finite product. -/
theorem upperTailValuation_eq_centralTailProduct_factorization
    (c : ℝ) (n p : ℕ) :
    upperTailValuation c n p =
      (centralTailProduct n (upperTailLength c n)).factorization p := by
  rw [centralTailProduct_factorization]
  rfl

/-- The fixed finite set of primes up to a natural bound. -/
def primesUpTo (B : ℕ) : Finset ℕ :=
  (Finset.range (B + 1)).filter Nat.Prime

@[simp]
theorem mem_primesUpTo {B p : ℕ} :
    p ∈ primesUpTo B ↔ p.Prime ∧ p ≤ B := by
  simp [primesUpTo, and_comm]

/-- It suffices to compare valuations on the displayed support bound. -/
theorem centralAnchorDivisor_dvd_centralTailProduct_of_support_bounds
    {n X B h : ℕ} {q : ℕ → ℕ}
    (hqChoice : IsLargeCentralCofactorChoice n X q)
    (hqBound : ∀ p ∈ largeCentralPrimes n X, q p ≤ B)
    (hvaluation : ∀ ℓ ∈ primesUpTo (max 2 B),
      (centralAnchorDivisor n X q).factorization ℓ ≤
        (centralTailProduct n h).factorization ℓ) :
    centralAnchorDivisor n X q ∣ centralTailProduct n h := by
  rw [← Nat.factorization_le_iff_dvd
    (centralAnchorDivisor_pos hqChoice).ne'
    (centralTailProduct_pos n h).ne']
  intro ℓ
  by_cases hℓPrime : ℓ.Prime
  · by_cases hℓDiv : ℓ ∣ centralAnchorDivisor n X q
    · apply hvaluation ℓ
      rw [mem_primesUpTo]
      exact ⟨hℓPrime,
        prime_dvd_centralAnchorDivisor_le hqChoice hqBound hℓPrime hℓDiv⟩
    · rw [Nat.factorization_eq_zero_of_not_dvd hℓDiv]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime _ hℓPrime]
    exact Nat.zero_le _

/-- Specialized form in which the right-hand valuations are supplied by the
upper tail of length `ceil (c n / log n)`. -/
theorem centralAnchorDivisor_dvd_upperTail_of_support_bounds
    {c : ℝ} {n X B : ℕ} {q : ℕ → ℕ}
    (hqChoice : IsLargeCentralCofactorChoice n X q)
    (hqBound : ∀ p ∈ largeCentralPrimes n X, q p ≤ B)
    (hvaluation : ∀ ℓ ∈ primesUpTo (max 2 B),
      (centralAnchorDivisor n X q).factorization ℓ ≤
        upperTailValuation c n ℓ) :
    centralAnchorDivisor n X q ∣
      centralTailProduct n (upperTailLength c n) := by
  apply centralAnchorDivisor_dvd_centralTailProduct_of_support_bounds
    hqChoice hqBound
  intro ℓ hℓ
  rw [← upperTailValuation_eq_centralTailProduct_factorization]
  exact hvaluation ℓ hℓ

/-- Once divisibility is known, the ordinary quotient gives the exact
division-free product identity expected by the final assembly theorem. -/
theorem centralTailQuotient_mul_centralAnchorDivisor
    {n X h : ℕ} {q : ℕ → ℕ}
    (hdiv : centralAnchorDivisor n X q ∣ centralTailProduct n h) :
    centralTailProduct n h / centralAnchorDivisor n X q *
        centralAnchorDivisor n X q =
      centralTailProduct n h := by
  exact Nat.div_mul_cancel hdiv

end

end Erdos390.WholePaper
