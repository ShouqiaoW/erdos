import Erdos390.WholePaper.BankPaperPrechargeDivisibilityAlgebra
import Erdos390.WholePaper.TailValuationTwoSided

/-!
# Numerical capacity algebra for the precharged bank

The abstract low-prime hypothesis in the precharge divisibility theorem can
be discharged from two explicit numerical inputs.  On the fixed support of
the guarded central divisor, its real valuation reserve absorbs the uniform
bank valuation bound.  Outside that support the central divisor has zero
valuation, and a cross-multiplied natural inequality forces enough capacity
in the literal factorial tail.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Cross-multiplied capacity in a literal tail -/

/-- The lower Legendre estimate turns a cross-multiplied numerical capacity
condition into a literal lower bound for the valuation of `(2n,2n+h]`. -/
theorem centralTailProduct_factorization_ge_of_cross_capacity
    {n h p K : ℕ} (hp : p.Prime)
    (hcapacity :
      (p - 1) * (K + Nat.log2 h + 1) ≤ h) :
    K ≤ (centralTailProduct n h).factorization p := by
  rw [centralTailProduct_factorization]
  have hlower := factorialValuationSub_lower_cross
    (a := 2 * n) (h := h) hp
  have hscaled :
      (p - 1) * (K + Nat.log2 h + 1) ≤
        (p - 1) *
          ((2 * n + h).factorial.factorization p -
              (2 * n).factorial.factorization p +
            Nat.log2 h + 1) :=
    hcapacity.trans hlower
  have hwithSlack :
      K + Nat.log2 h + 1 ≤
        (2 * n + h).factorial.factorization p -
            (2 * n).factorial.factorization p +
          Nat.log2 h + 1 :=
    le_of_mul_le_mul_left hscaled
      (Nat.sub_pos_of_lt hp.one_lt)
  exact Nat.le_of_add_le_add_right
    (Nat.le_of_add_le_add_right hwithSlack)

namespace BankPaperRealization

/-! ## A uniform valuation bound at an endpoint below `3n` -/

/-- At any realized endpoint at most `3n`, every prime coordinate of the
complete precharged base product is bounded by the global marker budget
times the literal binary logarithm of `3n`. -/
theorem prechargeBaseStateProduct_factorization_le_anchorMarkerBudget_log2_three_mul
    {n M p : ℕ} (R : BankPaperRealization n M) (hp : p.Prime)
    (hendpoint : M ≤ 3 * n) :
    (R.prechargeBaseStateProduct).factorization p ≤
      bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) := by
  simpa only [Nat.log2_eq_log_two] using
    (R.prechargeBaseStateProduct_factorization_le_anchorMarkerBudget hp).trans
      (Nat.mul_le_mul_left _ (Nat.log_mono_right hendpoint))

end BankPaperRealization

namespace GuardedCentralAnchorCertificate

/-! ## Discharging every low-prime coordinate -/

/-- On the fixed anchor support, split the visible post-guard reserve into
an amount spent on the precharged bank and an amount retained afterwards.
The conclusion keeps the retained amount explicit next to the exact anchor
and bank valuations.  No sign condition on either bookkeeping function is
needed: the pointwise split inequality is the complete hypothesis. -/
theorem precharge_fixedSupport_factorization_add_retainedReserve_le_upperTailValuation
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hendpoint :
      upperEndpoint n (upperTailLength c n) ≤ 3 * n)
    (spent retained : ℕ → ℝ)
    (hbankSpent : ∀ p ∈ primesUpTo (2 * depth + 1),
      ((bankPaperAnchorMarkerBudget n *
          Nat.log2 (3 * n) : ℕ) : ℝ) ≤ spent p)
    (hreserveSplit : ∀ p ∈ primesUpTo (2 * depth + 1),
      retained p + spent p ≤
        (c - C0) / (6 * (((p - 1 : ℕ) : ℝ))) *
          secondOrderScale n) :
    ∀ p ∈ primesUpTo (2 * depth + 1),
      retained p +
          (((centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q).factorization p +
            (R.prechargeBaseStateProduct).factorization p : ℕ) : ℝ) ≤
        (upperTailValuation c n p : ℝ) := by
  intro p hpSupport
  have hp := (mem_primesUpTo.mp hpSupport).1
  have hbank :=
    R.prechargeBaseStateProduct_factorization_le_anchorMarkerBudget_log2_three_mul
      hp hendpoint
  have hbankReal :
      ((R.prechargeBaseStateProduct).factorization p : ℝ) ≤
        ((bankPaperAnchorMarkerBudget n *
          Nat.log2 (3 * n) : ℕ) : ℝ) := by
    exact_mod_cast hbank
  have hbankActualSpent :
      ((R.prechargeBaseStateProduct).factorization p : ℝ) ≤ spent p :=
    hbankReal.trans (hbankSpent p hpSupport)
  calc
    retained p +
          (((centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q).factorization p +
            (R.prechargeBaseStateProduct).factorization p : ℕ) : ℝ) =
        ((centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q).factorization p : ℝ) + retained p +
          ((R.prechargeBaseStateProduct).factorization p : ℝ) := by
      rw [Nat.cast_add]
      ring
    _ ≤ ((centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q).factorization p : ℝ) + retained p +
          spent p := by
      linarith
    _ = ((centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q).factorization p : ℝ) +
          (retained p + spent p) := by ring
    _ ≤ ((centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q).factorization p : ℝ) +
          ((c - C0) / (6 * (((p - 1 : ℕ) : ℝ))) *
            secondOrderScale n) := by
      have hsplit := hreserveSplit p hpSupport
      linarith
    _ = (c - C0) / (6 * (((p - 1 : ℕ) : ℝ))) *
            secondOrderScale n +
          ((centralAnchorDivisor n (centralAnchorCutoff depth n)
            certificate.q).factorization p : ℝ) := by ring
    _ ≤ (upperTailValuation c n p : ℝ) :=
      certificate.divisor_reserve p hpSupport

/-- A clean symmetric specialization: one twelfth of the original
`c-C0` margin pays for the precharged bank and another twelfth remains
visible after charging both the guarded anchor and the bank. -/
theorem precharge_fixedSupport_factorization_add_twelfthReserve_le_upperTailValuation
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hendpoint :
      upperEndpoint n (upperTailLength c n) ≤ 3 * n)
    (hbankTwelfth : ∀ p ∈ primesUpTo (2 * depth + 1),
      ((bankPaperAnchorMarkerBudget n *
          Nat.log2 (3 * n) : ℕ) : ℝ) ≤
        (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
          secondOrderScale n) :
    ∀ p ∈ primesUpTo (2 * depth + 1),
      (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
            secondOrderScale n +
          (((centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q).factorization p +
            (R.prechargeBaseStateProduct).factorization p : ℕ) : ℝ) ≤
        (upperTailValuation c n p : ℝ) := by
  exact
    certificate.precharge_fixedSupport_factorization_add_retainedReserve_le_upperTailValuation
      R hendpoint
      (fun p ↦
        (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
          secondOrderScale n)
      (fun p ↦
        (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
          secondOrderScale n)
      hbankTwelfth
      (by
        intro p _hpSupport
        ring_nf
        exact le_rfl)

/-- The full low-prime valuation hypothesis follows from exactly two
numerical conditions:

* on the fixed divisor support, the visible real reserve pays the uniform
  bank bound;
* off that support, the cross-multiplied natural tail capacity pays the same
  uniform bank bound.
-/
theorem precharge_lowPrime_factorization_le_centralTailProduct
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hendpoint :
      upperEndpoint n (upperTailLength c n) ≤ 3 * n)
    (hfixedReserve : ∀ p ∈ primesUpTo (2 * depth + 1),
      ((bankPaperAnchorMarkerBudget n *
          Nat.log2 (3 * n) : ℕ) : ℝ) ≤
        (c - C0) / (6 * (((p - 1 : ℕ) : ℝ))) *
          secondOrderScale n)
    (huniformCapacity : ∀ p, p.Prime → p ≤ yNat n →
      p ∉ primesUpTo (2 * depth + 1) →
        (p - 1) *
            (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
              Nat.log2 (upperTailLength c n) + 1) ≤
          upperTailLength c n) :
    ∀ p, p.Prime → p ≤ yNat n →
      (centralAnchorDivisor n (centralAnchorCutoff depth n)
          certificate.q).factorization p +
        (R.prechargeBaseStateProduct).factorization p ≤
      (centralTailProduct n
        (upperTailLength c n)).factorization p := by
  intro p hp hpCutoff
  by_cases hpSupport : p ∈ primesUpTo (2 * depth + 1)
  · have hbank :=
      R.prechargeBaseStateProduct_factorization_le_anchorMarkerBudget_log2_three_mul
        hp hendpoint
    have hbankReal :
        ((R.prechargeBaseStateProduct).factorization p : ℝ) ≤
          ((bankPaperAnchorMarkerBudget n *
            Nat.log2 (3 * n) : ℕ) : ℝ) := by
      exact_mod_cast hbank
    have hbankReserve :
        ((R.prechargeBaseStateProduct).factorization p : ℝ) ≤
          (c - C0) / (6 * (((p - 1 : ℕ) : ℝ))) *
            secondOrderScale n :=
      hbankReal.trans (hfixedReserve p hpSupport)
    have hcombined :
        (((centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q).factorization p +
            (R.prechargeBaseStateProduct).factorization p : ℕ) : ℝ) ≤
          (upperTailValuation c n p : ℝ) := by
      rw [Nat.cast_add]
      calc
        ((centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q).factorization p : ℝ) +
            ((R.prechargeBaseStateProduct).factorization p : ℝ) ≤
            ((centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q).factorization p : ℝ) +
              ((c - C0) / (6 * (((p - 1 : ℕ) : ℝ))) *
                secondOrderScale n) := by
          linarith
        _ = (c - C0) / (6 * (((p - 1 : ℕ) : ℝ))) *
                secondOrderScale n +
              ((centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q).factorization p : ℝ) := by ring
        _ ≤ (upperTailValuation c n p : ℝ) :=
          certificate.divisor_reserve p hpSupport
    rw [← upperTailValuation_eq_centralTailProduct_factorization]
    exact_mod_cast hcombined
  · have hdivisorZero :
        (centralAnchorDivisor n (centralAnchorCutoff depth n)
          certificate.q).factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hpDvd
      exact hpSupport
        (certificate.divisor_prime_support p hp hpDvd)
    rw [hdivisorZero, zero_add]
    exact
      (R.prechargeBaseStateProduct_factorization_le_anchorMarkerBudget_log2_three_mul
          hp hendpoint).trans
        (centralTailProduct_factorization_ge_of_cross_capacity hp
          (huniformCapacity p hp hpCutoff hpSupport))

/-- Consequently the guarded anchor divisor times the actual precharged base
product divides the literal upper-tail product.  The only analytic inputs are
the displayed fixed-support real reserve and off-support natural capacity. -/
theorem mul_prechargeBaseStateProduct_dvd_centralTailProduct_of_capacity
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hsupportCutoff : 2 * depth + 1 ≤ yNat n)
    (hendpoint :
      upperEndpoint n (upperTailLength c n) ≤ 3 * n)
    (hfixedReserve : ∀ p ∈ primesUpTo (2 * depth + 1),
      ((bankPaperAnchorMarkerBudget n *
          Nat.log2 (3 * n) : ℕ) : ℝ) ≤
        (c - C0) / (6 * (((p - 1 : ℕ) : ℝ))) *
          secondOrderScale n)
    (huniformCapacity : ∀ p, p.Prime → p ≤ yNat n →
      p ∉ primesUpTo (2 * depth + 1) →
        (p - 1) *
            (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
              Nat.log2 (upperTailLength c n) + 1) ≤
          upperTailLength c n) :
    centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q *
        R.prechargeBaseStateProduct ∣
      centralTailProduct n (upperTailLength c n) := by
  apply certificate.mul_prechargeBaseStateProduct_dvd_centralTailProduct
    R hsupportCutoff
  exact certificate.precharge_lowPrime_factorization_le_centralTailProduct
    R hendpoint hfixedReserve huniformCapacity

end GuardedCentralAnchorCertificate

end

end Erdos390.WholePaper
