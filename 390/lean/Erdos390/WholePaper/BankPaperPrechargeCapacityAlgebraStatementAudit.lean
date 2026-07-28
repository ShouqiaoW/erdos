import Erdos390.WholePaper.BankPaperPrechargeCapacityAlgebra

/-! # Expanded statement audit for numerical precharge capacity -/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

example {n h p K : ℕ} (hp : p.Prime)
    (hcapacity : (p - 1) * (K + Nat.log2 h + 1) ≤ h) :
    K ≤ (centralTailProduct n h).factorization p :=
  centralTailProduct_factorization_ge_of_cross_capacity hp hcapacity

example {n h p K : ℕ} (hp : p.Prime)
    (hcapacity : (p - 1) * (K + Nat.log2 h + 1) ≤ h) :
    K ≤ ((factorInterval (2 * n) (2 * n + h)).prod id).factorization p := by
  simpa only [centralTailProduct] using
    centralTailProduct_factorization_ge_of_cross_capacity hp hcapacity

example {n M p : ℕ} (R : BankPaperRealization n M)
    (hp : p.Prime) (hendpoint : M ≤ 3 * n) :
    (R.prechargeBaseStateProduct).factorization p ≤
      bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) :=
  R.prechargeBaseStateProduct_factorization_le_anchorMarkerBudget_log2_three_mul
    hp hendpoint

example {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
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
        (upperTailValuation c n p : ℝ) :=
  certificate.precharge_fixedSupport_factorization_add_retainedReserve_le_upperTailValuation
    R hendpoint spent retained hbankSpent hreserveSplit

example {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
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
        (upperTailValuation c n p : ℝ) :=
  certificate.precharge_fixedSupport_factorization_add_twelfthReserve_le_upperTailValuation
    R hendpoint hbankTwelfth

example {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
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
        (upperTailLength c n)).factorization p :=
  certificate.precharge_lowPrime_factorization_le_centralTailProduct
    R hendpoint hfixedReserve huniformCapacity

example {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
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
      centralTailProduct n (upperTailLength c n) :=
  certificate.mul_prechargeBaseStateProduct_dvd_centralTailProduct_of_capacity
    R hsupportCutoff hendpoint hfixedReserve huniformCapacity

end

end Erdos390.WholePaper
