import Erdos390.WholePaper.BankPaperPrechargeDivisibilityAlgebra
import Erdos390.WholePaper.BankPaperPrechargeExactificationBridge

/-!
# The residual target after the guarded anchor charge

This file names the exact natural-number target passed to fractional
selection and guarded exactification.  Combined divisibility of the guarded
anchor divisor and the precharged bank immediately shows that the generic
exactification base product divides this target.  The final multiplication
identity is division-free.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace GuardedCentralAnchorCertificate

/-- The literal factorial-tail quotient remaining after charging the guarded
central-anchor divisor. -/
def prechargedTailTarget
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) : ℕ :=
  centralTailProduct n (upperTailLength c n) /
    centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q

/-- The quotient target is positive. -/
theorem prechargedTailTarget_pos
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    0 < certificate.prechargedTailTarget := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd
      (centralTailProduct_pos n (upperTailLength c n))
      certificate.divisor_dvd_tail
  · exact centralAnchorDivisor_pos certificate.isCofactorChoice

/-- Division-free target identity used by final product assembly. -/
theorem prechargedTailTarget_mul_centralAnchorDivisor
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    certificate.prechargedTailTarget *
        centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q =
      centralTailProduct n (upperTailLength c n) := by
  exact Nat.div_mul_cancel certificate.divisor_dvd_tail

/-- A simultaneous `divisor * bank` charge makes the actual precharge
product divide the residual target. -/
theorem prechargeBaseStateProduct_dvd_prechargedTailTarget
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hcombined :
      centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q *
          R.prechargeBaseStateProduct ∣
        centralTailProduct n (upperTailLength c n)) :
    R.prechargeBaseStateProduct ∣ certificate.prechargedTailTarget := by
  exact (Nat.dvd_div_iff_mul_dvd certificate.divisor_dvd_tail).2 hcombined

/-- The exact same divisibility in the generic exactification notation. -/
theorem baseExactificationBank_prod_dvd_prechargedTailTarget
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hcombined :
      centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q *
          R.prechargeBaseStateProduct ∣
        centralTailProduct n (upperTailLength c n)) :
    (baseBankFactors R.exactificationState).prod id ∣
      certificate.prechargedTailTarget := by
  rw [R.baseExactificationBank_prod_eq_prechargeBaseStateProduct]
  exact certificate.prechargeBaseStateProduct_dvd_prechargedTailTarget
    R hcombined

end GuardedCentralAnchorCertificate

end

end Erdos390.WholePaper
