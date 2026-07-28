import Erdos390.WholePaper.BankPaperPrechargedTailTarget

/-! # Expanded statement audit for the precharged residual target -/

namespace Erdos390.WholePaper

noncomputable section

example {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    certificate.prechargedTailTarget =
      centralTailProduct n (upperTailLength c n) /
        centralAnchorDivisor n (centralAnchorCutoff depth n)
          certificate.q :=
  rfl

example {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    0 < certificate.prechargedTailTarget ∧
      certificate.prechargedTailTarget *
          centralAnchorDivisor n (centralAnchorCutoff depth n)
            certificate.q =
        centralTailProduct n (upperTailLength c n) :=
  ⟨certificate.prechargedTailTarget_pos,
    certificate.prechargedTailTarget_mul_centralAnchorDivisor⟩

example {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hcombined :
      centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q *
          R.prechargeBaseStateProduct ∣
        centralTailProduct n (upperTailLength c n)) :
    R.prechargeBaseStateProduct ∣ certificate.prechargedTailTarget ∧
      (baseBankFactors R.exactificationState).prod id ∣
        certificate.prechargedTailTarget :=
  ⟨certificate.prechargeBaseStateProduct_dvd_prechargedTailTarget
      R hcombined,
    certificate.baseExactificationBank_prod_dvd_prechargedTailTarget
      R hcombined⟩

end

end Erdos390.WholePaper
