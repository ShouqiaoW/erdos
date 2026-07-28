import Erdos390.WholePaper.BankPaperPrechargeDivisibilityAlgebra

/-! # Expanded statement audit for precharge divisibility algebra -/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

example {D B T cutoff : ℕ}
    (hD : 0 < D) (hB : 0 < B) (hT : 0 < T)
    (hDhigh : ∀ p, p.Prime → cutoff < p → D.factorization p = 0)
    (hlow : ∀ p, p.Prime → p ≤ cutoff →
      D.factorization p + B.factorization p ≤ T.factorization p)
    (hhigh : ∀ p, p.Prime → cutoff < p →
      B.factorization p ≤ T.factorization p) :
    D * B ∣ T :=
  mul_dvd_of_factorization_split hD hB hT hDhigh hlow hhigh

example {D B donor T cutoff : ℕ}
    (hD : 0 < D) (hB : 0 < B) (hdonor : 0 < donor) (hT : 0 < T)
    (hdonorDvd : donor ∣ T)
    (hDhigh : ∀ p, p.Prime → cutoff < p → D.factorization p = 0)
    (hbaseDonor : ∀ p, p.Prime → cutoff < p →
      B.factorization p = donor.factorization p)
    (hlow : ∀ p, p.Prime → p ≤ cutoff →
      D.factorization p + B.factorization p ≤ T.factorization p) :
    D * B ∣ T :=
  mul_dvd_of_factorization_split_with_donor hD hB hdonor hT
    hdonorDvd hDhigh hbaseDonor hlow

example {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hsupportCutoff : 2 * depth + 1 ≤ yNat n)
    (hlow : ∀ p, p.Prime → p ≤ yNat n →
      (centralAnchorDivisor n (centralAnchorCutoff depth n)
          certificate.q).factorization p +
        (R.prechargeBaseStateProduct).factorization p ≤
      (centralTailProduct n
        (upperTailLength c n)).factorization p) :
    centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q *
        R.prechargeBaseStateProduct ∣
      centralTailProduct n (upperTailLength c n) :=
  certificate.mul_prechargeBaseStateProduct_dvd_centralTailProduct
    R hsupportCutoff hlow

end

end Erdos390.WholePaper
