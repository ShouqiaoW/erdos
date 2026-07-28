import Erdos390.WholePaper.BankPaperPrechargeCapacityEventually

namespace Erdos390.WholePaper

open Filter Topology

noncomputable section

example {c : ℝ} (hc : C0 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ bank : BankPaperRealization n
            (upperEndpoint n (upperTailLength c n)),
          ∃ certificate : GuardedCentralAnchorCertificate c depth n
              bank.anchorGuardLeftCore bank.anchorGuardRightCore
              (bank.centralChangedMarkers depth),
            centralAnchorDivisor n (centralAnchorCutoff depth n)
                  certificate.q * bank.prechargeBaseStateProduct ∣
                centralTailProduct n (upperTailLength c n) ∧
              (baseBankFactors bank.exactificationState).prod id ∣
                certificate.prechargedTailTarget ∧
              certificate.prechargedTailTarget *
                  centralAnchorDivisor n (centralAnchorCutoff depth n)
                    certificate.q =
                centralTailProduct n (upperTailLength c n) :=
  exists_eventually_bankPaperPrechargedTailTarget hc

example {c : ℝ} {depth n p : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ} {retained : ℝ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (bank : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hretained :
      retained +
          (((centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q).factorization p +
            bank.prechargeBaseStateProduct.factorization p : ℕ) : ℝ) ≤
        (upperTailValuation c n p : ℝ)) :
    retained +
        (bank.prechargeBaseStateProduct.factorization p : ℝ) ≤
      (certificate.prechargedTailTarget.factorization p : ℝ) :=
  certificate.prechargeBaseStateProduct_factorization_add_retained_le_prechargedTailTarget
    bank hretained

example {c : ℝ} (hc : C0 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ bank : BankPaperRealization n
            (upperEndpoint n (upperTailLength c n)),
          ∃ certificate : GuardedCentralAnchorCertificate c depth n
              bank.anchorGuardLeftCore bank.anchorGuardRightCore
              (bank.centralChangedMarkers depth),
            centralAnchorDivisor n (centralAnchorCutoff depth n)
                  certificate.q * bank.prechargeBaseStateProduct ∣
                centralTailProduct n (upperTailLength c n) ∧
              (∀ p ∈ primesUpTo (2 * depth + 1),
                (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
                      secondOrderScale n +
                    (((centralAnchorDivisor n (centralAnchorCutoff depth n)
                          certificate.q).factorization p +
                      bank.prechargeBaseStateProduct.factorization p : ℕ) : ℝ) ≤
                  (upperTailValuation c n p : ℝ)) ∧
              (∀ p ∈ primesUpTo (2 * depth + 1),
                (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
                      secondOrderScale n +
                    (bank.prechargeBaseStateProduct.factorization p : ℝ) ≤
                  (certificate.prechargedTailTarget.factorization p : ℝ)) ∧
              (baseBankFactors bank.exactificationState).prod id ∣
                certificate.prechargedTailTarget ∧
              certificate.prechargedTailTarget *
                  centralAnchorDivisor n (centralAnchorCutoff depth n)
                    certificate.q =
                centralTailProduct n (upperTailLength c n) :=
  exists_eventually_bankPaperPrechargedTailTarget_with_twelfthReserve hc

end

end Erdos390.WholePaper
