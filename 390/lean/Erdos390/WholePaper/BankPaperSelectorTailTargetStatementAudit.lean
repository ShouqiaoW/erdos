import Erdos390.WholePaper.BankPaperSelectorTailTarget

/-! # Expanded statement audit for the residual selector target -/

namespace Erdos390.WholePaper

noncomputable section

example {n M : ℕ} (R : BankPaperRealization n M)
    (fixed : Finset ℕ)
    (hfixedPositive : ∀ a ∈ fixed, 0 < a) :
    fixed.prod id * (baseBankFactors R.exactificationState).prod id =
        fixed.prod id * R.prechargeBaseStateProduct ∧
      0 < fixed.prod id *
        (baseBankFactors R.exactificationState).prod id := by
  constructor
  · simpa only [BankPaperRealization.selectorTailCharge] using
      R.selectorTailCharge_eq_fixed_mul_prechargeBaseStateProduct fixed
  · simpa only [BankPaperRealization.selectorTailCharge] using
      R.selectorTailCharge_pos fixed hfixedPositive

example {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (fixed : Finset ℕ)
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd :
      fixed.prod id * (baseBankFactors R.exactificationState).prod id ∣
        certificate.prechargedTailTarget) :
    0 < certificate.prechargedTailTarget /
        (fixed.prod id *
          (baseBankFactors R.exactificationState).prod id) ∧
      (certificate.prechargedTailTarget /
          (fixed.prod id *
            (baseBankFactors R.exactificationState).prod id)) *
          (fixed.prod id *
            (baseBankFactors R.exactificationState).prod id) =
        certificate.prechargedTailTarget ∧
      ∀ q,
        (certificate.prechargedTailTarget /
            (fixed.prod id *
              (baseBankFactors R.exactificationState).prod id)).factorization q =
          certificate.prechargedTailTarget.factorization q -
            (fixed.prod id *
              (baseBankFactors R.exactificationState).prod id).factorization q := by
  have hchargeDvd' : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget := by
    simpa only [BankPaperRealization.selectorTailCharge] using hchargeDvd
  constructor
  · simpa only [GuardedCentralAnchorCertificate.selectorTailTarget,
      BankPaperRealization.selectorTailCharge] using
      certificate.selectorTailTarget_pos R fixed hfixedPositive hchargeDvd'
  · constructor
    · simpa only [GuardedCentralAnchorCertificate.selectorTailTarget,
        BankPaperRealization.selectorTailCharge] using
        certificate.selectorTailTarget_mul_selectorTailCharge
          R fixed hchargeDvd'
    · intro q
      simpa only [GuardedCentralAnchorCertificate.selectorTailTarget,
        BankPaperRealization.selectorTailCharge] using
        certificate.selectorTailTarget_factorization_eq_sub
          R fixed hchargeDvd' q

example {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (fixed : Finset ℕ) (weighted : ℕ → ℝ)
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd :
      fixed.prod id * (baseBankFactors R.exactificationState).prod id ∣
        certificate.prechargedTailTarget) :
    (∀ q,
      ((fixed.prod id *
          (baseBankFactors R.exactificationState).prod id).factorization q :
            ℝ) + weighted q =
        (certificate.prechargedTailTarget.factorization q : ℝ)) ↔
      (∀ q, weighted q =
        ((certificate.prechargedTailTarget /
          (fixed.prod id *
            (baseBankFactors R.exactificationState).prod id)).factorization q :
              ℝ)) := by
  have hchargeDvd' : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget := by
    simpa only [BankPaperRealization.selectorTailCharge] using hchargeDvd
  simpa only [GuardedCentralAnchorCertificate.selectorTailTarget,
    BankPaperRealization.selectorTailCharge] using
    certificate.valuationCertificate_iff_selectorTailTarget
      R fixed weighted hfixedPositive hchargeDvd'

end

end Erdos390.WholePaper
