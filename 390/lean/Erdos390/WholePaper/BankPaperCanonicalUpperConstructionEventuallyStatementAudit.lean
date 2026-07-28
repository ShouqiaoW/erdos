import Erdos390.WholePaper.BankPaperCanonicalUpperConstructionEventually

/-! # Expanded statement audit for the eventual canonical upper connector -/

open scoped BigOperators
open Filter

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

example {c : ℝ} {depth : ℕ} :
    BankPaperCanonicalPostTangentContinuationAtDepth c depth =
      ((∀ᶠ n : ℕ in atTop,
          ∃ R : BankPaperRealization n
              (upperEndpoint n (upperTailLength c n)),
            ∃ certificate : GuardedCentralAnchorCertificate c depth n
                R.anchorGuardLeftCore R.anchorGuardRightCore
                (R.centralChangedMarkers depth),
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                    certificate.q * R.prechargeBaseStateProduct ∣
                  centralTailProduct n (upperTailLength c n) ∧
                (baseBankFactors R.exactificationState).prod id ∣
                  certificate.prechargedTailTarget ∧
                certificate.prechargedTailTarget *
                    centralAnchorDivisor n (centralAnchorCutoff depth n)
                      certificate.q =
                  centralTailProduct n (upperTailLength c n)) →
        ∀ᶠ n : ℕ in atTop,
          ∃ R : BankPaperRealization n
              (upperEndpoint n (upperTailLength c n)),
            ∃ certificate : GuardedCentralAnchorCertificate c depth n
                R.anchorGuardLeftCore R.anchorGuardRightCore
                (R.centralChangedMarkers depth),
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                    certificate.q * R.prechargeBaseStateProduct ∣
                  centralTailProduct n (upperTailLength c n) ∧
                (baseBankFactors R.exactificationState).prod id ∣
                  certificate.prechargedTailTarget ∧
                certificate.prechargedTailTarget *
                    centralAnchorDivisor n (centralAnchorCutoff depth n)
                      certificate.q =
                  centralTailProduct n (upperTailLength c n) ∧
                ∃ candidates : Finset ℕ, ∃ x : ℕ → ℝ,
                  ∃ fixed : Finset ℕ,
                    candidates ⊆
                        factorInterval n
                          (upperEndpoint n (upperTailLength c n)) ∧
                    fixed ⊆
                        factorInterval n
                          (upperEndpoint n (upperTailLength c n)) ∧
                    (∀ a ∈ candidates, 0 ≤ x a ∧ x a ≤ 1) ∧
                    (∀ label ∈
                        completeRoughLabelSet (yNat n) candidates,
                      ∃ k : ℤ,
                        ∑ a ∈ completeRoughRowFiber
                            (yNat n) candidates label, x a = (k : ℝ)) ∧
                    R.selectorTailCharge fixed ∣
                      certificate.prechargedTailTarget ∧
                    (∀ q,
                      ∑ a ∈ candidates,
                          x a * (a.factorization q : ℝ) =
                        ((certificate.selectorTailTarget R fixed).factorization q :
                          ℝ)) ∧
                    Disjoint fixed candidates ∧
                    (∀ slot selected,
                      Disjoint fixed
                        (R.exactificationState slot selected)) ∧
                    (∀ slot selected,
                      Disjoint candidates
                        (R.exactificationState slot selected)) ∧
                    Disjoint certificate.anchors fixed ∧
                    Disjoint certificate.anchors candidates) := rfl

example {c : ℝ} (hc : C0 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      (BankPaperCanonicalPostTangentContinuationAtDepth c depth →
        ∀ᶠ n : ℕ in atTop,
          f n ≤ upperEndpoint n (upperTailLength c n)) :=
  exists_depth_bankPaper_f_le_upperEndpoint_of_canonicalPostTangentContinuation
    hc

example
    {c : ℝ} (hc : C0 < c)
    (hcontinuation :
      ∀ depth : ℕ, 201 ≤ depth →
        ∀ᶠ n : ℕ in atTop,
          ∀ (R : BankPaperRealization n
                (upperEndpoint n (upperTailLength c n)))
            (certificate : GuardedCentralAnchorCertificate c depth n
              R.anchorGuardLeftCore R.anchorGuardRightCore
              (R.centralChangedMarkers depth)),
            (hcombined :
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                    certificate.q * R.prechargeBaseStateProduct ∣
                centralTailProduct n (upperTailLength c n)) →
            (hbaseDvd :
              (baseBankFactors R.exactificationState).prod id ∣
                certificate.prechargedTailTarget) →
            (htargetTail :
              certificate.prechargedTailTarget *
                    centralAnchorDivisor n
                      (centralAnchorCutoff depth n) certificate.q =
                centralTailProduct n (upperTailLength c n)) →
            ∃ candidates : Finset ℕ, ∃ x : ℕ → ℝ,
              ∃ fixed : Finset ℕ,
                candidates ⊆
                    factorInterval n
                      (upperEndpoint n (upperTailLength c n)) ∧
                fixed ⊆
                    factorInterval n
                      (upperEndpoint n (upperTailLength c n)) ∧
                (∀ a ∈ candidates, 0 ≤ x a ∧ x a ≤ 1) ∧
                (∀ label ∈ completeRoughLabelSet (yNat n) candidates,
                  ∃ k : ℤ,
                    ∑ a ∈ completeRoughRowFiber
                        (yNat n) candidates label, x a = (k : ℝ)) ∧
                R.selectorTailCharge fixed ∣
                  certificate.prechargedTailTarget ∧
                (∀ q,
                  ∑ a ∈ candidates,
                      x a * (a.factorization q : ℝ) =
                    ((certificate.selectorTailTarget R fixed).factorization q :
                      ℝ)) ∧
                Disjoint fixed candidates ∧
                (∀ slot selected,
                  Disjoint fixed (R.exactificationState slot selected)) ∧
                (∀ slot selected,
                  Disjoint candidates
                    (R.exactificationState slot selected)) ∧
                Disjoint certificate.anchors fixed ∧
                Disjoint certificate.anchors candidates) :
    ∀ᶠ n : ℕ in atTop,
      f n ≤ upperEndpoint n (upperTailLength c n) :=
  eventually_bankPaper_f_le_upperEndpoint_of_canonicalPostTangentContinuation
    hc hcontinuation

end

end Erdos390.WholePaper
