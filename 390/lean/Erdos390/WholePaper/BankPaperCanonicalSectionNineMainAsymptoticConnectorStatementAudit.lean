import Erdos390.WholePaper.BankPaperCanonicalSectionNineMainAsymptoticConnector

/-!
# Statement audit for the Section 9 to main-asymptotic connector

The census covers both output interfaces and all five connector theorems.
The expanded examples pin down the finite eventual payload, the conversion
to the capacity continuation, the literal normalized limit, and the literal
small-`o` target.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Complete public declaration census -/

#check BankPaperCanonicalSectionNineOutputAtDepth
#check bankPaperCanonicalSectionNineOutputAtDepth_to_postTangentContinuation
#check mainNormalizedLimit_of_canonicalSectionNineOutput
#check mainAsymptotic_of_canonicalSectionNineOutput
#check BankPaperCanonicalSharpSectionNineOutput
#check mainNormalizedLimit_of_sharpCanonicalSectionNineOutput
#check mainAsymptotic_of_sharpCanonicalSectionNineOutput

/-! ## Exact finite-output interface -/

example (c : ℝ) (depth : ℕ) :
    BankPaperCanonicalSectionNineOutputAtDepth c depth =
      (∀ᶠ n : ℕ in atTop,
        ∀ (R : BankPaperRealization n
              (upperEndpoint n (upperTailLength c n)))
          (certificate : GuardedCentralAnchorCertificate c depth n
            R.anchorGuardLeftCore R.anchorGuardRightCore
            (R.centralChangedMarkers depth)),
          (centralAnchorDivisor n (centralAnchorCutoff depth n)
                  certificate.q * R.prechargeBaseStateProduct ∣
              centralTailProduct n (upperTailLength c n)) →
          ((baseBankFactors R.exactificationState).prod id ∣
              certificate.prechargedTailTarget) →
          (certificate.prechargedTailTarget *
                centralAnchorDivisor n (centralAnchorCutoff depth n)
                  certificate.q =
              centralTailProduct n (upperTailLength c n)) →
          ∃ candidates fixed : Finset ℕ,
            ∃ _output : BankPaperCanonicalPostTangentOutput
                R certificate candidates fixed,
              candidates ⊆
                  factorInterval n
                    (upperEndpoint n (upperTailLength c n)) ∧
              fixed ⊆
                  factorInterval n
                    (upperEndpoint n (upperTailLength c n)) ∧
              R.selectorTailCharge fixed ∣
                  certificate.prechargedTailTarget ∧
              Disjoint fixed candidates ∧
              (∀ slot selected,
                Disjoint fixed
                  (R.exactificationState slot selected)) ∧
              (∀ slot selected,
                Disjoint candidates
                  (R.exactificationState slot selected)) ∧
              Disjoint certificate.anchors fixed ∧
              Disjoint certificate.anchors candidates) := by
  rfl

example {c : ℝ} {depth : ℕ}
    (houtput : BankPaperCanonicalSectionNineOutputAtDepth c depth) :
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
              ∃ candidates : Finset ℕ, ∃ selector : ℕ → ℝ,
                ∃ fixed : Finset ℕ,
                  candidates ⊆
                      factorInterval n
                        (upperEndpoint n (upperTailLength c n)) ∧
                  fixed ⊆
                      factorInterval n
                        (upperEndpoint n (upperTailLength c n)) ∧
                  (∀ a ∈ candidates,
                    0 ≤ selector a ∧ selector a ≤ 1) ∧
                  (∀ label ∈
                      completeRoughLabelSet (yNat n) candidates,
                    ∃ k : ℤ,
                      ∑ a ∈ completeRoughRowFiber
                          (yNat n) candidates label,
                            selector a = (k : ℝ)) ∧
                  R.selectorTailCharge fixed ∣
                    certificate.prechargedTailTarget ∧
                  (∀ q,
                    ∑ a ∈ candidates,
                        selector a * (a.factorization q : ℝ) =
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
                  Disjoint certificate.anchors candidates) := by
  simpa only [BankPaperCanonicalPostTangentContinuationAtDepth] using
    bankPaperCanonicalSectionNineOutputAtDepth_to_postTangentContinuation
      houtput

/-! ## Direct exact main targets -/

example
    (houtput : ∀ c : ℝ,
      ((4029639598 : ℝ) / 25970038185) < c →
        ∀ depth : ℕ, 201 ≤ depth →
          BankPaperCanonicalSectionNineOutputAtDepth c depth) :
    Tendsto
      (fun n : ℕ =>
        (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) / (n : ℝ))
      atTop (nhds ((4029639598 : ℝ) / 25970038185)) := by
  have houtput' : ∀ c : ℝ, C0 < c →
      ∀ depth : ℕ, 201 ≤ depth →
        BankPaperCanonicalSectionNineOutputAtDepth c depth := by
    intro c hc depth hdepth
    exact houtput c (by simpa only [C0] using hc) depth hdepth
  simpa only [MainNormalizedLimit, C0] using
    mainNormalizedLimit_of_canonicalSectionNineOutput houtput'

example
    (houtput : ∀ c : ℝ,
      ((4029639598 : ℝ) / 25970038185) < c →
        ∀ depth : ℕ, 201 ≤ depth →
          BankPaperCanonicalSectionNineOutputAtDepth c depth) :
    (fun n : ℕ =>
        (f n : ℝ) -
          (2 * (n : ℝ) +
            ((4029639598 : ℝ) / 25970038185) *
              ((n : ℝ) / Real.log (n : ℝ))))
      =o[atTop]
        (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
  have houtput' : ∀ c : ℝ, C0 < c →
      ∀ depth : ℕ, 201 ≤ depth →
        BankPaperCanonicalSectionNineOutputAtDepth c depth := by
    intro c hc depth hdepth
    exact houtput c (by simpa only [C0] using hc) depth hdepth
  simpa only [MainAsymptotic, mainError, C0, secondOrderScale] using
    mainAsymptotic_of_canonicalSectionNineOutput houtput'

/-! ## Closed sharp specialization -/

example :
    BankPaperCanonicalSharpSectionNineOutput =
      (RoughSaiasEndpointApproximationUpToFive
          (roughSaiasInvLogSqEndpointRate roughSaiasSharpDefectConstant)
          (roughSaiasInvLogSqEndpointCutoff roughSaiasSharpDefectCutoff) →
        ∀ c : ℝ, C0 < c →
          ∀ depth : ℕ, 201 ≤ depth →
            BankPaperCanonicalSectionNineOutputAtDepth c depth) := by
  rfl

example (houtput : BankPaperCanonicalSharpSectionNineOutput) :
    Tendsto
      (fun n : ℕ =>
        (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) / (n : ℝ))
      atTop (nhds ((4029639598 : ℝ) / 25970038185)) := by
  simpa only [MainNormalizedLimit, C0] using
    mainNormalizedLimit_of_sharpCanonicalSectionNineOutput houtput

example (houtput : BankPaperCanonicalSharpSectionNineOutput) :
    (fun n : ℕ =>
        (f n : ℝ) -
          (2 * (n : ℝ) +
            ((4029639598 : ℝ) / 25970038185) *
              ((n : ℝ) / Real.log (n : ℝ))))
      =o[atTop]
        (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
  simpa only [MainAsymptotic, mainError, C0, secondOrderScale] using
    mainAsymptotic_of_sharpCanonicalSectionNineOutput houtput

end

end Erdos390.WholePaper
