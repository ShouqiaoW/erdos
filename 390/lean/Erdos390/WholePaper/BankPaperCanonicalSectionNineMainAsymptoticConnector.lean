import Erdos390.WholePaper.BankPaperCanonicalSectionNineAssembly
import Erdos390.WholePaper.BankPaperMainAsymptoticReduction
import Erdos390.WholePaper.RoughSaiasSharpCorrectionTarget

/-!
# Section 9 output to the exact main asymptotic

This file closes the previously implicit logical seam between the finite
Section 9 output and the final main-asymptotic reduction.

For an actual capacity-stage bank and guarded anchor certificate,
`BankPaperCanonicalSectionNineOutputAtDepth` asks for the literal
`BankPaperCanonicalPostTangentOutput` together with exactly the interval,
tail-charge divisibility, and collision geometry required by
`canonicalPostTangentContinuationData_of_output`.  Its premises are the
three capacity facts already visible in
`BankPaperCanonicalPostTangentContinuationAtDepth`.

The first connector converts that finite output into the canonical
post-tangent continuation.  The direct terminals then invoke the audited
main-asymptotic reduction.  Finally, the sharp terminals specialize the
formerly conditional defect input to
`roughSaiasSharpReverseNormalFormDefectInvLogSqBound`; their only remaining
premise is a Section 9 output supplier after receiving the corresponding
paper-scale endpoint approximation.  No premise mentions
`MainNormalizedLimit`, `MainAsymptotic`, or an eventual upper bound for `f`.
-/

open Filter

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Literal eventual Section 9 output -/

/-- The exact Section 9 output required for one paper scale and depth.

The supplier sees only actual capacity-stage witnesses and their three
capacity facts.  It returns the finite post-tangent output and the eight
geometric facts which are not fields of that output structure itself. -/
def BankPaperCanonicalSectionNineOutputAtDepth
    (c : ℝ) (depth : ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
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
            Disjoint fixed (R.exactificationState slot selected)) ∧
          (∀ slot selected,
            Disjoint candidates (R.exactificationState slot selected)) ∧
          Disjoint certificate.anchors fixed ∧
          Disjoint certificate.anchors candidates

/-- A literal eventual Section 9 output gives exactly the post-tangent
continuation consumed by the capacity-to-upper-endpoint theorem. -/
theorem bankPaperCanonicalSectionNineOutputAtDepth_to_postTangentContinuation
    {c : ℝ} {depth : ℕ}
    (houtput : BankPaperCanonicalSectionNineOutputAtDepth c depth) :
    BankPaperCanonicalPostTangentContinuationAtDepth c depth := by
  simp only [BankPaperCanonicalSectionNineOutputAtDepth] at houtput
  simp only [BankPaperCanonicalPostTangentContinuationAtDepth]
  intro hcapacity
  filter_upwards [hcapacity, houtput]
      with n hcapacityN houtputN
  obtain ⟨R, certificate, hcombined, hbaseDvd, htargetTail⟩ :=
    hcapacityN
  obtain ⟨candidates, fixed, output, hcandidates, hfixed, hchargeDvd,
      hfixedCandidate, hfixedBank, hcandidateBank, hanchorsFixed,
      hanchorsCandidate⟩ :=
    houtputN R certificate hcombined hbaseDvd htargetTail
  refine ⟨R, certificate, hcombined, hbaseDvd, htargetTail, ?_⟩
  exact R.canonicalPostTangentContinuationData_of_output certificate
    candidates fixed output hcandidates hfixed hchargeDvd hfixedCandidate
    hfixedBank hcandidateBank hanchorsFixed hanchorsCandidate

/-! ## Direct main terminals -/

/-- Section 9 output at every required scale and depth implies the exact
normalized limit. -/
theorem mainNormalizedLimit_of_canonicalSectionNineOutput
    (houtput : ∀ c : ℝ, C0 < c →
      ∀ depth : ℕ, 201 ≤ depth →
        BankPaperCanonicalSectionNineOutputAtDepth c depth) :
    MainNormalizedLimit := by
  apply mainNormalizedLimit_of_canonicalPostTangentContinuation
  intro c hc depth hdepth
  exact bankPaperCanonicalSectionNineOutputAtDepth_to_postTangentContinuation
    (houtput c hc depth hdepth)

/-- Section 9 output at every required scale and depth implies the paper's
literal small-`o` main theorem. -/
theorem mainAsymptotic_of_canonicalSectionNineOutput
    (houtput : ∀ c : ℝ, C0 < c →
      ∀ depth : ℕ, 201 ≤ depth →
        BankPaperCanonicalSectionNineOutputAtDepth c depth) :
    MainAsymptotic := by
  apply mainAsymptotic_of_canonicalPostTangentContinuation
  intro c hc depth hdepth
  exact bankPaperCanonicalSectionNineOutputAtDepth_to_postTangentContinuation
    (houtput c hc depth hdepth)

/-! ## Closed sharp-defect specialization -/

/-- The remaining selector/geometry interface after the sharp Saias
endpoint approximation has been supplied.  Its conclusion is still only
literal finite Section 9 output, not an asymptotic target. -/
def BankPaperCanonicalSharpSectionNineOutput : Prop :=
  RoughSaiasEndpointApproximationUpToFive
      (roughSaiasInvLogSqEndpointRate roughSaiasSharpDefectConstant)
      (roughSaiasInvLogSqEndpointCutoff roughSaiasSharpDefectCutoff) →
    ∀ c : ℝ, C0 < c →
      ∀ depth : ℕ, 201 ≤ depth →
        BankPaperCanonicalSectionNineOutputAtDepth c depth

/-- The fully closed sharp reverse-normal-form defect, followed by literal
Section 9 output, implies the exact normalized main limit. -/
theorem mainNormalizedLimit_of_sharpCanonicalSectionNineOutput
    (houtput : BankPaperCanonicalSharpSectionNineOutput) :
    MainNormalizedLimit := by
  have hC : 0 ≤ roughSaiasSharpDefectConstant := by
    unfold roughSaiasSharpDefectConstant
    have htheta : 0 ≤ roughSaiasThetaFourthPowerConstant :=
      roughSaiasThetaFourthPowerConstant_pos.le
    positivity
  apply
    mainNormalizedLimit_of_sharpSaiasDefect_and_selectorGeometryContinuation
      hC roughSaiasSharpReverseNormalFormDefectInvLogSqBound
  intro hendpoint c hc depth hdepth
  exact bankPaperCanonicalSectionNineOutputAtDepth_to_postTangentContinuation
    (houtput hendpoint c hc depth hdepth)

/-- The same closed sharp-defect/Section 9 composition with the paper's
literal small-`o` conclusion. -/
theorem mainAsymptotic_of_sharpCanonicalSectionNineOutput
    (houtput : BankPaperCanonicalSharpSectionNineOutput) :
    MainAsymptotic := by
  have hC : 0 ≤ roughSaiasSharpDefectConstant := by
    unfold roughSaiasSharpDefectConstant
    have htheta : 0 ≤ roughSaiasThetaFourthPowerConstant :=
      roughSaiasThetaFourthPowerConstant_pos.le
    positivity
  apply mainAsymptotic_of_sharpSaiasDefect_and_selectorGeometryContinuation
    hC roughSaiasSharpReverseNormalFormDefectInvLogSqBound
  intro hendpoint c hc depth hdepth
  exact bankPaperCanonicalSectionNineOutputAtDepth_to_postTangentContinuation
    (houtput hendpoint c hc depth hdepth)

end

end Erdos390.WholePaper
