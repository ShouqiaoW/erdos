import Erdos390.WholePaper.BankPaperCanonicalSignedResidualSelectorIdentification

/-!
# Statement audit for exact signed-residual selector identification

The expanded examples expose the two finite facts separately.  The charged
target identity follows from existing product divisibility in the
medium-prime range.  The complete four-sign identity then needs exactly the
named guarded-source reindexing; no final residual equality is hidden in a
package.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BankPaperRealization

#check roughCanonicalRawSignedValuationResidual
#check BankPaperCanonicalSignedResidualTargetLedger
#check BankPaperCanonicalSignedResidualSelectorLedger
#check roughCanonicalNonexceptionalGuardedCandidateSet
#check mem_roughCanonicalNonexceptionalGuardedCandidateSet
#check sum_raw_sub_exceptional_sub_nonexceptionalDeleted_eq_guardedNonexceptional
#check roughCanonicalSourceValuationCorrectionMoment
#check roughCanonicalSourceRawCorrectionValuationDefect
#check bankPaperCanonicalSignedResidualSelectorLedger_iff_correctionMoment_eq_raw
#check bankPaperCanonicalSignedResidualSelectorLedger_iff_sourceRawCorrectionDefect_eq_zero
#check sum_bankPaperConstantPoolCorrection_mul_eq
#check roughCanonicalGuardedPostchargeCorrectionDensity_eq_rawLedger
#check sum_guardedPostchargeRowCorrectedWeight_mul_factorization_eq
#check roughCanonicalAggregateGuardedPostchargeRowCorrection
#check bankPaperCanonicalGlobalCorrectedSourceSelector_apply_of_mem_nonsmoothRow
#check bankPaperCanonicalGlobalCorrectedSourceSelector_apply_of_mem_exceptionalNonsmoothRow
#check paperExceptionalUpperFactors_eq_fixed_union_exceptionalDonors
#check bankPaperCanonicalSignedResidualTargetLedger_of_chargeDvd
#check bankPaperCanonicalSelectorValuationDeficit_eq_completeSignedResidual
#check bankPaperCanonicalSelectorValuationDeficit_eq_completeSignedResidual_sub_sourceDefect
#check bankPaperCanonicalSelectorValuationDeficit_eq_completeSignedResidual_of_chargeDvd
#check bankPaperCanonicalStructuredPreSelector_deficit_eq_completeSignedResidual_sub_moment
#check bankPaperCanonicalStructuredPreSelector_deficit_eq_completeSignedResidual_sub_sourceDefect_sub_moment
#check bankPaperCanonicalStructuredPreSelector_deficit_eq_completeSignedResidual_of_moment_eq_zero
#check roughCanonicalPostHfitCompleteSignedResidual
#check roughCanonicalPostHfitGlobalSourceValuationCorrectionMoment
#check roughCanonicalPostHfitGlobalSourceRawCorrectionValuationDefect
#check BankPaperCanonicalPostHfitSourceToGuardedCorrectionValuationReindex
#check BankPaperCanonicalPostHfitGuardedToRawCorrectionValuationReindex
#check BankPaperCanonicalPostHfitGlobalSourceSignedResidualSelectorLedger
#check bankPaperCanonicalPostHfitGlobalSourceSignedResidualSelectorLedger_iff_correctionMoment_eq_raw
#check bankPaperCanonicalPostHfitGlobalSourceSignedResidualSelectorLedger_of_reindexes
#check bankPaperCanonicalPostHfitStructuredPreSelector_deficit_eq_completeSignedResidual_sub_sourceDefect_sub_moment
#check bankPaperCanonicalPostHfitStructuredPreSelector_deficit_eq_completeSignedResidual_sub_sourceDefect_sub_moment_of_chargeDvd
#check bankPaperCanonicalPostHfitStructuredPreSelector_deficit_eq_completeSignedResidual_sub_moment
#check bankPaperCanonicalPostHfitStructuredPreSelector_deficit_eq_completeSignedResidual_sub_moment_of_chargeDvd
#check bankPaperCanonicalPostHfitStructuredPreSelector_deficit_eq_completeSignedResidual_of_moment_eq_zero

/-- The paper exceptional upper family is literally partitioned into fixed
factors and exceptional designated donors. -/
example
    {n h : Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : Real) :
    paperExceptionalUpperFactors n h deltaStar =
      R.paperFixedExceptionalFactors deltaStar ∪
        R.roughCanonicalExceptionalDonorSet deltaStar :=
  paperExceptionalUpperFactors_eq_fixed_union_exceptionalDonors
    R deltaStar

/-- Expanded charged-target valuation identity. -/
example
    {c : Real} {depth n W p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (hprefix : 2 * depth + 1 <= W)
    (hp : p.Prime) (hWp : W < p)
    (hchargeDvd :
      R.selectorTailCharge (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget) :
    ((certificate.selectorTailTarget R
      (R.paperFixedExceptionalFactors deltaStar)).factorization p : Real) =
        (∑ a ∈ roughUpperBlock n (upperTailLength c n),
          (a.factorization p : Real)) -
        (∑ a ∈ paperExceptionalUpperFactors n
            (upperTailLength c n) deltaStar,
          (a.factorization p : Real)) +
        (∑ a ∈ R.roughCanonicalExceptionalDonorSet deltaStar,
          (a.factorization p : Real)) -
        ∑ a ∈ R.prechargeBaseState, (a.factorization p : Real) := by
  exact bankPaperCanonicalSignedResidualTargetLedger_of_chargeDvd
    (W := W) R certificate deltaStar hprefix hp hWp hchargeDvd

/-- Fully expanded four-sign selector deficit.  The sole new finite input is
the source ledger `hselector`; the target side is derived from divisibility. -/
example
    {c : Real} {depth n W K p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (selector : Nat -> Real)
    (hprefix : 2 * depth + 1 <= W)
    (hp : p.Prime) (hWp : W < p)
    (hchargeDvd :
      R.selectorTailCharge (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget)
    (hselector : BankPaperCanonicalSignedResidualSelectorLedger
      (W := W) (K := K)
        R certificate deltaStar alpha beta ell selector p) :
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        selector p =
      ((∑ a ∈ roughUpperBlock n (upperTailLength c n),
          (a.factorization p : Real)) -
        ∑ a ∈ roughRawCandidateSet n (upperTailLength c n) K,
          roughHeadCompatibleRawWeight W n (upperTailLength c n) K
              alpha beta ell a * (a.factorization p : Real)) -
      ((∑ a ∈ paperExceptionalUpperFactors n
            (upperTailLength c n) deltaStar,
          (a.factorization p : Real)) -
        ∑ a ∈ roughCanonicalExceptionalRawLowerSet n
            (upperTailLength c n) K deltaStar,
          roughHeadCompatibleRawWeight W n (upperTailLength c n) K
              alpha beta ell a * (a.factorization p : Real)) -
      roughCanonicalAggregateRawRowCorrection W n
        (upperTailLength c n) K deltaStar alpha beta ell p +
      ((∑ a ∈ R.roughCanonicalNonexceptionalGuardDeletedSet certificate
            deltaStar K,
          roughHeadCompatibleRawWeight W n (upperTailLength c n) K
              alpha beta ell a * (a.factorization p : Real)) +
        (∑ a ∈ R.roughCanonicalExceptionalDonorSet deltaStar,
          (a.factorization p : Real)) -
        ∑ a ∈ R.prechargeBaseState, (a.factorization p : Real)) := by
  simpa only [roughCanonicalCompleteSignedResidual,
    roughCanonicalRawSignedValuationResidual,
    roughCanonicalSignedExceptionalResidual,
    roughCanonicalAggregateGuardResidual] using
    (bankPaperCanonicalSelectorValuationDeficit_eq_completeSignedResidual_of_chargeDvd
      (W := W) R certificate deltaStar alpha beta ell selector
        hprefix hp hWp hchargeDvd hselector)

/-- Expanded form of the exact remaining finite equality.  It compares the
actual source correction moment to the raw-pool correction moment; row
integrality alone does not state this weighted identity. -/
example
    {c : Real} {depth n W K p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (selector : Nat -> Real) :
    BankPaperCanonicalSignedResidualSelectorLedger
        (W := W) (K := K)
        R certificate deltaStar alpha beta ell selector p ↔
      (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
          selector a * (a.factorization p : Real)) -
        (∑ a ∈
            R.roughCanonicalNonexceptionalGuardedCandidateSet certificate
              deltaStar K,
          roughHeadCompatibleRawWeight W n (upperTailLength c n) K
              alpha beta ell a * (a.factorization p : Real)) =
        roughCanonicalAggregateRawRowCorrection W n
          (upperTailLength c n) K deltaStar alpha beta ell p := by
  simpa only [roughCanonicalSourceValuationCorrectionMoment] using
    (bankPaperCanonicalSignedResidualSelectorLedger_iff_correctionMoment_eq_raw
      (W := W) (K := K)
      R certificate deltaStar alpha beta ell selector p)

end BankPaperRealization

end

end Erdos390.WholePaper
