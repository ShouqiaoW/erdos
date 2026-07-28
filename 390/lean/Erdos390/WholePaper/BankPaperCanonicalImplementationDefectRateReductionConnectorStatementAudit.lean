import Erdos390.WholePaper.BankPaperCanonicalImplementationDefectRateReductionConnector

/-!
# Statement audit for the two implementation-defect reductions

The source-to-guarded term is reduced to one smooth-row defect.  The
guarded/raw term is reduced to the exact rowwise pool-moment and numerator
shifts, with the finite guard census and pool-denominator wrappers visible.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

#check roughCanonicalSourceGuardedRowValuationDefectAtLabel
#check completeRoughRowFiber_nonexceptionalGuarded_eq_guardedRow
#check completeRoughRowFiber_nonexceptionalGuarded_eq_empty
#check roughCanonicalSourceValuationCorrectionMoment_sub_guardedCorrection_eq_sum_rowDefects
#check roughCanonicalPostHfitSourceGuardedRowValuationDefectAtLabel
#check roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect_eq_sum_rowDefects
#check roughCanonicalPostHfitSourceGuardedRowValuationDefectAtLabel_eq_zero_of_active
#check roughCanonicalPostHfitSourceGuardedRowValuationDefectAtLabel_eq_zero_of_exceptional
#check roughCanonicalPostHfitSmoothSourceToGuardedValuationDefect
#check roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect_eq_smooth
#check RoughCanonicalPostHfitSmoothSourceToGuardedValuationDefectBound
#check abs_roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect_le_of_smooth

#check roughCanonicalBroadCorrectionPoolGuardDeleted
#check roughCanonicalBroadCorrectionPoolGuardDeleted_card_le_three
#check roughCanonicalGuardedRawPoolValuationMomentCrossNumerator
#check roughCanonicalGuardedRawPoolValuationMomentCrossNumerator_eq_deleted
#check roughCanonicalGuardedNormalizedValuationMoment_sub_raw_eq_crossNumerator_div
#check roughCanonicalRaw_and_guardedBroadCorrectionPool_card_ne_zero_of_linear_lower
#check roughCanonicalGuardedRawRowCorrectionValuationMajorantAtLabel
#check roughCanonicalGuardedRawRowCorrectionValuationMajorantAtLabel_eq_crossNumerator
#check abs_roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel_le_majorant
#check abs_roughCanonicalAggregateGuardedRawCorrectionValuationDefect_le_rowwiseMajorant
#check RoughCanonicalGuardedRawCorrectionValuationRowwiseBound
#check RoughCanonicalGuardedRawPoolMomentChangeContributionBound
#check RoughCanonicalGuardedRawNumeratorShiftContributionBound
#check abs_roughCanonicalAggregateGuardedRawCorrectionValuationDefect_le_of_splitContributions
#check abs_roughCanonicalAggregateGuardedRawCorrectionValuationDefect_le_of_rowwise
#check abs_roughCanonicalGuardedPostchargeRawNumeratorShift_le_fixed

#check BankPaperCanonicalPostHfitTwoImplementationDefectRateInputs
#check bankPaperCanonicalPostHfitMediumPrimeImplementationRateInputs_of_defectReductions
#check eventually_bankPaperCanonicalPostHfitMediumPrimeImplementationRateInputs_of_defectReductions

/-- The guarded/raw public input contains the two terms from the exact row
formula and no hidden reindex assertion. -/
example
    {c : Real} {depth n W K p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell bound : Real)
    (hrow :
      RoughCanonicalGuardedRawCorrectionValuationRowwiseBound
        R certificate deltaStar W K alpha beta ell p bound) :
    abs
      (R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect
        certificate deltaStar W K alpha beta ell p) <= bound :=
  R.abs_roughCanonicalAggregateGuardedRawCorrectionValuationDefect_le_of_rowwise
    certificate deltaStar alpha beta ell bound hrow

/-- The finite guard ledger already supplies the complete numerator-shift
loss; the remaining guarded/raw input is genuinely a pool-moment estimate. -/
example
    {c : Real} {depth n W K label : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell M : Real)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hactive : RoughCanonicalActiveNonexceptionalLabel n deltaStar label)
    (hM : 0 <= M)
    (hweight :
      ∀ a ∈ completeRoughRowFiber (yNat n)
          (roughRawCandidateSet n (upperTailLength c n) K) label,
        abs
          (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell a) <= M) :
    abs
      (R.roughCanonicalGuardedPostchargeRawNumeratorShift certificate
        deltaStar K label
        (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
          alpha beta ell)) <= 1 + 3 * M :=
  R.abs_roughCanonicalGuardedPostchargeRawNumeratorShift_le_fixed
    certificate deltaStar alpha beta ell M hnCutoff hyCutoff hactive hM
      hweight

end BankPaperRealization

end

end Erdos390.WholePaper
