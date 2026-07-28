import Erdos390.WholePaper.BankPaperCanonicalGuardedRawCorrectionMomentDefectConnector

/-!
# Statement audit for the guarded-versus-raw correction-moment defect

The audited interface exposes an unconditional row defect, its aggregate
sum, and the exact equivalence between the previously requested reindex and
vanishing of that defect.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

#check roughCanonicalRawBroadCorrectionPoolNormalizedValuationMoment
#check roughCanonicalGuardedBroadCorrectionPoolNormalizedValuationMoment
#check roughCanonicalGuardedPostchargeRawNumeratorShift
#check roughCanonicalGuardedPostchargeRawNumeratorShift_eq_of_active
#check roughCanonicalRawCorrectionDensityAtLabel_eq_rawDiscrepancy_div
#check roughCanonicalGuardedPostchargeCorrectionDensity_eq_rawDiscrepancy_add_shift_div
#check roughCanonicalRawRowCorrectionValuationMomentAtLabel
#check roughCanonicalGuardedPostchargeRowCorrectionValuationMomentAtLabel
#check roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel
#check roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel_eq_explicit
#check roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel_eq_explicit_of_active
#check roughCanonicalAggregateGuardedRawCorrectionValuationDefect
#check roughCanonicalAggregateGuardedRawCorrectionValuationDefect_eq_sum_rowDefects
#check roughCanonicalAggregateGuardedRawCorrectionValuationDefect_eq_sum_explicit
#check roughCanonicalAggregateGuardedRawCorrectionValuationDefect_eq_sum_explicit_active
#check roughCanonicalAggregateGuardedPostchargeRowCorrection_eq_raw_iff_defect_eq_zero
#check bankPaperCanonicalPostHfitGuardedToRawCorrectionValuationReindex_iff_guardedRawDefect_eq_zero
#check roughCanonicalAggregateGuardedRawCorrectionValuationDefect_eq_zero_of_rowwise

/-- The aggregate defect is exactly the sum of the independently visible row
defects; no reindex assumption occurs in the statement. -/
example
    {c : Real} {depth n W K p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real) :
    R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect certificate
        deltaStar W K alpha beta ell p =
      ∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
          (upperTailLength c n) K deltaStar,
        R.roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel
          certificate deltaStar W K label alpha beta ell p :=
  R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect_eq_sum_rowDefects
    certificate deltaStar alpha beta ell

/-- The old exact-reindex request contains no additional algebra: it is
precisely zero aggregate defect. -/
example
    {c : Real} {depth n W K p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real) :
    R.roughCanonicalAggregateGuardedPostchargeRowCorrection certificate
        deltaStar W K alpha beta ell p =
        roughCanonicalAggregateRawRowCorrection W n
          (upperTailLength c n) K deltaStar alpha beta ell p ↔
      R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect certificate
        deltaStar W K alpha beta ell p = 0 :=
  R.roughCanonicalAggregateGuardedPostchargeRowCorrection_eq_raw_iff_defect_eq_zero
    certificate deltaStar alpha beta ell

end BankPaperRealization

end

end Erdos390.WholePaper
