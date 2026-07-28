import Erdos390.WholePaper.BankPaperCanonicalTopFrozenImplementationRateReductionConnector

/-!
# Statement audit for literal frozen-top implementation-rate reductions

This audit makes visible that the source-to-guarded term uses the rounded
frozen-top selector itself, that the guarded/raw input is the existing
rowwise majorant, and that the placement theorem requires an explicit
outside-selector compatibility rather than an equality with the legacy
source.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

#check roughCanonicalPostchargeSourceGuardedRowValuationDefectAtLabel
#check roughCanonicalSourceToGuardedCorrectionValuationDefect_eq_sum_postchargeRowDefects
#check roughCanonicalPostchargeSourceGuardedRowValuationDefectAtLabel_eq_zero_of_active
#check roughCanonicalPostchargeSourceGuardedRowValuationDefectAtLabel_eq_zero_of_exceptional
#check roughCanonicalSmoothSourceToGuardedValuationDefect
#check roughCanonicalSourceToGuardedCorrectionValuationDefect_eq_smooth_of_nonsmooth

#check roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect
#check roughCanonicalTopFrozenRoundedSourceToGuardedCorrectionValuationDefect_eq_smooth
#check RoughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefectBound
#check abs_roughCanonicalTopFrozenRoundedSourceToGuardedCorrectionValuationDefect_le_of_smooth
#check BankPaperCanonicalTopFrozenRoundedTwoImplementationDefectRateInputs
#check bankPaperCanonicalTopFrozenRoundedMediumPrimeImplementationRateInputs_of_defectReductions
#check bankPaperCanonicalTopFrozenRoundedMediumPrimeImplementationRateInputs_of_smooth_aggregateGuardedRaw_and_placement

#check bankPaperCanonicalTwoZeroHeadCellSourceStructuredPlacementValuationMoment_eq
#check abs_bankPaperCanonicalTwoZeroHeadCellSourceStructuredPlacementValuationMoment_le_paperRate
#check BankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility
#check BankPaperCanonicalTopFrozenSmoothTopInvisibleOnStructuredActive
#check bankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility_of_topInvisible
#check bankPaperCanonicalTopFrozenRoundedStructuredPlacementValuationMoment_twoZeroHeadCells_eq
#check abs_bankPaperCanonicalTopFrozenRoundedStructuredPlacementValuationMoment_twoZeroHeadCells_le_paperRate
#check bankPaperCanonicalTopFrozenRoundedMediumPrimeImplementationRateInputs_of_defectReductions_and_twoZeroHeadCellMean

/-- Expanded source audit: the conclusion contains the literal top-frozen
selector in the source-to-guarded defect. -/
example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat} (K0 : Nat)
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt betaAct qTilde : Real)
    (p : Nat) :
    roughCanonicalSourceToGuardedCorrectionValuationDefect
        (W := B.sampleData.W) (K := K0 + 1)
        R certificate deltaStar
          (bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct)
          (betaProt + betaAct) B.L
          (bankPaperCanonicalTopFrozenRoundedSourceSelector
            (K := K0 + 1) B R certificate T deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct)
              (betaProt + betaAct) qTilde) p =
      roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect
        B K0 R certificate T deltaStar betaProt betaAct qTilde p :=
  roughCanonicalTopFrozenRoundedSourceToGuardedCorrectionValuationDefect_eq_smooth
    B K0 R certificate T deltaStar betaProt betaAct qTilde p

/-- Expanded guarded/raw audit: the frozen-top wrapper consumes exactly the
source-independent rowwise majorant already justified by the guard census. -/
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

end BankPaperRealization

end

end Erdos390.WholePaper
