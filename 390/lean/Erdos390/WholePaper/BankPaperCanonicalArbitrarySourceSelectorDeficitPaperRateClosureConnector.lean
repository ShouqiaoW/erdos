import Erdos390.WholePaper.BankPaperCanonicalArbitrarySourcePostHfitConnector
import Erdos390.WholePaper.BankPaperCanonicalSelectorDeficitPaperRateClosureConnector

/-!
# Selector-deficit paper-rate closure for an arbitrary verified source

The original selector-deficit closure is specialized to the legacy
no-top Post-Hfit source.  The actual Section 8 producer can instead start
from an arbitrary verified source, and in particular from the rounded
frozen-top source.  This file transports the exact residual bookkeeping to
that interface without identifying either source with the legacy selector.

For a supplied `sourceSelector`, its raw-correction defect splits
unconditionally into

* the source moment minus the implemented guarded postcharge correction;
* the guarded postcharge correction minus the older raw-pool correction.

After structured placement this gives the same seven visible terms as in
the legacy closure: the four complete-residual terms, the two implementation
defects, and the placement moment.  The quantitative theorem deliberately
retains all three implementation bounds as inputs.
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

/-! ## Source-parametric correction defects -/

/-- The correction moment of an arbitrary source minus the correction
actually installed on the guarded postcharge pools. -/
def roughCanonicalSourceToGuardedCorrectionValuationDefect
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (sourceSelector : Nat -> Real) (p : Nat) : Real :=
  roughCanonicalSourceValuationCorrectionMoment
      (W := W) (K := K)
      R certificate deltaStar alpha beta ell sourceSelector p -
    R.roughCanonicalAggregateGuardedPostchargeRowCorrection certificate
      deltaStar W K alpha beta ell p

/-- For every source, its source-to-raw defect is exactly the sum of the
source-to-guarded and guarded-to-raw defects. -/
theorem
    roughCanonicalSourceRawCorrectionValuationDefect_eq_sourceToGuarded_add_guardedRaw
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (sourceSelector : Nat -> Real) (p : Nat) :
    roughCanonicalSourceRawCorrectionValuationDefect
        (W := W) (K := K)
        R certificate deltaStar alpha beta ell sourceSelector p =
      roughCanonicalSourceToGuardedCorrectionValuationDefect
          (W := W) (K := K)
          R certificate deltaStar alpha beta ell sourceSelector p +
        R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect
          certificate deltaStar W K alpha beta ell p := by
  unfold roughCanonicalSourceRawCorrectionValuationDefect
  unfold roughCanonicalSourceToGuardedCorrectionValuationDefect
  unfold roughCanonicalAggregateGuardedRawCorrectionValuationDefect
  ring

/-! ## A named source-parametric complete residual -/

/-- The four-term complete signed residual at arbitrary raw-weight
parameters.  Naming it keeps the source-parametric closure readable. -/
def roughCanonicalParameterizedCompleteSignedResidual
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (W K : Nat)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real) (p : Nat) : Real :=
  roughCanonicalCompleteSignedResidual
    (roughCanonicalRawSignedValuationResidual n
      (upperTailLength c n) K
      (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
        alpha beta ell) p)
    (roughCanonicalSignedExceptionalResidual n
      (upperTailLength c n) K deltaStar
      (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
        alpha beta ell) p)
    (roughCanonicalAggregateRawRowCorrection W n
      (upperTailLength c n) K deltaStar alpha beta ell p)
    (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
      (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
        alpha beta ell) p)

/-- At balanced depth `K0 + 1`, the parameterized residual is exactly the
balanced residual already closed by the existing eventual rate theorem. -/
theorem roughCanonicalParameterizedCompleteSignedResidual_eq_balanced
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (W K0 : Nat)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar beta : Real) (p : Nat) :
    R.roughCanonicalParameterizedCompleteSignedResidual
        W (K0 + 1) certificate deltaStar
          (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n))
          beta (L n) p =
      R.roughCanonicalBalancedCompleteSignedResidual
        W K0 certificate deltaStar beta p := by
  unfold roughCanonicalParameterizedCompleteSignedResidual
  unfold roughCanonicalBalancedCompleteSignedResidual
  rfl

/-! ## Exact seven-term identity for an arbitrary source -/

/-- Exact selector-deficit decomposition for the arbitrary-source
Post-Hfit preselector.  No source ledger and no source identification is
assumed. -/
theorem
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource_deficit_eq_completeSignedResidual_sub_sourceToGuardedDefect_sub_guardedRawDefect_sub_moment
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta ell : Real)
    (sourceSelector : Nat -> Real)
    (placementSeed : B.sampleData.Sample -> Real)
    (p : Nat)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (htarget : BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p) :
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
          B R certificate deltaStar betaProt
            sourceSelector placementSeed) p =
      R.roughCanonicalParameterizedCompleteSignedResidual
          B.sampleData.W K certificate deltaStar alpha beta ell p -
        roughCanonicalSourceToGuardedCorrectionValuationDefect
          (W := B.sampleData.W) (K := K)
          R certificate deltaStar alpha beta ell sourceSelector p -
        R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect
          certificate deltaStar B.sampleData.W K alpha beta ell p -
        bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
          (K := K) B R certificate deltaStar betaProt
            sourceSelector placementSeed p := by
  unfold bankPaperCanonicalPostHfitStructuredPreSelectorOfSource
  unfold roughCanonicalParameterizedCompleteSignedResidual
  rw [
    bankPaperCanonicalStructuredPreSelector_deficit_eq_completeSignedResidual_sub_sourceDefect_sub_moment
      B R certificate deltaStar betaProt alpha beta ell
        sourceSelector placementSeed p hactiveSmooth htarget,
    roughCanonicalSourceRawCorrectionValuationDefect_eq_sourceToGuarded_add_guardedRaw
      (W := B.sampleData.W) (K := K)
      R certificate deltaStar alpha beta ell sourceSelector p]
  ring

/-- Charge divisibility supplies the target ledger in the source-parametric
seven-term identity. -/
theorem
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource_deficit_eq_completeSignedResidual_sub_sourceToGuardedDefect_sub_guardedRawDefect_sub_moment_of_chargeDvd
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta ell : Real)
    (sourceSelector : Nat -> Real)
    (placementSeed : B.sampleData.Sample -> Real)
    (p : Nat)
    (hprefix : 2 * depth + 1 <= B.sampleData.W)
    (hp : p.Prime) (hWp : B.sampleData.W < p)
    (hchargeDvd :
      R.selectorTailCharge (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1) :
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
          B R certificate deltaStar betaProt
            sourceSelector placementSeed) p =
      R.roughCanonicalParameterizedCompleteSignedResidual
          B.sampleData.W K certificate deltaStar alpha beta ell p -
        roughCanonicalSourceToGuardedCorrectionValuationDefect
          (W := B.sampleData.W) (K := K)
          R certificate deltaStar alpha beta ell sourceSelector p -
        R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect
          certificate deltaStar B.sampleData.W K alpha beta ell p -
        bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
          (K := K) B R certificate deltaStar betaProt
            sourceSelector placementSeed p := by
  exact
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource_deficit_eq_completeSignedResidual_sub_sourceToGuardedDefect_sub_guardedRawDefect_sub_moment
      B R certificate deltaStar betaProt alpha beta ell
        sourceSelector placementSeed p hactiveSmooth
        (bankPaperCanonicalSignedResidualTargetLedger_of_chargeDvd
          (W := B.sampleData.W) R certificate deltaStar
            hprefix hp hWp hchargeDvd)

/-! ## Quantitative arbitrary-source interface -/

/-- The three implementation estimates needed after the generic four-term
complete residual has been bounded. -/
def BankPaperCanonicalMediumPrimeImplementationRateInputsOfSource
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta ell : Real)
    (sourceSelector : Nat -> Real)
    (placementSeed : B.sampleData.Sample -> Real)
    (p : Nat)
    (scale Csource CguardedRaw Cplacement : Real) : Prop :=
  abs
      (roughCanonicalSourceToGuardedCorrectionValuationDefect
        (W := B.sampleData.W) (K := K)
        R certificate deltaStar alpha beta ell sourceSelector p) <=
        Csource * scale ∧
    abs
      (R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect
        certificate deltaStar B.sampleData.W K
          alpha beta ell p) <=
        CguardedRaw * scale ∧
    abs
      (bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
        (K := K) B R certificate deltaStar betaProt
          sourceSelector placementSeed p) <=
        Cplacement * scale

/-- The arbitrary-source deficit has the paper rate as soon as the generic
complete residual and the three literal implementation terms have it. -/
theorem
    abs_bankPaperCanonicalPostHfitStructuredPreSelectorOfSource_deficit_le_scale_of_complete_and_implementation
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta ell : Real)
    (sourceSelector : Nat -> Real)
    (placementSeed : B.sampleData.Sample -> Real)
    (p : Nat)
    (scale Ccomplete Csource CguardedRaw Cplacement : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (htarget : BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p)
    (hcomplete :
      abs (R.roughCanonicalParameterizedCompleteSignedResidual
        B.sampleData.W K certificate deltaStar alpha beta ell p) <=
          Ccomplete * scale)
    (himplementation :
      BankPaperCanonicalMediumPrimeImplementationRateInputsOfSource
        (K := K) B R certificate deltaStar betaProt alpha beta ell
          sourceSelector placementSeed p scale
          Csource CguardedRaw Cplacement) :
    abs
      (bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
          B R certificate deltaStar betaProt
            sourceSelector placementSeed) p) <=
      (Ccomplete + Csource + CguardedRaw + Cplacement) * scale := by
  rcases himplementation with
    ⟨hsource, hguardedRaw, hplacement⟩
  rw [
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource_deficit_eq_completeSignedResidual_sub_sourceToGuardedDefect_sub_guardedRawDefect_sub_moment
      B R certificate deltaStar betaProt alpha beta ell
        sourceSelector placementSeed p hactiveSmooth htarget]
  exact abs_sub_sub_sub_le_scale
    hcomplete hsource hguardedRaw hplacement

/-! ## Frozen-top balanced specialization -/

/-- Exact balanced seven-term identity for the rounded frozen-top source.
The source occurs literally on both implementation terms; no equality with
the legacy no-top selector is used. -/
theorem
    bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector_deficit_eq_balancedCompleteSignedResidual_sub_sourceToGuardedDefect_sub_guardedRawDefect_sub_moment
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
    (placementSeed : B.sampleData.Sample -> Real)
    (p : Nat)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1)
    (htarget : BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p) :
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1))
        (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
          (K := K0 + 1) B R certificate T deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            (betaProt + betaAct) qTilde placementSeed) p =
      R.roughCanonicalBalancedCompleteSignedResidual
          B.sampleData.W K0 certificate deltaStar
            (betaProt + betaAct) p -
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
                (betaProt + betaAct) qTilde) p -
        R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect
          certificate deltaStar B.sampleData.W (K0 + 1)
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            (betaProt + betaAct) B.L p -
        bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
            (bankPaperCanonicalTopFrozenRoundedSourceSelector
              (K := K0 + 1) B R certificate T deltaStar betaProt
                (bankPaperCanonicalPostHfitBalancedAlpha
                  B c K0 betaProt betaAct)
                (betaProt + betaAct) qTilde)
            placementSeed p := by
  unfold bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
  rw [
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource_deficit_eq_completeSignedResidual_sub_sourceToGuardedDefect_sub_guardedRawDefect_sub_moment
      B R certificate deltaStar betaProt
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) B.L
        (bankPaperCanonicalTopFrozenRoundedSourceSelector
          (K := K0 + 1) B R certificate T deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            (betaProt + betaAct) qTilde)
        placementSeed p hactiveSmooth htarget,
    bankPaperCanonicalPostHfitBalancedAlpha,
    show B.L = L B.sampleData.n by rfl,
    roughCanonicalParameterizedCompleteSignedResidual_eq_balanced]

/-- The implementation-rate package specialized to the balanced rounded
frozen-top source. -/
def BankPaperCanonicalTopFrozenRoundedMediumPrimeImplementationRateInputs
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
    (placementSeed : B.sampleData.Sample -> Real)
    (p : Nat)
    (scale Csource CguardedRaw Cplacement : Real) : Prop :=
  BankPaperCanonicalMediumPrimeImplementationRateInputsOfSource
    (K := K0 + 1) B R certificate deltaStar betaProt
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      (betaProt + betaAct) B.L
      (bankPaperCanonicalTopFrozenRoundedSourceSelector
        (K := K0 + 1) B R certificate T deltaStar betaProt
          (bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct)
          (betaProt + betaAct) qTilde)
      placementSeed p scale Csource CguardedRaw Cplacement

/-- Balanced complete-residual closure plus the three literal frozen-top
implementation bounds gives the final selector-deficit paper rate. -/
theorem
    abs_bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector_deficit_le_scale_of_balancedComplete_and_implementation
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
    (placementSeed : B.sampleData.Sample -> Real)
    (p : Nat)
    (scale Ccomplete Csource CguardedRaw Cplacement : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1)
    (htarget : BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p)
    (hcomplete :
      abs (R.roughCanonicalBalancedCompleteSignedResidual
        B.sampleData.W K0 certificate deltaStar
          (betaProt + betaAct) p) <=
        Ccomplete * scale)
    (himplementation :
      BankPaperCanonicalTopFrozenRoundedMediumPrimeImplementationRateInputs
        B K0 R certificate T deltaStar betaProt betaAct qTilde
          placementSeed p scale Csource CguardedRaw Cplacement) :
    abs
      (bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1))
        (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
          (K := K0 + 1) B R certificate T deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            (betaProt + betaAct) qTilde placementSeed) p) <=
      (Ccomplete + Csource + CguardedRaw + Cplacement) * scale := by
  rcases himplementation with
    ⟨hsource, hguardedRaw, hplacement⟩
  rw [
    bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector_deficit_eq_balancedCompleteSignedResidual_sub_sourceToGuardedDefect_sub_guardedRawDefect_sub_moment
      B K0 R certificate T deltaStar betaProt betaAct qTilde
        placementSeed p hactiveSmooth htarget]
  exact abs_sub_sub_sub_le_scale
    hcomplete hsource hguardedRaw hplacement

end BankPaperRealization

end

end Erdos390.WholePaper
