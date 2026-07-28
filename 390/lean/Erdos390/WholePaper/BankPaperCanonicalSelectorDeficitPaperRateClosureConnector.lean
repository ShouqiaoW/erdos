import Erdos390.WholePaper.BankPaperCanonicalGuardedRawCorrectionMomentDefectConnector
import Erdos390.WholePaper.BankPaperCanonicalRawRowCorrectionRateClosure
import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveResidualBoundConnector

/-!
# Honest paper-rate closure for the canonical selector deficit

The literal Post-Hfit structured pre-selector is already known to have the
unconditional expansion

`complete signed residual - source/raw defect - placement moment`.

There are two mathematically different changes hidden in the source/raw
defect:

* the actual global source versus the correction installed on guarded
  postcharge pools;
* the guarded postcharge correction versus the older raw-pool correction.

The second change is the guarded/raw defect isolated in
`BankPaperCanonicalGuardedRawCorrectionMomentDefectConnector`.  This file
splits the source/raw defect into those two literal finite differences and
keeps both of them visible.  In particular, no guarded-to-raw equality is
assumed.

The quantitative interface has two layers.  A pointwise theorem combines
the four signed-residual component bounds with paper-rate bounds for the two
implementation defects and the structured-placement moment.  An eventual
theorem closes the exceptional, raw-row-correction, and guard terms from
the existing rate theorems; only the raw signed residual remains as an
analytic input at that layer.  Thus downstream source-specific work can see
exactly which medium-prime estimates remain.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## The two independent implementation defects -/

/-- The finite difference between the correction moment of the actual
Post-Hfit global source and the correction moment installed on guarded
postcharge pools.  This is independent of the guarded-versus-raw pool
change. -/
def roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect
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
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real) (p : Nat) : Real :=
  roughCanonicalPostHfitGlobalSourceValuationCorrectionMoment
      B K0 R certificate deltaStar betaProt betaAct oldSeed p -
    R.roughCanonicalAggregateGuardedPostchargeRowCorrection certificate
      deltaStar B.sampleData.W (K0 + 1)
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      (betaProt + betaAct) B.L p

/-- The named source-to-guarded reindex is exactly zero
source-to-guarded defect.  No guarded-to-raw statement occurs here. -/
theorem
    bankPaperCanonicalPostHfitSourceToGuardedCorrectionValuationReindex_iff_defect_eq_zero
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
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real) (p : Nat) :
    BankPaperCanonicalPostHfitSourceToGuardedCorrectionValuationReindex
        B K0 R certificate deltaStar betaProt betaAct oldSeed p ↔
      roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect
        B K0 R certificate deltaStar betaProt betaAct oldSeed p = 0 := by
  unfold
    BankPaperCanonicalPostHfitSourceToGuardedCorrectionValuationReindex
  unfold
    roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect
  constructor <;> intro h <;> linarith

/-- The previously exposed source/raw defect is unconditionally the sum of
the source-to-guarded defect and the guarded-to-raw defect. -/
theorem
    roughCanonicalPostHfitGlobalSourceRawCorrectionValuationDefect_eq_sourceToGuarded_add_guardedRaw
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
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real) (p : Nat) :
    roughCanonicalPostHfitGlobalSourceRawCorrectionValuationDefect
        B K0 R certificate deltaStar betaProt betaAct oldSeed p =
      roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect
          B K0 R certificate deltaStar betaProt betaAct oldSeed p +
        R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect
          certificate deltaStar B.sampleData.W (K0 + 1)
          (bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct)
          (betaProt + betaAct) B.L p := by
  unfold roughCanonicalPostHfitGlobalSourceRawCorrectionValuationDefect
  unfold roughCanonicalSourceRawCorrectionValuationDefect
  unfold
    roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect
  unfold roughCanonicalPostHfitGlobalSourceValuationCorrectionMoment
  unfold roughCanonicalAggregateGuardedRawCorrectionValuationDefect
  ring

/-! ## Exact seven-term selector decomposition -/

/-- Exact unconditional decomposition of the literal structured
pre-selector.  The four paper terms retain their original signs, followed
by the source-to-guarded defect, the guarded-to-raw defect, and the smooth
placement moment, all with negative sign. -/
theorem
    bankPaperCanonicalPostHfitStructuredPreSelector_deficit_eq_completeSignedResidual_sub_sourceToGuardedDefect_sub_guardedRawDefect_sub_moment
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
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass : Real) (p : Nat)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1)
    (htarget : BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p) :
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1))
        (bankPaperCanonicalPostHfitStructuredPreSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed
            minusMass plusMass) p =
      roughCanonicalPostHfitCompleteSignedResidual
          B K0 R certificate deltaStar betaProt betaAct p -
        roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect
          B K0 R certificate deltaStar betaProt betaAct oldSeed p -
        R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect
          certificate deltaStar B.sampleData.W (K0 + 1)
          (bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct)
          (betaProt + betaAct) B.L p -
        bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
          (bankPaperCanonicalPostHfitGlobalSourceSelector
            B K0 R certificate deltaStar betaProt betaAct oldSeed)
          (bankPaperCanonicalTwoZeroHeadCellRebalance
            B.sampleData oldSeed minusMass plusMass) p := by
  rw [
    bankPaperCanonicalPostHfitStructuredPreSelector_deficit_eq_completeSignedResidual_sub_sourceDefect_sub_moment
      B K0 R certificate deltaStar betaProt betaAct oldSeed
        minusMass plusMass p hactiveSmooth htarget,
    roughCanonicalPostHfitGlobalSourceRawCorrectionValuationDefect_eq_sourceToGuarded_add_guardedRaw
      B K0 R certificate deltaStar betaProt betaAct oldSeed p]
  ring

/-- Medium-prime charge divisibility discharges the target ledger in the
preceding unconditional decomposition. -/
theorem
    bankPaperCanonicalPostHfitStructuredPreSelector_deficit_eq_completeSignedResidual_sub_sourceToGuardedDefect_sub_guardedRawDefect_sub_moment_of_chargeDvd
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
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass : Real) (p : Nat)
    (hprefix : 2 * depth + 1 <= B.sampleData.W)
    (hp : p.Prime) (hWp : B.sampleData.W < p)
    (hchargeDvd :
      R.selectorTailCharge (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1) :
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1))
        (bankPaperCanonicalPostHfitStructuredPreSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed
            minusMass plusMass) p =
      roughCanonicalPostHfitCompleteSignedResidual
          B K0 R certificate deltaStar betaProt betaAct p -
        roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect
          B K0 R certificate deltaStar betaProt betaAct oldSeed p -
        R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect
          certificate deltaStar B.sampleData.W (K0 + 1)
          (bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct)
          (betaProt + betaAct) B.L p -
        bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
          (bankPaperCanonicalPostHfitGlobalSourceSelector
            B K0 R certificate deltaStar betaProt betaAct oldSeed)
          (bankPaperCanonicalTwoZeroHeadCellRebalance
            B.sampleData oldSeed minusMass plusMass) p := by
  exact
    bankPaperCanonicalPostHfitStructuredPreSelector_deficit_eq_completeSignedResidual_sub_sourceToGuardedDefect_sub_guardedRawDefect_sub_moment
      B K0 R certificate deltaStar betaProt betaAct oldSeed
        minusMass plusMass p hactiveSmooth
        (bankPaperCanonicalSignedResidualTargetLedger_of_chargeDvd
          (W := B.sampleData.W) R certificate deltaStar
            hprefix hp hWp hchargeDvd)

/-! ## Named remaining paper-rate inputs -/

/-- Paper-rate input for the raw upper-minus-lower signed valuation
residual at the balanced physical depth. -/
def RoughCanonicalBalancedRawSignedValuationResidualBound
    (W n K0 : Nat) (c beta : Real) (p : Nat) (bound : Real) : Prop :=
  abs (roughCanonicalRawSignedValuationResidual n
    (upperTailLength c n) (K0 + 1)
    (roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
      (roughHeadBalancedAlpha W n (upperTailLength c n)
        (K0 + 1) beta (L n))
      beta (L n)) p) <= bound

/-- The three source-specific medium-prime estimates not supplied by the
generic signed-residual rate files.  Keeping them in separate conjuncts
prevents a source-to-guarded estimate from being confused with the genuinely
different guarded-to-raw pool defect. -/
def BankPaperCanonicalPostHfitMediumPrimeImplementationRateInputs
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
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass : Real) (p : Nat)
    (scale Csource CguardedRaw Cplacement : Real) : Prop :=
  abs
      (roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect
        B K0 R certificate deltaStar betaProt betaAct oldSeed p) <=
        Csource * scale ∧
    abs
      (R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect
        certificate deltaStar B.sampleData.W (K0 + 1)
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) B.L p) <=
        CguardedRaw * scale ∧
    abs
      (bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
        (K := K0 + 1) B R certificate deltaStar betaProt
        (bankPaperCanonicalPostHfitGlobalSourceSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed)
        (bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass) p) <=
        Cplacement * scale

/-! ## Pointwise paper-rate closure -/

/-- Three successive finite defects add exactly their three constants to a
paper-rate bound. -/
theorem abs_sub_sub_sub_le_scale
    {base defect₁ defect₂ defect₃ scale
      Cbase C₁ C₂ C₃ : Real}
    (hbase : abs base <= Cbase * scale)
    (hdefect₁ : abs defect₁ <= C₁ * scale)
    (hdefect₂ : abs defect₂ <= C₂ * scale)
    (hdefect₃ : abs defect₃ <= C₃ * scale) :
    abs (base - defect₁ - defect₂ - defect₃) <=
      (Cbase + C₁ + C₂ + C₃) * scale := by
  calc
    abs (base - defect₁ - defect₂ - defect₃) <=
        abs (base - defect₁ - defect₂) + abs defect₃ :=
      abs_sub _ _
    _ <= (abs (base - defect₁) + abs defect₂) + abs defect₃ :=
      add_le_add (abs_sub _ _) le_rfl
    _ <= ((abs base + abs defect₁) + abs defect₂) + abs defect₃ :=
      add_le_add (add_le_add (abs_sub _ _) le_rfl) le_rfl
    _ <= ((Cbase * scale + C₁ * scale) + C₂ * scale) +
        C₃ * scale := by
      exact
        add_le_add
          (add_le_add (add_le_add hbase hdefect₁) hdefect₂)
          hdefect₃
    _ = (Cbase + C₁ + C₂ + C₃) * scale := by ring

/-- Once the four-term complete residual is bounded, the only additional
costs are the two independently named implementation defects and the
structured-placement moment. -/
theorem
    abs_bankPaperCanonicalPostHfitStructuredPreSelector_deficit_le_scale_of_complete_and_implementation
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
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass : Real) (p : Nat)
    (scale Ccomplete Csource CguardedRaw Cplacement : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1)
    (htarget : BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p)
    (hcomplete :
      abs (roughCanonicalPostHfitCompleteSignedResidual
        B K0 R certificate deltaStar betaProt betaAct p) <=
          Ccomplete * scale)
    (himplementation :
      BankPaperCanonicalPostHfitMediumPrimeImplementationRateInputs
        B K0 R certificate deltaStar betaProt betaAct oldSeed
          minusMass plusMass p scale
          Csource CguardedRaw Cplacement) :
    abs
      (bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1))
        (bankPaperCanonicalPostHfitStructuredPreSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed
            minusMass plusMass) p) <=
      (Ccomplete + Csource + CguardedRaw + Cplacement) * scale := by
  rcases himplementation with
    ⟨hsource, hguardedRaw, hplacement⟩
  rw [
    bankPaperCanonicalPostHfitStructuredPreSelector_deficit_eq_completeSignedResidual_sub_sourceToGuardedDefect_sub_guardedRawDefect_sub_moment
      B K0 R certificate deltaStar betaProt betaAct oldSeed
        minusMass plusMass p hactiveSmooth htarget]
  exact abs_sub_sub_sub_le_scale
    hcomplete hsource hguardedRaw hplacement

/-- Charge divisibility supplies the target ledger for the preceding
pointwise rate closure throughout the medium-prime range. -/
theorem
    abs_bankPaperCanonicalPostHfitStructuredPreSelector_deficit_le_scale_of_complete_and_implementation_of_chargeDvd
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
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass : Real) (p : Nat)
    (scale Ccomplete Csource CguardedRaw Cplacement : Real)
    (hprefix : 2 * depth + 1 <= B.sampleData.W)
    (hp : p.Prime) (hWp : B.sampleData.W < p)
    (hchargeDvd :
      R.selectorTailCharge (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1)
    (hcomplete :
      abs (roughCanonicalPostHfitCompleteSignedResidual
        B K0 R certificate deltaStar betaProt betaAct p) <=
          Ccomplete * scale)
    (himplementation :
      BankPaperCanonicalPostHfitMediumPrimeImplementationRateInputs
        B K0 R certificate deltaStar betaProt betaAct oldSeed
          minusMass plusMass p scale
          Csource CguardedRaw Cplacement) :
    abs
      (bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1))
        (bankPaperCanonicalPostHfitStructuredPreSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed
            minusMass plusMass) p) <=
      (Ccomplete + Csource + CguardedRaw + Cplacement) * scale := by
  exact
    abs_bankPaperCanonicalPostHfitStructuredPreSelector_deficit_le_scale_of_complete_and_implementation
      B K0 R certificate deltaStar betaProt betaAct oldSeed
        minusMass plusMass p scale Ccomplete Csource CguardedRaw Cplacement
        hactiveSmooth
        (bankPaperCanonicalSignedResidualTargetLedger_of_chargeDvd
          (W := B.sampleData.W) R certificate deltaStar
            hprefix hp hWp hchargeDvd)
        hcomplete himplementation

/-- Full pointwise seven-term paper-rate closure.  The first four hypotheses
are the raw, signed-exceptional, raw-row-correction, and aggregate-guard
bounds.  The final package contains exactly the three source-specific
medium-prime estimates still needed by the implemented selector. -/
theorem
    abs_bankPaperCanonicalPostHfitStructuredPreSelector_deficit_le_scale_of_components
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
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass : Real) (p : Nat)
    (scale Craw Cexceptional Crow Cguard
      Csource CguardedRaw Cplacement : Real)
    (hscale : 0 <= scale)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1)
    (htarget : BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p)
    (hraw :
      RoughCanonicalBalancedRawSignedValuationResidualBound
        B.sampleData.W B.sampleData.n K0 c (betaProt + betaAct) p
          (Craw * scale))
    (hexceptional :
      RoughCanonicalSignedExceptionalResidualBound
        B.sampleData.n (upperTailLength c B.sampleData.n) (K0 + 1)
        deltaStar
        (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) (K0 + 1)
          (roughHeadBalancedAlpha B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) (K0 + 1)
            (betaProt + betaAct) (L B.sampleData.n))
          (betaProt + betaAct) (L B.sampleData.n))
        p (Cexceptional * scale))
    (hrow :
      RoughCanonicalAggregateRawRowCorrectionBound
        B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) (K0 + 1) deltaStar
        (roughHeadBalancedAlpha B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) (K0 + 1)
          (betaProt + betaAct) (L B.sampleData.n))
        (betaProt + betaAct) (L B.sampleData.n) p
        (Crow * scale))
    (hguard :
      RoughCanonicalAggregateGuardResidualBound R certificate deltaStar
        (K0 + 1)
        (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) (K0 + 1)
          (roughHeadBalancedAlpha B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) (K0 + 1)
            (betaProt + betaAct) (L B.sampleData.n))
          (betaProt + betaAct) (L B.sampleData.n))
        p (Cguard * scale))
    (himplementation :
      BankPaperCanonicalPostHfitMediumPrimeImplementationRateInputs
        B K0 R certificate deltaStar betaProt betaAct oldSeed
          minusMass plusMass p scale
          Csource CguardedRaw Cplacement) :
    abs
      (bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1))
        (bankPaperCanonicalPostHfitStructuredPreSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed
            minusMass plusMass) p) <=
      (Craw + Cexceptional + Crow + Cguard +
        Csource + CguardedRaw + Cplacement) * scale := by
  have hcomplete :
      abs (roughCanonicalPostHfitCompleteSignedResidual
        B K0 R certificate deltaStar betaProt betaAct p) <=
        (Craw + Cexceptional + Crow + Cguard) * scale := by
    unfold roughCanonicalPostHfitCompleteSignedResidual
    unfold RoughCanonicalBalancedRawSignedValuationResidualBound at hraw
    unfold RoughCanonicalSignedExceptionalResidualBound at hexceptional
    unfold RoughCanonicalAggregateRawRowCorrectionBound at hrow
    unfold RoughCanonicalAggregateGuardResidualBound at hguard
    unfold bankPaperCanonicalPostHfitBalancedAlpha
    exact
      abs_roughCanonicalCompleteSignedResidual_le_scale
        hscale hraw hexceptional hrow hguard
  exact
    abs_bankPaperCanonicalPostHfitStructuredPreSelector_deficit_le_scale_of_complete_and_implementation
      B K0 R certificate deltaStar betaProt betaAct oldSeed
        minusMass plusMass p scale
        (Craw + Cexceptional + Crow + Cguard)
        Csource CguardedRaw Cplacement
        hactiveSmooth htarget hcomplete himplementation

/-! ## Eventual closure of the generic four-term residual -/

/-- The balanced four-term residual without any source-specific structured
data.  This is the B-free specialization to which the existing exceptional,
raw-row-correction, and aggregate-guard rate theorems apply directly. -/
def roughCanonicalBalancedCompleteSignedResidual
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (W K0 : Nat)
    {left right : Nat -> Nat} {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar beta : Real) (p : Nat) : Real :=
  roughCanonicalCompleteSignedResidual
    (roughCanonicalRawSignedValuationResidual n
      (upperTailLength c n) (K0 + 1)
      (roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n)) p)
    (roughCanonicalSignedExceptionalResidual n
      (upperTailLength c n) (K0 + 1) deltaStar
      (roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n)) p)
    (roughCanonicalAggregateRawRowCorrection W n
      (upperTailLength c n) (K0 + 1) deltaStar
      (roughHeadBalancedAlpha W n (upperTailLength c n)
        (K0 + 1) beta (L n))
      beta (L n) p)
    (R.roughCanonicalAggregateGuardResidual certificate deltaStar
      (K0 + 1)
      (roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n)) p)

/-- The Post-Hfit four-term residual is definitionally the balanced generic
residual with `beta = betaProt + betaAct`. -/
theorem roughCanonicalPostHfitCompleteSignedResidual_eq_balanced
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
    (deltaStar betaProt betaAct : Real) (p : Nat) :
    roughCanonicalPostHfitCompleteSignedResidual
        B K0 R certificate deltaStar betaProt betaAct p =
      R.roughCanonicalBalancedCompleteSignedResidual
        B.sampleData.W K0 certificate deltaStar
          (betaProt + betaAct) p := by
  unfold roughCanonicalPostHfitCompleteSignedResidual
  unfold roughCanonicalBalancedCompleteSignedResidual
  unfold bankPaperCanonicalPostHfitBalancedAlpha
  rfl

/-- Existing theorems close three of the four generic signed-residual
components.  The signed exceptional constant is existential, the raw-row
constant is explicit, and the guard constant can be any fixed positive
`epsilon`.  Only the balanced raw signed residual bound remains as a
premise. -/
theorem
    exists_eventually_roughCanonicalBalancedCompleteSignedResidualBound_of_raw
    (W K0 depth : Nat) {c deltaStar beta Craw epsilon : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18)
    (hepsilon : 0 < epsilon)
    (hTwoW : 2 <= W) (hprefix : 2 * depth + 1 <= W) :
    ∃ Cexceptional : Real, 0 <= Cexceptional ∧
      ∀ᶠ n : Nat in atTop,
        ∀ (R : BankPaperRealization n
            (upperEndpoint n (upperTailLength c n)))
          (left right : Nat -> Nat) (changed : Finset Nat)
          (certificate : GuardedCentralAnchorCertificate c depth n
            left right changed) (p : Nat),
        (0 <= roughHeadBalancedAlpha W n (upperTailLength c n)
              (K0 + 1) beta (L n) ∧
          roughHeadBalancedAlpha W n (upperTailLength c n)
              (K0 + 1) beta (L n) <= 1) ->
        (0 <= beta / L n ∧ beta / L n <= 1) ->
        p.Prime -> W < p -> p <= yNat n ->
        RoughCanonicalBalancedRawSignedValuationResidualBound
          W n K0 c beta p
            (Craw * secondOrderScale n / ((p : Real) * L n)) ->
        abs (R.roughCanonicalBalancedCompleteSignedResidual
          W K0 certificate deltaStar beta p) <=
          (Craw + Cexceptional +
              roughCanonicalUniformRawRowCorrectionDensityConstant
                W K0 c beta +
              epsilon) *
            secondOrderScale n / ((p : Real) * L n) := by
  obtain ⟨Cexceptional, hCexceptional, hexceptional⟩ :=
    exists_eventually_roughCanonicalSignedExceptionalResidualBound_fourFive
      W K0 (beta := beta) hc hdelta hdeltaUpper
  have hrow :=
    eventually_roughCanonicalAggregateRawRowCorrectionBound_strictScale
      W K0 (beta := beta) hc hdelta
  have hguard :=
    eventually_roughCanonicalAggregateGuardResidualBound
      hc hepsilon depth W hTwoW hprefix
  refine ⟨Cexceptional, hCexceptional, ?_⟩
  filter_upwards [eventually_gt_atTop 1,
      hexceptional, hrow, hguard]
      with n hn hexceptionalN hrowN hguardN
  intro R left right changed certificate p
    halpha hbeta hp hWp hpY hraw
  have hpReal : (0 : Real) < p := by
    exact_mod_cast hp.pos
  have hscale :
      0 <= secondOrderScale n / ((p : Real) * L n) := by
    exact div_nonneg (secondOrderScale_pos hn).le
      (mul_nonneg hpReal.le (L_pos hn).le)
  have hexceptionalP := hexceptionalN p hp hWp hpY
  have hrowP := hrowN p hp
  have hguardP :=
    hguardN R left right changed certificate deltaStar
      (roughHeadBalancedAlpha W n (upperTailLength c n)
        (K0 + 1) beta (L n))
      beta (K0 + 1) p halpha hbeta hp hWp hpY
  unfold roughCanonicalBalancedCompleteSignedResidual
  unfold RoughCanonicalBalancedRawSignedValuationResidualBound at hraw
  simpa only [mul_div_assoc] using
    (abs_roughCanonicalCompleteSignedResidual_le_scale
      (scale :=
        secondOrderScale n / ((p : Real) * L n))
      (C_raw := Craw) (C_exceptional := Cexceptional)
      (C_row :=
        roughCanonicalUniformRawRowCorrectionDensityConstant
          W K0 c beta)
      (C_guard := epsilon)
      hscale
      (by simpa only [mul_div_assoc] using hraw)
      (by
        simpa only [RoughCanonicalSignedExceptionalResidualBound,
          mul_div_assoc] using hexceptionalP)
      (by
        simpa only [RoughCanonicalAggregateRawRowCorrectionBound,
          mul_div_assoc] using hrowP)
      (by
        simpa only [RoughCanonicalAggregateGuardResidualBound,
          mul_div_assoc] using hguardP))

end BankPaperRealization

end

end Erdos390.WholePaper
