import Erdos390.WholePaper.BankPaperCanonicalSectionNineSynchronizedPostHfitProducer

/-!
# Symmetric-height producer for the finite Post-Hfit input

`BankPaperCanonicalSectionNinePostHfitLocalInputsAt` is intentionally a
generic finite interface.  In the literal Section 8 construction, however,
several of its fields are consequences of the already audited symmetric
two-zero-cell machinery rather than independent analytic inputs.

This file records that specialization.  The legacy rounded-source API
separates the remaining data into three natural packages:

* the rounded global source and the two-zero-cell geometry/capacity data;
* the local Proposition 8.7 analytic tail; and
* the numerical and nonsmooth endpoint-slack data.

The primary weak API factors the first package into a selector-independent
core and the minimal `BankPaperCanonicalSelectorSourceState`, and combines
the two dependent analytic tails without duplicating a parallel P87/slack
hierarchy.

From these packages the connector constructs, rather than assumes,

* the signed row change `-d`;
* the structured placement;
* the actual active-measure constructor for the original scaled seed;
* the bridge-baseline/active-seed identity;
* the frozen-layer `Cfixed / L` estimate;
* the rebalanced placement-seed `(Cactive + gamma) / L` estimate; and
* the protected reserve needed at the actual endpoint.

No final payload, Section 9 output, collision statement, or asymptotic
budget occurs in this file.
-/

open Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Natural finite input packages -/

/-- Rounded-source, geometry, and scalar two-zero-cell data at one bank.

The four geometric fields are exactly the output of
`bankPaperCanonicalSectionEight_twoZeroHeadCell_geometryInputs`.  The
two scalar capacity inequalities are the hypotheses consumed by the two
finite symmetric-height capacity lemmas.  The fit-loss bound is the output
used by the actual-measure connector. -/
structure BankPaperCanonicalSectionNineSymmetricHeightSourceInputsAt
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (K0 : Nat)
    (deltaStar : Real) where
  betaProt : Real
  betaAct : Real
  q0 : Real
  d : Int
  T : BarycentricTarget B.sampleData
  sourceCellIndex : BankPaperCanonicalTangentPrime
    B.sampleData.n B.sampleData.W → Nat
  sourcePointwiseUpper : BankPaperCanonicalTangentPrime
    B.sampleData.n B.sampleData.W → Real
  sourcePrefixUpper : Band → Nat → Real
  betaProt_nonneg : 0 ≤ betaProt
  q0_one_le : 1 ≤ q0
  baseline_seed :
    ∀ m : B.sampleData.Sample,
      B.baseline.baseWeight m =
        bankPaperCanonicalScaledActiveSeed T q0 m
  roundedSource :
    BankPaperCanonicalRoundedSelectorTangentInput
      R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate
        deltaStar (K0 + 1))
      B.partition.band sourceCellIndex
      sourcePointwiseUpper sourcePrefixUpper
      (bankPaperCanonicalPostHfitGlobalSourceSelector
        B K0 R certificate deltaStar betaProt betaAct
          (bankPaperCanonicalScaledActiveSeed T q0))
  headSeparated : B.sampleData.HeadPatternsSeparated
  activeSmooth :
    bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
      R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1
  minusPool :
    ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) →
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool
            certificate deltaStar B.sampleData.W (K0 + 1) 1
  plusPool :
    ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) →
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool
            certificate deltaStar B.sampleData.W (K0 + 1) 1
  scalarCapacity :
    ∀ sign : PhysicalSign,
      (d : Real) / 2 ≤ q0 * T.baseline.cellMass (none, sign) ∧
        q0 * T.baseline.cellMass (none, sign) - (d : Real) / 2 ≤
          (Fintype.card
              (B.sampleData.SampleAt (none, sign)) : Real) *
            (1 - betaProt / B.L)
  fitLoss :
    ∀ sign : PhysicalSign,
      -bankPaperCanonicalSymmetricHeightCellMass d ≤
        (Fintype.card
            (B.sampleData.SampleAt (none, sign)) : Real) *
          (betaProt / B.L)

/-- The genuinely analytic local Proposition 8.7 tail.

The frozen ledger is not assumed.  `heightUpper` and `gamma_nonneg` feed the
existing exact two-zero-cell frozen-weight estimate, while `fixedRoom`
simultaneously pays for that estimate and the rebalanced placement-seed
bound. -/
structure BankPaperCanonicalSectionNineSymmetricHeightP87InputsAt
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (K0 : Nat)
    (deltaStar Cpost : Real)
    (S : BankPaperCanonicalSectionNineSymmetricHeightSourceInputsAt
      B R certificate K0 deltaStar) where
  Ctarget : Real
  Cinitial : Real
  Cfixed : Real
  Cactive : Real
  gamma : Real
  radius : NNReal
  targetEnvelopes :
    B.HasTargetEnvelopes Ctarget
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget
          B R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          (bankPaperCanonicalPostHfitStructuredPreSelector
            B K0 R certificate deltaStar S.betaProt S.betaAct
              (bankPaperCanonicalScaledActiveSeed S.T S.q0)
              (bankPaperCanonicalSymmetricHeightCellMass S.d)
              (bankPaperCanonicalSymmetricHeightCellMass S.d))
          (bankPaperCanonicalScaledActiveSeed S.T S.q0)) 0 j)
  selectorDeficit :
    ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          (bankPaperCanonicalPostHfitStructuredPreSelector
            B K0 R certificate deltaStar S.betaProt S.betaAct
              (bankPaperCanonicalScaledActiveSeed S.T S.q0)
              (bankPaperCanonicalSymmetricHeightCellMass S.d)
              (bankPaperCanonicalSymmetricHeightCellMass S.d)) p) ≤
        Cinitial * B.q / ((p : Real) * B.L)
  activeLedger :
    ∀ m : B.sampleData.Sample,
      B.baseline.baseWeight m ≤ Cactive / B.L
  localP87 :
    ∀ (Delta : Band → Real),
      B.HasTargetEnvelopes Ctarget Delta →
      ∀ (markedTarget : Nat → Real) (N : Real),
        0 ≤ N →
        B.q ≤ (1 : Real) * N →
        (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
          abs (markedTarget p -
            B.paperMoment (B.markedValuation p) 0) ≤
              Cinitial * N / ((p : Real) * B.L)) →
        (∀ j, Delta j = B.markedBandResidual markedTarget 0 j) →
        ∀ {Fixed : Type} [Fintype Fixed],
          ∀ (fixedValue : Fixed → Nat) (fixedWeight : Fixed → Real)
            (quota : Int),
            (quota : Real) = (∑ f, fixedWeight f) + B.q →
            B.sampleData.HeadPatternsSeparated →
            (∀ x,
              BridgeData.frozenAmbientWeight
                fixedValue fixedWeight x ∈ Icc (0 : Real) 1) →
            (∀ m : B.sampleData.Sample,
              BridgeData.frozenAmbientWeight fixedValue fixedWeight
                  (B.sampleData.value m) ≤
                Cfixed / B.L) →
            (∀ m : B.sampleData.Sample,
              B.baseline.baseWeight m ≤ Cactive / B.L) →
            B.HasPaperProposition87Conclusion
              Delta radius markedTarget N Cpost
                fixedValue fixedWeight quota
  Cactive_nonneg : 0 ≤ Cactive
  gamma_nonneg : 0 ≤ gamma
  heightUpper :
    ∀ sign : PhysicalSign,
      bankPaperCanonicalSymmetricHeightCellMass S.d ≤
        (Fintype.card
            (B.sampleData.SampleAt (none, sign)) : Real) *
          (gamma / B.L)
  fixedRoom :
    S.betaProt + (Cactive + gamma) ≤ Cfixed

/-- Numerical and nonsmooth inputs of the endpoint-slack theorem.

The protected-reserve inequality itself is not a field: it is constructed
from `reserveLoss` by the audited symmetric-height reserve theorem. -/
structure BankPaperCanonicalSectionNineSymmetricHeightSlackInputsAt
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (K0 : Nat)
    (deltaStar sigma Cpost : Real)
    (S : BankPaperCanonicalSectionNineSymmetricHeightSourceInputsAt
      B R certificate K0 deltaStar)
    (A : BankPaperCanonicalSectionNineSymmetricHeightP87InputsAt
      B R certificate K0 deltaStar Cpost S) where
  C : Real
  C_one_le : 1 ≤ C
  W_large : 1 < B.sampleData.W
  physicalUpper :
    ∀ sign, B.sampleData.hi sign ≤ physicalBound C B.sampleData.n
  reserveGap : 0 < S.betaProt - sigma
  reserveLoss :
    ∀ sign : PhysicalSign,
      -bankPaperCanonicalSymmetricHeightCellMass S.d ≤
        (Fintype.card
            (B.sampleData.SampleAt (none, sign)) : Real) *
          ((S.betaProt - sigma) / B.L)
  largeL :
    A.Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (A.radius : Real)))) *
          A.Cactive + sigma ≤
      B.L
  nonsmooth :
    RoughCanonicalBalancedNonsmoothBounds
      R certificate deltaStar B.sampleData.W K0
        S.betaProt S.betaAct sigma

/-! ## Source-state finite input packages -/

/-- The selector-independent symmetric-height data at one bank.

This is the common geometric and scalar core of the legacy rounded-source
package and the weaker source-state package below. -/
structure BankPaperCanonicalSectionNineSymmetricHeightCoreInputsAt
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (K0 : Nat)
    (deltaStar : Real) where
  betaProt : Real
  betaAct : Real
  q0 : Real
  d : Int
  T : BarycentricTarget B.sampleData
  betaProt_nonneg : 0 ≤ betaProt
  q0_one_le : 1 ≤ q0
  baseline_seed :
    ∀ m : B.sampleData.Sample,
      B.baseline.baseWeight m =
        bankPaperCanonicalScaledActiveSeed T q0 m
  headSeparated : B.sampleData.HeadPatternsSeparated
  activeSmooth :
    bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
      R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1
  minusPool :
    ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) →
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool
            certificate deltaStar B.sampleData.W (K0 + 1) 1
  plusPool :
    ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) →
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool
            certificate deltaStar B.sampleData.W (K0 + 1) 1
  scalarCapacity :
    ∀ sign : PhysicalSign,
      (d : Real) / 2 ≤ q0 * T.baseline.cellMass (none, sign) ∧
        q0 * T.baseline.cellMass (none, sign) - (d : Real) / 2 ≤
          (Fintype.card
              (B.sampleData.SampleAt (none, sign)) : Real) *
            (1 - betaProt / B.L)
  fitLoss :
    ∀ sign : PhysicalSign,
      -bankPaperCanonicalSymmetricHeightCellMass d ≤
        (Fintype.card
            (B.sampleData.SampleAt (none, sign)) : Real) *
          (betaProt / B.L)

/-- The weak symmetric-height source package.  It retains the common
geometry/capacity core and only the selector state consumed before P87. -/
structure BankPaperCanonicalSectionNineSymmetricHeightSourceStateInputsAt
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (K0 : Nat)
    (deltaStar : Real) where
  core : BankPaperCanonicalSectionNineSymmetricHeightCoreInputsAt
    B R certificate K0 deltaStar
  sourceState :
    BankPaperCanonicalSelectorSourceState
      (W := B.sampleData.W) R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate
        deltaStar (K0 + 1))
      (bankPaperCanonicalPostHfitGlobalSourceSelector
        B K0 R certificate deltaStar core.betaProt core.betaAct
          (bankPaperCanonicalScaledActiveSeed core.T core.q0))

/-- The single dependent analytic tail for the weak symmetric-height
source.  It is the exact union of the local P87 and endpoint-slack fields;
no second weak P87/slack hierarchy is introduced. -/
structure BankPaperCanonicalSectionNineSymmetricHeightDependentInputsAt
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (K0 : Nat)
    (deltaStar sigma Cpost : Real)
    (S :
      BankPaperCanonicalSectionNineSymmetricHeightSourceStateInputsAt
        B R certificate K0 deltaStar) where
  Ctarget : Real
  Cinitial : Real
  Cfixed : Real
  Cactive : Real
  gamma : Real
  radius : NNReal
  targetEnvelopes :
    B.HasTargetEnvelopes Ctarget
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget
          B R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          (bankPaperCanonicalPostHfitStructuredPreSelector
            B K0 R certificate deltaStar
              S.core.betaProt S.core.betaAct
              (bankPaperCanonicalScaledActiveSeed S.core.T S.core.q0)
              (bankPaperCanonicalSymmetricHeightCellMass S.core.d)
              (bankPaperCanonicalSymmetricHeightCellMass S.core.d))
          (bankPaperCanonicalScaledActiveSeed S.core.T S.core.q0)) 0 j)
  selectorDeficit :
    ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          (bankPaperCanonicalPostHfitStructuredPreSelector
            B K0 R certificate deltaStar
              S.core.betaProt S.core.betaAct
              (bankPaperCanonicalScaledActiveSeed S.core.T S.core.q0)
              (bankPaperCanonicalSymmetricHeightCellMass S.core.d)
              (bankPaperCanonicalSymmetricHeightCellMass S.core.d)) p) ≤
        Cinitial * B.q / ((p : Real) * B.L)
  activeLedger :
    ∀ m : B.sampleData.Sample,
      B.baseline.baseWeight m ≤ Cactive / B.L
  localP87 :
    ∀ (Delta : Band → Real),
      B.HasTargetEnvelopes Ctarget Delta →
      ∀ (markedTarget : Nat → Real) (N : Real),
        0 ≤ N →
        B.q ≤ (1 : Real) * N →
        (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
          abs (markedTarget p -
            B.paperMoment (B.markedValuation p) 0) ≤
              Cinitial * N / ((p : Real) * B.L)) →
        (∀ j, Delta j = B.markedBandResidual markedTarget 0 j) →
        ∀ {Fixed : Type} [Fintype Fixed],
          ∀ (fixedValue : Fixed → Nat) (fixedWeight : Fixed → Real)
            (quota : Int),
            (quota : Real) = (∑ f, fixedWeight f) + B.q →
            B.sampleData.HeadPatternsSeparated →
            (∀ x,
              BridgeData.frozenAmbientWeight
                fixedValue fixedWeight x ∈ Icc (0 : Real) 1) →
            (∀ m : B.sampleData.Sample,
              BridgeData.frozenAmbientWeight fixedValue fixedWeight
                  (B.sampleData.value m) ≤
                Cfixed / B.L) →
            (∀ m : B.sampleData.Sample,
              B.baseline.baseWeight m ≤ Cactive / B.L) →
            B.HasPaperProposition87Conclusion
              Delta radius markedTarget N Cpost
                fixedValue fixedWeight quota
  Cactive_nonneg : 0 ≤ Cactive
  gamma_nonneg : 0 ≤ gamma
  heightUpper :
    ∀ sign : PhysicalSign,
      bankPaperCanonicalSymmetricHeightCellMass S.core.d ≤
        (Fintype.card
            (B.sampleData.SampleAt (none, sign)) : Real) *
          (gamma / B.L)
  fixedRoom :
    S.core.betaProt + (Cactive + gamma) ≤ Cfixed
  C : Real
  C_one_le : 1 ≤ C
  W_large : 1 < B.sampleData.W
  physicalUpper :
    ∀ sign, B.sampleData.hi sign ≤ physicalBound C B.sampleData.n
  reserveGap : 0 < S.core.betaProt - sigma
  reserveLoss :
    ∀ sign : PhysicalSign,
      -bankPaperCanonicalSymmetricHeightCellMass S.core.d ≤
        (Fintype.card
            (B.sampleData.SampleAt (none, sign)) : Real) *
          ((S.core.betaProt - sigma) / B.L)
  largeL :
    Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) *
          Cactive + sigma ≤
      B.L
  nonsmooth :
    RoughCanonicalBalancedNonsmoothBounds
      R certificate deltaStar B.sampleData.W K0
        S.core.betaProt S.core.betaAct sigma

/-! ## Rounded-source compatibility builders -/

/-- Forget the source-only tangent witnesses from a legacy symmetric-height
source, retaining its selector-independent core. -/
def bankPaperCanonicalSectionNineSymmetricHeightCoreInputsAt_of_sourceInputs
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (K0 : Nat)
    (deltaStar : Real)
    (S : BankPaperCanonicalSectionNineSymmetricHeightSourceInputsAt
      B R certificate K0 deltaStar) :
    BankPaperCanonicalSectionNineSymmetricHeightCoreInputsAt
      B R certificate K0 deltaStar where
  betaProt := S.betaProt
  betaAct := S.betaAct
  q0 := S.q0
  d := S.d
  T := S.T
  betaProt_nonneg := S.betaProt_nonneg
  q0_one_le := S.q0_one_le
  baseline_seed := S.baseline_seed
  headSeparated := S.headSeparated
  activeSmooth := S.activeSmooth
  minusPool := S.minusPool
  plusPool := S.plusPool
  scalarCapacity := S.scalarCapacity
  fitLoss := S.fitLoss

/-- Project a legacy rounded symmetric-height source to its weak
source-state package. -/
def
    bankPaperCanonicalSectionNineSymmetricHeightSourceStateInputsAt_of_sourceInputs
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (K0 : Nat)
    (deltaStar : Real)
    (S : BankPaperCanonicalSectionNineSymmetricHeightSourceInputsAt
      B R certificate K0 deltaStar) :
    BankPaperCanonicalSectionNineSymmetricHeightSourceStateInputsAt
      B R certificate K0 deltaStar where
  core :=
    bankPaperCanonicalSectionNineSymmetricHeightCoreInputsAt_of_sourceInputs
      B R certificate K0 deltaStar S
  sourceState := by
    simpa only [
      bankPaperCanonicalSectionNineSymmetricHeightCoreInputsAt_of_sourceInputs]
      using
        (bankPaperCanonicalSelectorSourceState_of_roundedSelectorTangentInput
          R certificate (R.paperFixedExceptionalFactors deltaStar)
            (R.roughCanonicalGuardedCandidateSet certificate
              deltaStar (K0 + 1))
          B.partition.band S.sourceCellIndex S.sourcePointwiseUpper
          S.sourcePrefixUpper
          (bankPaperCanonicalPostHfitGlobalSourceSelector
            B K0 R certificate deltaStar S.betaProt S.betaAct
              (bankPaperCanonicalScaledActiveSeed S.T S.q0))
          S.roundedSource)

/-- Merge the legacy P87 and slack tails after projecting their rounded
source to the weak source-state package. -/
def
    bankPaperCanonicalSectionNineSymmetricHeightDependentInputsAt_of_p87_slack
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (K0 : Nat)
    (deltaStar sigma Cpost : Real)
    (S : BankPaperCanonicalSectionNineSymmetricHeightSourceInputsAt
      B R certificate K0 deltaStar)
    (A : BankPaperCanonicalSectionNineSymmetricHeightP87InputsAt
      B R certificate K0 deltaStar Cpost S)
    (N : BankPaperCanonicalSectionNineSymmetricHeightSlackInputsAt
      B R certificate K0 deltaStar sigma Cpost S A) :
    BankPaperCanonicalSectionNineSymmetricHeightDependentInputsAt
      B R certificate K0 deltaStar sigma Cpost
        (bankPaperCanonicalSectionNineSymmetricHeightSourceStateInputsAt_of_sourceInputs
          B R certificate K0 deltaStar S) where
  Ctarget := A.Ctarget
  Cinitial := A.Cinitial
  Cfixed := A.Cfixed
  Cactive := A.Cactive
  gamma := A.gamma
  radius := A.radius
  targetEnvelopes := A.targetEnvelopes
  selectorDeficit := A.selectorDeficit
  activeLedger := A.activeLedger
  localP87 := A.localP87
  Cactive_nonneg := A.Cactive_nonneg
  gamma_nonneg := A.gamma_nonneg
  heightUpper := A.heightUpper
  fixedRoom := A.fixedRoom
  C := N.C
  C_one_le := N.C_one_le
  W_large := N.W_large
  physicalUpper := N.physicalUpper
  reserveGap := N.reserveGap
  reserveLoss := N.reserveLoss
  largeL := N.largeL
  nonsmooth := N.nonsmooth

/-! ## Derived exact finite estimates -/

/-- A pointwise active-seed upper bound and a scalar upper bound for the
symmetric cell increment give the required upper bound for the rebalanced
placement seed. -/
theorem bankPaperCanonicalSymmetricHeightRebalance_le_div_log
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (T : BarycentricTarget B.sampleData) (q0 : Real) (d : Int)
    (Cactive gamma : Real)
    (hactive :
      ∀ m : B.sampleData.Sample,
        bankPaperCanonicalScaledActiveSeed T q0 m ≤ Cactive / B.L)
    (hgamma : 0 ≤ gamma)
    (hheight :
      ∀ sign : PhysicalSign,
        bankPaperCanonicalSymmetricHeightCellMass d ≤
          (Fintype.card
              (B.sampleData.SampleAt (none, sign)) : Real) *
            (gamma / B.L)) :
    ∀ m : B.sampleData.Sample,
      bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q0)
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d) m ≤
        (Cactive + gamma) / B.L := by
  intro m
  rcases hcell : B.sampleData.cellOf m with ⟨head, sign⟩
  cases head with
  | none =>
      have hcard : 0 <
          (Fintype.card
            (B.sampleData.SampleAt (none, sign)) : Real) := by
        exact_mod_cast B.sampleData.sampleAt_card_pos (none, sign)
      have hincrement :
          bankPaperCanonicalSymmetricHeightCellMass d /
              Fintype.card (B.sampleData.SampleAt (none, sign)) ≤
            gamma / B.L := by
        apply (div_le_iff₀ hcard).2
        simpa only [mul_comm] using hheight sign
      have hold :
          bankPaperCanonicalScaledActiveSeed T q0 m =
            (q0 * T.baseline.cellMass (none, sign)) /
              Fintype.card
                (B.sampleData.SampleAt (none, sign)) := by
        unfold bankPaperCanonicalScaledActiveSeed
          BaselineAllocation.baseWeight
        rw [hcell]
        ring
      calc
        bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
              (bankPaperCanonicalScaledActiveSeed T q0)
              (bankPaperCanonicalSymmetricHeightCellMass d)
              (bankPaperCanonicalSymmetricHeightCellMass d) m =
            bankPaperCanonicalScaledActiveSeed T q0 m +
              bankPaperCanonicalSymmetricHeightCellMass d /
                Fintype.card
                  (B.sampleData.SampleAt (none, sign)) := by
            rw [
              bankPaperCanonicalSymmetricHeightRebalance_apply_of_zeroHeadCell
                B.sampleData T q0 d m sign hcell,
              hold]
            unfold bankPaperCanonicalSymmetricHeightCellMass
            ring
        _ ≤ Cactive / B.L + gamma / B.L :=
          add_le_add (hactive m) hincrement
        _ = (Cactive + gamma) / B.L := by ring
  | some head =>
      have hunchanged :
          bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
              (bankPaperCanonicalScaledActiveSeed T q0)
              (bankPaperCanonicalSymmetricHeightCellMass d)
              (bankPaperCanonicalSymmetricHeightCellMass d) m =
            bankPaperCanonicalScaledActiveSeed T q0 m := by
        simp [bankPaperCanonicalTwoZeroHeadCellRebalance,
          bankPaperCanonicalUniformCellIncrement, hcell]
      rw [hunchanged]
      calc
        bankPaperCanonicalScaledActiveSeed T q0 m ≤
            Cactive / B.L := hactive m
        _ ≤ Cactive / B.L + gamma / B.L :=
          le_add_of_nonneg_right (div_nonneg hgamma B.L_pos.le)
        _ = (Cactive + gamma) / B.L := by ring

/-! ## Assembly into the generic finite interface -/

/-- The weak symmetric-height source state and its single dependent
analytic tail produce the generic source-state local Post-Hfit input.
The actual measure, frozen ledger, reserve, placement-seed bound, and signed
row identity are all proved inside the connector. -/
theorem
    bankPaperCanonicalSectionNinePostHfitSourceStateLocalInputsAt_of_symmetricHeight
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar sigma Cpost : Real)
    (Sweak :
      BankPaperCanonicalSectionNineSymmetricHeightSourceStateInputsAt
      B R certificate K0 deltaStar)
    (A : BankPaperCanonicalSectionNineSymmetricHeightDependentInputsAt
      B R certificate K0 deltaStar sigma Cpost Sweak) :
    BankPaperCanonicalSectionNinePostHfitSourceStateLocalInputsAt
      (K0 := K0) B R certificate deltaStar sigma Cpost := by
  let S := Sweak.core
  let oldSeed : B.sampleData.Sample → Real :=
    bankPaperCanonicalScaledActiveSeed S.T S.q0
  let cellMass : Real :=
    bankPaperCanonicalSymmetricHeightCellMass S.d
  let sourceSelector : Nat → Real :=
    bankPaperCanonicalPostHfitGlobalSourceSelector
      B K0 R certificate deltaStar S.betaProt S.betaAct oldSeed
  have hminusCapacity :
      ∀ m : B.sampleData.Sample,
        B.sampleData.cellOf m = (none, .minus) →
          0 ≤ bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed cellMass cellMass m ∧
            S.betaProt / B.L +
                bankPaperCanonicalTwoZeroHeadCellRebalance
                  B.sampleData oldSeed cellMass cellMass m ≤
              1 := by
    intro m hm
    constructor
    · exact
        bankPaperCanonicalSymmetricHeightRebalance_nonneg_of_cellMass
          B.sampleData S.T S.q0 S.d m .minus hm
            (S.scalarCapacity .minus).1
    · exact
        bankPaperCanonicalSymmetricHeightRebalance_protected_le_one_of_cellMass
          B S.T S.q0 S.d S.betaProt m .minus hm
            (S.scalarCapacity .minus).2
  have hplusCapacity :
      ∀ m : B.sampleData.Sample,
        B.sampleData.cellOf m = (none, .plus) →
          0 ≤ bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed cellMass cellMass m ∧
            S.betaProt / B.L +
                bankPaperCanonicalTwoZeroHeadCellRebalance
                  B.sampleData oldSeed cellMass cellMass m ≤
              1 := by
    intro m hm
    constructor
    · exact
        bankPaperCanonicalSymmetricHeightRebalance_nonneg_of_cellMass
          B.sampleData S.T S.q0 S.d m .plus hm
            (S.scalarCapacity .plus).1
    · exact
        bankPaperCanonicalSymmetricHeightRebalance_protected_le_one_of_cellMass
          B S.T S.q0 S.d S.betaProt m .plus hm
            (S.scalarCapacity .plus).2
  have SsourceState :
      BankPaperCanonicalSelectorSourceState
        (W := B.sampleData.W) R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K0 + 1)
          B R certificate deltaStar S.betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 S.betaProt S.betaAct)
            (S.betaProt + S.betaAct)
            (bankPaperCanonicalScaledActiveSeed S.T S.q0)) := by
    simpa only [S,
      bankPaperCanonicalPostHfitGlobalSourceSelector,
      bankPaperCanonicalPostHfitBalancedAlpha] using Sweak.sourceState
  have Hplacement :
      BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K0 + 1)
        B R certificate (R.paperFixedExceptionalFactors deltaStar)
          deltaStar S.betaProt sourceSelector
          (bankPaperCanonicalTwoZeroHeadCellRebalance
            B.sampleData oldSeed cellMass cellMass) := by
    simpa only [oldSeed, cellMass, sourceSelector,
      bankPaperCanonicalPostHfitGlobalSourceSelector,
      bankPaperCanonicalPostHfitBalancedAlpha] using
      (bankPaperCanonicalGlobalCorrectedStructuredAdditivePlacement_twoZeroHeadCells_of_sourceState
        (K := K0 + 1) B R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          deltaStar S.betaProt
          (bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 S.betaProt S.betaAct)
          (S.betaProt + S.betaAct) S.betaProt_nonneg
          (bankPaperCanonicalScaledActiveSeed S.T S.q0)
          (bankPaperCanonicalSymmetricHeightCellMass S.d)
          (bankPaperCanonicalSymmetricHeightCellMass S.d)
          (-S.d) SsourceState S.headSeparated
          S.activeSmooth S.minusPool S.plusPool
          hminusCapacity hplusCapacity
          (bankPaperCanonicalSymmetricHeightCellMass_add_self S.d))
  have Hmeasure :
      BankPaperCanonicalActualActiveMeasureConstructor
        B.sampleData S.T
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        (bankPaperCanonicalPostHfitStructuredPreSelector
          B K0 R certificate deltaStar S.betaProt S.betaAct
            (bankPaperCanonicalScaledActiveSeed S.T S.q0)
            (bankPaperCanonicalSymmetricHeightCellMass S.d)
            (bankPaperCanonicalSymmetricHeightCellMass S.d))
        (bankPaperCanonicalScaledActiveSeed S.T S.q0) := by
    simpa only [bankPaperCanonicalPostHfitStructuredPreSelector,
      bankPaperCanonicalPostHfitGlobalSourceSelector,
      bankPaperCanonicalPostHfitBalancedAlpha] using
      (bankPaperCanonicalActualActiveMeasureConstructor_symmetricHeight
        (K := K0 + 1) B R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          deltaStar S.betaProt sourceSelector S.T S.q0 S.d
          S.q0_one_le S.headSeparated S.activeSmooth
          S.betaProt_nonneg S.minusPool S.plusPool S.fitLoss
          Hplacement)
  have hfrozenLedger :
      ∀ m : B.sampleData.Sample,
        BridgeData.frozenAmbientWeight
            (bankPaperCanonicalActualFrozenValue
              (candidates :=
                R.roughCanonicalGuardedCandidateSet certificate
                  deltaStar (K0 + 1)))
            (bankPaperCanonicalActualFrozenWeight B.sampleData
              (R.roughCanonicalGuardedCandidateSet certificate
                deltaStar (K0 + 1))
              (bankPaperCanonicalPostHfitStructuredPreSelector
                B K0 R certificate deltaStar S.betaProt S.betaAct
                  (bankPaperCanonicalScaledActiveSeed S.T S.q0)
                  (bankPaperCanonicalSymmetricHeightCellMass S.d)
                  (bankPaperCanonicalSymmetricHeightCellMass S.d))
              (bankPaperCanonicalScaledActiveSeed S.T S.q0))
            (B.sampleData.value m) ≤
          A.Cfixed / B.L := by
    intro m
    have hraw :=
      bankPaperCanonicalActualFrozenWeight_symmetricHeight_le
        (K := K0 + 1) B R certificate deltaStar S.betaProt
          S.betaProt_nonneg sourceSelector S.T S.q0 S.d
          S.headSeparated Hmeasure A.gamma A.gamma_nonneg
          A.heightUpper m
    have hconstant :
        S.betaProt + A.gamma ≤ A.Cfixed := by
      nlinarith [A.fixedRoom, A.Cactive_nonneg]
    have hdiv :
        (S.betaProt + A.gamma) / B.L ≤ A.Cfixed / B.L :=
      div_le_div_of_nonneg_right hconstant B.L_pos.le
    exact hraw.trans hdiv
  have hplacementSeedUpper :
      ∀ m : B.sampleData.Sample,
        bankPaperCanonicalTwoZeroHeadCellRebalance
            B.sampleData
            (bankPaperCanonicalScaledActiveSeed S.T S.q0)
            (bankPaperCanonicalSymmetricHeightCellMass S.d)
            (bankPaperCanonicalSymmetricHeightCellMass S.d) m ≤
          (A.Cactive + A.gamma) / B.L := by
    apply bankPaperCanonicalSymmetricHeightRebalance_le_div_log
      B S.T S.q0 S.d A.Cactive A.gamma
    · intro m
      rw [← S.baseline_seed m]
      exact A.activeLedger m
    · exact A.gamma_nonneg
    · exact A.heightUpper
  have hprotectedReserve :
      ∀ x ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W (K0 + 1) 1,
        sigma / B.L +
            bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalScaledActiveSeed S.T S.q0) x ≤
          bankPaperCanonicalPostHfitStructuredPreSelector
            B K0 R certificate deltaStar S.betaProt S.betaAct
              (bankPaperCanonicalScaledActiveSeed S.T S.q0)
              (bankPaperCanonicalSymmetricHeightCellMass S.d)
              (bankPaperCanonicalSymmetricHeightCellMass S.d) x := by
    simpa only [bankPaperCanonicalPostHfitStructuredPreSelector,
      bankPaperCanonicalPostHfitGlobalSourceSelector,
      bankPaperCanonicalPostHfitBalancedAlpha] using
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_protectedReserve_symmetricHeight
        (K := K0 + 1) B R certificate deltaStar S.betaProt sigma
          sourceSelector S.T S.q0 S.d S.headSeparated
          A.reserveGap A.reserveLoss)
  unfold BankPaperCanonicalSectionNinePostHfitSourceStateLocalInputsAt
  refine
    ⟨S.betaProt, S.betaAct,
      bankPaperCanonicalScaledActiveSeed S.T S.q0,
      bankPaperCanonicalScaledActiveSeed S.T S.q0,
      bankPaperCanonicalSymmetricHeightCellMass S.d,
      bankPaperCanonicalSymmetricHeightCellMass S.d,
      -S.d, S.T, A.Ctarget, A.Cinitial,
      A.Cfixed, A.Cactive, A.radius, A.Cactive + A.gamma, A.C,
      S.betaProt_nonneg, Sweak.sourceState, S.headSeparated,
      S.activeSmooth, S.minusPool, S.plusPool,
      hminusCapacity, hplusCapacity,
      bankPaperCanonicalSymmetricHeightCellMass_add_self S.d,
      Hmeasure, S.baseline_seed, A.targetEnvelopes,
      A.selectorDeficit, hfrozenLedger, A.activeLedger,
      A.localP87, add_nonneg A.Cactive_nonneg A.gamma_nonneg,
      hplacementSeedUpper, A.fixedRoom, A.C_one_le, A.W_large,
      A.physicalUpper, A.Cactive_nonneg, hprotectedReserve,
      A.largeL, A.nonsmooth⟩

/-- The backwards-compatible rounded-source connector, preserving the
original strong finite interface. -/
theorem bankPaperCanonicalSectionNinePostHfitLocalInputsAt_of_symmetricHeight
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar sigma Cpost : Real)
    (S : BankPaperCanonicalSectionNineSymmetricHeightSourceInputsAt
      B R certificate K0 deltaStar)
    (A : BankPaperCanonicalSectionNineSymmetricHeightP87InputsAt
      B R certificate K0 deltaStar Cpost S)
    (N : BankPaperCanonicalSectionNineSymmetricHeightSlackInputsAt
      B R certificate K0 deltaStar sigma Cpost S A) :
    BankPaperCanonicalSectionNinePostHfitLocalInputsAt
      (K0 := K0) B R certificate deltaStar sigma Cpost := by
  let oldSeed : B.sampleData.Sample → Real :=
    bankPaperCanonicalScaledActiveSeed S.T S.q0
  let cellMass : Real :=
    bankPaperCanonicalSymmetricHeightCellMass S.d
  let sourceSelector : Nat → Real :=
    bankPaperCanonicalPostHfitGlobalSourceSelector
      B K0 R certificate deltaStar S.betaProt S.betaAct oldSeed
  have hminusCapacity :
      ∀ m : B.sampleData.Sample,
        B.sampleData.cellOf m = (none, .minus) →
          0 ≤ bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed cellMass cellMass m ∧
            S.betaProt / B.L +
                bankPaperCanonicalTwoZeroHeadCellRebalance
                  B.sampleData oldSeed cellMass cellMass m ≤
              1 := by
    intro m hm
    constructor
    · exact
        bankPaperCanonicalSymmetricHeightRebalance_nonneg_of_cellMass
          B.sampleData S.T S.q0 S.d m .minus hm
            (S.scalarCapacity .minus).1
    · exact
        bankPaperCanonicalSymmetricHeightRebalance_protected_le_one_of_cellMass
          B S.T S.q0 S.d S.betaProt m .minus hm
            (S.scalarCapacity .minus).2
  have hplusCapacity :
      ∀ m : B.sampleData.Sample,
        B.sampleData.cellOf m = (none, .plus) →
          0 ≤ bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed cellMass cellMass m ∧
            S.betaProt / B.L +
                bankPaperCanonicalTwoZeroHeadCellRebalance
                  B.sampleData oldSeed cellMass cellMass m ≤
              1 := by
    intro m hm
    constructor
    · exact
        bankPaperCanonicalSymmetricHeightRebalance_nonneg_of_cellMass
          B.sampleData S.T S.q0 S.d m .plus hm
            (S.scalarCapacity .plus).1
    · exact
        bankPaperCanonicalSymmetricHeightRebalance_protected_le_one_of_cellMass
          B S.T S.q0 S.d S.betaProt m .plus hm
            (S.scalarCapacity .plus).2
  have SsourceState :
      BankPaperCanonicalSelectorSourceState
        (W := B.sampleData.W) R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K0 + 1)
          B R certificate deltaStar S.betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 S.betaProt S.betaAct)
            (S.betaProt + S.betaAct)
            (bankPaperCanonicalScaledActiveSeed S.T S.q0)) := by
    simpa only [
      bankPaperCanonicalPostHfitGlobalSourceSelector,
      bankPaperCanonicalPostHfitBalancedAlpha] using
      (bankPaperCanonicalSelectorSourceState_of_roundedSelectorTangentInput
        R certificate (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
        B.partition.band S.sourceCellIndex S.sourcePointwiseUpper
        S.sourcePrefixUpper
        (bankPaperCanonicalPostHfitGlobalSourceSelector
          B K0 R certificate deltaStar S.betaProt S.betaAct
            (bankPaperCanonicalScaledActiveSeed S.T S.q0))
        S.roundedSource)
  have Hplacement :
      BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K0 + 1)
        B R certificate (R.paperFixedExceptionalFactors deltaStar)
          deltaStar S.betaProt sourceSelector
          (bankPaperCanonicalTwoZeroHeadCellRebalance
            B.sampleData oldSeed cellMass cellMass) := by
    simpa only [oldSeed, cellMass, sourceSelector,
      bankPaperCanonicalPostHfitGlobalSourceSelector,
      bankPaperCanonicalPostHfitBalancedAlpha] using
      (bankPaperCanonicalGlobalCorrectedStructuredAdditivePlacement_twoZeroHeadCells_of_sourceState
        (K := K0 + 1) B R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          deltaStar S.betaProt
          (bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 S.betaProt S.betaAct)
          (S.betaProt + S.betaAct) S.betaProt_nonneg
          (bankPaperCanonicalScaledActiveSeed S.T S.q0)
          (bankPaperCanonicalSymmetricHeightCellMass S.d)
          (bankPaperCanonicalSymmetricHeightCellMass S.d)
          (-S.d) SsourceState S.headSeparated
          S.activeSmooth S.minusPool S.plusPool
          hminusCapacity hplusCapacity
          (bankPaperCanonicalSymmetricHeightCellMass_add_self S.d))
  have Hmeasure :
      BankPaperCanonicalActualActiveMeasureConstructor
        B.sampleData S.T
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        (bankPaperCanonicalPostHfitStructuredPreSelector
          B K0 R certificate deltaStar S.betaProt S.betaAct
            (bankPaperCanonicalScaledActiveSeed S.T S.q0)
            (bankPaperCanonicalSymmetricHeightCellMass S.d)
            (bankPaperCanonicalSymmetricHeightCellMass S.d))
        (bankPaperCanonicalScaledActiveSeed S.T S.q0) := by
    simpa only [bankPaperCanonicalPostHfitStructuredPreSelector,
      bankPaperCanonicalPostHfitGlobalSourceSelector,
      bankPaperCanonicalPostHfitBalancedAlpha] using
      (bankPaperCanonicalActualActiveMeasureConstructor_symmetricHeight
        (K := K0 + 1) B R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          deltaStar S.betaProt sourceSelector S.T S.q0 S.d
          S.q0_one_le S.headSeparated S.activeSmooth
          S.betaProt_nonneg S.minusPool S.plusPool S.fitLoss
          Hplacement)
  have hfrozenLedger :
      ∀ m : B.sampleData.Sample,
        BridgeData.frozenAmbientWeight
            (bankPaperCanonicalActualFrozenValue
              (candidates :=
                R.roughCanonicalGuardedCandidateSet certificate
                  deltaStar (K0 + 1)))
            (bankPaperCanonicalActualFrozenWeight B.sampleData
              (R.roughCanonicalGuardedCandidateSet certificate
                deltaStar (K0 + 1))
              (bankPaperCanonicalPostHfitStructuredPreSelector
                B K0 R certificate deltaStar S.betaProt S.betaAct
                  (bankPaperCanonicalScaledActiveSeed S.T S.q0)
                  (bankPaperCanonicalSymmetricHeightCellMass S.d)
                  (bankPaperCanonicalSymmetricHeightCellMass S.d))
              (bankPaperCanonicalScaledActiveSeed S.T S.q0))
            (B.sampleData.value m) ≤
          A.Cfixed / B.L := by
    intro m
    have hraw :=
      bankPaperCanonicalActualFrozenWeight_symmetricHeight_le
        (K := K0 + 1) B R certificate deltaStar S.betaProt
          S.betaProt_nonneg sourceSelector S.T S.q0 S.d
          S.headSeparated Hmeasure A.gamma A.gamma_nonneg
          A.heightUpper m
    have hconstant :
        S.betaProt + A.gamma ≤ A.Cfixed := by
      nlinarith [A.fixedRoom, A.Cactive_nonneg]
    have hdiv :
        (S.betaProt + A.gamma) / B.L ≤ A.Cfixed / B.L :=
      div_le_div_of_nonneg_right hconstant B.L_pos.le
    exact hraw.trans hdiv
  have hplacementSeedUpper :
      ∀ m : B.sampleData.Sample,
        bankPaperCanonicalTwoZeroHeadCellRebalance
            B.sampleData
            (bankPaperCanonicalScaledActiveSeed S.T S.q0)
            (bankPaperCanonicalSymmetricHeightCellMass S.d)
            (bankPaperCanonicalSymmetricHeightCellMass S.d) m ≤
          (A.Cactive + A.gamma) / B.L := by
    apply bankPaperCanonicalSymmetricHeightRebalance_le_div_log
      B S.T S.q0 S.d A.Cactive A.gamma
    · intro m
      rw [← S.baseline_seed m]
      exact A.activeLedger m
    · exact A.gamma_nonneg
    · exact A.heightUpper
  have hprotectedReserve :
      ∀ x ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W (K0 + 1) 1,
        sigma / B.L +
            bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalScaledActiveSeed S.T S.q0) x ≤
          bankPaperCanonicalPostHfitStructuredPreSelector
            B K0 R certificate deltaStar S.betaProt S.betaAct
              (bankPaperCanonicalScaledActiveSeed S.T S.q0)
              (bankPaperCanonicalSymmetricHeightCellMass S.d)
              (bankPaperCanonicalSymmetricHeightCellMass S.d) x := by
    simpa only [bankPaperCanonicalPostHfitStructuredPreSelector,
      bankPaperCanonicalPostHfitGlobalSourceSelector,
      bankPaperCanonicalPostHfitBalancedAlpha] using
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_protectedReserve_symmetricHeight
        (K := K0 + 1) B R certificate deltaStar S.betaProt sigma
          sourceSelector S.T S.q0 S.d S.headSeparated
          N.reserveGap N.reserveLoss)
  unfold BankPaperCanonicalSectionNinePostHfitLocalInputsAt
  refine
    ⟨S.betaProt, S.betaAct,
      bankPaperCanonicalScaledActiveSeed S.T S.q0,
      bankPaperCanonicalScaledActiveSeed S.T S.q0,
      bankPaperCanonicalSymmetricHeightCellMass S.d,
      bankPaperCanonicalSymmetricHeightCellMass S.d,
      -S.d, S.sourceCellIndex, S.sourcePointwiseUpper,
      S.sourcePrefixUpper, S.T, A.Ctarget, A.Cinitial,
      A.Cfixed, A.Cactive, A.radius, A.Cactive + A.gamma, N.C,
      S.betaProt_nonneg, S.roundedSource, S.headSeparated,
      S.activeSmooth, S.minusPool, S.plusPool,
      hminusCapacity, hplusCapacity,
      bankPaperCanonicalSymmetricHeightCellMass_add_self S.d,
      Hmeasure, S.baseline_seed, A.targetEnvelopes,
      A.selectorDeficit, hfrozenLedger, A.activeLedger,
      A.localP87, add_nonneg A.Cactive_nonneg A.gamma_nonneg,
      hplacementSeedUpper, A.fixedRoom, N.C_one_le, N.W_large,
      N.physicalUpper, A.Cactive_nonneg, hprotectedReserve,
      N.largeL, N.nonsmooth⟩

end BankPaperRealization

end

end Erdos390.WholePaper
