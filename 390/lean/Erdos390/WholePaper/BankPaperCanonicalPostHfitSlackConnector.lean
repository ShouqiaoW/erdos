import Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellPostHfitConnector
import Erdos390.WholePaper.BankPaperCanonicalGlobalCorrectedSourceSelector
import Erdos390.WholePaper.BankPaperCanonicalNonsmoothSlackClosure

/-!
# Exact Post-Hfit endpoint/slack connector

This file joins the three finite interfaces immediately before the remaining
Section 9 tangent-flow and traffic assembly:

* the global corrected source and its two-zero-head-cell structured placement;
* the split-seed Post-Hfit endpoint handoff; and
* the balanced nonsmooth density bounds used by the actual endpoint-slack
  theorem.

The placement seed is the two-cell rebalance of `oldSeed`.  The actual bridge
measure, marked target, frozen weights, P87 path, and endpoint all retain the
single input `activeSeed`.  The returned package records the exact path and
defines `endpoint` to be the push-forward of that same path and active seed.

This connector deliberately stops at
`BankPaperCanonicalGuardedEndpointSlackConstruction`.  It does not assume or
conclude a tangent flow, collision census, clean-list traffic estimate, or a
terminal Section 9 output.  Those obligations remain visible downstream.
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

/-! ## Canonical balanced source and structured preselector -/

/-- The balanced postcharge parameter used at the actual rough level
`K0 + 1`. -/
def bankPaperCanonicalPostHfitBalancedAlpha
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (c : Real) (K0 : Nat)
    (betaProt betaAct : Real) : Real :=
  roughHeadBalancedAlpha B.sampleData.W B.sampleData.n
    (upperTailLength c B.sampleData.n) (K0 + 1)
    (betaProt + betaAct) B.L

/-- The global corrected source at the balanced postcharge parameters. -/
def bankPaperCanonicalPostHfitGlobalSourceSelector
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
    (oldSeed : B.sampleData.Sample -> Real) : Nat -> Real :=
  bankPaperCanonicalGlobalCorrectedSourceSelector (K := K0 + 1)
    B R certificate deltaStar betaProt
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      (betaProt + betaAct) oldSeed

/-- The literal structured selector passed to the split-seed Post-Hfit
interface.  Its additive placement seed is the two-zero-cell rebalance, not
the actual bridge seed. -/
def bankPaperCanonicalPostHfitStructuredPreSelector
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
    (minusMass plusMass : Real) : Nat -> Real :=
  bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
    (K := K0 + 1) B R certificate deltaStar betaProt
      (bankPaperCanonicalPostHfitGlobalSourceSelector
        B K0 R certificate deltaStar betaProt betaAct oldSeed)
      (bankPaperCanonicalTwoZeroHeadCellRebalance
        B.sampleData oldSeed minusMass plusMass)

/-! ## Exact finite output package -/

/-- The finite output produced by the connector.

The first conjunct preserves the constructed global structured placement.
The next four conjuncts preserve the exact Post-Hfit quota, path, endpoint
identity, and rounded tangent input.  The last conjunct is the endpoint
slack construction for that very endpoint. -/
def BankPaperCanonicalPostHfitGuardedSlackPackage
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
    (fixed : Finset Nat)
    (deltaStar betaProt betaAct sigma : Real)
    (oldSeed activeSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass : Real)
    (radius : NNReal) (Cpost : Real)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (quota : Int) (path : Real -> B.ParamSpace)
    (endpoint : Nat -> Real) : Prop :=
  let candidates :=
    R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1)
  let sourceSelector :=
    bankPaperCanonicalPostHfitGlobalSourceSelector
      B K0 R certificate deltaStar betaProt betaAct oldSeed
  let placementSeed :=
    bankPaperCanonicalTwoZeroHeadCellRebalance
      B.sampleData oldSeed minusMass plusMass
  let preSelector :=
    bankPaperCanonicalPostHfitStructuredPreSelector
      B K0 R certificate deltaStar betaProt betaAct oldSeed
        minusMass plusMass
  let markedTarget :=
    bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
      candidates preSelector activeSeed
  let Delta := fun j => B.markedBandResidual markedTarget 0 j
  BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K0 + 1)
      B R certificate fixed deltaStar betaProt
        sourceSelector placementSeed ∧
    B.HasPaperProposition87Conclusion
      Delta radius markedTarget B.q Cpost
      (bankPaperCanonicalActualFrozenValue (candidates := candidates))
      (bankPaperCanonicalActualFrozenWeight B.sampleData candidates
        preSelector activeSeed)
      quota ∧
    B.IsPaperProposition87Path
      Delta radius markedTarget B.q Cpost
      (bankPaperCanonicalActualFrozenValue (candidates := candidates))
      (bankPaperCanonicalActualFrozenWeight B.sampleData candidates
        preSelector activeSeed)
      quota path ∧
    endpoint =
      bankPaperCanonicalActualP87EndpointSelector B candidates
        preSelector activeSeed path ∧
    BankPaperCanonicalRoundedSelectorTangentInput R certificate fixed
      candidates B.partition.band cellIndex
      (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
      (tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
        B.partition.band cellIndex)
      endpoint ∧
    R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
      deltaStar B.sampleData.W (K0 + 1)
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      (betaProt + betaAct) B.L sigma endpoint

/-! ## Production connector -/

/-- From the minimal global source state, construct the structured placement,
pass it through the split-seed Post-Hfit endpoint interface, and close both
the smooth and nonsmooth endpoint-slack obligations.  Source-band balance
and tangent residual bounds are not inputs to this theorem.

All numerical and bridge hypotheses used by the constituent interfaces stay
explicit.  In particular, `Cplacement` controls the rebalanced placement
seed, while `Cactive` controls the actual bridge seed; no equality between
those constants or seeds is introduced. -/
theorem exists_bankPaperCanonicalPostHfitGuardedSlackPackage_of_sourceState
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
    (fixed : Finset Nat)
    (deltaStar betaProt betaAct sigma : Real)
    (hbetaProt : 0 <= betaProt)
    (oldSeed activeSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass : Real) (rowChange : Int)
    (Ssource : BankPaperCanonicalSelectorSourceState
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1))
      (bankPaperCanonicalPostHfitGlobalSourceSelector
        B K0 R certificate deltaStar betaProt betaAct oldSeed))
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1)
    (hminus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W (K0 + 1) 1)
    (hplus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W (K0 + 1) 1)
    (hminusCapacity : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        0 <= bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass m ∧
        betaProt / B.L +
            bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass m <= 1)
    (hplusCapacity : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        0 <= bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass m ∧
        betaProt / B.L +
            bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass m <= 1)
    (hmass : minusMass + plusMass = (rowChange : Real))
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1))
      (bankPaperCanonicalPostHfitStructuredPreSelector
        B K0 R certificate deltaStar betaProt betaAct oldSeed
          minusMass plusMass)
      activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (Ctarget Cinitial Cfixed Cactive : Real)
    (henv : B.HasTargetEnvelopes Ctarget
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
          (R.roughCanonicalGuardedCandidateSet
            certificate deltaStar (K0 + 1))
          (bankPaperCanonicalPostHfitStructuredPreSelector
            B K0 R certificate deltaStar betaProt betaAct oldSeed
              minusMass plusMass)
          activeSeed) 0 j))
    (hdeficit : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed
          (R.roughCanonicalGuardedCandidateSet
            certificate deltaStar (K0 + 1))
          (bankPaperCanonicalPostHfitStructuredPreSelector
            B K0 R certificate deltaStar betaProt betaAct oldSeed
              minusMass plusMass) p) <=
        Cinitial * B.q / ((p : Real) * B.L))
    (hfrozenLedger : forall m : B.sampleData.Sample,
      BridgeData.frozenAmbientWeight
          (bankPaperCanonicalActualFrozenValue
            (candidates :=
              R.roughCanonicalGuardedCandidateSet
                certificate deltaStar (K0 + 1)))
          (bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet
              certificate deltaStar (K0 + 1))
            (bankPaperCanonicalPostHfitStructuredPreSelector
              B K0 R certificate deltaStar betaProt betaAct oldSeed
                minusMass plusMass)
            activeSeed)
          (B.sampleData.value m) <= Cfixed / B.L)
    (hactiveLedger : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (radius : NNReal) (Cpost : Real)
    (hP87 :
      forall (Delta : Band -> Real),
        B.HasTargetEnvelopes Ctarget Delta ->
        forall (markedTarget : Nat -> Real) (N : Real),
          0 <= N ->
          B.q <= (1 : Real) * N ->
          (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
            abs (markedTarget p -
              B.paperMoment (B.markedValuation p) 0) <=
                Cinitial * N / ((p : Real) * B.L)) ->
          (forall j,
            Delta j = B.markedBandResidual markedTarget 0 j) ->
          forall {Fixed : Type} [Fintype Fixed]
            (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
            (quota : Int),
            (quota : Real) = (∑ f, fixedWeight f) + B.q ->
            B.sampleData.HeadPatternsSeparated ->
            (forall x,
              BridgeData.frozenAmbientWeight
                fixedValue fixedWeight x ∈ Icc (0 : Real) 1) ->
            (forall m : B.sampleData.Sample,
              BridgeData.frozenAmbientWeight fixedValue fixedWeight
                (B.sampleData.value m) <= Cfixed / B.L) ->
            (forall m : B.sampleData.Sample,
              B.baseline.baseWeight m <= Cactive / B.L) ->
            B.HasPaperProposition87Conclusion Delta radius
              markedTarget N Cpost fixedValue fixedWeight quota)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (Cplacement : Real) (hCplacement : 0 <= Cplacement)
    (hplacementSeedUpper : forall m : B.sampleData.Sample,
      bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass m <=
        Cplacement / B.L)
    (hfixed : betaProt + Cplacement <= Cfixed)
    (C : Real) (hC : 1 <= C) (hW : 1 < B.sampleData.W)
    (hhi : forall sign,
      B.sampleData.hi sign <= physicalBound C B.sampleData.n)
    (hCactive : 0 <= Cactive)
    (hprotectedReserve : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W (K0 + 1) 1,
      sigma / B.L +
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData activeSeed x <=
        bankPaperCanonicalPostHfitStructuredPreSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed
            minusMass plusMass x)
    (hlarge : Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive + sigma <= B.L)
    (Hnonsmooth : RoughCanonicalBalancedNonsmoothBounds
      R certificate deltaStar B.sampleData.W K0
        betaProt betaAct sigma) :
    ∃ quota : Int, ∃ path : Real -> B.ParamSpace,
    ∃ endpoint : Nat -> Real,
    BankPaperCanonicalPostHfitGuardedSlackPackage
        B K0 R certificate fixed deltaStar betaProt betaAct sigma
          oldSeed activeSeed minusMass plusMass radius Cpost cellIndex
          quota path endpoint := by
  have Sglobal :
      BankPaperCanonicalSelectorSourceState
        (W := B.sampleData.W) R certificate fixed
        (R.roughCanonicalGuardedCandidateSet
          certificate deltaStar (K0 + 1))
        (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K0 + 1)
          B R certificate deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            (betaProt + betaAct) oldSeed) := by
    simpa only [
      bankPaperCanonicalPostHfitGlobalSourceSelector,
      bankPaperCanonicalPostHfitBalancedAlpha] using Ssource
  have Hplacement :
      BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K0 + 1)
        B R certificate fixed deltaStar betaProt
        (bankPaperCanonicalPostHfitGlobalSourceSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed)
        (bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass) := by
    simpa only [
      bankPaperCanonicalPostHfitGlobalSourceSelector,
      bankPaperCanonicalPostHfitBalancedAlpha] using
      (bankPaperCanonicalGlobalCorrectedStructuredAdditivePlacement_twoZeroHeadCells_of_sourceState
        (K := K0 + 1) B R certificate fixed deltaStar betaProt
          (bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct)
          (betaProt + betaAct) hbetaProt oldSeed minusMass plusMass
          rowChange Sglobal hsep hactiveSmooth hminus hplus
          hminusCapacity hplusCapacity hmass)
  obtain ⟨hpreUpper, hpreNonsmooth⟩ :=
    bankPaperCanonicalGlobalCorrectedStructuredPlacement_slackInputs
      (K := K0 + 1) B R certificate deltaStar betaProt
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) oldSeed
        (bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass)
        hactiveSmooth hsep Cplacement hCplacement hplacementSeedUpper
        Cfixed hfixed
  obtain ⟨quota, path, endpoint, Hfit, Hpath, hendpoint, Sendpoint⟩ :=
    exists_bankPaperCanonicalActualP87EndpointSelector_of_localCanonical_structuredAdditivePlacement_splitSeed
      (K := K0 + 1) B R certificate fixed deltaStar betaProt
      (bankPaperCanonicalPostHfitGlobalSourceSelector
        B K0 R certificate deltaStar betaProt betaAct oldSeed)
      (bankPaperCanonicalTwoZeroHeadCellRebalance
        B.sampleData oldSeed minusMass plusMass)
      activeSeed Hmeasure hseed Hplacement hsep
      Ctarget Cinitial Cfixed Cactive henv hdeficit hfrozenLedger
      hactiveLedger radius Cpost hP87 cellIndex
  have hactiveSeed : forall m : B.sampleData.Sample,
      activeSeed m <= Cactive / B.L := by
    intro m
    rw [← hseed m]
    exact hactiveLedger m
  have hnonsmoothBounds :=
    RoughCanonicalBalancedNonsmoothBounds.to_actualEndpointBounds
      B R certificate deltaStar betaProt betaAct sigma Hnonsmooth
  have HslackActual :=
    bankPaperCanonicalActualP87EndpointSelector_guardedSlackConstruction_of_reserve
      (K := K0 + 1) B R certificate deltaStar
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      (betaProt + betaAct)
      (bankPaperCanonicalPostHfitStructuredPreSelector
        B K0 R certificate deltaStar betaProt betaAct oldSeed
          minusMass plusMass)
      activeSeed Hmeasure hseed
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
          (R.roughCanonicalGuardedCandidateSet
            certificate deltaStar (K0 + 1))
          (bankPaperCanonicalPostHfitStructuredPreSelector
            B K0 R certificate deltaStar betaProt betaAct oldSeed
              minusMass plusMass)
          activeSeed) 0 j)
      radius
      (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
        (R.roughCanonicalGuardedCandidateSet
          certificate deltaStar (K0 + 1))
        (bankPaperCanonicalPostHfitStructuredPreSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed
            minusMass plusMass)
        activeSeed)
      B.q Cpost quota path Hpath C sigma Cfixed Cactive
      hC hW hhi hsep hCactive hactiveSeed hprotectedReserve hpreUpper
      hlarge hnonsmoothBounds hpreNonsmooth
  have Hslack :
      R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
        deltaStar B.sampleData.W (K0 + 1)
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) B.L sigma endpoint := by
    rw [hendpoint]
    exact HslackActual
  refine ⟨quota, path, endpoint, ?_⟩
  unfold BankPaperCanonicalPostHfitGuardedSlackPackage
  exact
    ⟨Hplacement, Hfit, Hpath, hendpoint, Sendpoint, Hslack⟩

/-- Compatibility entry point for a fully rounded source.  The rounded
input is projected to the minimal source state consumed by the primary
Post-Hfit constructor. -/
theorem exists_bankPaperCanonicalPostHfitGuardedSlackPackage
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
    (fixed : Finset Nat)
    (deltaStar betaProt betaAct sigma : Real)
    (hbetaProt : 0 <= betaProt)
    (oldSeed activeSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass : Real) (rowChange : Int)
    (sourceCellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (sourcePointwiseUpper : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Real)
    (sourcePrefixUpper : Band -> Nat -> Real)
    (Ssource : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1))
      B.partition.band sourceCellIndex
      sourcePointwiseUpper sourcePrefixUpper
      (bankPaperCanonicalPostHfitGlobalSourceSelector
        B K0 R certificate deltaStar betaProt betaAct oldSeed))
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1)
    (hminus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W (K0 + 1) 1)
    (hplus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W (K0 + 1) 1)
    (hminusCapacity : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        0 <= bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass m ∧
        betaProt / B.L +
            bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass m <= 1)
    (hplusCapacity : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        0 <= bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass m ∧
        betaProt / B.L +
            bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass m <= 1)
    (hmass : minusMass + plusMass = (rowChange : Real))
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1))
      (bankPaperCanonicalPostHfitStructuredPreSelector
        B K0 R certificate deltaStar betaProt betaAct oldSeed
          minusMass plusMass)
      activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (Ctarget Cinitial Cfixed Cactive : Real)
    (henv : B.HasTargetEnvelopes Ctarget
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
          (R.roughCanonicalGuardedCandidateSet
            certificate deltaStar (K0 + 1))
          (bankPaperCanonicalPostHfitStructuredPreSelector
            B K0 R certificate deltaStar betaProt betaAct oldSeed
              minusMass plusMass)
          activeSeed) 0 j))
    (hdeficit : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed
          (R.roughCanonicalGuardedCandidateSet
            certificate deltaStar (K0 + 1))
          (bankPaperCanonicalPostHfitStructuredPreSelector
            B K0 R certificate deltaStar betaProt betaAct oldSeed
              minusMass plusMass) p) <=
        Cinitial * B.q / ((p : Real) * B.L))
    (hfrozenLedger : forall m : B.sampleData.Sample,
      BridgeData.frozenAmbientWeight
          (bankPaperCanonicalActualFrozenValue
            (candidates :=
              R.roughCanonicalGuardedCandidateSet
                certificate deltaStar (K0 + 1)))
          (bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet
              certificate deltaStar (K0 + 1))
            (bankPaperCanonicalPostHfitStructuredPreSelector
              B K0 R certificate deltaStar betaProt betaAct oldSeed
                minusMass plusMass)
            activeSeed)
          (B.sampleData.value m) <= Cfixed / B.L)
    (hactiveLedger : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (radius : NNReal) (Cpost : Real)
    (hP87 :
      forall (Delta : Band -> Real),
        B.HasTargetEnvelopes Ctarget Delta ->
        forall (markedTarget : Nat -> Real) (N : Real),
          0 <= N ->
          B.q <= (1 : Real) * N ->
          (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
            abs (markedTarget p -
              B.paperMoment (B.markedValuation p) 0) <=
                Cinitial * N / ((p : Real) * B.L)) ->
          (forall j,
            Delta j = B.markedBandResidual markedTarget 0 j) ->
          forall {Fixed : Type} [Fintype Fixed]
            (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
            (quota : Int),
            (quota : Real) = (∑ f, fixedWeight f) + B.q ->
            B.sampleData.HeadPatternsSeparated ->
            (forall x,
              BridgeData.frozenAmbientWeight
                fixedValue fixedWeight x ∈ Icc (0 : Real) 1) ->
            (forall m : B.sampleData.Sample,
              BridgeData.frozenAmbientWeight fixedValue fixedWeight
                (B.sampleData.value m) <= Cfixed / B.L) ->
            (forall m : B.sampleData.Sample,
              B.baseline.baseWeight m <= Cactive / B.L) ->
            B.HasPaperProposition87Conclusion Delta radius
              markedTarget N Cpost fixedValue fixedWeight quota)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (Cplacement : Real) (hCplacement : 0 <= Cplacement)
    (hplacementSeedUpper : forall m : B.sampleData.Sample,
      bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass m <=
        Cplacement / B.L)
    (hfixed : betaProt + Cplacement <= Cfixed)
    (C : Real) (hC : 1 <= C) (hW : 1 < B.sampleData.W)
    (hhi : forall sign,
      B.sampleData.hi sign <= physicalBound C B.sampleData.n)
    (hCactive : 0 <= Cactive)
    (hprotectedReserve : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W (K0 + 1) 1,
      sigma / B.L +
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData activeSeed x <=
        bankPaperCanonicalPostHfitStructuredPreSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed
            minusMass plusMass x)
    (hlarge : Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive + sigma <= B.L)
    (Hnonsmooth : RoughCanonicalBalancedNonsmoothBounds
      R certificate deltaStar B.sampleData.W K0
        betaProt betaAct sigma) :
    ∃ quota : Int, ∃ path : Real -> B.ParamSpace,
    ∃ endpoint : Nat -> Real,
    BankPaperCanonicalPostHfitGuardedSlackPackage
        B K0 R certificate fixed deltaStar betaProt betaAct sigma
          oldSeed activeSeed minusMass plusMass radius Cpost cellIndex
          quota path endpoint := by
  have SsourceState :=
    bankPaperCanonicalSelectorSourceState_of_roundedSelectorTangentInput
      R certificate fixed
        (R.roughCanonicalGuardedCandidateSet
          certificate deltaStar (K0 + 1))
      B.partition.band sourceCellIndex sourcePointwiseUpper sourcePrefixUpper
      (bankPaperCanonicalPostHfitGlobalSourceSelector
        B K0 R certificate deltaStar betaProt betaAct oldSeed)
      Ssource
  exact
    exists_bankPaperCanonicalPostHfitGuardedSlackPackage_of_sourceState
      (K0 := K0) B R certificate fixed
        deltaStar betaProt betaAct sigma hbetaProt
        oldSeed activeSeed minusMass plusMass rowChange SsourceState
        hsep hactiveSmooth hminus hplus hminusCapacity hplusCapacity hmass
        Hmeasure hseed Ctarget Cinitial Cfixed Cactive henv hdeficit
        hfrozenLedger hactiveLedger radius Cpost hP87 cellIndex
        Cplacement hCplacement hplacementSeedUpper hfixed
        C hC hW hhi hCactive hprotectedReserve hlarge Hnonsmooth

end BankPaperRealization

end

end Erdos390.WholePaper
