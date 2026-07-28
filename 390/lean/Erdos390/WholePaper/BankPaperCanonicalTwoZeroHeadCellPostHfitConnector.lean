import Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellHfitConnector
import Erdos390.WholePaper.BankPaperCanonicalDistributedCandidateSet

/-!
# Post-Hfit handoff from Section 8 to Section 9

The two-zero-cell Hfit connector ends with the literal
`HasPaperProposition87Conclusion` required by the actual endpoint theorem.
This file performs that previously implicit composition.

The production theorems below first obtain the integer quota and Hfit
conclusion from the local canonical Proposition 8.7 tail.  They then return
the actual P87 path, its pushed-forward selector, and
`BankPaperCanonicalRoundedSelectorTangentInput`.  The latter is exactly the
selector input `S` of
`exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates`.
The split-seed overload uses the weaker row-integral/deficit-supported
endpoint eliminator so that the structured placement may use a rebalanced
seed while the actual bridge measure retains its original baseline seed.

No Section 9 collision, endpoint-slack, occupied-cell, or analytic budget
premise is hidden here; those remain obligations of the downstream assembly.
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

/-- The local canonical P87 tail for the structured two-zero-cell placement
produces the actual endpoint selector and the rounded-selector tangent input
consumed at the front of the candidate-parametric Section 9 assembly.

The `HasPaperProposition87Conclusion` conjunct is retained in the conclusion
so that the Hfit-to-endpoint dependency is visible rather than hidden inside
an existential elimination. -/
theorem
    exists_bankPaperCanonicalActualP87EndpointSelector_of_localCanonical_structuredAdditivePlacement
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat) (deltaStar betaProt : Real)
    (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed)
      activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (Hplacement : BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
      B R certificate fixed deltaStar betaProt baseSelector activeSeed)
    (hhead : B.sampleData.HeadPatternsSeparated)
    (Ctarget Cinitial Cfixed Cactive : Real)
    (henv : B.HasTargetEnvelopes Ctarget
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
            (K := K) B R certificate deltaStar betaProt baseSelector
              activeSeed)
          activeSeed) 0 j))
    (hdeficit : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
            (K := K) B R certificate deltaStar betaProt baseSelector
              activeSeed) p) <=
        Cinitial * B.q / ((p : Real) * B.L))
    (hfrozenLedger : forall m : B.sampleData.Sample,
      BridgeData.frozenAmbientWeight
          (bankPaperCanonicalActualFrozenValue
            (candidates :=
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K))
          (bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt baseSelector
                activeSeed)
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
      B.sampleData.n B.sampleData.W -> Nat) :
    ∃ quota : Int, ∃ path : Real -> B.ParamSpace,
    ∃ endpoint : Nat -> Real,
      B.HasPaperProposition87Conclusion
          (fun j => B.markedBandResidual
            (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
              (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
              (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
                (K := K) B R certificate deltaStar betaProt baseSelector
                  activeSeed)
              activeSeed) 0 j)
          radius
          (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt baseSelector
                activeSeed)
            activeSeed)
          B.q Cpost
          (bankPaperCanonicalActualFrozenValue
            (candidates :=
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K))
          (bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt baseSelector
                activeSeed)
            activeSeed)
          quota ∧
      B.IsPaperProposition87Path
          (fun j => B.markedBandResidual
            (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
              (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
              (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
                (K := K) B R certificate deltaStar betaProt baseSelector
                  activeSeed)
              activeSeed) 0 j)
          radius
          (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt baseSelector
                activeSeed)
            activeSeed)
          B.q Cpost
          (bankPaperCanonicalActualFrozenValue
            (candidates :=
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K))
          (bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt baseSelector
                activeSeed)
            activeSeed)
          quota path ∧
      endpoint =
        bankPaperCanonicalActualP87EndpointSelector B
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
            (K := K) B R certificate deltaStar betaProt baseSelector
              activeSeed)
          activeSeed path ∧
      BankPaperCanonicalRoundedSelectorTangentInput R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        B.partition.band cellIndex
        (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
        (tangentRatioCellTailPointwiseUpper
          (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
          B.partition.band cellIndex)
        endpoint := by
  have hplacement := Hplacement
  unfold BankPaperCanonicalGuardedStructuredAdditivePlacement at hplacement
  obtain ⟨quota, Hfit⟩ :=
    exists_bankPaperCanonicalActualP87Conclusion_of_localCanonical
      B R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed)
      activeSeed Hmeasure hseed hplacement.1 hplacement.2.1 hhead
      Ctarget Cinitial Cfixed Cactive henv hdeficit
      hfrozenLedger hactiveLedger radius Cpost hP87
  obtain
      ⟨path, endpoint, hpath, hendpoint, _hsupport, _htarget,
        _houtside, Sendpoint⟩ :=
    exists_bankPaperCanonicalActualP87EndpointSelector_of_structuredAdditivePlacement
      (K := K) B R certificate fixed deltaStar betaProt baseSelector
      activeSeed Hmeasure hseed Hplacement
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
            (K := K) B R certificate deltaStar betaProt baseSelector
              activeSeed)
          activeSeed) 0 j)
      radius B.q Cpost quota Hfit cellIndex
  exact ⟨quota, path, endpoint, Hfit, hpath, hendpoint, Sendpoint⟩

/-- Split-seed form of the local canonical Post-Hfit handoff.

The structured placement selector is built from `placementSeed`, while the
actual active measure, bridge baseline, marked target, frozen weights, P87
path, and pushed-forward endpoint all retain `activeSeed`.  This is the
literal interface needed by the two-zero-cell construction: its placement
uses the rebalanced seed, whereas its actual bridge measure remains based on
the original scaled barycentric seed.

Only the row-integrality and outside-band deficit-support fields are
extracted from the placement predicate.  The endpoint is then produced by
the weaker row-integral/deficit-supported eliminator, so no equality between
the two seeds is assumed or hidden. -/
theorem
    exists_bankPaperCanonicalActualP87EndpointSelector_of_localCanonical_structuredAdditivePlacement_splitSeed
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat) (deltaStar betaProt : Real)
    (baseSelector : Nat -> Real)
    (placementSeed activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector placementSeed)
      activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (Hplacement : BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
      B R certificate fixed deltaStar betaProt baseSelector placementSeed)
    (hhead : B.sampleData.HeadPatternsSeparated)
    (Ctarget Cinitial Cfixed Cactive : Real)
    (henv : B.HasTargetEnvelopes Ctarget
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
            (K := K) B R certificate deltaStar betaProt baseSelector
              placementSeed)
          activeSeed) 0 j))
    (hdeficit : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
            (K := K) B R certificate deltaStar betaProt baseSelector
              placementSeed) p) <=
        Cinitial * B.q / ((p : Real) * B.L))
    (hfrozenLedger : forall m : B.sampleData.Sample,
      BridgeData.frozenAmbientWeight
          (bankPaperCanonicalActualFrozenValue
            (candidates :=
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K))
          (bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt baseSelector
                placementSeed)
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
      B.sampleData.n B.sampleData.W -> Nat) :
    ∃ quota : Int, ∃ path : Real -> B.ParamSpace,
    ∃ endpoint : Nat -> Real,
      B.HasPaperProposition87Conclusion
          (fun j => B.markedBandResidual
            (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
              (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
              (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
                (K := K) B R certificate deltaStar betaProt baseSelector
                  placementSeed)
              activeSeed) 0 j)
          radius
          (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt baseSelector
                placementSeed)
            activeSeed)
          B.q Cpost
          (bankPaperCanonicalActualFrozenValue
            (candidates :=
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K))
          (bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt baseSelector
                placementSeed)
            activeSeed)
          quota ∧
      B.IsPaperProposition87Path
          (fun j => B.markedBandResidual
            (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
              (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
              (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
                (K := K) B R certificate deltaStar betaProt baseSelector
                  placementSeed)
              activeSeed) 0 j)
          radius
          (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt baseSelector
                placementSeed)
            activeSeed)
          B.q Cpost
          (bankPaperCanonicalActualFrozenValue
            (candidates :=
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K))
          (bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt baseSelector
                placementSeed)
            activeSeed)
          quota path ∧
      endpoint =
        bankPaperCanonicalActualP87EndpointSelector B
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
            (K := K) B R certificate deltaStar betaProt baseSelector
              placementSeed)
          activeSeed path ∧
      BankPaperCanonicalRoundedSelectorTangentInput R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        B.partition.band cellIndex
        (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
        (tangentRatioCellTailPointwiseUpper
          (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
          B.partition.band cellIndex)
        endpoint := by
  have hplacement := Hplacement
  unfold BankPaperCanonicalGuardedStructuredAdditivePlacement at hplacement
  obtain ⟨quota, Hfit⟩ :=
    exists_bankPaperCanonicalActualP87Conclusion_of_localCanonical
      B R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector placementSeed)
      activeSeed Hmeasure hseed hplacement.1 hplacement.2.1 hhead
      Ctarget Cinitial Cfixed Cactive henv hdeficit
      hfrozenLedger hactiveLedger radius Cpost hP87
  obtain
      ⟨path, endpoint, hpath, hendpoint, _hsupport, _htarget,
        _houtside, Sendpoint⟩ :=
    exists_bankPaperCanonicalActualP87EndpointSelector_of_rowIntegral_deficitSupported
      B R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector placementSeed)
      activeSeed Hmeasure hseed hplacement.2.1 hplacement.2.2
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
            (K := K) B R certificate deltaStar betaProt baseSelector
              placementSeed)
          activeSeed) 0 j)
      radius B.q Cpost quota Hfit cellIndex
  exact ⟨quota, path, endpoint, Hfit, hpath, hendpoint, Sendpoint⟩

end BankPaperRealization

end

end Erdos390.WholePaper
