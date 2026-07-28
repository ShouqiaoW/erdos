import Erdos390.WholePaper.BankPaperCanonicalPostHfitSlackConnector

/-!
# Statement audit for the Post-Hfit endpoint/slack connector

The expanded audit below exposes the full finite package.  In particular,
the same `activeSeed` occurs in the actual frozen weight, P87 path, endpoint
push-forward, and endpoint-slack conclusion, while the structured placement
uses the separate two-zero-cell rebalanced seed.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-- Expanded package audit: no terminal tangent-flow or traffic conclusion is
folded into the connector's finite endpoint/slack output. -/
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
    (fixed : Finset Nat)
    (deltaStar betaProt betaAct sigma : Real)
    (oldSeed activeSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass : Real)
    (radius : NNReal) (Cpost : Real)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (quota : Int) (path : Real -> B.ParamSpace)
    (endpoint : Nat -> Real) :
    BankPaperCanonicalPostHfitGuardedSlackPackage
        B K0 R certificate fixed deltaStar betaProt betaAct sigma
          oldSeed activeSeed minusMass plusMass radius Cpost cellIndex
          quota path endpoint ↔
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
          (betaProt + betaAct) B.L sigma endpoint := by
  rfl

/-! ## Complete public declaration census -/

#check bankPaperCanonicalPostHfitBalancedAlpha
#check bankPaperCanonicalPostHfitGlobalSourceSelector
#check bankPaperCanonicalPostHfitStructuredPreSelector
#check BankPaperCanonicalPostHfitGuardedSlackPackage
#check exists_bankPaperCanonicalPostHfitGuardedSlackPackage_of_sourceState
#check exists_bankPaperCanonicalPostHfitGuardedSlackPackage

end BankPaperRealization

end

end Erdos390.WholePaper
