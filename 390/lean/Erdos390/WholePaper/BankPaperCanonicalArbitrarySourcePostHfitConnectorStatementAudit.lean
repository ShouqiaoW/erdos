import Erdos390.WholePaper.BankPaperCanonicalArbitrarySourcePostHfitConnector

/-! # Statement audit for arbitrary-source Post-Hfit production -/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-- The generic package exposes the source selector and placement seed
literally; neither is definitionally replaced by the legacy global source. -/
example
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
    (fixed : Finset Nat)
    (deltaStar betaProt alpha beta sigma : Real)
    (sourceSelector : Nat -> Real)
    (placementSeed activeSeed : B.sampleData.Sample -> Real)
    (radius : NNReal) (Cpost : Real)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (quota : Int) (path : Real -> B.ParamSpace)
    (endpoint : Nat -> Real) :
    BankPaperCanonicalPostHfitGuardedSlackPackageOfSource (K := K)
        B R certificate fixed deltaStar betaProt alpha beta sigma
          sourceSelector placementSeed activeSeed radius Cpost cellIndex
          quota path endpoint ↔
      let candidates :=
        R.roughCanonicalGuardedCandidateSet certificate deltaStar K
      let preSelector :=
        bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
          B R certificate deltaStar betaProt sourceSelector placementSeed
      let markedTarget :=
        bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
          candidates preSelector activeSeed
      let Delta := fun j => B.markedBandResidual markedTarget 0 j
      BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
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
          deltaStar B.sampleData.W K alpha beta B.L sigma endpoint := by
  rfl

#check bankPaperCanonicalPostHfitStructuredPreSelectorOfSource
#check BankPaperCanonicalPostHfitGuardedSlackPackageOfSource
#check bankPaperCanonicalPostHfitStructuredPreSelectorOfSource_hpreUpper
#check bankPaperCanonicalPostHfitStructuredPreSelectorOfSource_hpreNonsmooth
#check exists_bankPaperCanonicalPostHfitGuardedSlackPackageOfSource_of_sourceState
#check bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
#check BankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage
#check bankPaperCanonicalTopFrozenRoundedSourceSelector_hsourceNonsmooth
#check exists_bankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage_of_sourceState

end BankPaperRealization

end

end Erdos390.WholePaper
