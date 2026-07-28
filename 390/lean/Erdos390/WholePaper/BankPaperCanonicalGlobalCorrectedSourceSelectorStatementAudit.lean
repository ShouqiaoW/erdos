import Erdos390.WholePaper.BankPaperCanonicalGlobalCorrectedSourceSelector

/-! # Statement audit for the global corrected source selector -/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-- Expanded audit: after structured placement, the global corrected source
supplies the two pointwise premises consumed by the endpoint-slack theorem.
The smooth conclusion visibly retains the necessary pointwise upper bound
on the placement seed; the nonsmooth conclusion needs no quantitative seed
hypothesis. -/
example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta : Real)
    (oldSeed placementSeed : B.sampleData.Sample -> Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (Cactive : Real) (hCactive : 0 <= Cactive)
    (hplacementSeedUpper : forall m : B.sampleData.Sample,
      placementSeed m <= Cactive / B.L)
    (Cfixed : Real) (hfixed : betaProt + Cactive <= Cfixed) :
    (∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1,
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
              B R certificate deltaStar betaProt
              (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
                B R certificate deltaStar betaProt alpha beta oldSeed)
              placementSeed a <=
          Cfixed / B.L) ∧
      (forall label,
        RoughCanonicalActiveNonexceptionalLabel
            B.sampleData.n deltaStar label ->
          ∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar B.sampleData.W K label,
            bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
                  B R certificate deltaStar betaProt
                  (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
                    B R certificate deltaStar betaProt alpha beta oldSeed)
                  placementSeed a =
              R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
                deltaStar B.sampleData.W K label alpha beta B.L a) := by
  exact
    bankPaperCanonicalGlobalCorrectedStructuredPlacement_slackInputs
      B R certificate deltaStar betaProt alpha beta oldSeed placementSeed
        hactiveSmooth hsep Cactive hCactive hplacementSeedUpper
          Cfixed hfixed

/-- Expanded audit: the global source still proves the literal structured
support, integral smooth-row change, and all head-prime zero moments of the
two-zero-cell prebridge ledger. -/
example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass : Real) (rowChange : Int)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hminus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hplus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hmass : minusMass + plusMass = (rowChange : Real)) :
    bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1 ∧
      (∃ rowChange' : Int,
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
                B R certificate deltaStar betaProt
                (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
                  B R certificate deltaStar betaProt alpha beta oldSeed)
                (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
                  minusMass plusMass) a -
            bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
              B R certificate deltaStar betaProt alpha beta oldSeed a)) =
          (rowChange' : Real)) ∧
      ∀ q : Nat, q.Prime -> q <= B.sampleData.W ->
        bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
          (K := K) B R certificate deltaStar betaProt
            (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
              B R certificate deltaStar betaProt alpha beta oldSeed)
            (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
              minusMass plusMass) q = 0 := by
  simpa only [BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger]
    using
      bankPaperCanonicalGlobalCorrectedSourceSelector_prebridgeMomentLedger_twoZeroHeadCells
        (K := K) B R certificate deltaStar betaProt alpha beta oldSeed
          minusMass plusMass rowChange hactiveSmooth hminus hplus hmass

/-! ## Complete public declaration census -/

#check bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value_of_headPatternsSeparated
#check bankPaperCanonicalGlobalCorrectedOutsideSelector
#check bankPaperCanonicalGlobalCorrectedOutsideSelector_eq_ambient_of_mem_smoothRow
#check roughCanonicalGuardedBroadCorrectionPool_not_mem_smoothRow_of_ne_one
#check bankPaperCanonicalGlobalCorrectedOutsideSelector_eq_corrected_of_mem_nonsmoothPool
#check bankPaperCanonicalGlobalCorrectedSourceSelector
#check bankPaperCanonicalGlobalCorrectedSourceSelector_apply_of_mem_smoothPool
#check bankPaperCanonicalGlobalCorrectedSourceSelector_apply_of_mem_nonsmoothPool
#check bankPaperCanonicalGlobalCorrectedSourceSelector_prebridgeMomentLedger_twoZeroHeadCells
#check bankPaperCanonicalGlobalCorrectedStructuredPlacementSelector_twoZeroHeadCells_feasible_of_source
#check bankPaperCanonicalGlobalCorrectedStructuredAdditivePlacement_twoZeroHeadCells_of_sourceState
#check bankPaperCanonicalGlobalCorrectedStructuredAdditivePlacement_twoZeroHeadCells_of_roundedSource
#check bankPaperCanonicalActiveSeedAmbientWeight_le_of_pointwise
#check bankPaperCanonicalGlobalCorrectedStructuredPlacement_hpreNonsmooth
#check bankPaperCanonicalGlobalCorrectedStructuredPlacement_hpreUpper
#check bankPaperCanonicalGlobalCorrectedStructuredPlacement_slackInputs

end BankPaperRealization

end

end Erdos390.WholePaper
