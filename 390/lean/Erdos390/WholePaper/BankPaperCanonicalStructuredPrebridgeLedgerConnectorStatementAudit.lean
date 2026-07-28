import Erdos390.WholePaper.BankPaperCanonicalStructuredPrebridgeLedgerConnector

/-! # Statement audit for the structured prebridge ledger connector -/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-- Expanded audit: the concrete two-zero-cell construction proves the
guarded support, integer whole-row change, and every fixed head-prime zero
moment appearing in the structured prebridge ledger. -/
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
    (deltaStar betaProt : Real)
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
                (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
                  B R certificate deltaStar betaProt oldSeed)
                (bankPaperCanonicalTwoZeroHeadCellRebalance
                  B.sampleData oldSeed minusMass plusMass) a -
            bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
              B R certificate deltaStar betaProt oldSeed a)) =
          (rowChange' : Real)) ∧
      ∀ q : Nat, q.Prime -> q <= B.sampleData.W ->
        bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
          (K := K)
          B R certificate deltaStar betaProt
            (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
              B R certificate deltaStar betaProt oldSeed)
            (bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass) q = 0 := by
  simpa only [BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger]
    using
      bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_twoZeroHeadCells
        (K := K) B R certificate deltaStar betaProt oldSeed minusMass plusMass
          rowChange hactiveSmooth hminus hplus hmass

/-! ## Complete public declaration census -/

#check bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector
#check bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector_apply_of_mem
#check bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector_apply_of_not_mem
#check bankPaperCanonicalTwoZeroHeadCellRebalance_ambient_sub_eq_zero_of_not_mem
#check bankPaperCanonicalOutsideSelector_eq_scaledActiveSeedAmbientWeight_of_mem
#check bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_twoZeroHeadCells_sub_source_of_active
#check bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_twoZeroHeadCells_sub_source
#check bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_twoZeroHeadCells_of_active
#check bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_twoZeroHeadCells_scaled
#check bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_twoZeroHeadCells_scaled_of_physicalIntervals
#check bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_twoZeroHeadCells
#check bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_twoZeroHeadCells_of_physicalIntervals

end BankPaperRealization

end

end Erdos390.WholePaper
