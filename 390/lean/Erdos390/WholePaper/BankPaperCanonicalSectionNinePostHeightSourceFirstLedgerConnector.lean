import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstActualData
import Erdos390.WholePaper.BankPaperCanonicalSectionEightPrechargedLogConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionEightTopFrozenInitialMassConnector

/-!
# Exact source-first Section 8 ledger

This connector constructs the analytic ledger from an honest family of
pre-rounding scaled source data.  Its hypotheses are only:

* the finite actual active-measure constructor;
* the literal interval geometry;
* and the finite top-frozen balanced initial realization.

The selector-mass estimate is proved by the existing balanced-row theorem,
the central-tail ledger is proved by the actual-data connector, and the
logarithmic target is then replaced by the exact precharged target.  The
literal frozen logarithmic family remains visible in the conclusion.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open BankPaperRealization

noncomputable section

/-- Build the exact precharged Section 8 ledger from the source-first
pre-rounding actual-data family. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_sourceFirstAnalyticLedger_of_actualData
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {c betaAct deltaStar betaTotal : Real} {N : Nat}
    (hc : 0 < c) (hdeltaStar : 0 < deltaStar)
    (hdeltaStarUpper : deltaStar < 1)
    (depth W K0 poolMinimum : Nat)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (D : Nat → StructuredSampleData Head)
    (T : ∀ n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat → Finset Nat)
    (preSelector : Nat → Nat → Real)
    (mFrozen : Nat → Real)
    (Hconstructor : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (preSelector n)
        (bankPaperCanonicalScaledActiveSeed (T n)
          (F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar n)))
    (Hgeometry : BankPaperCanonicalActualFrozenIntervalGeometry
      (c := c) fixed bankBase candidates)
    (Hbalanced : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalTopFrozenBalancedInitialRealization
        depth W K0 n c deltaStar betaTotal
          (fixed n) (bankBase n) (candidates n)
          (preSelector n)) :
    BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) (K0 + 1) betaAct)
      (F.extendedGuardedSmoothBaseMass
        W (K0 + 1) betaAct deltaStar)
      (bankPaperCanonicalSmoothA0Family
        F.extendedPrechargedTailLogTarget
        (bankPaperCanonicalActualFrozenLogMassFamily
          D fixed bankBase candidates preSelector
          (fun n => bankPaperCanonicalScaledActiveSeed (T n)
            (F.extendedGuardedSmoothBaseMass
              W (K0 + 1) betaAct deltaStar n)))
        mFrozen
        (F.extendedGuardedSmoothBaseMass
          W (K0 + 1) betaAct deltaStar)) := by
  have Hselector :
      BankPaperCanonicalActualSelectorMassEstimate
        c fixed bankBase candidates preSelector :=
    bankPaperCanonicalActualSelectorMassEstimate_of_topFrozenBalancedInitial
      depth W K0 poolMinimum hc hdeltaStar hdeltaStarUpper
        fixed bankBase candidates preSelector Hbalanced
  have Hcentral :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n => bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) (K0 + 1) betaAct)
        (F.extendedGuardedSmoothBaseMass
          W (K0 + 1) betaAct deltaStar)
        (bankPaperCanonicalSmoothA0Family
          (bankPaperCanonicalCentralTailLogTarget c)
          (bankPaperCanonicalActualFrozenLogMassFamily
            D fixed bankBase candidates preSelector
            (fun n => bankPaperCanonicalScaledActiveSeed (T n)
              (F.extendedGuardedSmoothBaseMass
                W (K0 + 1) betaAct deltaStar n)))
          mFrozen
          (F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar)) :=
    bankPaperCanonicalSectionEightAnalyticLedger_of_scaledActualData_intervalGeometry
      hc depth W (K0 + 1) betaAct deltaStar F D T fixed bankBase
        candidates preSelector mFrozen Hconstructor Hgeometry Hselector
  exact
    bankPaperCanonicalSectionEightAnalyticLedger_precharged_of_centralTail
      hc F
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) (K0 + 1) betaAct)
      (F.extendedGuardedSmoothBaseMass
        W (K0 + 1) betaAct deltaStar)
      (bankPaperCanonicalActualFrozenLogMassFamily
        D fixed bankBase candidates preSelector
        (fun n => bankPaperCanonicalScaledActiveSeed (T n)
          (F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar n)))
      mFrozen Hcentral

end

end Erdos390.WholePaper
