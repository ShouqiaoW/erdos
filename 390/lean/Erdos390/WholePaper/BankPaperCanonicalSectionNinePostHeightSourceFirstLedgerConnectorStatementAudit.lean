import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstLedgerConnector

/-!
# Statement audit for the exact source-first Section 8 ledger
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

example
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
          W (K0 + 1) betaAct deltaStar)) :=
  bankPaperCanonicalSectionNinePostHeight_sourceFirstAnalyticLedger_of_actualData
    hc hdeltaStar hdeltaStarUpper depth W K0 poolMinimum F D T
      fixed bankBase candidates preSelector mFrozen
      Hconstructor Hgeometry Hbalanced

#check
  bankPaperCanonicalSectionNinePostHeight_sourceFirstAnalyticLedger_of_actualData

end

end Erdos390.WholePaper
