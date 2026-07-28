import Erdos390.WholePaper.BankPaperCanonicalSectionNineTopFrozenPlacedDominationConnector

/-!
# Statement audit for frozen-top placed domination

The expanded examples expose the literal frozen-top preselector, the exact
core-height placement seed, and the scaled core seed carried by the actual
measure.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

example
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
    (K0 : Nat) (deltaStar : Real)
    (core : BankPaperCanonicalSectionNineSymmetricHeightCoreInputsAt
      B R certificate K0 deltaStar) :
    bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacementSeed
        B R certificate K0 deltaStar core =
      bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
        (bankPaperCanonicalScaledActiveSeed core.T core.q0)
        (bankPaperCanonicalSymmetricHeightCellMass core.d)
        (bankPaperCanonicalSymmetricHeightCellMass core.d) := by
  rfl

example
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
    (K0 : Nat) (deltaStar : Real)
    (core : BankPaperCanonicalSectionNineSymmetricHeightCoreInputsAt
      B R certificate K0 deltaStar)
    (Tsource : BarycentricTarget B.sampleData)
    (alpha beta qTilde : Real) :
    ∀ m : B.sampleData.Sample,
      bankPaperCanonicalScaledActiveSeed core.T core.q0 m ≤
        bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
          (K := K0 + 1) B R certificate Tsource deltaStar
            core.betaProt alpha beta qTilde
            (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
              (bankPaperCanonicalScaledActiveSeed core.T core.q0)
              (bankPaperCanonicalSymmetricHeightCellMass core.d)
              (bankPaperCanonicalSymmetricHeightCellMass core.d))
            (B.sampleData.value m) := by
  simpa only [
    BankPaperCanonicalActualCoordinateFit,
    bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacementSeed] using
    (bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacedPreSelector_coordinateFit
      B R certificate K0 deltaStar core Tsource alpha beta qTilde)

#check bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacementSeed
#check bankPaperCanonicalLiteralActiveMass_sectionNineTopFrozenCoreHeightPlacementSeed
#check bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacementSeed_ne_scaledCoreSeed_of_d_ne_zero
#check bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacedPreSelector_coordinateFit
#check bankPaperCanonicalSectionNineTopFrozenCoreHeightPlaced_actualMeasure
#check bankPaperCanonicalSectionNineTopFrozenSymmetricHeightSourceInputsAt_of_coreHeightPlacement

end BankPaperRealization

end

end Erdos390.WholePaper
