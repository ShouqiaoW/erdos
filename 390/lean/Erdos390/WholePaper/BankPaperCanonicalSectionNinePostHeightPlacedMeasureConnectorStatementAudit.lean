import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightPlacedMeasureConnector

/-!
# Statement audit for the post-height placed measure

The expanded examples expose the two central claims: the literal
frozen-top preselector contains the newly constructed post-height seed
pointwise, and that seed has exact paper mass `q0-d`.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex

noncomputable section

namespace BankPaperRealization

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
    (Tsource : BarycentricTarget B.sampleData)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (deltaStar betaProt alpha beta qTilde : Real)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hbetaProt : 0 ≤ betaProt) :
    ∀ m : B.sampleData.Sample,
      bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H m ≤
        bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K)
          B R certificate Tsource I hlo hhi H
            deltaStar betaProt alpha beta qTilde
            (B.sampleData.value m) := by
  simpa only [
    BankPaperCanonicalActualCoordinateFit,
    bankPaperCanonicalSectionNinePostHeightActiveSeed] using
    (bankPaperCanonicalSectionNinePostHeightPlacedPreSelector_coordinateFit
      (K := K) B R certificate Tsource I hlo hhi H
        deltaStar betaProt alpha beta qTilde hsep hbetaProt)

example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget) :
    bankPaperCanonicalLiteralActiveMass B.sampleData
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H) =
      q0 - (d : Real) := by
  simpa only [
    bankPaperCanonicalSectionNinePostHeightActiveMass_eq] using
    (bankPaperCanonicalSectionNinePostHeight_literalActiveMass_activeSeed
      B I hlo hhi H)

#check bankPaperCanonicalSectionNinePostHeightPlacedPreSelector
#check bankPaperCanonicalSectionNinePostHeightPlacedPreSelector_eq_structuredPlacement
#check bankPaperCanonicalSectionNinePostHeightPlacedPreSelector_coordinateFit
#check bankPaperCanonicalSectionNinePostHeightPlaced_actualMeasure
#check bankPaperCanonicalSectionNinePostHeightActiveSeed_le_of_massAndCellDensity
#check bankPaperCanonicalSectionNinePostHeightPlacementCapacity_of_massAndCellDensity
#check bankPaperCanonicalSectionNinePostHeightPlaced_actualMeasure_and_feasible_of_massAndCellDensity

end BankPaperRealization

end

end Erdos390.WholePaper
