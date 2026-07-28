import Erdos390.WholePaper.BankPaperCanonicalMediumPrimeStructuredPlacementMomentRateConnector

/-! Statement audit for the medium-prime structured-placement rate. -/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BankPaperRealization

#check sum_bankPaperCanonicalUniformCellIncrement_mul_valuation_eq_mass_mul_guardedCellProbability_expect
#check bankPaperCanonicalGlobalCorrectedStructuredPlacementValuationMoment_twoZeroHeadCells_eq
#check abs_bankPaperCanonicalGlobalCorrectedStructuredPlacementValuationMoment_twoZeroHeadCells_le_paperRate
#check abs_bankPaperCanonicalPostHfitStructuredPlacementValuationMoment_twoZeroHeadCells_le_paperRate
#check bankPaperCanonicalPostHfitMediumPrimeImplementationRateInputs_of_twoZeroHeadCellMean

/-- Expanded audit: arbitrary two-cell masses are controlled only after an
absolute mass-change budget and the two literal uniform-cell mean bounds are
supplied. -/
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
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass Aval Cmass : Real) (p : Nat)
    (hp : p.Prime)
    (hAval : 0 <= Aval) (hCmass : 0 <= Cmass)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1)
    (hmean : forall sigma : PhysicalSign,
      (B.guardedCellProbability (none, sigma)).expect
          (fun m ↦ valuation p (m : Nat)) <= Aval / (p : Real))
    (hmass :
      |minusMass| + |plusMass| <=
        Cmass * secondOrderScale B.sampleData.n / B.L) :
    abs
      (bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
        (K := K0 + 1) B R certificate deltaStar betaProt
        (bankPaperCanonicalPostHfitGlobalSourceSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed)
        (bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass) p) <=
      Cmass * Aval * secondOrderScale B.sampleData.n /
        ((p : Real) * B.L) :=
  abs_bankPaperCanonicalPostHfitStructuredPlacementValuationMoment_twoZeroHeadCells_le_paperRate
    B K0 R certificate deltaStar betaProt betaAct oldSeed
      minusMass plusMass Aval Cmass p hp hAval hCmass
      hactiveSmooth hmean hmass

end BankPaperRealization

end

end Erdos390.WholePaper
