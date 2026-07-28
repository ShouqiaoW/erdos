import Erdos390.WholePaper.BankPaperCanonicalTopFrozenEventualOrdinaryLogRateConnector

/-!
# Statement audit for the eventual frozen-top ordinary-log rate
-/

open Filter

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

#check exists_eventually_bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_ordinaryLogCompatibleUpTo_of_implementationRates

/-- Expanded eventual interface.  The three implementation rates, the
bridge-mass comparison, and all finite feasibility premises remain explicit. -/
example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (W K0 depth : Nat)
    {c deltaStar betaProt betaAct epsilon cMass
      Csource CguardedRaw Cplacement : Real}
    (hc : 0 < c)
    (hdelta : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18)
    (hepsilon : 0 < epsilon)
    (hcMass : 0 < cMass)
    (hCsource : 0 <= Csource)
    (hCguardedRaw : 0 <= CguardedRaw)
    (hCplacement : 0 <= Cplacement)
    (hTwoW : 2 <= W)
    (hprefix : 2 * depth + 1 <= W) :
    ∃ Clog : Real, 0 <= Clog ∧
      ∀ᶠ n : Nat in atTop,
        ∀ (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        B.sampleData.W = W ->
        ∀
          (R : BankPaperRealization B.sampleData.n
            (upperEndpoint B.sampleData.n
              (upperTailLength c B.sampleData.n)))
          (certificate : GuardedCentralAnchorCertificate c depth
            B.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
            (R.centralChangedMarkers depth))
          (T : BarycentricTarget B.sampleData)
          (qTilde : Real)
          (placementSeed : B.sampleData.Sample -> Real),
        cMass * secondOrderScale n <= B.q ->
        (0 <=
            bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct ∧
          bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct <= 1) ->
        (0 <= (betaProt + betaAct) / B.L ∧
          (betaProt + betaAct) / B.L <= 1) ->
        bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
          R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1 ->
        R.selectorTailCharge (R.paperFixedExceptionalFactors deltaStar) ∣
          certificate.prechargedTailTarget ->
        (∀ p : Nat, p.Prime -> W < p -> p <= yNat n ->
          BankPaperCanonicalTopFrozenRoundedMediumPrimeImplementationRateInputs
            B K0 R certificate T deltaStar betaProt betaAct qTilde
              placementSeed p
              (secondOrderScale n / ((p : Real) * L n))
              Csource CguardedRaw Cplacement) ->
        BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo
          (W := B.sampleData.W) R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet
            certificate deltaStar (K0 + 1))
          (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K0 + 1) B R certificate T deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct)
              (betaProt + betaAct) qTilde placementSeed)
          ((B.q / B.L) * Clog) :=
  exists_eventually_bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_ordinaryLogCompatibleUpTo_of_implementationRates
    W K0 depth hc hdelta hdeltaUpper hepsilon hcMass
      hCsource hCguardedRaw hCplacement hTwoW hprefix

end BankPaperRealization

end

end Erdos390.WholePaper
