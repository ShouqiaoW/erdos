import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceResidualConnector

/-!
# Statement audit for the coherent post-height source residual

The main example expands the residual definition.  In particular, the
premises contain only literal target construction, source-mass
synchronization, and primitive geometry; none of the three displayed
conclusions is assumed.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Expanded main terminal -/

example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (Patterns : PaperHeadSimplex.Tag P -> Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : forall n, Ledger n Cprom Cbank)
    (depth W K0 : Nat)
    {c deltaStar betaProt betaAct sigma : Real}
    (hc : 0 < c) (hdeltaStar : 0 < deltaStar)
    (hbetaProt : 0 <= betaProt) (hbetaAct : 0 < betaAct)
    (hsigmaNonneg : 0 <= sigma) (hsigmaProt : sigma <= betaProt)
    (hbetaUpper :
      betaProt + betaAct <= c / roughHeadDensity W)
    (hKlarge :
      1 / roughHeadDensity W <= (((K0 + 1 : Nat) : Real)))
    (hprefix : 2 * depth + 1 <= W) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        B.sampleData.W = W ->
        forall
          (hcanonicalSep :
            physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell : Cell (PaperHeadSimplex.Tag P),
            (rawCell Patterns I B.sampleData.n cell \
              (G B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Patterns I (G B.sampleData.n)
                  hcanonicalSep hremaining ->
        forall
          (R : BankPaperRealization B.sampleData.n
            (upperEndpoint B.sampleData.n
              (upperTailLength c B.sampleData.n)))
          (certificate : GuardedCentralAnchorCertificate c depth
            B.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
            (R.centralChangedMarkers depth))
          (T : BarycentricTarget B.sampleData)
          (qTilde : Real),
          qTilde =
              bankPaperCanonicalGuardedSmoothBaseMass R certificate
                deltaStar B.sampleData.W (K0 + 1) betaAct ->
        forall
          (hprime : ∀ p ∈ P, p.Prime)
          (Rhead : HeadSimplexReserve P)
          (Kphysical : PhysicalInterpolationTarget I)
          (hlo : forall sign, B.sampleData.lo sign =
            physicalBound (I.lower sign) B.sampleData.n)
          (hhi : forall sign, B.sampleData.hi sign =
            physicalBound (I.upper sign) B.sampleData.n),
          T =
              B.barycentricTargetOfPaperData
                I hlo hhi Rhead Kphysical ->
          qTilde = Rhead.activeMass ->
          B.sampleData.pattern =
              PaperHeadSimplex.pattern P hprime Rhead.exponent ->
          primesUpTo B.sampleData.W ⊆ P ->
          B.sampleData.HeadPatternsSeparated ->
          (forall sign, 1 <= I.lower sign) ->
          (forall sign, I.upper sign <= 2) ->
          (forall sign,
            physicalBound (I.upper sign) B.sampleData.n <=
              2 * B.sampleData.n -
                (K0 + 1) * upperTailLength c B.sampleData.n) ->
          (K0 + 1) * upperTailLength c B.sampleData.n <=
              B.sampleData.n ->
          (forall m : B.sampleData.Sample,
            B.sampleData.value m ∉
              R.roughCanonicalGuardSet certificate deltaStar) ->
          (forall p : {p : Nat // p ∈ P},
            p.1 <= B.sampleData.W ->
              Rhead.target p =
                ((certificate.selectorTailTarget R
                  (R.paperFixedExceptionalFactors deltaStar)).factorization
                    p.1 : Real)) ->
          R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) ∣
              certificate.prechargedTailTarget ->
          (∀ a ∈
              R.roughCanonicalGuardedCandidateSet certificate
                deltaStar (K0 + 1),
            0 <=
                bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
                  (K := K0 + 1) B R certificate deltaStar betaProt
                    (bankPaperCanonicalPostHfitBalancedAlpha
                      B c K0 betaProt betaAct)
                    (betaProt + betaAct)
                    (bankPaperCanonicalScaledActiveSeed T qTilde) a ∧
              bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
                  (K := K0 + 1) B R certificate deltaStar betaProt
                    (bankPaperCanonicalPostHfitBalancedAlpha
                      B c K0 betaProt betaAct)
                    (betaProt + betaAct)
                    (bankPaperCanonicalScaledActiveSeed T qTilde) a <= 1) ∧
            BankPaperCanonicalChargedNonsmoothRowRealization
              (K := K0 + 1) R certificate deltaStar
                (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
                  (K := K0 + 1) B R certificate deltaStar betaProt
                    (bankPaperCanonicalPostHfitBalancedAlpha
                      B c K0 betaProt betaAct)
                    (betaProt + betaAct)
                    (bankPaperCanonicalScaledActiveSeed T qTilde)) ∧
            BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
              (W := B.sampleData.W) R certificate
              (R.paperFixedExceptionalFactors deltaStar)
              (R.roughCanonicalGuardedCandidateSet certificate
                deltaStar (K0 + 1))
              (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
                (K := K0 + 1) B R certificate deltaStar betaProt
                  (bankPaperCanonicalPostHfitBalancedAlpha
                    B c K0 betaProt betaAct)
                  (betaProt + betaAct)
                  (bankPaperCanonicalScaledActiveSeed T qTilde)) := by
  simpa only [
    BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt] using
    (eventually_bankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt_of_coherentTarget
      (Band := Band) Patterns I Cprom Cbank G depth W K0
        hc hdeltaStar hbetaProt hbetaAct hsigmaNonneg hsigmaProt
        hbetaUpper hKlarge hprefix)

/-! ## Complete declaration census -/

#check bankPaperCanonical_scaledActiveSeed_le_divLog_of_cellDensity
#check eventually_bankPaperCanonical_canonicalSample_cellDensityFloor
#check
  eventually_bankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt_of_coherentTarget

end BankPaperRealization

end

end Erdos390.WholePaper
