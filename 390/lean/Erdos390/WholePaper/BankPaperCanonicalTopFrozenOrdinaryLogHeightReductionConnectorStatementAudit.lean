import Erdos390.WholePaper.BankPaperCanonicalTopFrozenOrdinaryLogHeightReductionConnector

/-!
# Statement audit for the frozen-top ordinary-log height reduction

The expanded examples expose the height-ledger-free finite source identity
and the exact premise of the conditional normalized-height identification.
The remaining check records the usable target-minus-moment bound.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex

noncomputable section

namespace BankPaperRealization

#check bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_weightedResidual_eq
#check bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_ordinaryLogCompatibleUpTo_of_target_sub_primeLogMoment
#check bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_weightedResidual_eq_normalizedHeightRoundingDefect
#check bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_ordinaryLogCompatibleUpTo_of_heightLedger

/-- Expanded height-ledger-free identity at a Post-Hfit initial selector
built from the literal frozen-top base source. -/
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
    (fixed : Finset Nat)
    (Tsource : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde : Real)
    (placementSeed activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
        (K := K) B R certificate Tsource deltaStar betaProt alpha beta
          qTilde placementSeed)
      activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m) :
    (∑ p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      tPrime B.sampleData.n p.1 *
        bankPaperCanonicalTangentResidual R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K) B R certificate Tsource deltaStar betaProt alpha beta
              qTilde placementSeed) p) =
      (∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 *
          bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
              (K := K) B R certificate Tsource deltaStar betaProt alpha beta
                qTilde placementSeed)
            activeSeed p.1) -
        B.paperMoment B.primeLogScore 0 :=
  bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_weightedResidual_eq
    B R certificate fixed Tsource deltaStar betaProt alpha beta qTilde
      placementSeed activeSeed Hmeasure hseed

/-- Expanded statement of the exact missing height-ledger bridge. -/
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
    (fixed : Finset Nat)
    (Tsource : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde mu A0 : Real)
    (placementSeed activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
        (K := K) B R certificate Tsource deltaStar betaProt alpha beta
          qTilde placementSeed)
      activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (hheightLedger :
      (∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 *
          bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
              (K := K) B R certificate Tsource deltaStar betaProt alpha beta
                qTilde placementSeed)
            activeSeed p.1) -
          B.paperMoment B.primeLogScore 0 =
        bankPaperCanonicalSmoothNormalizedHeightRoundingDefect
          B.sampleData.n mu
          (bankPaperCanonicalTopFrozenRoundedActiveMass (K := K)
            B R certificate deltaStar betaProt alpha qTilde)
          A0) :
    (∑ p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      tPrime B.sampleData.n p.1 *
        bankPaperCanonicalTangentResidual R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K) B R certificate Tsource deltaStar betaProt alpha beta
              qTilde placementSeed) p) =
      bankPaperCanonicalSmoothNormalizedHeightRoundingDefect
        B.sampleData.n mu
        (bankPaperCanonicalTopFrozenRoundedActiveMass (K := K)
          B R certificate deltaStar betaProt alpha qTilde)
        A0 :=
  bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_weightedResidual_eq_normalizedHeightRoundingDefect
    B R certificate fixed Tsource deltaStar betaProt alpha beta qTilde mu A0
      placementSeed activeSeed Hmeasure hseed hheightLedger

/-- Expanded finite approximate-compatibility reduction. -/
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
    (fixed : Finset Nat)
    (Tsource : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde E : Real)
    (placementSeed activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
        (K := K) B R certificate Tsource deltaStar betaProt alpha beta
          qTilde placementSeed)
      activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (hmoment :
      abs (
        (∑ p : BankPaperCanonicalTangentPrime
            B.sampleData.n B.sampleData.W,
          tPrime B.sampleData.n p.1 *
            bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
              (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
              (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
                (K := K) B R certificate Tsource deltaStar betaProt alpha beta
                  qTilde placementSeed)
              activeSeed p.1) -
          B.paperMoment B.primeLogScore 0) <= E) :
    BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
        (K := K) B R certificate Tsource deltaStar betaProt alpha beta
          qTilde placementSeed)
      E :=
  bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_ordinaryLogCompatibleUpTo_of_target_sub_primeLogMoment
    B R certificate fixed Tsource deltaStar betaProt alpha beta qTilde E
      placementSeed activeSeed Hmeasure hseed hmoment

end BankPaperRealization

end

end Erdos390.WholePaper
