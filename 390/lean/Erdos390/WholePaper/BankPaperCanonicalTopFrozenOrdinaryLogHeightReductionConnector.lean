import Erdos390.WholePaper.BankPaperCanonicalArbitrarySourcePostHfitConnector
import Erdos390.WholePaper.BankPaperCanonicalP87ApproximateOrdinaryLogTargetEnvelopeConnector

/-!
# Ordinary-log reduction for the frozen-top Post-Hfit source

The nearest-integer frozen-top source is the literal Section 8 base source
used by the arbitrary-source Post-Hfit connector.  This file specializes the
exact ordinary-log identity at a Post-Hfit initial P87 selector built from
that source.  As in the arbitrary-source API, the placement seed and the
actual bridge seed remain explicit parameters.

The height-ledger-free finite identity obtained here (from the actual-measure
constructor and baseline/seed identification) is

`sum_p t_p r_p = (weighted active target) - (initial prime-log moment)`.

That identity is already sufficient to prove an approximate ordinary-log
bound from a bound on the right-hand side.  Identifying the right-hand side
with `bankPaperCanonicalSmoothNormalizedHeightRoundingDefect` requires one
additional source-height ledger equality.  The final two theorems retain that
equality as an explicit premise; no such equality is inferred from the scalar
quota/height ledger.

The explicit equality premise bundles the still-missing target/frozen
ordinary-log ledger, the prime-log/physical-score split, and the physical
moment of the chosen placement seed.  In particular, this file does not claim
that the generic placement seed realizes the scalar height move.
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

/-! ## Exact finite source identity -/

/-- At a Post-Hfit initial selector built from the literal frozen-top base
source, the weighted tangent residual is exactly the weighted active marked
target minus the initial prime-log moment.

This is the strongest height-ledger-free finite ordinary-log identity currently
available for the source. -/
theorem
    bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_weightedResidual_eq
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
        B.paperMoment B.primeLogScore 0 := by
  exact
    bankPaperCanonicalActualInitialSelector_weightedResidual_eq
      B R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
          (K := K) B R certificate Tsource deltaStar betaProt alpha beta
            qTilde placementSeed)
        activeSeed Hmeasure hseed

/-! ## Approximate compatibility from the exact finite identity -/

/-- A bound for the explicit target-minus-moment expression gives the
approximate ordinary-log compatibility consumed by the target-envelope
connector.  This form does not require a height-ledger identification. -/
theorem
    bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_ordinaryLogCompatibleUpTo_of_target_sub_primeLogMoment
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
      E := by
  unfold BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo
  rw [
    bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_weightedResidual_eq
      B R certificate fixed Tsource deltaStar betaProt alpha beta qTilde
        placementSeed activeSeed Hmeasure hseed]
  exact hmoment

/-! ## Exact boundary of the scalar height ledger -/

/-- If the source-specific target-minus-moment expression is identified with
the normalized height-rounding defect, then the frozen-top-based Post-Hfit
initial residual has that exact value.

The hypothesis `hheightLedger` is the missing physical/logarithmic split
between the actual selector data and the scalar quota/height ledger. -/
theorem
    bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_weightedResidual_eq_normalizedHeightRoundingDefect
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
        A0 := by
  calc
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
    _ =
        bankPaperCanonicalSmoothNormalizedHeightRoundingDefect
          B.sampleData.n mu
          (bankPaperCanonicalTopFrozenRoundedActiveMass (K := K)
            B R certificate deltaStar betaProt alpha qTilde)
          A0 := hheightLedger

/-- The preceding exact reduction plus any bound for the normalized
height-rounding defect gives the approximate ordinary-log compatibility
required by the target-envelope connector. -/
theorem
    bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_ordinaryLogCompatibleUpTo_of_heightLedger
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
    (deltaStar betaProt alpha beta qTilde mu A0 E : Real)
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
          A0)
    (hround :
      abs (bankPaperCanonicalSmoothNormalizedHeightRoundingDefect
        B.sampleData.n mu
        (bankPaperCanonicalTopFrozenRoundedActiveMass (K := K)
          B R certificate deltaStar betaProt alpha qTilde)
        A0) <= E) :
    BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
        (K := K) B R certificate Tsource deltaStar betaProt alpha beta
          qTilde placementSeed)
      E := by
  unfold BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo
  rw [
    bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_weightedResidual_eq_normalizedHeightRoundingDefect
      B R certificate fixed Tsource deltaStar betaProt alpha beta qTilde
        mu A0 placementSeed activeSeed Hmeasure hseed hheightLedger]
  exact hround

end BankPaperRealization

end

end Erdos390.WholePaper
