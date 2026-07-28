import Erdos390.WholePaper.BankPaperCanonicalDirectOrdinaryLogRateConnector

/-!
# Statement audit for the direct ordinary-log rate connector

The checks expose the generic pointwise-to-weighted estimate, its
mesh-scaled target-envelope form, and the two literal frozen-top
specializations.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

#check bankPaperCanonicalSelector_ordinaryLogCompatibleUpTo_of_pointwisePaperRate
#check bankPaperCanonicalSelector_ordinaryLogCompatibleUpTo_meshScale_of_pointwisePaperRate
#check bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_ordinaryLogCompatibleUpTo_of_pointwisePaperRate
#check bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_target_sub_primeLogMoment_abs_le_of_pointwisePaperRate

/-- Expanded generic pointwise-to-weighted estimate. -/
example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (selector : Nat -> Real)
    (C Kbound : Real)
    (hC : 0 <= C)
    (hdeficit : ∀ p ∈
      primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed candidates selector p) <=
          C * B.q / ((p : Real) * B.L))
    (hbandT :
      Erdos390.Full.PrimeSums.bandTReciprocalSum
        B.sampleData.n B.sampleData.W <= Kbound) :
    BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo
      (W := B.sampleData.W) R certificate fixed candidates selector
      ((B.q / B.L) * (C * Kbound)) :=
  bankPaperCanonicalSelector_ordinaryLogCompatibleUpTo_of_pointwisePaperRate
    B R certificate fixed candidates selector C Kbound
      hC hdeficit hbandT

/-- Expanded mesh-scaled form, including the sign of its exported
constant. -/
example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (selector : Nat -> Real)
    (C Kbound : Real)
    (hC : 0 <= C) (hKbound : 0 <= Kbound)
    (hdeficit : ∀ p ∈
      primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed candidates selector p) <=
          C * B.q / ((p : Real) * B.L))
    (hbandT :
      Erdos390.Full.PrimeSums.bandTReciprocalSum
        B.sampleData.n B.sampleData.W <= Kbound) :
    0 <= C * Kbound / B.w ∧
      BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo
        (W := B.sampleData.W) R certificate fixed candidates selector
        ((B.q / B.L) * (C * Kbound / B.w) * B.w) :=
  bankPaperCanonicalSelector_ordinaryLogCompatibleUpTo_meshScale_of_pointwisePaperRate
    B R certificate fixed candidates selector C Kbound
      hC hKbound hdeficit hbandT

/-- Expanded frozen-top direct ordinary-log estimate. -/
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
    (placementSeed : B.sampleData.Sample -> Real)
    (C Kbound : Real)
    (hC : 0 <= C)
    (hdeficit : ∀ p ∈
      primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K) B R certificate Tsource deltaStar betaProt alpha beta
              qTilde placementSeed) p) <=
        C * B.q / ((p : Real) * B.L))
    (hbandT :
      Erdos390.Full.PrimeSums.bandTReciprocalSum
        B.sampleData.n B.sampleData.W <= Kbound) :
    BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
        (K := K) B R certificate Tsource deltaStar betaProt alpha beta
          qTilde placementSeed)
      ((B.q / B.L) * (C * Kbound)) :=
  bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_ordinaryLogCompatibleUpTo_of_pointwisePaperRate
    B R certificate fixed Tsource deltaStar betaProt alpha beta qTilde
      placementSeed C Kbound hC hdeficit hbandT

/-- Expanded target-minus-prime-log-moment form.  In particular, the
active-measure witness and the baseline-seed identity remain visible
premises rather than being hidden in a package. -/
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
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (C Kbound : Real)
    (hC : 0 <= C)
    (hdeficit : ∀ p ∈
      primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K) B R certificate Tsource deltaStar betaProt alpha beta
              qTilde placementSeed) p) <=
        C * B.q / ((p : Real) * B.L))
    (hbandT :
      Erdos390.Full.PrimeSums.bandTReciprocalSum
        B.sampleData.n B.sampleData.W <= Kbound) :
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
        B.paperMoment B.primeLogScore 0) <=
      (B.q / B.L) * (C * Kbound) :=
  bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_target_sub_primeLogMoment_abs_le_of_pointwisePaperRate
    B R certificate fixed Tsource deltaStar betaProt alpha beta qTilde
      placementSeed activeSeed Hmeasure hseed C Kbound hC hdeficit hbandT

end BankPaperRealization

end

end Erdos390.WholePaper
