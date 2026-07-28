import Erdos390.Full.PrimeSums
import Erdos390.WholePaper.BankPaperCanonicalTopFrozenOrdinaryLogHeightReductionConnector

/-!
# Direct paper-rate closure of the ordinary-log defect

The ordinary-log defect of a selector is its `tPrime`-weighted valuation
deficit.  Consequently, the pointwise paper-rate estimate already required
by the P87 input controls the whole ordinary-log defect after summing against
the uniformly bounded mass

`sum_{W < p <= y} t_p / p`.

This route is deliberately independent of a scalar height-ledger
identification.  In particular, the nearest-integer change in the two
zero-head cells and the later structured placement need no separate
ordinary-log formula once their effects have already been included in the
pointwise bound for the final preselector.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## A generic finite weighted-sum estimate -/

/-- A pointwise selector-deficit bound at scale `C q / (p L)`, together
with a bound for `sum t_p / p`, gives the corresponding direct
ordinary-log bound. -/
theorem
    bankPaperCanonicalSelector_ordinaryLogCompatibleUpTo_of_pointwisePaperRate
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
      ((B.q / B.L) * (C * Kbound)) := by
  have hfactor : 0 <= C * B.q / B.L :=
    div_nonneg (mul_nonneg hC B.q_pos.le) B.L_pos.le
  unfold BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo
  calc
    abs (∑ p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      tPrime B.sampleData.n p.1 *
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p) <=
        ∑ p : BankPaperCanonicalTangentPrime
            B.sampleData.n B.sampleData.W,
          abs (tPrime B.sampleData.n p.1 *
            bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector p) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <=
        ∑ p : BankPaperCanonicalTangentPrime
            B.sampleData.n B.sampleData.W,
          tPrime B.sampleData.n p.1 *
            (C * B.q / ((p.1 : Real) * B.L)) := by
      apply Finset.sum_le_sum
      intro p _hp
      rw [abs_mul,
        abs_of_nonneg (B.bandPrime_tPrime_pos p).le]
      exact
        mul_le_mul_of_nonneg_left
          (hdeficit p.1 p.2)
          (B.bandPrime_tPrime_pos p).le
    _ =
        ∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
          tPrime B.sampleData.n p *
            (C * B.q / ((p : Real) * B.L)) := by
      simpa only [bankPaperCanonicalTangentResidual] using
        (Finset.sum_subtype
          (primeBand B.sampleData.n B.sampleData.W)
          (fun _p => Iff.rfl)
          (fun p =>
            tPrime B.sampleData.n p *
              (C * B.q / ((p : Real) * B.L)))).symm
    _ =
        (C * B.q / B.L) *
          ∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
            tPrime B.sampleData.n p / (p : Real) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      have hpPos : (0 : Real) < p := by
        exact_mod_cast (prime_of_mem_primeBand hp).pos
      field_simp [hpPos.ne', B.L_pos.ne']
    _ =
        (C * B.q / B.L) *
          Erdos390.Full.PrimeSums.bandTReciprocalSum
            B.sampleData.n B.sampleData.W := by
      rfl
    _ <= (C * B.q / B.L) * Kbound :=
      mul_le_mul_of_nonneg_left hbandT hfactor
    _ = (B.q / B.L) * (C * Kbound) := by ring

/-- The same estimate in the exact mesh-scaled form consumed by the
approximate target-envelope connector.  It also returns the nonnegativity
of the resulting ordinary-log constant. -/
theorem
    bankPaperCanonicalSelector_ordinaryLogCompatibleUpTo_meshScale_of_pointwisePaperRate
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
        ((B.q / B.L) * (C * Kbound / B.w) * B.w) := by
  constructor
  · exact div_nonneg (mul_nonneg hC hKbound) B.w_pos.le
  · have hordinary :=
      bankPaperCanonicalSelector_ordinaryLogCompatibleUpTo_of_pointwisePaperRate
        B R certificate fixed candidates selector C Kbound
          hC hdeficit hbandT
    have hscale :
        (B.q / B.L) * (C * Kbound) =
          (B.q / B.L) * (C * Kbound / B.w) * B.w := by
      field_simp [B.w_pos.ne']
    rw [← hscale]
    exact hordinary

/-! ## Literal frozen-top Post-Hfit specialization -/

/-- The final frozen-top structured preselector needs no additional
height-ledger premise: its pointwise deficit estimate directly supplies
the quantitative ordinary-log input. -/
theorem
    bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_ordinaryLogCompatibleUpTo_of_pointwisePaperRate
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
      ((B.q / B.L) * (C * Kbound)) := by
  exact
    bankPaperCanonicalSelector_ordinaryLogCompatibleUpTo_of_pointwisePaperRate
      B R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
          (K := K) B R certificate Tsource deltaStar betaProt alpha beta
            qTilde placementSeed)
        C Kbound hC hdeficit hbandT

/-- Expanded target-minus-prime-log-moment form of the preceding result.
This theorem records explicitly that the direct pointwise argument bounds
the source expression isolated by the frozen-top height reduction. -/
theorem
    bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_target_sub_primeLogMoment_abs_le_of_pointwisePaperRate
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
      (B.q / B.L) * (C * Kbound) := by
  have hordinary :=
    bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_ordinaryLogCompatibleUpTo_of_pointwisePaperRate
      B R certificate fixed Tsource deltaStar betaProt alpha beta qTilde
        placementSeed C Kbound hC hdeficit hbandT
  unfold BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo at hordinary
  rw [
    bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_weightedResidual_eq
      B R certificate fixed Tsource deltaStar betaProt alpha beta qTilde
        placementSeed activeSeed Hmeasure hseed] at hordinary
  exact hordinary

end BankPaperRealization

end

end Erdos390.WholePaper
