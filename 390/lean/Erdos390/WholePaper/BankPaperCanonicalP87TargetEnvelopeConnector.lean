import Erdos390.WholePaper.BankPaperProposition87ActualDataConnector
import Erdos390.Full.PaperPrimeDeviationGeometry

/-!
# Finite target envelopes from the canonical selector residual

The paper obtains the slow target estimate from two genuinely different
inputs:

* the pointwise medium-prime residual rate; and
* exact ordinary-log compatibility
  `sum_p t_p r_p = 0`.

The latter is not implied by the current guarded-selector state.  This file
therefore names it explicitly and proves only the finite algebra which
follows from it.  In particular, no selector construction or logarithmic
compatibility theorem is hidden in a structure field.

For a residual `r_p`, exact compatibility rewrites

`sum_j alpha_j Delta_j = sum_p (alpha_{j(p)} - t_p) r_p`.

The pointwise rate and the literal prime-deviation `L¹` bound then give the
two target envelopes, with the uniform constant enlarged from `Cinitial` to
`7 * Cinitial`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

/-! ## The explicit ordinary-log input -/

/-- Exact normalized ordinary-log compatibility of the prebridge selector.

This is the finite identity used in the paper after the head, physical, and
frozen logarithmic ledgers have been fitted.  It is deliberately a visible
input: the currently constructed guarded-selector state does not yet prove
it. -/
def BankPaperCanonicalSelectorOrdinaryLogCompatible
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat) (selector : Nat -> Real) : Prop :=
  ∑ p : BankPaperCanonicalTangentPrime n W,
      tPrime n p.1 *
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p = 0

/-! ## General finite residual algebra -/

/-- Exact compensated-sum identity for a residual distributed over the
actual arithmetic bands. -/
theorem bankPaperCanonicalBandCenterResidual_eq_primeDeviationResidual
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    (Delta : Band -> Real)
    (residual : BandPrime B.sampleData.n B.sampleData.W -> Real)
    (hDelta : forall j,
      Delta j =
        ∑ p ∈ B.partition.data.fiber j, residual p)
    (hordinary :
      (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 * residual p) = 0) :
    (∑ j : Band, B.bandCenter j * Delta j) =
      ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation p * residual p := by
  have hcenter :
      (∑ j : Band, B.bandCenter j * Delta j) =
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.bandCenter (B.partition.band p) * residual p := by
    calc
      (∑ j : Band, B.bandCenter j * Delta j) =
          ∑ j : Band, B.bandCenter j *
            (∑ p ∈ B.partition.data.fiber j, residual p) := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [hDelta j]
      _ = ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.bandCenter (B.partition.band p) * residual p := by
        rw [← Finset.sum_fiberwise Finset.univ B.partition.band
          (fun p : BandPrime B.sampleData.n B.sampleData.W =>
            B.bandCenter (B.partition.band p) * residual p)]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        have hpj : B.partition.band p = j :=
          (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff
            B.partition.data).mp hp
        rw [hpj]
  calc
    (∑ j : Band, B.bandCenter j * Delta j) =
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.bandCenter (B.partition.band p) * residual p := hcenter
    _ = (∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.bandCenter (B.partition.band p) * residual p) -
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          tPrime B.sampleData.n p.1 * residual p := by
      rw [hordinary, sub_zero]
    _ = ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation p * residual p := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _hp
      unfold BridgeData.primeDeviation
      ring

/-- Pointwise residual control, exact ordinary-log compatibility, and the
canonical `L¹` mesh estimate imply both target envelopes. -/
theorem bankPaperCanonicalHasTargetEnvelopes_seven_of_primeResidual
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (Delta : Band -> Real)
    (residual : BandPrime B.sampleData.n B.sampleData.W -> Real)
    (Cinitial : Real) (hCinitial : 0 <= Cinitial)
    (hDelta : forall j,
      Delta j =
        ∑ p ∈ B.partition.data.fiber j, residual p)
    (hpointwise : forall p,
      abs (residual p) <=
        Cinitial * B.q / ((p.1 : Real) * B.L))
    (hordinary :
      (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 * residual p) = 0)
    (hdeviation : B.primeDeviationL1 <= 7 * B.w) :
    B.HasTargetEnvelopes (7 * Cinitial) Delta := by
  have hqL : 0 <= B.q / B.L :=
    (div_pos B.q_pos B.L_pos).le
  have hCseven : Cinitial <= 7 * Cinitial := by
    linarith
  constructor
  · intro j
    have hrateSum :
        (∑ p ∈ B.partition.data.fiber j,
          Cinitial * B.q / ((p.1 : Real) * B.L)) =
            (B.q / B.L) * Cinitial * B.harmonicMass j := by
      unfold BridgeData.harmonicMass
      change
        (∑ p ∈ B.partition.data.fiber j,
          Cinitial * B.q / ((p.1 : Real) * B.L)) =
            (B.q / B.L) * Cinitial *
              (∑ p ∈ B.partition.data.fiber j,
                1 / (p.1 : Real))
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      have hpPos : (0 : Real) < (p.1 : Real) := by
        exact_mod_cast (prime_of_mem_primeBand p.2).pos
      field_simp [ne_of_gt hpPos, ne_of_gt B.L_pos]
    calc
      abs (Delta j) =
          abs (∑ p ∈ B.partition.data.fiber j, residual p) := by
        rw [hDelta j]
      _ <= ∑ p ∈ B.partition.data.fiber j, abs (residual p) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ p ∈ B.partition.data.fiber j,
          Cinitial * B.q / ((p.1 : Real) * B.L) := by
        exact Finset.sum_le_sum fun p _hp => hpointwise p
      _ = (B.q / B.L) * Cinitial * B.harmonicMass j :=
        hrateSum
      _ = (B.q / B.L) * Cinitial * abs (B.harmonicMass j) := by
        rw [abs_of_pos (B.harmonicMass_pos j)]
      _ <= (B.q / B.L) * (7 * Cinitial) *
          abs (B.harmonicMass j) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCseven hqL) (abs_nonneg _)
  · rw [bankPaperCanonicalBandCenterResidual_eq_primeDeviationResidual
      B Delta residual hDelta hordinary]
    have hweightedRate :
        (∑ p : BandPrime B.sampleData.n B.sampleData.W,
          abs (B.primeDeviation p) *
            (Cinitial * B.q / ((p.1 : Real) * B.L))) =
          (B.q / B.L) * Cinitial * B.primeDeviationL1 := by
      unfold BridgeData.primeDeviationL1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      have hpPos : (0 : Real) < (p.1 : Real) := by
        exact_mod_cast (prime_of_mem_primeBand p.2).pos
      field_simp [ne_of_gt hpPos, ne_of_gt B.L_pos]
    have hfactor : 0 <= (B.q / B.L) * Cinitial :=
      mul_nonneg hqL hCinitial
    calc
      abs (∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation p * residual p) <=
          ∑ p : BandPrime B.sampleData.n B.sampleData.W,
            abs (B.primeDeviation p * residual p) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          abs (B.primeDeviation p) *
            (Cinitial * B.q / ((p.1 : Real) * B.L)) := by
        apply Finset.sum_le_sum
        intro p _hp
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (hpointwise p) (abs_nonneg _)
      _ = (B.q / B.L) * Cinitial * B.primeDeviationL1 :=
        hweightedRate
      _ <= (B.q / B.L) * Cinitial * (7 * B.w) :=
        mul_le_mul_of_nonneg_left hdeviation hfactor
      _ = (B.q / B.L) * (7 * Cinitial) * B.w := by
        ring

/-! ## Specialization to the literal initial P87 residual -/

/-- The actual initial marked-band target has the required envelopes once
the selector deficit has the pointwise rate and the explicit normalized
ordinary-log compatibility identity.

The conversion from selector deficit to the active marked residual is
derived from the actual-measure constructor and the initial-seed identity;
it is not an additional hypothesis. -/
theorem bankPaperCanonicalActualInitialHasTargetEnvelopes_of_selectorDeficit
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
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (Cinitial : Real) (hCinitial : 0 <= Cinitial)
    (hdeficit : ∀ p ∈
      primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed candidates preSelector p) <=
          Cinitial * B.q / ((p : Real) * B.L))
    (hordinary : BankPaperCanonicalSelectorOrdinaryLogCompatible
      (W := B.sampleData.W)
      R certificate fixed candidates preSelector)
    (hdeviation : B.primeDeviationL1 <= 7 * B.w) :
    B.HasTargetEnvelopes (7 * Cinitial)
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget
          B R certificate fixed candidates preSelector activeSeed) 0 j) := by
  let markedTarget : Nat -> Real :=
    bankPaperCanonicalActualActiveMarkedTarget
      B R certificate fixed candidates preSelector activeSeed
  let residual : BandPrime B.sampleData.n B.sampleData.W -> Real :=
    fun p =>
      bankPaperCanonicalTangentResidual
        R certificate fixed candidates preSelector p
  have hDelta : forall j : Band,
      B.markedBandResidual markedTarget 0 j =
        ∑ p ∈ B.partition.data.fiber j, residual p := by
    intro j
    unfold BridgeData.markedBandResidual
    apply Finset.sum_congr rfl
    intro p _hp
    dsimp only [markedTarget, residual,
      bankPaperCanonicalTangentResidual]
    exact (bankPaperCanonicalActualInitial_deficit_eq_activeResidual
      B R certificate fixed candidates preSelector activeSeed
        Hmeasure hseed p.1).symm
  have hpointwise : forall p,
      abs (residual p) <=
        Cinitial * B.q / ((p.1 : Real) * B.L) := by
    intro p
    simpa only [residual, bankPaperCanonicalTangentResidual] using
      hdeficit p.1 p.2
  have hordinaryResidual :
      (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 * residual p) = 0 := by
    simpa only [BankPaperCanonicalSelectorOrdinaryLogCompatible,
      residual] using hordinary
  exact bankPaperCanonicalHasTargetEnvelopes_seven_of_primeResidual
    B
    (fun j => B.markedBandResidual markedTarget 0 j)
    residual Cinitial hCinitial hDelta hpointwise
      hordinaryResidual hdeviation

end

end Erdos390.WholePaper
