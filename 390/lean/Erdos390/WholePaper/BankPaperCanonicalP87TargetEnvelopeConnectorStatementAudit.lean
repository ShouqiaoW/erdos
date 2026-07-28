import Erdos390.WholePaper.BankPaperCanonicalP87TargetEnvelopeConnector

/-!
# Statement audit for the finite P87 target-envelope connector

The examples below expose the exact normalized ordinary-log identity, the
general finite algebra, and its specialization to the literal initial
selector residual.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

/-- The named compatibility input is exactly `sum_p t_p r_p = 0`. -/
example
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat) (selector : Nat -> Real) :
    BankPaperCanonicalSelectorOrdinaryLogCompatible
        (W := W) R certificate fixed candidates selector ↔
      (∑ p : BankPaperCanonicalTangentPrime n W,
        tPrime n p.1 *
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p) = 0 := by
  rfl

/-- Expanded exact compensated-sum identity. -/
example
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
        (B.bandCenter (B.partition.band p) -
          tPrime B.sampleData.n p.1) * residual p := by
  simpa only [BridgeData.primeDeviation] using
    bankPaperCanonicalBandCenterResidual_eq_primeDeviationResidual
      B Delta residual hDelta hordinary

/-- Expanded general constant-seven envelope statement. -/
example
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
    (forall j,
      abs (Delta j) <=
        (B.q / B.L) * (7 * Cinitial) *
          abs (B.harmonicMass j)) ∧
      abs (∑ j, B.bandCenter j * Delta j) <=
        (B.q / B.L) * (7 * Cinitial) * B.w :=
  bankPaperCanonicalHasTargetEnvelopes_seven_of_primeResidual
    B Delta residual Cinitial hCinitial hDelta hpointwise
      hordinary hdeviation

/-- Expanded actual initial-target specialization. -/
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
    (forall j,
      abs (B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget
          B R certificate fixed candidates preSelector activeSeed) 0 j) <=
        (B.q / B.L) * (7 * Cinitial) *
          abs (B.harmonicMass j)) ∧
      abs (∑ j, B.bandCenter j *
        B.markedBandResidual
          (bankPaperCanonicalActualActiveMarkedTarget
            B R certificate fixed candidates preSelector activeSeed) 0 j) <=
        (B.q / B.L) * (7 * Cinitial) * B.w :=
  bankPaperCanonicalActualInitialHasTargetEnvelopes_of_selectorDeficit
    B R certificate fixed candidates preSelector activeSeed
      Hmeasure hseed Cinitial hCinitial hdeficit
        hordinary hdeviation

end

end Erdos390.WholePaper
