import Erdos390.WholePaper.BankPaperCanonicalP87ApproximateOrdinaryLogTargetEnvelopeConnector

/-!
# Statement audit for approximate ordinary-log target envelopes
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale

noncomputable section

#check BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo
#check BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo.of_exact
#check bankPaperCanonicalActualP87EndpointSelector_ordinaryLogCompatibleUpTo
#check BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo.of_eq_normalizedHeightRoundingDefect
#check bankPaperCanonicalBandCenterResidual_eq_primeDeviationResidual_add_ordinaryDefect
#check bankPaperCanonicalHasTargetEnvelopes_seven_add_of_primeResidual
#check bankPaperCanonicalActualInitialHasTargetEnvelopes_of_selectorDeficit_of_approximateOrdinaryLog
#check bankPaperCanonicalSmoothNormalizedHeightRoundingDefect
#check bankPaperCanonicalSmoothNormalizedHeightRoundingDefect_abs_le
#check eventually_bankPaperCanonicalSmoothNormalizedHeightRoundingDefect_abs_le_nine_halves
#check eventually_constant_le_activeMass_div_L_mul_mesh
#check eventually_bankPaperCanonicalSmoothNormalizedHeightRoundingDefect_abs_le_activeMass_div_L_mul_mesh

/-- Expanded finite compensated identity with the defect retained. -/
example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    (Delta : Band -> Real)
    (residual : BandPrime B.sampleData.n B.sampleData.W -> Real)
    (hDelta : forall j,
      Delta j =
        ∑ p ∈ B.partition.data.fiber j, residual p) :
    (∑ j : Band, B.bandCenter j * Delta j) =
      (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation p * residual p) +
      ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 * residual p :=
  bankPaperCanonicalBandCenterResidual_eq_primeDeviationResidual_add_ordinaryDefect
    B Delta residual hDelta

/-- Expanded target-envelope statement with additive ordinary-log cost. -/
example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (Delta : Band -> Real)
    (residual : BandPrime B.sampleData.n B.sampleData.W -> Real)
    (Cinitial Cordinary : Real)
    (hCinitial : 0 <= Cinitial) (hCordinary : 0 <= Cordinary)
    (hDelta : forall j,
      Delta j =
        ∑ p ∈ B.partition.data.fiber j, residual p)
    (hpointwise : forall p,
      abs (residual p) <=
        Cinitial * B.q / ((p.1 : Real) * B.L))
    (hordinary :
      abs (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 * residual p) <=
        (B.q / B.L) * Cordinary * B.w)
    (hdeviation : B.primeDeviationL1 <= 7 * B.w) :
    (forall j,
      abs (Delta j) <=
        (B.q / B.L) * (7 * Cinitial + Cordinary) *
          abs (B.harmonicMass j)) ∧
      abs (∑ j, B.bandCenter j * Delta j) <=
        (B.q / B.L) * (7 * Cinitial + Cordinary) * B.w :=
  bankPaperCanonicalHasTargetEnvelopes_seven_add_of_primeResidual
    B Delta residual Cinitial Cordinary hCinitial hCordinary
      hDelta hpointwise hordinary hdeviation

/-- Expanded asymptotic absorption of the normalized rounding defect. -/
example
    (mu : Real) (hmu : 0 <= mu)
    (q0 A0 q : Nat -> Real)
    (Hq : BankPaperCanonicalActiveMassPaperScaleLower q)
    {w : Real} (hw : 0 < w) :
    ∀ᶠ n : Nat in atTop,
      abs (bankPaperCanonicalSmoothNormalizedHeightRoundingDefect
        n mu (q0 n) (A0 n)) <= q n / L n * w :=
  eventually_bankPaperCanonicalSmoothNormalizedHeightRoundingDefect_abs_le_activeMass_div_L_mul_mesh
    mu hmu q0 A0 q Hq hw

end

end Erdos390.WholePaper
