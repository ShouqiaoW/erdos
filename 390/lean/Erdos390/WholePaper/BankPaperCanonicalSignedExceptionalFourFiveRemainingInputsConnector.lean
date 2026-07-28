import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveGeometryPrecursorConnector
import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveDeepIntervalEstimateConnector
import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveCutoffIntervalPrecursorConnector

/-!
# Remaining inputs for the signed exceptional four/five chamber

This connector combines the three independent precursor layers:

* the routine scalar and padded-coordinate geometry;
* the three frozen deep-prefix interval estimates;
* the three positive cutoff-band interval estimates.

The result is the exact six-constant
`RoughCanonicalSignedExceptionalFourFiveRemainingInputs` package consumed
by the existing chamber connector.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Finite assembly -/

/-- At one value of `n`, the geometry precursor and the two three-interval
packages give the exact chamber input record. -/
theorem
    roughCanonicalSignedExceptionalFourFiveChamberInputAt_of_precursors
    {W K0 n : Nat} {c deltaStar : Real}
    {deepPlus deepHigh deepBroad
      cutoffPlus cutoffHigh cutoffBroad : Real}
    (hgeometry :
      RoughCanonicalSignedExceptionalFourFiveGeometryPrecursorAt
        W n deltaStar)
    (hdeep :
      ∀ b ∈ roughCanonicalExceptionalDeepCoreSet deltaStar n,
        RoughCanonicalSignedExceptionalDeepIntervalEstimate
          K0 n b c deltaStar deepPlus deepHigh deepBroad)
    (hcutoff :
      ∀ b ∈ roughCanonicalExceptionalCutoffCoreSet deltaStar n,
        RoughCanonicalSignedExceptionalCutoffIntervalEstimate
          K0 n b c deltaStar cutoffPlus cutoffHigh cutoffBroad) :
    RoughCanonicalSignedExceptionalFourFiveChamberInputAt
      W K0 n c deltaStar
      deepPlus deepHigh deepBroad
      cutoffPlus cutoffHigh cutoffBroad := by
  exact
    { n_two := hgeometry.scalar_bounds.n_two
      head_le_yNat := hgeometry.scalar_bounds.head_le_yNat
      core_cutoff_le_yNat :=
        hgeometry.scalar_bounds.core_cutoff_le_yNat
      log_scale_one := hgeometry.scalar_bounds.log_scale_one
      log_yNat_one := hgeometry.scalar_bounds.log_yNat_one
      deep_intervals := hdeep
      cutoff_intervals := hcutoff
      variation_coordinates := hgeometry.variation_coordinates }

/-! ## Eventual six-constant package -/

/-- The geometry, deep-prefix, and cutoff-band connectors supply all six
nonnegative constants and the exact eventual remaining-input certificate
required by the signed exceptional four/five chamber. -/
theorem
    exists_roughCanonicalSignedExceptionalFourFiveRemainingInputs
    (W K0 : Nat) {c deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18) :
    ∃ deepPlus deepHigh deepBroad
        cutoffPlus cutoffHigh cutoffBroad : Real,
      0 <= deepPlus ∧ 0 <= deepHigh ∧ 0 <= deepBroad ∧
      0 <= cutoffPlus ∧ 0 <= cutoffHigh ∧ 0 <= cutoffBroad ∧
      RoughCanonicalSignedExceptionalFourFiveRemainingInputs
        W K0 c deltaStar
        deepPlus deepHigh deepBroad
        cutoffPlus cutoffHigh cutoffBroad := by
  obtain ⟨deepPlus, deepHigh, deepBroad,
      hdeepPlus, hdeepHigh, hdeepBroad, hdeepEventually⟩ :=
    exists_eventually_roughCanonicalSignedExceptionalDeepIntervalEstimates
      K0 hc hdelta hdeltaUpper
  obtain ⟨cutoffPlus, cutoffHigh, cutoffBroad,
      hcutoffPlus, hcutoffHigh, hcutoffBroad, hcutoffEventually⟩ :=
    exists_eventually_roughCanonicalSignedExceptionalCutoffIntervalEstimates
      K0 hc hdelta.le hdeltaUpper
  have hgeometryEventually :=
    eventually_roughCanonicalSignedExceptionalFourFiveGeometryPrecursorAt
      W hdelta.le hdeltaUpper
  refine
    ⟨deepPlus, deepHigh, deepBroad,
      cutoffPlus, cutoffHigh, cutoffBroad,
      hdeepPlus, hdeepHigh, hdeepBroad,
      hcutoffPlus, hcutoffHigh, hcutoffBroad, ?_⟩
  unfold RoughCanonicalSignedExceptionalFourFiveRemainingInputs
  filter_upwards [
      hgeometryEventually, hdeepEventually, hcutoffEventually]
      with n hgeometry hdeep hcutoff
  exact
    roughCanonicalSignedExceptionalFourFiveChamberInputAt_of_precursors
      hgeometry hdeep hcutoff

end BankPaperRealization

end

end Erdos390.WholePaper
