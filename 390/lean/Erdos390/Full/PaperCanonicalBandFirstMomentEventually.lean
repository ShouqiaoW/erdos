import Erdos390.Full.PaperBridgeFit
import Erdos390.Full.PaperCompensatedCoefficientBounds
import Erdos390.Full.PrimeSums

/-!
# Canonical band first-moment bound

The target and speed packages in Proposition 8.7 use the literal arithmetic
first moment `sum_j H_j * alpha_j`.  It is exactly the reciprocal prime-band
moment, independently of the chosen partition, and hence is eventually at
most `2 * log 4`.  Keeping this elementary conversion in a named terminal
prevents the final orchestration from retaining a moment inequality as an
analytic call-site hypothesis.
-/

open scoped BigOperators
open Filter

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PrimeSums

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- The partition first moment has the universal eventual prime-band bound. -/
theorem eventually_bandFirstMoment_le_two_log_four (W : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band),
        B.sampleData.n = n → B.sampleData.W = W →
        (∑ j : Band, B.harmonicMass j * B.bandCenter j) ≤
          2 * Real.log 4 := by
  filter_upwards [eventually_bandTReciprocalSum_le W] with n hband
  intro B hBn hBW
  subst n
  subst W
  calc
    (∑ j : Band, B.harmonicMass j * B.bandCenter j) =
        bandTReciprocalSum B.sampleData.n B.sampleData.W := by
      simpa only [harmonicMass, bandCenter] using
        B.partition.sum_mass_mul_center_eq_bandTReciprocalSum
    _ ≤ 2 * Real.log 4 := hband

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
