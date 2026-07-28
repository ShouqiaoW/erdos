import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalClippedIntervalGeometry

/-!
# Statement audit for signed exceptional clipped-interval geometry

The checks below keep the exact natural floor, the three physical endpoint
alternatives, and the padded `[4.1,4.7]` coordinate certificate visible at
the public boundary.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Erdos390.Full.PaperScaleMarkedCell

namespace BankPaperRealization

#check roughCanonicalExceptionalPhysicalLowerEndpoint
#check roughCanonicalExceptionalPhysicalUpperEndpoint
#check roughCanonicalExceptionalClippedRoughInterval_eq_endpoints
#check RoughCanonicalExceptionalPhysicalIntervalGeometry
#check RoughCanonicalExceptionalCommonEndpointGeometry
#check RoughCanonicalExceptionalPhysicalIntervalGeometry.counting_inputs
#check fourFiveRoughInterval_eq_empty_of_upper_le_lower
#check roughCanonicalExceptionalClippedRoughInterval_eq_empty
#check roughCanonicalExceptionalClippedRoughInterval_card_eq_zero
#check roughCanonicalExceptionalClippedInterval_geometry
#check roughCanonicalExceptionalClippedInterval_geometry_or_empty
#check roughCanonicalExceptional_threePhysicalIntervals_geometry_or_empty
#check rpow_one_sub_le_roughCanonicalRealExceptionalRoughCutoff
#check one_le_roughCanonicalRealExceptionalRoughCutoff
#check yNat_le_roughCanonicalRealExceptionalRoughCutoff
#check roughCanonicalExceptionalPaddedLogThreshold
#check roughCanonicalExceptional_common_padded_log_range
#check three_mul_lt_yNat_succ_pow_five
#check roughCanonicalExceptionalCommonEndpointGeometry_of_bounds
#check eventually_roughCanonicalExceptionalCommonEndpointGeometry
#check eventually_roughCanonicalExceptional_threePhysicalIntervals_geometry_or_empty

example {n b A B : Nat} {deltaStar : Real}
    (h :
      RoughCanonicalExceptionalPhysicalIntervalGeometry
        n deltaStar b A B) :
    1 <= A ∧ A <= B ∧ B < (yNat n + 1) ^ 5 ∧
      yNat n <= B ∧
      (∀ t ∈ Set.Icc (A : Real) (B : Real),
        Real.log t / Real.log (yNat n : Real) ∈
          Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) ∧
      (B : Real) <= (3 * n / b + 1 : Nat) :=
  h.counting_inputs

example {n b lo hi : Nat} {deltaStar : Real}
    (hBA :
      roughCanonicalExceptionalPhysicalUpperEndpoint b hi <=
        roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b lo) :
    (roughCanonicalExceptionalClippedRoughInterval
        n deltaStar b lo hi).card = 0 :=
  roughCanonicalExceptionalClippedRoughInterval_card_eq_zero hBA

end BankPaperRealization

end Erdos390.WholePaper
