import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveDeepDisplacementConnector

/-!
# Statement audit for deep frozen-coordinate displacement
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

namespace BankPaperRealization

#check abs_normalizedLog_sub_le_of_div_le_and_abs_sub_le
#check roughCanonicalFourFiveDeepUpperDisplacementConstant
#check roughCanonicalFourFiveDeepHighDisplacementConstant
#check roughCanonicalFourFiveDeepBroadDisplacementConstant
#check roughCanonicalFourFiveDeepUpperDisplacementConstant_nonneg
#check roughCanonicalFourFiveDeepHighDisplacementConstant_nonneg
#check roughCanonicalFourFiveDeepBroadDisplacementConstant_pos
#check roughCanonicalFourFiveDeepUpperFrozenDisplacement_le
#check roughCanonicalFourFiveDeepHighFrozenDisplacement_le
#check roughCanonicalFourFiveDeepBroadFrozenDisplacement_le
#check RoughCanonicalFourFiveDeepFrozenDisplacementBoundsAt
#check roughCanonicalFourFiveDeepFrozenDisplacementBoundsAt_of_scale
#check RoughCanonicalFourFiveDeepFrozenDisplacementBoundsAt.upper_adapter_inputs
#check RoughCanonicalFourFiveDeepFrozenDisplacementBoundsAt.high_adapter_inputs
#check RoughCanonicalFourFiveDeepFrozenDisplacementBoundsAt.broad_adapter_inputs
#check eventually_deepFrozenDisplacement_depth_le_half
#check eventually_roughCanonicalFourFiveDeepFrozenDisplacementBoundsAt

example {K0 n b : Nat} {c deltaStar : Real}
    (h :
      RoughCanonicalFourFiveDeepFrozenDisplacementBoundsAt
        K0 n b c deltaStar) :
    0 <= roughCanonicalFourFiveDeepUpperDisplacementConstant c / L n ^ 2 ∧
      (∀ t ∈ Set.Icc
          (roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b (2 * n) : Real)
          (roughCanonicalExceptionalPhysicalUpperEndpoint
            b (2 * n + upperTailLength c n) : Real),
        abs (Real.log t / Real.log (yNat n : Real) -
            roughCanonicalFourFiveFrozenCoordinate n b) <=
          roughCanonicalFourFiveDeepUpperDisplacementConstant c /
            L n ^ 2) :=
  h.upper_adapter_inputs

end BankPaperRealization

end Erdos390.WholePaper
