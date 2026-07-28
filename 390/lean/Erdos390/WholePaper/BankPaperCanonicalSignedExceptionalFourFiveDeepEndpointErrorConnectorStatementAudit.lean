import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveDeepEndpointErrorConnector

/-!
# Statement audit for deep exceptional endpoint-length errors
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

namespace BankPaperRealization

#check abs_clippedNatIntervalLength_sub_ideal_le
#check roughCanonicalRealExceptionalRoughCutoff_le_natQuotient_of_real_le
#check roughCanonicalFourFiveDeepUpperHigh_noClipping_of_scale
#check roughCanonicalFourFiveDeepUpperEndpointLengthError_le_one
#check roughCanonicalFourFiveDeepHighEndpointLengthError_le_one
#check roughCanonicalFourFiveDeepBroadClippingExcess_le
#check roughCanonicalFourFiveDeepBroadEndpointLengthError_le
#check RoughCanonicalFourFiveDeepEndpointLengthErrorsAt
#check roughCanonicalFourFiveDeepEndpointLengthErrorsAt_of_scale
#check RoughCanonicalFourFiveDeepEndpointLengthErrorsAt.upper_adapter_inputs
#check RoughCanonicalFourFiveDeepEndpointLengthErrorsAt.high_adapter_inputs
#check RoughCanonicalFourFiveDeepEndpointLengthErrorsAt.broad_adapter_inputs
#check eventually_deepEndpointError_L_le_rpow
#check eventually_roughCanonicalFourFiveDeepUpperHigh_noClipping
#check eventually_roughCanonicalFourFiveDeepEndpointLengthErrorsAt

/-- The broad adapter input visibly retains the clipped lower endpoint and
the `Z/L+1` endpoint budget used by the deep six-estimate assembly. -/
example {K0 n b : Nat} {c deltaStar : Real}
    (h :
      RoughCanonicalFourFiveDeepEndpointLengthErrorsAt
        K0 n b c deltaStar) :
    0 <=
        2 *
          (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) ∧
      abs (((roughCanonicalExceptionalPhysicalUpperEndpoint b
              (2 * n - (K0 + 1) * upperTailLength c n) -
            roughCanonicalExceptionalPhysicalLowerEndpoint
              n deltaStar b n : Nat) : Real) -
          ((n - (K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real)) <=
        2 *
          (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) :=
  h.broad_adapter_inputs

end BankPaperRealization

end Erdos390.WholePaper
