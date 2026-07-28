import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalOrderedMixtureConnector

/-!
# Statement audit for the exceptional ordered-mixture connector
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

namespace BankPaperRealization

#check fourFiveReciprocalBVError_le_one_of_log_large
#check fourFiveLogLogPrimitive_sub_le_log_twentyfour_fifths_of_paperRange
#check fourFiveOrderedPrimeMixtureEstimate_realEndpoint_compact_of_paperRange
#check roughCanonicalExceptional_yNat_tendsto_atTop
#check roughCanonicalExceptional_log_yNat_tendsto_atTop
#check exists_eventually_roughCanonicalExceptionalPhysicalInterval_orderedMixtureEstimate

example {deltaStar : Real} :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ n : Nat in atTop, ∀ b A B : Nat,
        RoughCanonicalExceptionalPhysicalIntervalGeometry
            n deltaStar b A B ->
          FourFiveOrderedPrimeMixtureEstimate (yNat n) A B
            (fourFiveContinuumMixtureIntegralMain (yNat n) A B)
            (fourFiveRealEndpointFullyBoundedAssemblyError
              C (yNat n) A B fourFiveCompactReciprocalMass) :=
  exists_eventually_roughCanonicalExceptionalPhysicalInterval_orderedMixtureEstimate

end BankPaperRealization

end Erdos390.WholePaper
