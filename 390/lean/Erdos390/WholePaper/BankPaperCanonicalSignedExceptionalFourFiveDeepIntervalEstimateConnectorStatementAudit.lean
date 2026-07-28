import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveDeepIntervalEstimateConnector

/-!
# Statement audit for deep exceptional four/five interval estimates
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

namespace BankPaperRealization

#check roughCanonicalFourFiveDeep_shortFreezingEndpointRate_le
#check roughCanonicalFourFiveDeep_broadFreezingEndpointRate_le
#check roughCanonicalFourFiveDeepShortEstimateConstant
#check roughCanonicalFourFiveDeepBroadEstimateConstant
#check roughCanonicalFourFiveDeepShortEstimateConstant_nonneg
#check roughCanonicalFourFiveDeepBroadEstimateConstant_nonneg
#check abs_roughCanonicalExceptionalPhysicalInterval_card_sub_idealFrozen_le_deepShortRate
#check abs_roughCanonicalExceptionalPhysicalInterval_card_sub_idealFrozen_le_deepBroadRate
#check roughCanonicalFourFiveDeep_self_div_core_le_rateScale
#check roughCanonicalFourFiveDeep_shortIdealLength_le
#check roughCanonicalFourFiveDeep_broadEndpointRate_le
#check abs_fourFiveRoughInterval_card_sub_idealFrozen_le_deepBroadRate_of_empty
#check roughCanonicalFourFiveDeepUpperEstimateConstant
#check roughCanonicalFourFiveDeepHighEstimateConstant
#check roughCanonicalFourFiveDeepBroadFinalEstimateConstant
#check roughCanonicalFourFiveDeepUpperEstimateConstant_nonneg
#check roughCanonicalFourFiveDeepHighEstimateConstant_nonneg
#check roughCanonicalFourFiveDeepBroadFinalEstimateConstant_nonneg
#check roughCanonicalSignedExceptionalDeepIntervalEstimate_of_inputs
#check exists_eventually_roughCanonicalSignedExceptionalDeepIntervalEstimates

/-- The exported package has exactly the shape consumed by the final
remaining-inputs aggregator. -/
example (K0 : Nat) {c deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18) :
    ∃ Cplus Chigh Cbroad : Real,
      0 <= Cplus ∧ 0 <= Chigh ∧ 0 <= Cbroad ∧
      ∀ᶠ n : Nat in atTop, ∀ b : Nat,
        b ∈ roughCanonicalExceptionalDeepCoreSet deltaStar n ->
          RoughCanonicalSignedExceptionalDeepIntervalEstimate
            K0 n b c deltaStar Cplus Chigh Cbroad :=
  exists_eventually_roughCanonicalSignedExceptionalDeepIntervalEstimates
    K0 hc hdelta hdeltaUpper

end BankPaperRealization

end Erdos390.WholePaper
