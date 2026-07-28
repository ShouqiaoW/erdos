import Erdos390.WholePaper.BankPaperCanonicalRawRowCorrectionRateClosure

open Filter

namespace Erdos390.WholePaper.BankPaperRealization

open Erdos390.Full.Scale

#check roughCanonicalUniformRawRowCorrectionDensityConstant
#check roughCanonicalUniformRawRowCorrectionDensityConstant_nonneg
#check eventually_roughCanonicalUniformRawRowCorrectionDensityBound
#check eventually_roughCanonicalAggregateRawRowCorrectionBound_strictScale

example
    (W K0 : Nat) {c beta deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop,
      RoughCanonicalUniformRawRowCorrectionDensityBound
        W n (upperTailLength c n) (K0 + 1) deltaStar
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n)
        (roughCanonicalUniformRawRowCorrectionDensityConstant
          W K0 c beta / (4 * L n ^ 2)) :=
  eventually_roughCanonicalUniformRawRowCorrectionDensityBound
    W K0 (beta := beta) hc hdelta

end Erdos390.WholePaper.BankPaperRealization
