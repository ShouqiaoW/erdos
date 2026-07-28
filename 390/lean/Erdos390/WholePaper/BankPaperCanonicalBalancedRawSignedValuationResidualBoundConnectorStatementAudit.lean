import Erdos390.WholePaper.BankPaperCanonicalBalancedRawSignedValuationResidualBoundConnector

/-! Statement audit for the balanced raw signed valuation connector. -/

open Filter

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

#check factorization_cast_eq_sum_primeExponentIndicators
#check sum_factorization_cast_eq_sum_primePowerDivisorCounts
#check sum_weight_mul_factorization_cast_eq_sum_primePowerIndicators
#check Ioc_filter_dvd_card_sub_realLengthDiv_abs_lt_one
#check roughCanonicalRawPrimePowerColumnResidual
#check sum_roughHeadCompatibleRawWeight_mul_primePowerIndicator
#check roughCanonicalRawSignedValuationResidual_eq_sum_primePowerColumns
#check abs_roughCanonicalRawPrimePowerColumnResidual_le
#check abs_roughCanonicalRawSignedValuationResidual_le_log_mul_columnBound
#check roughCanonicalBalancedRawPrimePowerColumnConstant
#check roughCanonicalBalancedRawPrimePowerColumnConstant_nonneg
#check roughCanonicalBalancedRawSignedValuationConstant
#check roughCanonicalBalancedRawSignedValuationConstant_nonneg
#check eventually_yNat_sq_le_secondOrderScale_div_L
#check eventually_balancedRaw_primePowerColumnBound_le_constant
#check eventually_roughCanonicalBalancedRawSignedValuationResidualBound
#check exists_eventually_roughCanonicalBalancedRawSignedValuationResidualBound

example
    (W K0 : Nat) {c beta : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop, ∀ p : Nat,
      p.Prime -> W < p -> p <= yNat n ->
      RoughCanonicalBalancedRawSignedValuationResidualBound
        W n K0 c beta p
        (roughCanonicalBalancedRawSignedValuationConstant W K0 c beta *
          secondOrderScale n / ((p : Real) * L n)) :=
  eventually_roughCanonicalBalancedRawSignedValuationResidualBound
    W K0 hc

example
    (W K0 : Nat) {c beta : Real} (hc : 0 < c) :
    ∃ Craw : Real, 0 <= Craw ∧
      ∀ᶠ n : Nat in atTop, ∀ p : Nat,
        p.Prime -> W < p -> p <= yNat n ->
        RoughCanonicalBalancedRawSignedValuationResidualBound
          W n K0 c beta p
          (Craw * secondOrderScale n / ((p : Real) * L n)) :=
  exists_eventually_roughCanonicalBalancedRawSignedValuationResidualBound
    W K0 hc

end BankPaperRealization

end

end Erdos390.WholePaper
