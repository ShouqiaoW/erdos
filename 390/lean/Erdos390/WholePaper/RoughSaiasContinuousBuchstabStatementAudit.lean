import Erdos390.WholePaper.RoughSaiasContinuousBuchstab

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory

noncomputable section

#check roughSaiasZeroExtendedRho
#check roughSaiasZeroExtendedRho_of_neg
#check roughSaiasZeroExtendedRho_of_nonneg
#check roughSaiasZeroExtendedRho_zero
#check measurable_roughSaiasZeroExtendedRho
#check roughSaiasZeroExtendedRho_mem_unitInterval
#check roughSaiasZeroExtendedRho_abs_le_one
#check roughSaiasStieltjesDickmanProfile
#check measurable_roughSaiasStieltjesDickmanProfile
#check roughSaiasStieltjesDickmanProfile_eq_zero_of_lt
#check roughSaiasStieltjesDickmanProfile_self
#check roughSaiasStieltjesDickmanProfile_one
#check roughSaiasStieltjesCoordinate_eq_log_div
#check roughSaiasStieltjesDickmanProfile_div_eq_test
#check roughSaiasStieltjesDickmanProfile_eq_mul_test
#check roughSaiasStieltjesTest_self
#check roughSaiasFloorDensity
#check measurable_roughSaiasFloorDensity
#check roughSaiasStieltjesAtomPart
#check roughSaiasStieltjesDensityPart
#check roughSaiasFiniteStieltjesFunctional
#check roughSaiasStieltjesAtomPart_zero
#check roughSaiasStieltjesDensityPart_zero
#check roughSaiasFiniteStieltjesFunctional_zero
#check roughSaiasStieltjesAtomPart_add
#check roughSaiasStieltjesDensityPart_add
#check roughSaiasFiniteStieltjesFunctional_add
#check roughSaiasFiniteStieltjesFunctional_congr
#check roughSaiasStieltjesAtomPart_eq_of_cutoff
#check roughSaiasStieltjesDensityPart_eq_of_cutoff
#check roughSaiasFiniteStieltjesFunctional_eq_of_cutoff
#check roughSaiasLambdaStieltjesWithCutoff
#check roughSaiasLambdaStieltjes
#check roughSaiasLambdaStieltjesWithCutoff_eq_of_le
#check roughSaiasLambdaStieltjesWithCutoff_eq_canonical
#check roughSaiasStieltjesAtomPart_profile_nat
#check roughSaiasStieltjesTest_sum_eq_endpoint_sub_integral
#check roughSaiasLambdaStieltjesWithCutoff_nat_eq_test_sub_density
#check roughSaiasLambdaStieltjesWithCutoff_nat_eq_abel_ledger
#check roughSaiasLambdaStieltjes_nat
#check roughSaiasContinuousBuchstabProfile
#check roughSaiasStieltjesDickmanProfile_eq_mul_antiderivative
#check roughSaiasContinuousBuchstabProfile_eq_mul_dickmanWeight
#check roughSaiasContinuousBuchstabProfile_eq_zero_of_lt
#check roughSaiasStieltjesDickmanProfile_eq_first_of_one_le_ratio
#check intervalIntegrable_roughSaiasContinuousBuchstabProfile_to_birth
#check intervalIntegrable_roughSaiasContinuousBuchstabProfile_from_birth
#check roughSaiasContinuousBuchstabProfile_integral_from_birth_eq_zero
#check roughSaiasStieltjesDickmanProfile_buchstab_active
#check roughSaiasStieltjesDickmanProfile_buchstab_birth
#check roughSaiasStieltjesDickmanProfile_buchstab_inactive
#check roughSaiasStieltjesDickmanProfile_buchstab_cross_birth
#check intervalIntegrable_roughSaiasContinuousBuchstabProfile
#check roughSaiasStieltjesDickmanProfile_buchstab

example {R S : ℕ} {f : ℝ → ℝ} (hRS : R ≤ S)
    (hzero : ∀ t, (R : ℝ) < t → t ≤ (S : ℝ) → f t = 0) :
    roughSaiasFiniteStieltjesFunctional R f =
      roughSaiasFiniteStieltjesFunctional S f :=
  roughSaiasFiniteStieltjesFunctional_eq_of_cutoff hRS hzero

example {R S : ℕ} {x y : ℝ} (hRS : R ≤ S)
    (hx : 0 < x) (hy : 1 < y) (hxR : x ≤ (R : ℝ)) :
    roughSaiasLambdaStieltjesWithCutoff R x y =
      roughSaiasLambdaStieltjesWithCutoff S x y :=
  roughSaiasLambdaStieltjesWithCutoff_eq_of_le hRS hx hy hxR

example {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    roughSaiasLambdaStieltjesWithCutoff X (X : ℝ) y =
      ((X : ℝ) -
          (∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
            roughSaiasStieltjesTestRightDerivative (X : ℝ) y t *
              (((⌊t⌋₊ : ℕ) : ℝ)))) -
        roughSaiasStieltjesDensityPart X
          (roughSaiasStieltjesDickmanProfile (X : ℝ) y) :=
  roughSaiasLambdaStieltjesWithCutoff_nat_eq_abel_ledger hX hy hu5

example {x t y z : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hy : 1 < y) (hyz : y ≤ z)
    (hu6 : Real.log (x / t) / Real.log y ≤ 6) :
    roughSaiasStieltjesDickmanProfile x y t =
      roughSaiasStieltjesDickmanProfile x z t -
        ∫ s in y..z, roughSaiasContinuousBuchstabProfile x s t :=
  roughSaiasStieltjesDickmanProfile_buchstab hx ht hy hyz hu6

example {x t y z : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hy : 1 < y) (hyz : y ≤ z)
    (hu6 : Real.log (x / t) / Real.log y ≤ 6) :
    IntervalIntegrable (roughSaiasContinuousBuchstabProfile x · t)
      volume y z :=
  intervalIntegrable_roughSaiasContinuousBuchstabProfile
    hx ht hy hyz hu6

end

end Erdos390.WholePaper
