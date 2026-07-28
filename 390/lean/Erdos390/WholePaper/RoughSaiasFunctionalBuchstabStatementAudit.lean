import Erdos390.WholePaper.RoughSaiasFunctionalBuchstab

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory

noncomputable section

#check roughSaiasBuchstabDensityKernel
#check RoughSaiasBuchstabDensityFubini
#check roughSaiasFiniteStieltjesFunctional_div
#check roughSaiasFiniteStieltjesFunctional_buchstabProfile
#check roughSaias_log_div_t_ratio_le
#check measurable_uncurry_roughSaiasBuchstabDensityKernel
#check exists_roughSaiasZeroExtendedRho_abs_bound_six
#check roughSaiasFloorDensity_mem_unitInterval
#check roughSaias_profile_coordinate_le_six
#check roughSaias_inner_profile_coordinate_le_six
#check integrableOn_roughSaiasProfile_mul_floorDensity_six
#check roughSaiasBuchstabDensityKernel_abs_le
#check integrable_roughSaiasBuchstabDensityKernel
#check roughSaiasBuchstabDensityFubini_of_compact
#check roughSaiasStieltjesAtomPart_buchstab
#check roughSaiasStieltjesDensityPart_buchstab
#check roughSaiasFiniteStieltjesFunctional_buchstab
#check roughSaiasLambdaStieltjesWithCutoff_buchstab
#check intervalIntegrable_roughSaiasLambdaStieltjesWithCutoff_buchstab
#check roughSaiasStieltjesDensityPart_buchstab_unconditional
#check roughSaiasFiniteStieltjesFunctional_buchstab_unconditional
#check roughSaiasLambdaStieltjesWithCutoff_buchstab_unconditional

example {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6)
    (hFubini : RoughSaiasBuchstabDensityFubini R x y z) :
    roughSaiasFiniteStieltjesFunctional R
        (roughSaiasStieltjesDickmanProfile x y) =
      roughSaiasFiniteStieltjesFunctional R
          (roughSaiasStieltjesDickmanProfile x z) -
        ∫ s in y..z,
          roughSaiasFiniteStieltjesFunctional R
            (roughSaiasContinuousBuchstabProfile x s) :=
  roughSaiasFiniteStieltjesFunctional_buchstab
    hx hy hyz hu6 hFubini

example {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6)
    (hFubini : RoughSaiasBuchstabDensityFubini R x y z) :
    roughSaiasLambdaStieltjesWithCutoff R x y =
      roughSaiasLambdaStieltjesWithCutoff R x z -
        ∫ s in y..z,
          roughSaiasLambdaStieltjesWithCutoff R (x / s) s /
            Real.log s :=
  roughSaiasLambdaStieltjesWithCutoff_buchstab
    hx hy hyz hu6 hFubini

example {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    IntervalIntegrable
      (fun s ↦ roughSaiasLambdaStieltjesWithCutoff R (x / s) s /
        Real.log s) volume y z :=
  intervalIntegrable_roughSaiasLambdaStieltjesWithCutoff_buchstab
    hx hy hyz hu6

example {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    RoughSaiasBuchstabDensityFubini R x y z :=
  roughSaiasBuchstabDensityFubini_of_compact hx hy hyz hu6

example {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    roughSaiasFiniteStieltjesFunctional R
        (roughSaiasStieltjesDickmanProfile x y) =
      roughSaiasFiniteStieltjesFunctional R
          (roughSaiasStieltjesDickmanProfile x z) -
        ∫ s in y..z,
          roughSaiasFiniteStieltjesFunctional R
            (roughSaiasContinuousBuchstabProfile x s) :=
  roughSaiasFiniteStieltjesFunctional_buchstab_unconditional
    hx hy hyz hu6

example {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    roughSaiasLambdaStieltjesWithCutoff R x y =
      roughSaiasLambdaStieltjesWithCutoff R x z -
        ∫ s in y..z,
          roughSaiasLambdaStieltjesWithCutoff R (x / s) s /
            Real.log s :=
  roughSaiasLambdaStieltjesWithCutoff_buchstab_unconditional
    hx hy hyz hu6

end

end Erdos390.WholePaper
