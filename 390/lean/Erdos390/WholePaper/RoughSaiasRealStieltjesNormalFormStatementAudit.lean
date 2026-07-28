import Erdos390.WholePaper.RoughSaiasRealStieltjesNormalForm

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory

noncomputable section

#check roughSaiasRealStieltjesFloorCorrection
#check roughSaiasRealStieltjesSmoothCorrection
#check roughSaiasRealStieltjesFractionalCorrection
#check roughSaiasRealStieltjesFloorCorrection_eq_smooth_sub_fractional
#check roughSaiasRealStieltjesDerivativeFloor_add_density
#check integrableOn_roughSaiasRealStieltjesTestRightDerivative
#check integrableOn_roughSaiasRealStieltjesDerivative_mul_floor
#check integrableOn_roughSaiasRealStieltjesProfile_mul_floorDensity
#check roughSaiasStieltjesAtomPart_ceil_profile_eq_floor_test
#check roughSaiasStieltjesTest_floor_sum_eq_endpoint_sub_integral
#check roughSaiasStieltjesDensityPart_ceil_profile_eq_realCap
#check roughSaiasLambdaStieltjes_eq_floor_add_floorCorrection
#check integrableOn_roughSaiasRealRhoCoordinateRightDerivative
#check integral_roughSaiasRealRhoCoordinateRightDerivative
#check integral_roughSaiasRealStieltjesSmoothCorrection
#check integrableOn_roughSaiasRealStieltjesSmoothCorrection
#check roughSaiasRealStieltjesFractionalCorrection_eq_baseFree_of_ne
#check integrableOn_roughSaiasRealStieltjesFractionalCorrection
#check integral_roughSaiasRealStieltjesFractionalCorrection
#check roughSaiasLambdaStieltjes_eq_normalForm

example {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        roughSaiasStieltjesTest x y (n : ℝ)) =
      (⌊x⌋₊ : ℝ) -
        ∫ t in Set.Ioc (1 : ℝ) x,
          roughSaiasStieltjesTestRightDerivative x y t *
            (((⌊t⌋₊ : ℕ) : ℝ)) :=
  roughSaiasStieltjesTest_floor_sum_eq_endpoint_sub_integral
    hx1 hy hu5

example {x : ℝ} {m : ℕ} (hx1 : 1 ≤ x) (hm2 : 2 ≤ m)
    (hu5 : Real.log x / Real.log (m : ℝ) ≤ 5) :
    roughSaiasLambdaStieltjes x (m : ℝ) =
      roughSaiasLambdaNormalForm x m :=
  roughSaiasLambdaStieltjes_eq_normalForm hx1 hm2 hu5

end

end Erdos390.WholePaper
