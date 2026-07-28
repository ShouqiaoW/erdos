import Erdos390.WholePaper.RoughSaiasStieltjesNormalForm

namespace Erdos390.WholePaper

#check roughSaiasStieltjesFloorCorrection
#check roughSaiasStieltjesSmoothCorrection
#check roughSaiasStieltjesFractionalCorrection
#check roughSaiasNatFloor_cast_eq_sub_fract
#check roughSaiasStieltjesFloorCorrection_eq_smooth_sub_fractional
#check roughSaiasStieltjesDerivativeFloor_add_density
#check roughSaiasPositiveIncrement_prefix
#check integrableOn_roughSaiasStieltjesDerivative_mul_floor
#check integrableOn_roughSaiasStieltjesProfile_mul_floorDensity
#check roughSaiasLambdaStieltjesWithCutoff_nat_eq_add_floorCorrection
#check hasDerivWithinAt_roughSaiasRhoCoordinate_right
#check continuousOn_roughSaiasRhoCoordinate
#check integrableOn_roughSaiasRhoCoordinateRightDerivative
#check integral_roughSaiasRhoCoordinateRightDerivative
#check integral_roughSaiasStieltjesSmoothCorrection
#check integrableOn_roughSaiasStieltjesSmoothCorrection
#check roughSaias_natCast_le_rpow_five
#check roughSaiasBaseFreeFractionalIntegral_eq_natCap
#check roughSaiasStieltjesFractionalCorrection_eq_baseFree_of_ne
#check integrableOn_roughSaiasStieltjesFractionalCorrection
#check integral_roughSaiasStieltjesFractionalCorrection
#check roughSaiasLambdaStieltjesWithCutoff_nat_eq_normalForm
#check roughSaiasLambdaStieltjes_nat_eq_normalForm

example {X Y : ℕ} (hX : 1 ≤ X) (hY : 2 ≤ Y)
    (hu5 : Real.log (X : ℝ) / Real.log (Y : ℝ) ≤ 5) :
    roughSaiasLambdaStieltjesWithCutoff X (X : ℝ) (Y : ℝ) =
      roughSaiasLambdaNormalForm (X : ℝ) Y :=
  roughSaiasLambdaStieltjesWithCutoff_nat_eq_normalForm hX hY hu5

example {X Y : ℕ} (hX : 1 ≤ X) (hY : 2 ≤ Y)
    (hu5 : Real.log (X : ℝ) / Real.log (Y : ℝ) ≤ 5) :
    roughSaiasLambdaStieltjes (X : ℝ) (Y : ℝ) =
      roughSaiasLambdaNormalForm (X : ℝ) Y :=
  roughSaiasLambdaStieltjes_nat_eq_normalForm hX hY hu5

example {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    (∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
        roughSaiasStieltjesSmoothCorrection X y t) =
      (X : ℝ) *
        (Erdos390.Full.DickmanBasic.rho
          (Real.log (X : ℝ) / Real.log y) - 1) :=
  integral_roughSaiasStieltjesSmoothCorrection hX hy hu5

end Erdos390.WholePaper
