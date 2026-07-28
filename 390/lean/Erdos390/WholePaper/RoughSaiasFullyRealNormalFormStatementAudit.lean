import Erdos390.WholePaper.RoughSaiasFullyRealNormalForm

open scoped Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full

noncomputable section

#check roughSaiasFullyRealFractionalWeight
#check roughSaiasFullyRealG
#check roughSaiasFullyRealLambdaNormalForm
#check roughSaiasFullyRealBaseFreeFractionalKernel
#check roughSaiasFullyRealBaseFreeFractionalIntegral
#check measurable_roughSaiasFullyRealFractionalWeight
#check roughSaiasFullyRealFractionalWeight_mem_unitInterval
#check roughSaiasFullyRealIntegrand_intervalIntegrable
#check roughSaiasFullyRealBaseFreeKernel_rpow_mul_jacobian
#check roughSaiasFullyRealFractionalIntegral_eq_baseFree
#check roughSaiasFullyRealBaseFreeKernel_intervalIntegrable
#check roughSaiasFullyRealBaseFreeKernel_eq_zero_of_div_lt
#check roughSaiasFullyReal_le_rpow_five
#check roughSaiasFullyRealBaseFreeIntegral_eq_realCap
#check roughSaiasFullyRealG_eq_rho_sub_baseFree
#check roughSaiasFullyRealG_eq_one_of_le_one
#check roughSaiasFullyRealG_lipschitz_three
#check roughSaiasFullyRealG_abs_le_sixteen
#check roughSaiasFullyRealLambdaNormalForm_eq_floor_of_le_one
#check roughSaiasFullyRealFractionalWeight_nat
#check roughSaiasFullyRealG_nat
#check roughSaiasFullyRealLambdaNormalForm_nat
#check roughSaiasFullyRealBaseFreeKernel_nat
#check roughSaiasRealStieltjesFractionalCorrection_eq_fullyRealBaseFree_of_ne
#check integrableOn_roughSaiasFullyRealStieltjesFractionalCorrection
#check integral_roughSaiasFullyRealStieltjesFractionalCorrection
#check roughSaiasLambdaStieltjes_eq_fullyRealNormalForm
#check roughSaiasLambdaStieltjes_eq_normalForm_via_fullyReal

example {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    roughSaiasLambdaStieltjes x y =
      roughSaiasFullyRealLambdaNormalForm x y :=
  roughSaiasLambdaStieltjes_eq_fullyRealNormalForm hx1 hy hu5

example (x : ℝ) (m : ℕ) :
    roughSaiasFullyRealLambdaNormalForm x (m : ℝ) =
      roughSaiasLambdaNormalForm x m :=
  roughSaiasFullyRealLambdaNormalForm_nat x m

end

end Erdos390.WholePaper
