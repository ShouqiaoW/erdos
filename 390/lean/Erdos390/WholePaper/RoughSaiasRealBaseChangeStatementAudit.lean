import Erdos390.WholePaper.RoughSaiasRealBaseChange

open scoped Interval

namespace Erdos390.WholePaper

open MeasureTheory
open Erdos390.Full

noncomputable section

#check roughSaiasRealBaseFreeFractionalKernel
#check roughSaiasRealBaseFreeFractionalIntegral
#check roughSaiasRealBaseFreeFractionalKernel_rpow_mul_jacobian
#check roughSaiasFractionalIntegral_eq_realBaseFree
#check roughSaiasRealBaseFreeFractionalKernel_intervalIntegrable
#check roughSaiasRealBaseFreeFractionalKernel_eq_zero_of_div_lt
#check roughSaiasReal_le_rpow_five
#check roughSaiasRealBaseFreeFractionalIntegral_eq_realCap
#check roughSaiasG_at_realEndpoint_eq_realBaseFree

example {x : ℝ} {m : ℕ} (hm2 : 2 ≤ m) :
    (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative
            (Real.log x / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v) =
      roughSaiasRealBaseFreeFractionalIntegral x m :=
  roughSaiasFractionalIntegral_eq_realBaseFree hm2

example {x : ℝ} {m : ℕ} (hx1 : 1 ≤ x) (hm2 : 2 ≤ m)
    (hu5 : Real.log x / Real.log (m : ℝ) ≤ 5) :
    roughSaiasRealBaseFreeFractionalIntegral x m =
      ∫ t in (1 : ℝ)..x,
        roughSaiasRealBaseFreeFractionalKernel x m t :=
  roughSaiasRealBaseFreeFractionalIntegral_eq_realCap hx1 hm2 hu5

example {x : ℝ} {m : ℕ} (hm2 : 2 ≤ m) :
    roughSaiasG m (Real.log x / Real.log (m : ℝ)) =
      Erdos390.Full.DickmanBasic.rho
          (Real.log x / Real.log (m : ℝ)) -
        roughSaiasRealBaseFreeFractionalIntegral x m :=
  roughSaiasG_at_realEndpoint_eq_realBaseFree hm2

end

end Erdos390.WholePaper
