import Erdos390.WholePaper.RoughSaiasStieltjesKernel

open scoped Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full.DickmanBasic

noncomputable section

#check roughSaiasOpenFaceDickmanDerivative
#check roughSaiasOpenFaceDickmanDerivative_of_le_one
#check roughSaiasOpenFaceDickmanDerivative_of_one_lt
#check roughSaiasOpenFaceDickmanDerivative_one
#check roughSaiasOpenFaceDickmanDerivative_eq_roughSaias
#check measurable_roughSaiasOpenFaceDickmanDerivative
#check roughSaiasOpenFaceDickmanDerivative_abs_le_one
#check roughSaiasOpenFace_convolution_eq_rightLimit
#check roughSaiasStieltjesCoordinate
#check roughSaiasStieltjesTest
#check roughSaiasStieltjesTestRightDerivative
#check roughSaiasStieltjesCoordinate_mem
#check continuousOn_roughSaiasStieltjesTest
#check hasDerivWithinAt_roughSaiasStieltjesTest_right
#check roughSaiasStieltjesTest_hasRightDerivOn
#check measurable_roughSaiasStieltjesCoordinate
#check measurable_roughSaiasStieltjesTestRightDerivative
#check roughSaiasStieltjesTestRightDerivative_abs_le
#check integrableOn_roughSaiasStieltjesTestRightDerivative

example {u : ℝ} (hu : u ≠ 1) :
    roughSaiasOpenFaceDickmanDerivative u =
      roughSaiasDickmanDerivative u :=
  roughSaiasOpenFaceDickmanDerivative_eq_roughSaias hu

example (u a b : ℝ) (w : ℝ → ℝ) :
    (∫ v in a..b,
        roughSaiasOpenFaceDickmanDerivative (u - v) * w v) =
      ∫ v in a..b,
        roughSaiasDickmanDerivative (u - v) * w v :=
  roughSaiasOpenFace_convolution_eq_rightLimit u a b w

example {x y t : ℝ} (hy : 1 < y) (ht1 : 1 ≤ t) (htx : t ≤ x)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    HasDerivWithinAt (roughSaiasStieltjesTest x y)
      (roughSaiasStieltjesTestRightDerivative x y t)
      (Set.Ioi t) t :=
  hasDerivWithinAt_roughSaiasStieltjesTest_right hy ht1 htx hu5

example {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    IntegrableOn
      (roughSaiasStieltjesTestRightDerivative (X : ℝ) y)
      (Set.Icc (1 : ℝ) (X : ℝ)) :=
  integrableOn_roughSaiasStieltjesTestRightDerivative hX hy hu5

end

end Erdos390.WholePaper
