import Erdos390.WholePaper.RoughCompactBVTranslation

/-! Literal statement checks for the closed compact-BV translation seam. -/

open scoped ENNReal Interval

namespace Erdos390.WholePaper

open Set MeasureTheory

noncomputable section

example : RoughCompactBVTranslationPrinciple :=
  roughCompactBVTranslationPrinciple

example {f : ℝ → ℝ}
    (hfvar : eVariationOn f (Icc (-5 : ℝ) 5) ≤ ENNReal.ofReal 2)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 5)
    (hb : b ∈ Icc (0 : ℝ) 5) (hab : a ≤ b) :
    (∫ v in (0 : ℝ)..5, |f (a - v) - f (b - v)|) ≤
      2 * (b - a) :=
  roughCompactBV_translation_le_of_le hfvar ha hb hab

example {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 5)
    (hb : b ∈ Icc (0 : ℝ) 5) :
    (∫ v in (0 : ℝ)..5,
      |roughSaiasDickmanDerivative (a - v) -
        roughSaiasDickmanDerivative (b - v)|) ≤
      2 * |a - b| :=
  roughSaiasDickmanDerivative_translation_le_two_unconditional ha hb

example {y : ℕ} (hy2 : 2 ≤ y)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 5)
    (hb : b ∈ Icc (0 : ℝ) 5) :
    |roughSaiasG y a - roughSaiasG y b| ≤ 3 * |a - b| :=
  roughSaiasG_lipschitz_three_unconditional hy2 ha hb

example {y : ℕ} (hy2 : 2 ≤ y)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 5)
    (hb : b ∈ Icc (0 : ℝ) 5) :
    |(roughSaiasG y a - Erdos390.Full.DickmanBasic.rho a) -
        (roughSaiasG y b - Erdos390.Full.DickmanBasic.rho b)| ≤
      4 * |a - b| :=
  roughSaiasG_sub_rho_lipschitz_four_unconditional hy2 ha hb

example {A B y : ℕ} (hA : 0 < A) (hAB : A ≤ B) (hy2 : 2 ≤ y)
    (hB5 : Erdos390.Full.FriableAsymptotic.dickmanU B y ≤ 5) :
    |roughSaiasDickmanCorrection B y -
        roughSaiasDickmanCorrection A y| ≤
      5 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) :=
  roughSaiasDickmanCorrection_difference_abs_le_unconditional
    hA hAB hy2 hB5

end

end Erdos390.WholePaper
