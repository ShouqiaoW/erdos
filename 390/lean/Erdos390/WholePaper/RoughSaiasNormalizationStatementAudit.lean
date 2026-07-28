import Erdos390.WholePaper.RoughSaiasNormalization

/-! Literal statement checks for the finite Saias normalization module. -/

open scoped Interval ENNReal

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

example (u : ℝ) :
    roughSaiasDickmanDerivative u =
      if u < 1 then 0 else -rho (u - 1) / u := rfl

example (y : ℕ) (u : ℝ) :
    roughSaiasG y u =
      rho u - ∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative (u - v) *
          (Int.fract ((y : ℝ) ^ v) * (y : ℝ) ^ (-v)) := rfl

example {y : ℕ} (hy2 : 2 ≤ y) {u : ℝ} (hu5 : u ≤ 5) :
    roughSaiasG y u = roughSaiasGMoving y u :=
  roughSaiasG_eq_moving hy2 hu5

example {y : ℕ} {u : ℝ} (hu : u ≤ 1) :
    roughSaiasG y u = 1 :=
  roughSaiasG_eq_one_of_le_one hu

example :
    eVariationOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 5) ≤
      ENNReal.ofReal 2 :=
  roughSaiasDickmanDerivative_eVariationOn_le_two

example (hBV : RoughCompactBVTranslationPrinciple)
    {y : ℕ} (hy2 : 2 ≤ y)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 5)
    (hb : b ∈ Icc (0 : ℝ) 5) :
    |roughSaiasGMoving y a - roughSaiasGMoving y b| ≤
      3 * |a - b| :=
  roughSaiasGMoving_lipschitz_three hBV hy2 ha hb

example {y : ℕ} (hy2 : 2 ≤ y) {u : ℝ} (hu5 : u ≤ 5) :
    |roughSaiasG y u - rho u| ≤ 1 / Real.log (y : ℝ) :=
  roughSaiasG_sub_rho_abs_le_inv_log hy2 hu5

example (X y : ℕ) :
    roughFriableResidual X y =
      roughSaiasEndpointError X y + roughSaiasDickmanCorrection X y :=
  roughFriableResidual_eq_saiasError_add_correction X y

example {A B y : ℕ} (hyB : y ≤ B) (hAB : A ≤ B) :
    roughFriablePrimeTransitionLedger A B y =
      |(roughSaiasEndpointError B y - roughSaiasEndpointError A y) +
        (roughSaiasDickmanCorrection B y -
          roughSaiasDickmanCorrection A y)| :=
  roughFriablePrimeTransitionLedger_eq_saias hyB hAB

example (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ A B y : ℕ}
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y) (hyB : y ≤ B)
    (hA : 0 < A) (hAB : A ≤ B)
    (hlogB : Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    roughFriablePrimeTransitionLedger A B y ≤
      eta y * ((A : ℝ) + (B : ℝ)) +
        5 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) :=
  roughFriablePrimeTransitionLedger_le_of_saiasEndpointApproximation
    hBV happrox hY hy2 hyB hA hAB hlogB

/-! ## Supporting public API -/

example (y : ℕ) (v : ℝ) :
    roughSaiasFractionalWeight y v =
      Int.fract ((y : ℝ) ^ v) * (y : ℝ) ^ (-v) := rfl

example (z : ℝ) (y : ℕ) :
    roughSaiasLambdaNormalForm z y =
      z * roughSaiasG y (Real.log z / Real.log (y : ℝ)) - Int.fract z := rfl

example (X y : ℕ) :
    roughSaiasNaturalMain X y =
      (X : ℝ) * roughSaiasG y (FriableAsymptotic.dickmanU X y) := rfl

example {u : ℝ} (hu : u < 1) :
    roughSaiasDickmanDerivative u = 0 :=
  roughSaiasDickmanDerivative_of_lt_one hu

example {u : ℝ} (hu : 1 ≤ u) :
    roughSaiasDickmanDerivative u = -rho (u - 1) / u :=
  roughSaiasDickmanDerivative_of_one_le hu

example : roughSaiasDickmanDerivative 1 = -1 :=
  roughSaiasDickmanDerivative_one

example : Measurable roughSaiasDickmanDerivative :=
  measurable_roughSaiasDickmanDerivative

example {y : ℕ} (hy : 0 < y) :
    Continuous (fun v : ℝ => (y : ℝ) ^ v) :=
  continuous_roughSaiasBaseRpow hy

example {y : ℕ} (hy : 0 < y) :
    Measurable (roughSaiasFractionalWeight y) :=
  measurable_roughSaiasFractionalWeight hy

example {y : ℕ} (hy : 1 ≤ y) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ roughSaiasFractionalWeight y v ∧
      roughSaiasFractionalWeight y v ≤ 1 :=
  roughSaiasFractionalWeight_mem_unitInterval hy hv

example {u : ℝ} (hu5 : u ≤ 5) :
    |roughSaiasDickmanDerivative u| ≤ 1 :=
  roughSaiasDickmanDerivative_abs_le_one hu5

example {u : ℝ} (hu5 : u ≤ 5) :
    IntervalIntegrable
      (fun v : ℝ => roughSaiasDickmanDerivative (u - v))
      volume 0 5 :=
  roughSaiasDickmanDerivative_translate_intervalIntegrable hu5

example {y : ℕ} (hy2 : 2 ≤ y) {u : ℝ} (hu5 : u ≤ 5) :
    IntervalIntegrable
      (fun v : ℝ => roughSaiasDickmanDerivative (u - v) *
        roughSaiasFractionalWeight y v)
      volume 0 5 :=
  roughSaiasIntegrand_intervalIntegrable hy2 hu5

example (X y : ℕ) :
    roughSaiasLambdaNormalForm (X : ℝ) y =
      (X : ℝ) * roughSaiasG y (FriableAsymptotic.dickmanU X y) :=
  roughSaiasLambdaNormalForm_nat X y

example {z : ℝ} {y : ℕ}
    (hu : Real.log z / Real.log (y : ℝ) ≤ 1) :
    roughSaiasLambdaNormalForm z y = ((⌊z⌋ : ℤ) : ℝ) :=
  roughSaiasLambdaNormalForm_eq_floor hu

example {X y : ℕ} (hX : 0 < X) (hy : 1 < y) (hXy : X ≤ y) :
    roughSaiasLambdaNormalForm (X : ℝ) y =
      (FriableAsymptotic.friableCount X y : ℝ) :=
  roughSaiasLambdaNormalForm_eq_friableCount_initial hX hy hXy

example : AntitoneOn rho (Icc (0 : ℝ) 5) :=
  roughRho_antitoneOn_zero_five

example :
    AntitoneOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 1) :=
  roughSaiasDickmanDerivative_antitoneOn_left

example :
    MonotoneOn roughSaiasDickmanDerivative (Icc (1 : ℝ) 5) :=
  roughSaiasDickmanDerivative_monotoneOn_right

example (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => -f x) s = eVariationOn f s :=
  eVariationOn_neg_real f s

example :
    BoundedVariationOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 5) :=
  roughSaiasDickmanDerivative_boundedVariationOn

example (hBV : RoughCompactBVTranslationPrinciple)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 5)
    (hb : b ∈ Icc (0 : ℝ) 5) :
    (∫ v in (0 : ℝ)..5,
      |roughSaiasDickmanDerivative (a - v) -
        roughSaiasDickmanDerivative (b - v)|) ≤
      2 * |a - b| :=
  roughSaiasDickmanDerivative_translation_le_two hBV ha hb

example (hBV : RoughCompactBVTranslationPrinciple)
    {y : ℕ} (hy2 : 2 ≤ y)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 5)
    (hb : b ∈ Icc (0 : ℝ) 5) :
    |roughSaiasG y a - roughSaiasG y b| ≤ 3 * |a - b| :=
  roughSaiasG_lipschitz_three hBV hy2 ha hb

example {y : ℕ} (hy : 0 < y) {v : ℝ} :
    roughSaiasFractionalWeight y v ≤ (y : ℝ) ^ (-v) :=
  roughSaiasFractionalWeight_le_rpow_neg hy

example {y : ℕ} (hy : 1 < y) :
    (∫ v in (0 : ℝ)..5, (y : ℝ) ^ (-v)) =
      (1 - (y : ℝ) ^ (-(5 : ℝ))) / Real.log (y : ℝ) :=
  roughSaias_integral_rpow_neg hy

example {y : ℕ} (hy : 1 < y) :
    (∫ v in (0 : ℝ)..5, (y : ℝ) ^ (-v)) ≤
      1 / Real.log (y : ℝ) :=
  roughSaias_integral_rpow_neg_le_inv_log hy

example (hBV : RoughCompactBVTranslationPrinciple)
    {y : ℕ} (hy2 : 2 ≤ y)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 5)
    (hb : b ∈ Icc (0 : ℝ) 5) :
    |(roughSaiasG y a - rho a) - (roughSaiasG y b - rho b)| ≤
      4 * |a - b| :=
  roughSaiasG_sub_rho_lipschitz_four hBV hy2 ha hb

example (X y : ℕ) :
    roughSaiasNaturalMain X y =
      roughSaiasLambdaNormalForm (X : ℝ) y :=
  roughSaiasNaturalMain_eq_lambdaNormalForm X y

example {X y : ℕ} (hX : 0 < X) (hy : 1 < y) (hXy : X ≤ y) :
    roughSaiasEndpointError X y = 0 :=
  roughSaiasEndpointError_initial hX hy hXy

example (hBV : RoughCompactBVTranslationPrinciple)
    {A B y : ℕ} (hA : 0 < A) (hAB : A ≤ B) (hy2 : 2 ≤ y)
    (hB5 : FriableAsymptotic.dickmanU B y ≤ 5) :
    |roughSaiasDickmanCorrection B y -
        roughSaiasDickmanCorrection A y| ≤
      5 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) :=
  roughSaiasDickmanCorrection_difference_abs_le hBV hA hAB hy2 hB5

example (A B y : ℕ) :
    roughFriableResidual B y - roughFriableResidual A y =
      (roughSaiasEndpointError B y - roughSaiasEndpointError A y) +
        (roughSaiasDickmanCorrection B y -
          roughSaiasDickmanCorrection A y) :=
  roughFriableResidual_difference_eq_saias A B y

end

end Erdos390.WholePaper
