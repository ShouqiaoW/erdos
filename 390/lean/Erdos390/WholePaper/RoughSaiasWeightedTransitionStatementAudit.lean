import Erdos390.WholePaper.RoughSaiasWeightedTransition

/-! Literal statement checks for the paper-scale weighted Saias interface. -/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

example (eta : ℕ → ℝ) (A B y : ℕ) :
    roughSaiasPairTransitionBudget eta A B y =
      eta y * ((A : ℝ) + (B : ℝ)) +
        5 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) :=
  rfl

example (eta : ℕ → ℝ) (δ α β L : ℝ)
    (Xplus X Xminus Xhalf y : ℕ) :
    roughPhysicalSaiasTransitionBudget eta δ α β L
        Xplus X Xminus Xhalf y =
      roughSaiasPairTransitionBudget eta X Xplus y +
        |δ * α| * roughSaiasPairTransitionBudget eta Xminus X y +
        |δ * (β / L)| *
          roughSaiasPairTransitionBudget eta Xhalf Xminus y :=
  rfl

example (δ α β L : ℝ) (Xplus X Xminus Xhalf y : ℕ) :
    roughPhysicalDickmanTransitionLedger δ α β L
        Xplus X Xminus Xhalf y =
      (∑ i : Fin 4,
        |roughPhysicalBlockCoefficient δ α β L i| *
          (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) *
            |FriableAsymptotic.dickmanU
                  (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i) y -
              FriableAsymptotic.dickmanU X y|) +
      |∑ i : Fin 4,
        roughPhysicalBlockCoefficient δ α β L i *
          (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ)| :=
  rfl

example (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ A B y : ℕ}
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hA : 0 < A) (hAB : A ≤ B)
    (hlogB : Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |roughFriableResidual B y - roughFriableResidual A y| ≤
      eta y * ((A : ℝ) + (B : ℝ)) +
        5 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) := by
  simpa only [roughSaiasPairTransitionBudget] using
    roughFriableResidual_difference_abs_le_of_saiasEndpointApproximation
      hBV happrox hY hy2 hA hAB hlogB

example (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ : ℕ}
    {δ α β L : ℝ} {Xplus X Xminus Xhalf y : ℕ}
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hhalf : 0 < Xhalf) (hHalfMinus : Xhalf ≤ Xminus)
    (hMinusX : Xminus ≤ X) (hXPlus : X ≤ Xplus)
    (hlogs : ∀ i : Fin 4,
      Real.log
          (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) ≤
        5 * Real.log (y : ℝ)) :
    |roughPhysicalResidualTransition δ α β L
        Xplus X Xminus Xhalf y| ≤
      roughPhysicalSaiasTransitionBudget eta δ α β L
        Xplus X Xminus Xhalf y :=
  roughPhysicalResidualTransition_abs_le_of_saiasEndpointApproximation
    hBV happrox hY hy2 hhalf hHalfMinus hMinusX hXPlus hlogs

example (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ : ℕ}
    {δ α β L : ℝ} {Xplus X Xminus Xhalf y : ℕ}
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hhalf : 0 < Xhalf) (hHalfMinus : Xhalf ≤ Xminus)
    (hMinusX : Xminus ≤ X) (hXPlus : X ≤ Xplus)
    (hlogs : ∀ i : Fin 4,
      Real.log
          (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) ≤
        5 * Real.log (y : ℝ)) :
    |roughPhysicalFriableCombination δ α β L
        Xplus X Xminus Xhalf y| ≤
      roughPhysicalDickmanTransitionLedger δ α β L
          Xplus X Xminus Xhalf y +
        roughPhysicalSaiasTransitionBudget eta δ α β L
          Xplus X Xminus Xhalf y :=
  roughPhysicalFriableCombination_abs_le_of_saiasEndpointApproximation
    hBV happrox hY hy2 hhalf hHalfMinus hMinusX hXPlus hlogs

example (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ : ℕ}
    {δ α β L mainAllowance transitionAllowance : ℝ}
    {Xplus X Xminus Xhalf y : ℕ}
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hhalf : 0 < Xhalf) (hHalfMinus : Xhalf ≤ Xminus)
    (hMinusX : Xminus ≤ X) (hXPlus : X ≤ Xplus)
    (hlogs : ∀ i : Fin 4,
      Real.log
          (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) ≤
        5 * Real.log (y : ℝ))
    (hmain : roughPhysicalDickmanTransitionLedger δ α β L
        Xplus X Xminus Xhalf y ≤ mainAllowance)
    (htransition : roughPhysicalSaiasTransitionBudget eta δ α β L
        Xplus X Xminus Xhalf y ≤ transitionAllowance) :
    |roughPhysicalFriableCombination δ α β L
        Xplus X Xminus Xhalf y| ≤
      mainAllowance + transitionAllowance :=
  roughPhysicalFriableCombination_abs_le_of_saiasPaperScale
    hBV happrox hY hy2 hhalf hHalfMinus hMinusX hXPlus hlogs
      hmain htransition

example (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ : ℕ}
    {δ α β L E : ℝ} {Xplus X Xminus Xhalf y : ℕ}
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hhalf : 0 < Xhalf) (hHalfMinus : Xhalf ≤ Xminus)
    (hMinusX : Xminus ≤ X) (hXPlus : X ≤ Xplus)
    (hlogs : ∀ i : Fin 4,
      Real.log
          (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) ≤
        5 * Real.log (y : ℝ))
    (hmain : roughPhysicalDickmanTransitionLedger δ α β L
        Xplus X Xminus Xhalf y ≤ E)
    (htransition :
      roughSaiasPairTransitionBudget eta X Xplus y +
          |δ * α| * roughSaiasPairTransitionBudget eta Xminus X y +
          |δ * (β / L)| *
            roughSaiasPairTransitionBudget eta Xhalf Xminus y ≤ E) :
    |roughPhysicalFriableCombination δ α β L
        Xplus X Xminus Xhalf y| ≤ 2 * E := by
  apply roughPhysicalFriableCombination_abs_le_two_mul_of_saiasPaperScale
    hBV happrox hY hy2 hhalf hHalfMinus hMinusX hXPlus hlogs hmain
  simpa only [roughPhysicalSaiasTransitionBudget] using htransition

end

end Erdos390.WholePaper
