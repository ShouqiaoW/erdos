import Erdos390.WholePaper.RoughSaiasUnconditionalDownstream

/-!
Statement audit for the unconditional weighted, canonical-row, and forward
selector-handoff wrappers.  In particular, no example below takes a
`RoughCompactBVTranslationPrinciple` argument.  Every example still takes an
arbitrary endpoint rate and its endpoint proof explicitly; none defaults to
the closed but paper-insufficient inverse-log witness.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

example {eta : ℕ → ℝ} {Y₀ : ℕ}
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
    (htransition : roughPhysicalSaiasTransitionBudget eta δ α β L
        Xplus X Xminus Xhalf y ≤ E) :
    |roughPhysicalFriableCombination δ α β L
        Xplus X Xminus Xhalf y| ≤ 2 * E :=
  roughPhysicalFriableCombination_abs_le_two_mul_of_saiasPaperScale_unconditional
    happrox hY hy2 hhalf hHalfMinus hMinusX hXPlus hlogs
      hmain htransition

example {eta : ℕ → ℝ} {Y₀ W n h K y : ℕ}
    {α β L E : ℝ}
    (hWy : W ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hrowN : row.1 ≤ n) (hKh : K * h ≤ n)
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hlogs : ∀ i : Fin 4,
      Real.log (roughPhysicalNatEndpoint
          ((2 * n + h) / row.1) ((2 * n) / row.1)
          ((2 * n - K * h) / row.1) (n / row.1) i : ℝ) ≤
        5 * Real.log (y : ℝ))
    (hmain : roughPhysicalDickmanTransitionLedger
        (roughHeadDensity W) α β L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤ E)
    (htransition : roughPhysicalSaiasTransitionBudget eta
        (roughHeadDensity W) α β L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤ E)
    (hhead : roughCanonicalFixedHeadShiftLedger
        W n h K y α β L row ≤ E) :
    |roughCanonicalRawRowQuotaError W n h K y α β L row| ≤ 3 * E :=
  roughCanonicalRawRowQuotaError_abs_le_three_mul_paperAllowance_unconditional
    hWy row hrowN hKh happrox hY hy2 hlogs hmain htransition hhead

end

end Erdos390.WholePaper

#check Erdos390.WholePaper.roughFriableResidual_difference_abs_le_of_saiasEndpointApproximation_unconditional
#check Erdos390.WholePaper.roughPhysicalResidualTransition_abs_le_of_saiasEndpointApproximation_unconditional
#check Erdos390.WholePaper.roughPhysicalFriableCombination_abs_le_of_saiasEndpointApproximation_unconditional
#check Erdos390.WholePaper.roughPhysicalFriableCombination_abs_le_of_saiasPaperScale_unconditional
#check Erdos390.WholePaper.roughPhysicalFriableCombination_abs_le_two_mul_of_saiasPaperScale_unconditional
#check Erdos390.WholePaper.roughCanonicalRawRowQuotaError_abs_le_of_saiasPaperScale_unconditional
#check Erdos390.WholePaper.roughCanonicalRawRowQuotaError_abs_le_of_literalSaiasPaperScale_unconditional
#check Erdos390.WholePaper.roughCanonicalRawRowQuotaError_abs_le_of_literalSaiasAndHeadLedger_unconditional
#check Erdos390.WholePaper.roughCanonicalRawRowQuotaError_abs_le_three_mul_paperAllowance_unconditional
#check Erdos390.WholePaper.bankPaper_activeRoughRowQuota_and_isAdmissibleEndpoint_of_canonicalSaiasHandoff_unconditional
