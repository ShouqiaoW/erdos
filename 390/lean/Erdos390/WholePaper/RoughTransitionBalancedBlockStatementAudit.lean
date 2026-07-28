import Erdos390.WholePaper.RoughTransitionBalancedBlock

/-! # Expanded statement audit for transition-complete balanced blocks -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example {ι : Type*} (I : Finset ι)
    (coeff endpoint displacement : ι → ℝ)
    (x u : ℝ) (profile : ℝ → ℝ)
    (hbalance : ∑ i ∈ I, coeff i * endpoint i = 0) :
    ∑ i ∈ I,
        coeff i *
          (endpoint i * x * profile (u + displacement i)) =
      x * ∑ i ∈ I,
        coeff i * endpoint i *
          (profile (u + displacement i) - profile u) :=
  roughBalancedBlock_centered_identity I coeff endpoint displacement
    x u profile hbalance

example {ι : Type*} (I : Finset ι)
    (coeff endpoint displacement : ι → ℝ)
    (x u C : ℝ) (profile : ℝ → ℝ)
    (hx : 0 ≤ x)
    (hendpoint : ∀ i ∈ I, 0 ≤ endpoint i)
    (hC : 0 ≤ C)
    (hbalance : ∑ i ∈ I, coeff i * endpoint i = 0)
    (hprofile : ∀ i ∈ I,
      |profile (u + displacement i) - profile u| ≤
        C * |displacement i|) :
    |∑ i ∈ I,
        coeff i *
          (endpoint i * x * profile (u + displacement i))| ≤
      x * C * ∑ i ∈ I,
        |coeff i| * endpoint i * |displacement i| :=
  roughBalancedBlock_model_abs_le I coeff endpoint displacement
    x u C profile hx hendpoint hC hbalance hprofile

example {ι : Type*} (I : Finset ι)
    (coeff endpoint : ι → ℝ) (logY : ℝ)
    (hlogY : 0 < logY) :
    ∑ i ∈ I,
        |coeff i| * endpoint i *
          |Real.log (endpoint i) / logY| =
      (1 / logY) * ∑ i ∈ I,
        |coeff i| * endpoint i * |Real.log (endpoint i)| :=
  roughBalancedBlock_logDisplacementMoment I coeff endpoint logY hlogY

example {ι : Type*} (I : Finset ι)
    (coeff endpoint : ι → ℝ)
    (x u C logY : ℝ) (profile : ℝ → ℝ)
    (hx : 0 ≤ x)
    (hendpoint : ∀ i ∈ I, 0 ≤ endpoint i)
    (hC : 0 ≤ C) (hlogY : 0 < logY)
    (hbalance : ∑ i ∈ I, coeff i * endpoint i = 0)
    (hprofile : ∀ i ∈ I,
      |profile (u + Real.log (endpoint i) / logY) - profile u| ≤
        C * |Real.log (endpoint i) / logY|) :
    |∑ i ∈ I,
        coeff i * (endpoint i * x *
          profile (u + Real.log (endpoint i) / logY))| ≤
      x * C / logY * ∑ i ∈ I,
        |coeff i| * endpoint i * |Real.log (endpoint i)| :=
  roughBalancedBlock_logModel_abs_le I coeff endpoint x u C logY
    profile hx hendpoint hC hlogY hbalance hprofile

example {ι : Type*} (I : Finset ι)
    (coeff endpoint observed error : ι → ℝ)
    (x u C logY : ℝ) (profile : ℝ → ℝ)
    (hx : 0 ≤ x)
    (hendpoint : ∀ i ∈ I, 0 ≤ endpoint i)
    (hC : 0 ≤ C) (hlogY : 0 < logY)
    (hbalance : ∑ i ∈ I, coeff i * endpoint i = 0)
    (hprofile : ∀ i ∈ I,
      |profile (u + Real.log (endpoint i) / logY) - profile u| ≤
        C * |Real.log (endpoint i) / logY|)
    (happrox : ∀ i ∈ I,
      |observed i - endpoint i * x *
        profile (u + Real.log (endpoint i) / logY)| ≤ error i) :
    |∑ i ∈ I, coeff i * observed i| ≤
      x * C / logY * ∑ i ∈ I,
          |coeff i| * endpoint i * |Real.log (endpoint i)| +
        ∑ i ∈ I, |coeff i| * error i :=
  roughBalancedBlock_observed_abs_le I coeff endpoint observed error
    x u C logY profile hx hendpoint hC hlogY hbalance hprofile happrox

example (δ α β L K κ : ℝ)
    (hnormalization :
      δ * (α * (K * κ) + (β / L) * (1 / 2 - K * κ)) = κ) :
    ∑ i : Fin 4,
      (![1, -(1 + δ * α), δ * (α - β / L), δ * (β / L)] i) *
        (![1 + κ, 1, 1 - K * κ, 1 / 2] i) = 0 := by
  simpa only [roughPhysicalBlockCoefficient,
    roughPhysicalBlockEndpoint] using
    roughPhysicalBlock_firstMoment_eq_zero δ α β L K κ
      hnormalization

example {δ β L K κ : ℝ} (hδ : δ ≠ 0) (hKκ : K * κ ≠ 0) :
    δ *
      (((κ / δ - (β / L) * (1 / 2 - K * κ)) / (K * κ)) *
          (K * κ) + (β / L) * (1 / 2 - K * κ)) = κ ∧
      ∑ i : Fin 4,
        roughPhysicalBlockCoefficient δ
            ((κ / δ - (β / L) * (1 / 2 - K * κ)) / (K * κ)) β L i *
          roughPhysicalBlockEndpoint K κ i = 0 := by
  constructor
  · simpa only [roughPhysicalBalancedAlpha] using
      roughPhysicalBalancedAlpha_normalization hδ hKκ
  · simpa only [roughPhysicalBalancedAlpha] using
      roughPhysicalBalancedAlpha_firstMoment_eq_zero hδ hKκ

example {K κ : ℝ} (hκ : 0 ≤ κ) (hKκ : K * κ ≤ 1) :
    ∀ i : Fin 4, 0 ≤ roughPhysicalBlockEndpoint K κ i :=
  roughPhysicalBlockEndpoint_nonneg hκ hKκ

example (δ α β L K κ x u C logY : ℝ)
    (profile : ℝ → ℝ) (observed error : Fin 4 → ℝ)
    (hx : 0 ≤ x) (hκ : 0 ≤ κ) (hKκ : K * κ ≤ 1)
    (hC : 0 ≤ C) (hlogY : 0 < logY)
    (hnormalization :
      δ * (α * (K * κ) + (β / L) * (1 / 2 - K * κ)) = κ)
    (hprofile : ∀ i : Fin 4,
      |profile (u + Real.log
          (![1 + κ, 1, 1 - K * κ, 1 / 2] i) / logY) - profile u| ≤
        C * |Real.log
          (![1 + κ, 1, 1 - K * κ, 1 / 2] i) / logY|)
    (happrox : ∀ i : Fin 4,
      |observed i - (![1 + κ, 1, 1 - K * κ, 1 / 2] i) * x *
        profile (u + Real.log
          (![1 + κ, 1, 1 - K * κ, 1 / 2] i) / logY)| ≤ error i) :
    |∑ i : Fin 4,
        (![1, -(1 + δ * α), δ * (α - β / L), δ * (β / L)] i) *
          observed i| ≤
      x * C / logY * ∑ i : Fin 4,
        |![1, -(1 + δ * α), δ * (α - β / L), δ * (β / L)] i| *
          (![1 + κ, 1, 1 - K * κ, 1 / 2] i) *
            |Real.log (![1 + κ, 1, 1 - K * κ, 1 / 2] i)| +
        ∑ i : Fin 4,
          |![1, -(1 + δ * α), δ * (α - β / L), δ * (β / L)] i| *
            error i := by
  simpa only [roughPhysicalBlockCoefficient,
    roughPhysicalBlockEndpoint] using
    roughPhysicalBlock_transitionComplete_abs_le
      δ α β L K κ x u C logY profile observed error hx hκ hKκ hC
        hlogY hnormalization hprofile happrox

end

end Erdos390.WholePaper
