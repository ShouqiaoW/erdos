import Mathlib

/-!
# Finite algebra for transition-complete balanced rough blocks

The first analytic estimate after constructing the head-compatible raw
point compares a finite signed collection of smooth-count endpoints.  Its
main term cancels because the signed real lengths balance exactly.  This
file isolates that deterministic layer: exact centering, the finite
Lipschitz ledger, logarithmic displacement scaling, and retention of every
endpoint error.

The final specialization is the literal four-endpoint comparison from the
paper, with relative endpoints
`(1 + κ), 1, (1 - K * κ), 1 / 2`.  No smooth-number asymptotic or
regularity estimate is packaged as data here; those remain explicit
hypotheses for the later analytic module.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## General finite balanced-block algebra -/

/-- Exact removal of a constant profile from a signed block whose first
endpoint moment is zero. -/
theorem roughBalancedBlock_centered_identity
    {ι : Type*} (I : Finset ι)
    (coeff endpoint displacement : ι → ℝ)
    (x u : ℝ) (profile : ℝ → ℝ)
    (hbalance : ∑ i ∈ I, coeff i * endpoint i = 0) :
    ∑ i ∈ I,
        coeff i *
          (endpoint i * x * profile (u + displacement i)) =
      x * ∑ i ∈ I,
        coeff i * endpoint i *
          (profile (u + displacement i) - profile u) := by
  calc
    ∑ i ∈ I,
        coeff i *
          (endpoint i * x * profile (u + displacement i)) =
      ∑ i ∈ I,
        (x * (coeff i * endpoint i *
            (profile (u + displacement i) - profile u)) +
          (x * profile u) * (coeff i * endpoint i)) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
    _ = x * ∑ i ∈ I,
          coeff i * endpoint i *
            (profile (u + displacement i) - profile u) +
        (x * profile u) * ∑ i ∈ I, coeff i * endpoint i := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = x * ∑ i ∈ I,
          coeff i * endpoint i *
            (profile (u + displacement i) - profile u) := by
      rw [hbalance, mul_zero, add_zero]

/-- A pointwise Lipschitz estimate bounds the centered finite main term by
the exact weighted displacement moment. -/
theorem roughBalancedBlock_model_abs_le
    {ι : Type*} (I : Finset ι)
    (coeff endpoint displacement : ι → ℝ)
    (x u C : ℝ) (profile : ℝ → ℝ)
    (hx : 0 ≤ x)
    (hendpoint : ∀ i ∈ I, 0 ≤ endpoint i)
    (_hC : 0 ≤ C)
    (hbalance : ∑ i ∈ I, coeff i * endpoint i = 0)
    (hprofile : ∀ i ∈ I,
      |profile (u + displacement i) - profile u| ≤
        C * |displacement i|) :
    |∑ i ∈ I,
        coeff i *
          (endpoint i * x * profile (u + displacement i))| ≤
      x * C * ∑ i ∈ I,
        |coeff i| * endpoint i * |displacement i| := by
  rw [roughBalancedBlock_centered_identity I coeff endpoint
    displacement x u profile hbalance, abs_mul, abs_of_nonneg hx]
  calc
    x * |∑ i ∈ I,
        coeff i * endpoint i *
          (profile (u + displacement i) - profile u)| ≤
      x * ∑ i ∈ I,
        |coeff i * endpoint i *
          (profile (u + displacement i) - profile u)| := by
      exact mul_le_mul_of_nonneg_left
        (Finset.abs_sum_le_sum_abs _ _) hx
    _ ≤ x * ∑ i ∈ I,
        |coeff i| * endpoint i * (C * |displacement i|) := by
      apply mul_le_mul_of_nonneg_left _ hx
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_mul, abs_of_nonneg (hendpoint i hi)]
      exact mul_le_mul_of_nonneg_left (hprofile i hi)
        (mul_nonneg (abs_nonneg _) (hendpoint i hi))
    _ = x * C * ∑ i ∈ I,
        |coeff i| * endpoint i * |displacement i| := by
      have hsum :
          (∑ i ∈ I,
              |coeff i| * endpoint i * (C * |displacement i|)) =
            C * ∑ i ∈ I,
              |coeff i| * endpoint i * |displacement i| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      rw [hsum]
      ring

/-- Dividing the logarithmic endpoint shifts by `logY` pulls out exactly
one factor `1 / logY` from the absolute displacement moment. -/
theorem roughBalancedBlock_logDisplacementMoment
    {ι : Type*} (I : Finset ι)
    (coeff endpoint : ι → ℝ) (logY : ℝ)
    (hlogY : 0 < logY) :
    ∑ i ∈ I,
        |coeff i| * endpoint i *
          |Real.log (endpoint i) / logY| =
      (1 / logY) * ∑ i ∈ I,
        |coeff i| * endpoint i * |Real.log (endpoint i)| := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [abs_div, abs_of_pos hlogY]
  ring

/-- Logarithmic version of the centered main-term estimate. -/
theorem roughBalancedBlock_logModel_abs_le
    {ι : Type*} (I : Finset ι)
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
        |coeff i| * endpoint i * |Real.log (endpoint i)| := by
  have hmodel := roughBalancedBlock_model_abs_le I coeff endpoint
    (fun i ↦ Real.log (endpoint i) / logY) x u C profile hx
    hendpoint hC hbalance hprofile
  rw [roughBalancedBlock_logDisplacementMoment I coeff endpoint
    logY hlogY] at hmodel
  calc
    |∑ i ∈ I,
        coeff i * (endpoint i * x *
          profile (u + Real.log (endpoint i) / logY))| ≤
      x * C * ((1 / logY) * ∑ i ∈ I,
        |coeff i| * endpoint i * |Real.log (endpoint i)|) := hmodel
    _ = x * C / logY * ∑ i ∈ I,
        |coeff i| * endpoint i * |Real.log (endpoint i)| := by ring

/-- Transition-complete bound retaining every pointwise endpoint error.
The first term is the balanced main-term ledger; the second is the literal
sum of the endpoint approximation errors. -/
theorem roughBalancedBlock_observed_abs_le
    {ι : Type*} (I : Finset ι)
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
        ∑ i ∈ I, |coeff i| * error i := by
  let model : ι → ℝ := fun i ↦
    endpoint i * x *
      profile (u + Real.log (endpoint i) / logY)
  have hsplit :
      (∑ i ∈ I, coeff i * observed i) =
        (∑ i ∈ I, coeff i * (observed i - model i)) +
          ∑ i ∈ I, coeff i * model i := by
    calc
      ∑ i ∈ I, coeff i * observed i =
          ∑ i ∈ I,
            (coeff i * (observed i - model i) +
              coeff i * model i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = (∑ i ∈ I, coeff i * (observed i - model i)) +
          ∑ i ∈ I, coeff i * model i := by
        rw [Finset.sum_add_distrib]
  have herror :
      |∑ i ∈ I, coeff i * (observed i - model i)| ≤
        ∑ i ∈ I, |coeff i| * error i := by
    calc
      |∑ i ∈ I, coeff i * (observed i - model i)| ≤
          ∑ i ∈ I, |coeff i * (observed i - model i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ I, |coeff i| * error i := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [model] using happrox i hi) (abs_nonneg _)
  have hmodel :
      |∑ i ∈ I, coeff i * model i| ≤
        x * C / logY * ∑ i ∈ I,
          |coeff i| * endpoint i * |Real.log (endpoint i)| := by
    simpa only [model] using
      roughBalancedBlock_logModel_abs_le I coeff endpoint x u C logY
        profile hx hendpoint hC hlogY hbalance hprofile
  rw [hsplit]
  calc
      |(∑ i ∈ I, coeff i * (observed i - model i)) +
        ∑ i ∈ I, coeff i * model i| ≤
      |∑ i ∈ I, coeff i * (observed i - model i)| +
        |∑ i ∈ I, coeff i * model i| := abs_add_le _ _
    _ ≤ (∑ i ∈ I, |coeff i| * error i) +
        x * C / logY * ∑ i ∈ I,
          |coeff i| * endpoint i * |Real.log (endpoint i)| :=
      add_le_add herror hmodel
    _ = x * C / logY * ∑ i ∈ I,
          |coeff i| * endpoint i * |Real.log (endpoint i)| +
        ∑ i ∈ I, |coeff i| * error i := add_comm _ _

/-! ## The literal four physical endpoints -/

/-- Relative endpoints in the unscaled upper-block versus physical-block
comparison. -/
def roughPhysicalBlockEndpoint (K κ : ℝ) : Fin 4 → ℝ :=
  ![1 + κ, 1, 1 - K * κ, 1 / 2]

/-- Coefficients obtained by expanding
`upper block - δ * physical block` and combining equal endpoints. -/
def roughPhysicalBlockCoefficient
    (δ α β L : ℝ) : Fin 4 → ℝ :=
  ![1, -(1 + δ * α), δ * (α - β / L), δ * (β / L)]

/-- The scaled form of the paper's literal definition of `α`.  It is
chosen so that the physical lower blocks and the upper block have exactly
the same real length after the head-density factor `δ` is applied. -/
def roughPhysicalBalancedAlpha
    (δ β L K κ : ℝ) : ℝ :=
  (κ / δ - (β / L) * (1 / 2 - K * κ)) / (K * κ)

/-- The defining quotient for `roughPhysicalBalancedAlpha` satisfies the
paper's normalization as an exact identity, not asymptotically. -/
theorem roughPhysicalBalancedAlpha_normalization
    {δ β L K κ : ℝ} (hδ : δ ≠ 0) (hKκ : K * κ ≠ 0) :
    δ * (roughPhysicalBalancedAlpha δ β L K κ * (K * κ) +
      (β / L) * (1 / 2 - K * κ)) = κ := by
  rw [roughPhysicalBalancedAlpha, div_mul_cancel₀ _ hKκ,
    sub_add_cancel]
  exact mul_div_cancel₀ κ hδ

/-- The exact real-length normalization from the head-compatible raw point
is precisely the vanishing first moment of the four physical endpoints. -/
theorem roughPhysicalBlock_firstMoment_eq_zero
    (δ α β L K κ : ℝ)
    (hnormalization :
      δ * (α * (K * κ) + (β / L) * (1 / 2 - K * κ)) = κ) :
    ∑ i : Fin 4,
      roughPhysicalBlockCoefficient δ α β L i *
        roughPhysicalBlockEndpoint K κ i = 0 := by
  rw [Fin.sum_univ_four]
  change
    1 * (1 + κ) + (-(1 + δ * α)) * 1 +
      δ * (α - β / L) * (1 - K * κ) +
        δ * (β / L) * (1 / 2) = 0
  calc
    1 * (1 + κ) + (-(1 + δ * α)) * 1 +
        δ * (α - β / L) * (1 - K * κ) +
          δ * (β / L) * (1 / 2) =
      κ - δ *
        (α * (K * κ) + (β / L) * (1 / 2 - K * κ)) := by
      ring
    _ = 0 := by rw [hnormalization]; ring

/-- With the literal balanced choice of `α`, the four-endpoint first
moment vanishes without a remaining normalization hypothesis. -/
theorem roughPhysicalBalancedAlpha_firstMoment_eq_zero
    {δ β L K κ : ℝ} (hδ : δ ≠ 0) (hKκ : K * κ ≠ 0) :
    ∑ i : Fin 4,
      roughPhysicalBlockCoefficient δ
          (roughPhysicalBalancedAlpha δ β L K κ) β L i *
        roughPhysicalBlockEndpoint K κ i = 0 :=
  roughPhysicalBlock_firstMoment_eq_zero δ
    (roughPhysicalBalancedAlpha δ β L K κ) β L K κ
      (roughPhysicalBalancedAlpha_normalization hδ hKκ)

/-- The paper parameter inequalities make all four relative physical
endpoints nonnegative. -/
theorem roughPhysicalBlockEndpoint_nonneg
    {K κ : ℝ} (hκ : 0 ≤ κ) (hKκ : K * κ ≤ 1) :
    ∀ i : Fin 4, 0 ≤ roughPhysicalBlockEndpoint K κ i := by
  intro i
  fin_cases i <;> simp [roughPhysicalBlockEndpoint] <;> linarith

/-- The transition-complete finite estimate specialized to the paper's
four physical endpoints.  It exposes exactly the still-missing analytic
inputs: profile regularity and one approximation bound at each endpoint. -/
theorem roughPhysicalBlock_transitionComplete_abs_le
    (δ α β L K κ x u C logY : ℝ)
    (profile : ℝ → ℝ) (observed error : Fin 4 → ℝ)
    (hx : 0 ≤ x) (hκ : 0 ≤ κ) (hKκ : K * κ ≤ 1)
    (hC : 0 ≤ C) (hlogY : 0 < logY)
    (hnormalization :
      δ * (α * (K * κ) + (β / L) * (1 / 2 - K * κ)) = κ)
    (hprofile : ∀ i : Fin 4,
      |profile (u +
          Real.log (roughPhysicalBlockEndpoint K κ i) / logY) -
          profile u| ≤
        C * |Real.log (roughPhysicalBlockEndpoint K κ i) / logY|)
    (happrox : ∀ i : Fin 4,
      |observed i - roughPhysicalBlockEndpoint K κ i * x *
        profile (u +
          Real.log (roughPhysicalBlockEndpoint K κ i) / logY)| ≤
        error i) :
    |∑ i : Fin 4,
        roughPhysicalBlockCoefficient δ α β L i * observed i| ≤
      x * C / logY * ∑ i : Fin 4,
          |roughPhysicalBlockCoefficient δ α β L i| *
            roughPhysicalBlockEndpoint K κ i *
              |Real.log (roughPhysicalBlockEndpoint K κ i)| +
        ∑ i : Fin 4,
          |roughPhysicalBlockCoefficient δ α β L i| * error i := by
  apply roughBalancedBlock_observed_abs_le
    (I := Finset.univ)
    (coeff := roughPhysicalBlockCoefficient δ α β L)
    (endpoint := roughPhysicalBlockEndpoint K κ)
    (observed := observed) (error := error)
    (x := x) (u := u) (C := C) (logY := logY) (profile := profile)
  · exact hx
  · intro i _hi
    exact roughPhysicalBlockEndpoint_nonneg hκ hKκ i
  · exact hC
  · exact hlogY
  · exact roughPhysicalBlock_firstMoment_eq_zero δ α β L K κ
      hnormalization
  · intro i _hi
    exact hprofile i
  · intro i _hi
    exact happrox i

end

end Erdos390.WholePaper
