import Erdos390.WholePaper.BankPaperFourFiveLastPrimeContinuumDecomposition
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Exact moving-simplex to fixed-simplex identification

For `T = u - (m+1) > 0`, the affine map

`s_i = 1 + T z_i`

maps the closed unit `m`-simplex bijectively onto the logarithmic moving
simplex.  Its Jacobian is `T^m`, and the transformed density is exactly
`fourFiveFixedSimplexIntegrand`.  This discharges the third residual in the
continuum bridge by equality, not by an assumed estimate.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-- Coordinatewise affine map from the fixed simplex to the logarithmic
moving simplex. -/
def fourFiveSimplexAffineMap
    (m : Nat) (T : Real) (z : Fin m -> Real) : Fin m -> Real :=
  (1 : Fin m -> Real) + T • z

/-- Its constant Fréchet derivative. -/
def fourFiveSimplexAffineDerivative
    (m : Nat) (T : Real) :
    (Fin m -> Real) →L[Real] (Fin m -> Real) :=
  T • ContinuousLinearMap.id Real (Fin m -> Real)

theorem hasFDerivAt_fourFiveSimplexAffineMap
    (m : Nat) (T : Real) (z : Fin m -> Real) :
    HasFDerivAt (fourFiveSimplexAffineMap m T)
      (fourFiveSimplexAffineDerivative m T) z := by
  unfold fourFiveSimplexAffineMap fourFiveSimplexAffineDerivative
  simpa using
    ((hasFDerivAt_id (𝕜 := Real) z).const_smul T).const_add
    (1 : Fin m -> Real)

theorem fourFiveSimplexAffineMap_injective
    {m : Nat} {T : Real} (hT : T ≠ 0) :
    Function.Injective (fourFiveSimplexAffineMap m T) := by
  intro z w hzw
  funext i
  have hi := congrFun hzw i
  unfold fourFiveSimplexAffineMap at hi
  simp only [Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul] at hi
  apply (mul_left_cancel₀ hT)
  linarith

theorem abs_det_fourFiveSimplexAffineDerivative
    (m : Nat) {T : Real} (hT : 0 <= T) :
    abs (fourFiveSimplexAffineDerivative m T).det = T ^ m := by
  unfold fourFiveSimplexAffineDerivative ContinuousLinearMap.det
  rw [ContinuousLinearMap.coe_smul, ContinuousLinearMap.coe_id,
    LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_pi]
  simp only [Fintype.card_fin]
  exact abs_of_nonneg (pow_nonneg hT m)

theorem sum_fourFiveSimplexAffineMap
    (m : Nat) (T : Real) (z : Fin m -> Real) :
    (∑ i, fourFiveSimplexAffineMap m T z i) =
      (m : Real) + T * ∑ i, z i := by
  unfold fourFiveSimplexAffineMap
  simp only [Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum, mul_one]

/-- The affine image of the fixed simplex is exactly the moving simplex. -/
theorem image_fourFiveClosedSimplex_affine_eq_movingSimplex
    {m : Nat} {u : Real} (hT : 0 < u - (m + 1 : Nat)) :
    fourFiveSimplexAffineMap m (u - (m + 1 : Nat)) ''
        fourFiveClosedSimplex m =
      fourFiveLogarithmicMovingSimplex m u := by
  let T : Real := u - (m + 1 : Nat)
  have hT' : 0 < T := hT
  ext s
  constructor
  · rintro ⟨z, hz, rfl⟩
    apply And.intro
    · intro i
      unfold fourFiveSimplexAffineMap
      simp only [Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul]
      have := mul_nonneg hT'.le (hz.1 i)
      linarith
    · rw [sum_fourFiveSimplexAffineMap]
      have hmul := mul_le_mul_of_nonneg_left hz.2 hT'.le
      dsimp [T] at hmul ⊢
      push_cast at hmul ⊢
      linarith
  · intro hs
    let z : Fin m -> Real := fun i => (s i - 1) / T
    refine ⟨z, ?_, ?_⟩
    · constructor
      · intro i
        dsimp [z]
        exact div_nonneg (sub_nonneg.mpr (hs.1 i)) hT'.le
      · change (∑ i, (s i - 1) / T) <= 1
        rw [← Finset.sum_div, div_le_iff₀ hT']
        have hsum : (∑ i, (s i - 1)) =
            (∑ i, s i) - (m : Real) := by
          rw [Finset.sum_sub_distrib]
          simp
        rw [hsum]
        dsimp [T]
        push_cast
        linarith [hs.2]
    · funext i
      unfold fourFiveSimplexAffineMap
      simp only [Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul]
      dsimp [z]
      rw [mul_div_cancel₀ (s i - 1) hT'.ne']
      ring

/-- Pointwise Jacobian-density identity for the affine substitution. -/
theorem fourFive_movingSimplexIntegrand_affine
    {m : Nat} {u : Real} (_hT : 0 < u - (m + 1 : Nat))
    (z : Fin m -> Real) :
    (u - (m + 1 : Nat)) ^ m *
        fourFiveLogarithmicMovingSimplexIntegrand m u
          (fourFiveSimplexAffineMap m (u - (m + 1 : Nat)) z) =
      fourFiveFixedSimplexIntegrand m (u - (m + 1 : Nat)) z := by
  let T : Real := u - (m + 1 : Nat)
  have hsum := sum_fourFiveSimplexAffineMap m T z
  have hslack :
      u - ((m : Real) + T * ∑ i, z i) =
        1 + T * (1 - ∑ i, z i) := by
    dsimp [T]
    push_cast
    ring
  change T ^ m *
      fourFiveLogarithmicMovingSimplexIntegrand m u
        (fourFiveSimplexAffineMap m T z) =
    fourFiveFixedSimplexIntegrand m T z
  unfold fourFiveLogarithmicMovingSimplexIntegrand
  rw [hsum, hslack]
  unfold fourFiveFixedSimplexIntegrand fourFiveSimplexDenominator
    fourFiveSimplexFactorProduct fourFiveSimplexRemainderFactor
    fourFiveSimplexAffineMap
  simp only [Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul]
  rw [div_eq_mul_inv, mul_inv, ← Finset.prod_inv_distrib]

/-- Exact identification of the literal moving kernel with the existing
fixed-simplex kernel whenever `T = u-(m+1)` is positive. -/
theorem fourFiveLogarithmicMovingSimplexKernel_eq_fixedSimplexKernel
    {m : Nat} {u : Real} (hT : 0 < u - (m + 1 : Nat)) :
    fourFiveLogarithmicMovingSimplexKernel m u =
      fourFiveFixedSimplexKernel m (u - (m + 1 : Nat)) := by
  let T : Real := u - (m + 1 : Nat)
  have hT' : 0 < T := hT
  let f := fourFiveSimplexAffineMap m T
  let f' := fourFiveSimplexAffineDerivative m T
  have himage : f '' fourFiveClosedSimplex m =
      fourFiveLogarithmicMovingSimplex m u := by
    exact image_fourFiveClosedSimplex_affine_eq_movingSimplex hT
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul
    volume (isClosed_fourFiveClosedSimplex m).measurableSet
    (fun z _hz =>
      (hasFDerivAt_fourFiveSimplexAffineMap m T z).hasFDerivWithinAt)
    (fourFiveSimplexAffineMap_injective hT'.ne').injOn
    (fourFiveLogarithmicMovingSimplexIntegrand m u)
  unfold fourFiveLogarithmicMovingSimplexKernel
    fourFiveFixedSimplexKernel
  rw [← himage, hchange]
  apply setIntegral_congr_fun
    (isClosed_fourFiveClosedSimplex m).measurableSet
  intro z _hz
  change abs (fourFiveSimplexAffineDerivative m T).det *
      fourFiveLogarithmicMovingSimplexIntegrand m u
        (fourFiveSimplexAffineMap m T z) =
    fourFiveFixedSimplexIntegrand m T z
  rw [abs_det_fourFiveSimplexAffineDerivative m hT'.le]
  exact fourFive_movingSimplexIntegrand_affine hT z

/-! ## The four physical layer identities -/

theorem fourFivePhysicalMovingSimplexLayer_zero_eq_fixed
    (y A B : Nat) :
    fourFivePhysicalMovingSimplexLayer 0 y A B =
      fourFiveFixedContinuumLayer 0 y A B := by
  have hzero := fourFiveMovingToFixedSimplexError_zero y A B
  unfold fourFiveMovingToFixedSimplexError at hzero
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

theorem fourFivePhysicalMovingSimplexLayer_one_eq_fixed
    {y A B : Nat}
    (hu : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      2 < fourFiveRealLogCoordinate y t) :
    fourFivePhysicalMovingSimplexLayer 1 y A B =
      fourFiveFixedContinuumLayer 1 y A B := by
  unfold fourFivePhysicalMovingSimplexLayer fourFiveFixedContinuumLayer
    fourFiveContinuumLayerTwoMain fourFiveContinuumKernelTwo
  apply congrArg (fun z : Real => (1 / Real.log (y : Real)) * z)
  apply intervalIntegral.integral_congr
  intro t ht
  exact fourFiveLogarithmicMovingSimplexKernel_eq_fixedSimplexKernel
    (m := 1) (u := fourFiveRealLogCoordinate y t) (by
      norm_num
      linarith [hu t ht])

theorem fourFivePhysicalMovingSimplexLayer_two_eq_fixed
    {y A B : Nat}
    (hu : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      3 < fourFiveRealLogCoordinate y t) :
    fourFivePhysicalMovingSimplexLayer 2 y A B =
      fourFiveFixedContinuumLayer 2 y A B := by
  unfold fourFivePhysicalMovingSimplexLayer fourFiveFixedContinuumLayer
    fourFiveContinuumLayerThreeMain fourFiveContinuumKernelThree
  apply congrArg (fun z : Real => (1 / Real.log (y : Real)) * z)
  apply intervalIntegral.integral_congr
  intro t ht
  exact fourFiveLogarithmicMovingSimplexKernel_eq_fixedSimplexKernel
    (m := 2) (u := fourFiveRealLogCoordinate y t) (by
      norm_num
      linarith [hu t ht])

theorem fourFivePhysicalMovingSimplexLayer_three_eq_fixed
    {y A B : Nat}
    (hu : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      4 < fourFiveRealLogCoordinate y t) :
    fourFivePhysicalMovingSimplexLayer 3 y A B =
      fourFiveFixedContinuumLayer 3 y A B := by
  unfold fourFivePhysicalMovingSimplexLayer fourFiveFixedContinuumLayer
    fourFiveContinuumLayerFourMain fourFiveContinuumKernelFour
  apply congrArg (fun z : Real => (1 / Real.log (y : Real)) * z)
  apply intervalIntegral.integral_congr
  intro t ht
  exact fourFiveLogarithmicMovingSimplexKernel_eq_fixedSimplexKernel
    (m := 3) (u := fourFiveRealLogCoordinate y t) (by
      norm_num
      linarith [hu t ht])

theorem fourFiveMovingToFixedSimplexError_one_eq_zero
    {y A B : Nat}
    (hu : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      2 < fourFiveRealLogCoordinate y t) :
    fourFiveMovingToFixedSimplexError 1 y A B = 0 := by
  unfold fourFiveMovingToFixedSimplexError
  rw [fourFivePhysicalMovingSimplexLayer_one_eq_fixed hu, sub_self, abs_zero]

theorem fourFiveMovingToFixedSimplexError_two_eq_zero
    {y A B : Nat}
    (hu : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      3 < fourFiveRealLogCoordinate y t) :
    fourFiveMovingToFixedSimplexError 2 y A B = 0 := by
  unfold fourFiveMovingToFixedSimplexError
  rw [fourFivePhysicalMovingSimplexLayer_two_eq_fixed hu, sub_self, abs_zero]

theorem fourFiveMovingToFixedSimplexError_three_eq_zero
    {y A B : Nat}
    (hu : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      4 < fourFiveRealLogCoordinate y t) :
    fourFiveMovingToFixedSimplexError 3 y A B = 0 := by
  unfold fourFiveMovingToFixedSimplexError
  rw [fourFivePhysicalMovingSimplexLayer_three_eq_fixed hu, sub_self, abs_zero]

end Erdos390.WholePaper.BankPaperRealization
