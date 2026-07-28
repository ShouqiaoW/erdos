import Mathlib

/-!
# Stable inversion under an operator perturbation

This is the quantitative finite-dimensional perturbation lemma needed after
the continuum inverse has been transferred to the arithmetic gauge space.
It does not assume invertibility of the perturbed operator.  Instead it
derives it from a proved inverse for the reference operator and an operator
error smaller than the reciprocal inverse bound.
-/

namespace Erdos390.Full

noncomputable section

namespace StableInverse

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

omit [FiniteDimensional ℝ X] in
theorem reference_control
    (A Ainv E : X →L[ℝ] X) (C delta : ℝ)
    (hC : 0 ≤ C)
    (hleft : ∀ x, Ainv (A x) = x)
    (hinv : ∀ y, ‖Ainv y‖ ≤ C * ‖y‖)
    (herror : ∀ x, ‖E x‖ ≤ delta * ‖x‖) (x : X) :
    (1 - C * delta) * ‖x‖ ≤ C * ‖(A + E) x‖ := by
  have hA : ‖x‖ ≤ C * ‖A x‖ := by
    calc
      ‖x‖ = ‖Ainv (A x)‖ := by rw [hleft x]
      _ ≤ C * ‖A x‖ := hinv (A x)
  have hsplit : ‖A x‖ ≤ ‖(A + E) x‖ + ‖E x‖ := by
    have hid : A x = (A + E) x - E x := by
      simp
    rw [hid]
    exact norm_sub_le _ _
  have hscaled : C * ‖A x‖ ≤
      C * (‖(A + E) x‖ + ‖E x‖) :=
    mul_le_mul_of_nonneg_left hsplit hC
  have herrscaled : C * (‖(A + E) x‖ + ‖E x‖) ≤
      C * (‖(A + E) x‖ + delta * ‖x‖) := by
    apply mul_le_mul_of_nonneg_left _ hC
    simpa [add_comm] using add_le_add_left (herror x) ‖(A + E) x‖
  nlinarith

omit [FiniteDimensional ℝ X] in
theorem perturbed_injective
    (A Ainv E : X →L[ℝ] X) (C delta : ℝ)
    (hC : 0 ≤ C)
    (hsmall : C * delta < 1)
    (hleft : ∀ x, Ainv (A x) = x)
    (hinv : ∀ y, ‖Ainv y‖ ≤ C * ‖y‖)
    (herror : ∀ x, ‖E x‖ ≤ delta * ‖x‖) :
    Function.Injective (A + E) := by
  intro x y hxy
  have hzero : (A + E) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hcontrol := reference_control A Ainv E C delta hC
    hleft hinv herror (x - y)
  rw [hzero, norm_zero, mul_zero] at hcontrol
  have hcoef : 0 < 1 - C * delta := sub_pos.mpr hsmall
  have hnorm : ‖x - y‖ = 0 := by
    apply le_antisymm
    · nlinarith [norm_nonneg (x - y)]
    · exact norm_nonneg _
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- The continuous linear equivalence represented by the perturbed operator.
Its existence is a conclusion, not a hypothesis. -/
def perturbedEquiv
    (A Ainv E : X →L[ℝ] X) (C delta : ℝ)
    (hC : 0 ≤ C)
    (hsmall : C * delta < 1)
    (hleft : ∀ x, Ainv (A x) = x)
    (hinv : ∀ y, ‖Ainv y‖ ≤ C * ‖y‖)
    (herror : ∀ x, ‖E x‖ ≤ delta * ‖x‖) : X ≃L[ℝ] X :=
  (LinearEquiv.ofInjectiveEndo ((A + E : X →L[ℝ] X) : X →ₗ[ℝ] X)
    (perturbed_injective A Ainv E C delta hC hsmall
      hleft hinv herror)).toContinuousLinearEquiv

theorem perturbedEquiv_apply
    (A Ainv E : X →L[ℝ] X) (C delta : ℝ)
    (hC : 0 ≤ C)
    (hsmall : C * delta < 1)
    (hleft : ∀ x, Ainv (A x) = x)
    (hinv : ∀ y, ‖Ainv y‖ ≤ C * ‖y‖)
    (herror : ∀ x, ‖E x‖ ≤ delta * ‖x‖) (x : X) :
    perturbedEquiv A Ainv E C delta hC hsmall
      hleft hinv herror x = (A + E) x := by
  simp [perturbedEquiv]

theorem perturbed_inverse_bound_mul
    (A Ainv E : X →L[ℝ] X) (C delta : ℝ)
    (hC : 0 ≤ C)
    (hsmall : C * delta < 1)
    (hleft : ∀ x, Ainv (A x) = x)
    (hinv : ∀ y, ‖Ainv y‖ ≤ C * ‖y‖)
    (herror : ∀ x, ‖E x‖ ≤ delta * ‖x‖) (y : X) :
    (1 - C * delta) *
        ‖(perturbedEquiv A Ainv E C delta hC hsmall
          hleft hinv herror).symm y‖ ≤ C * ‖y‖ := by
  let e := perturbedEquiv A Ainv E C delta hC hsmall
    hleft hinv herror
  have hcontrol := reference_control A Ainv E C delta hC
    hleft hinv herror (e.symm y)
  have happ : (A + E) (e.symm y) = y := by
    rw [← perturbedEquiv_apply A Ainv E C delta hC hsmall
      hleft hinv herror]
    exact e.apply_symm_apply y
  simpa [e, happ] using hcontrol

theorem perturbed_inverse_bound
    (A Ainv E : X →L[ℝ] X) (C delta : ℝ)
    (hC : 0 ≤ C)
    (hsmall : C * delta < 1)
    (hleft : ∀ x, Ainv (A x) = x)
    (hinv : ∀ y, ‖Ainv y‖ ≤ C * ‖y‖)
    (herror : ∀ x, ‖E x‖ ≤ delta * ‖x‖) (y : X) :
    ‖(perturbedEquiv A Ainv E C delta hC hsmall
        hleft hinv herror).symm y‖ ≤
      (C / (1 - C * delta)) * ‖y‖ := by
  have hcoef : 0 < 1 - C * delta := sub_pos.mpr hsmall
  rw [show (C / (1 - C * delta)) * ‖y‖ =
      (C * ‖y‖) / (1 - C * delta) by ring]
  apply (le_div_iff₀ hcoef).2
  simpa [mul_comm] using
    perturbed_inverse_bound_mul A Ainv E C delta hC
      hsmall hleft hinv herror y

end StableInverse

end

end Erdos390.Full
