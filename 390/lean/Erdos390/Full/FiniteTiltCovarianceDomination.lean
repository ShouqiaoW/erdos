import Erdos390.Full.OmittedTiltFallback
import Erdos390.Full.PrimePowerCovariance

/-!
# Covariance domination under a bounded finite exponential tilt

A bounded tilt need not be close to the baseline in total variation.  It
does, however, dominate the baseline measure by the exact density factor
`exp (-2K)`.  Since variance is the minimum mean-square distance from a
constant, the same factor transfers every covariance quadratic form.  This
is useful for passing a proved finite baseline gap to a whole preselected
tilt box without introducing a fictitious limiting covariance matrix.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

theorem expect_const (mu : FiniteProbability Omega) (c : ℝ) :
    mu.expect (fun _ ↦ c) = c := by
  unfold expect
  rw [← Finset.sum_mul, mu.mass_sum, one_mul]

/-- Mean-square distance from an arbitrary constant is variance plus the
square of the displacement from the mean. -/
theorem expect_sq_sub_const_eq_covariance_add_sq
    (mu : FiniteProbability Omega) (F : Omega → ℝ) (c : ℝ) :
    mu.expect (fun omega ↦ (F omega - c) ^ 2) =
      mu.covariance F F + (mu.expect F - c) ^ 2 := by
  have hfun : (fun omega ↦ (F omega - c) ^ 2) =
      fun omega ↦ F omega * F omega +
        ((-2 * c) * F omega + c ^ 2) := by
    funext omega
    ring
  rw [hfun, mu.expect_add]
  have htail : mu.expect (fun omega ↦ (-2 * c) * F omega + c ^ 2) =
      (-2 * c) * mu.expect F + c ^ 2 := by
    rw [mu.expect_add, mu.expect_smul, mu.expect_const]
  rw [htail]
  unfold covariance
  ring

theorem covariance_self_le_expect_sq_sub_const
    (mu : FiniteProbability Omega) (F : Omega → ℝ) (c : ℝ) :
    mu.covariance F F ≤ mu.expect (fun omega ↦ (F omega - c) ^ 2) := by
  rw [mu.expect_sq_sub_const_eq_covariance_add_sq F c]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Upper bound for the partition function of an absolutely `K`-bounded
score. -/
theorem expPartition_le_exp
    (mu : FiniteProbability Omega) (score : Omega → ℝ) (K : ℝ)
    (hscore : ∀ omega, |score omega| ≤ K) :
    mu.expPartition score ≤ Real.exp K := by
  unfold expPartition expect
  calc
    (∑ omega, mu.mass omega * Real.exp (score omega)) ≤
        ∑ omega, mu.mass omega * Real.exp K := by
      apply Finset.sum_le_sum
      intro omega homega
      apply mul_le_mul_of_nonneg_left _ (mu.mass_nonneg omega)
      exact Real.exp_le_exp.mpr
        ((le_abs_self (score omega)).trans (hscore omega))
    _ = Real.exp K := by
      rw [← Finset.sum_mul, mu.mass_sum, one_mul]

/-- A bounded exponential tilt dominates every nonnegative expectation by
the pointwise density-ratio factor `exp (-2K)`. -/
theorem exp_neg_two_mul_expect_le_exponentialTilt_expect
    (mu : FiniteProbability Omega) (A score : Omega → ℝ) (K : ℝ)
    (hA : ∀ omega, 0 ≤ A omega)
    (hscore : ∀ omega, |score omega| ≤ K) :
    Real.exp (-2 * K) * mu.expect A ≤
      (mu.exponentialTilt score).expect A := by
  let Z := mu.expPartition score
  let E := mu.expect A
  let numerator := mu.expect (fun omega ↦ A omega * Real.exp (score omega))
  have hE : 0 ≤ E := mu.expect_nonneg A hA
  have hZ : 0 < Z := mu.expPartition_pos score
  have hZupper : Z ≤ Real.exp K := mu.expPartition_le_exp score K hscore
  have hnum : Real.exp (-K) * E ≤ numerator := by
    unfold numerator E expect
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro omega homega
    have hexp : Real.exp (-K) ≤ Real.exp (score omega) :=
      Real.exp_le_exp.mpr
        ((neg_le_neg (hscore omega)).trans (neg_abs_le (score omega)))
    calc
      Real.exp (-K) * (mu.mass omega * A omega) =
          mu.mass omega * (A omega * Real.exp (-K)) := by ring
      _ ≤ mu.mass omega * (A omega * Real.exp (score omega)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp (hA omega))
          (mu.mass_nonneg omega)
  rw [mu.exponentialTilt_expect_eq A score]
  change Real.exp (-2 * K) * E ≤ numerator / Z
  calc
    Real.exp (-2 * K) * E =
        (Real.exp (-K) * E) / Real.exp K := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      rw [show Real.exp (-2 * K) =
          Real.exp (-K) * Real.exp (-K) by
        rw [← Real.exp_add]
        congr 1
        ring]
      ring
    _ ≤ (Real.exp (-K) * E) / Z := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg (Real.exp_pos _).le hE) hZ hZupper
    _ ≤ numerator / Z := by
      exact div_le_div_of_nonneg_right hnum hZ.le

/-- Every covariance quadratic form survives a bounded tilt with the same
exact density-ratio factor. -/
theorem exp_neg_two_mul_covariance_self_le_exponentialTilt
    (mu : FiniteProbability Omega) (F score : Omega → ℝ) (K : ℝ)
    (hscore : ∀ omega, |score omega| ≤ K) :
    Real.exp (-2 * K) * mu.covariance F F ≤
      (mu.exponentialTilt score).covariance F F := by
  let nu := mu.exponentialTilt score
  let c := nu.expect F
  have hdom := mu.exp_neg_two_mul_expect_le_exponentialTilt_expect
    (fun omega ↦ (F omega - c) ^ 2) score K
    (fun omega ↦ sq_nonneg _) hscore
  have hmin := mu.covariance_self_le_expect_sq_sub_const F c
  have hfactor : 0 ≤ Real.exp (-2 * K) := (Real.exp_pos _).le
  calc
    Real.exp (-2 * K) * mu.covariance F F ≤
        Real.exp (-2 * K) *
          mu.expect (fun omega ↦ (F omega - c) ^ 2) :=
      mul_le_mul_of_nonneg_left hmin hfactor
    _ ≤ nu.expect (fun omega ↦ (F omega - c) ^ 2) := hdom
    _ = nu.covariance F F := by
      rw [nu.expect_sq_sub_const_eq_covariance_add_sq F c]
      simp only [c, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, add_zero]

end FiniteProbability

end

end Erdos390.Full
