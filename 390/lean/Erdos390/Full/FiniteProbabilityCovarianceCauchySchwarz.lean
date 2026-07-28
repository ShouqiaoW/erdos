import Erdos390.Full.PrimePowerCovariance

/-!
# Cauchy--Schwarz for a literal finite covariance

The two-stage Schur argument needs Cauchy--Schwarz for the actual finite
tilted law, not an abstract positive-semidefinite assumption.  This file
derives it directly from the mass function of `FiniteProbability`.
-/

open scoped BigOperators

namespace Erdos390.Full.FiniteProbability

noncomputable section

variable {Omega : Type*} [Fintype Omega]

/-- Covariance is the weighted inner product of the two centered functions. -/
theorem covariance_eq_sum_mass_mul_centered
    (mu : FiniteProbability Omega) (F G : Omega → ℝ) :
    mu.covariance F G =
      ∑ omega, mu.mass omega * (F omega - mu.expect F) *
        (G omega - mu.expect G) := by
  unfold covariance
  generalize hEF : mu.expect F = EF
  generalize hEG : mu.expect G = EG
  unfold expect at hEF hEG ⊢
  symm
  calc
    (∑ omega, mu.mass omega * (F omega - EF) * (G omega - EG)) =
        (∑ omega, mu.mass omega * (F omega * G omega)) -
          (∑ omega, mu.mass omega * F omega) * EG -
          EF * (∑ omega, mu.mass omega * G omega) +
          (EF * EG) * (∑ omega, mu.mass omega) := by
      rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro omega homega
      ring
    _ = (∑ omega, mu.mass omega * (F omega * G omega)) - EF * EG := by
      rw [mu.mass_sum, ← hEF, ← hEG]
      ring

/-- Squared Cauchy--Schwarz inequality for the exact finite covariance. -/
theorem covariance_sq_le_mul_self
    (mu : FiniteProbability Omega) (F G : Omega → ℝ) :
    mu.covariance F G ^ 2 ≤
      mu.covariance F F * mu.covariance G G := by
  let f : Omega → ℝ := fun omega ↦
    Real.sqrt (mu.mass omega) * (F omega - mu.expect F)
  let g : Omega → ℝ := fun omega ↦
    Real.sqrt (mu.mass omega) * (G omega - mu.expect G)
  have hcross : (∑ omega, f omega * g omega) = mu.covariance F G := by
    rw [mu.covariance_eq_sum_mass_mul_centered]
    apply Finset.sum_congr rfl
    intro omega homega
    dsimp only [f, g]
    have hsqrt : Real.sqrt (mu.mass omega) ^ 2 = mu.mass omega :=
      Real.sq_sqrt (mu.mass_nonneg omega)
    calc
      Real.sqrt (mu.mass omega) * (F omega - mu.expect F) *
          (Real.sqrt (mu.mass omega) * (G omega - mu.expect G)) =
          Real.sqrt (mu.mass omega) ^ 2 *
            (F omega - mu.expect F) * (G omega - mu.expect G) := by ring
      _ = mu.mass omega * (F omega - mu.expect F) *
            (G omega - mu.expect G) := by rw [hsqrt]
  have hleft : (∑ omega, f omega ^ 2) = mu.covariance F F := by
    rw [mu.covariance_eq_sum_mass_mul_centered]
    apply Finset.sum_congr rfl
    intro omega homega
    dsimp only [f]
    have hsqrt : Real.sqrt (mu.mass omega) ^ 2 = mu.mass omega :=
      Real.sq_sqrt (mu.mass_nonneg omega)
    rw [mul_pow, hsqrt]
    ring
  have hright : (∑ omega, g omega ^ 2) = mu.covariance G G := by
    rw [mu.covariance_eq_sum_mass_mul_centered]
    apply Finset.sum_congr rfl
    intro omega homega
    dsimp only [g]
    have hsqrt : Real.sqrt (mu.mass omega) ^ 2 = mu.mass omega :=
      Real.sq_sqrt (mu.mass_nonneg omega)
    rw [mul_pow, hsqrt]
    ring
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  simpa only [hcross, hleft, hright] using hCS

end

end Erdos390.Full.FiniteProbability
