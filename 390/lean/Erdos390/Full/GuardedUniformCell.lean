import Erdos390.Full.GuardDeletionProbability
import Erdos390.Full.UniformFiniteProbability

/-!
# Guard deletion on an actual uniform arithmetic cell

The paper deletes an ambient finite guard set from each structured cell.
This module constructs the literal guard subset of the cell, proves that its
cardinality is no larger than the ambient guard census, and combines that fact
with the bounded-tilt density ratio.  No total-variation or covariance error is
assumed.
-/

namespace Erdos390.Full

open FiniteProbability

noncomputable section

namespace GuardedUniformCell

variable {Alpha : Type*} [DecidableEq Alpha]

/-- Members of `S` whose ambient value lies in the guard set `G`. -/
def guardSubtype (S G : Finset Alpha) : Finset S :=
  Finset.univ.filter fun x : S => (x : Alpha) ∈ G

@[simp] theorem mem_guardSubtype {S G : Finset Alpha} {x : S} :
    x ∈ guardSubtype S G ↔ (x : Alpha) ∈ G := by
  simp [guardSubtype]

/-- The subtype guard census injects into the ambient guard census. -/
theorem card_guardSubtype_le (S G : Finset Alpha) :
    (guardSubtype S G).card ≤ G.card := by
  apply Finset.card_le_card_of_injOn (fun x : S => (x : Alpha))
  · intro x hx
    exact mem_guardSubtype.mp hx
  · intro x hx y hy hxy
    exact Subtype.ext hxy

/-- Exact deleted mass before tilting the uniform cell. -/
theorem uniform_guardMass_eq
    (S G : Finset Alpha) (hS : S.Nonempty) :
    (uniformOnFinset S hS).guardMass (guardSubtype S G) =
      ((guardSubtype S G).card : ℝ) / (S.card : ℝ) := by
  unfold guardMass
  simp only [uniformOnFinset_mass, Finset.sum_const, nsmul_eq_mul]
  ring

/-- A bounded tilt assigns the actual guard subset at most its ambient
cardinality divided by the actual cell cardinality, times `exp (2K)`. -/
theorem tilted_uniform_guardMass_le
    (S G : Finset Alpha) (hS : S.Nonempty)
    (score : S → ℝ) (K : ℝ) (hscore : ∀ x, |score x| ≤ K) :
    ((uniformOnFinset S hS).exponentialTilt score).guardMass
        (guardSubtype S G) ≤
      Real.exp (2 * K) * (G.card : ℝ) / (S.card : ℝ) := by
  have hScard : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hS
  have hguardCard : ((guardSubtype S G).card : ℝ) ≤ (G.card : ℝ) := by
    exact_mod_cast card_guardSubtype_le S G
  calc
    ((uniformOnFinset S hS).exponentialTilt score).guardMass
          (guardSubtype S G) ≤
        Real.exp (2 * K) *
          (uniformOnFinset S hS).guardMass (guardSubtype S G) :=
      (uniformOnFinset S hS).exponentialTilt_guardMass_le_exp_two_mul
        (guardSubtype S G) score K hscore
    _ = Real.exp (2 * K) *
          (((guardSubtype S G).card : ℝ) / (S.card : ℝ)) := by
      rw [uniform_guardMass_eq]
    _ ≤ Real.exp (2 * K) * ((G.card : ℝ) / (S.card : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hguardCard hScard.le)
        (Real.exp_pos _).le
    _ = Real.exp (2 * K) * (G.card : ℝ) / (S.card : ℝ) := by ring

/-- The literal covariance perturbation caused by deleting the guarded
points from a boundedly tilted uniform cell.  The proof constructs the
renormalization witness from the census bound; it does not assume a
total-variation estimate. -/
theorem exists_deleteGuards_covariance_bound
    (S G : Finset Alpha) (hS : S.Nonempty)
    (score : S → ℝ) (K : ℝ) (hscore : ∀ x, |score x| ≤ K)
    (F H : S → ℝ) (KF KH : ℝ)
    (hKF : 0 ≤ KF) (hKH : 0 ≤ KH)
    (hF : ∀ x, |F x| ≤ KF) (hH : ∀ x, |H x| ≤ KH)
    (hsmallCensus :
      Real.exp (2 * K) * (G.card : ℝ) / (S.card : ℝ) ≤ (1 : ℝ) / 2) :
    ∃ hsmall :
        ((uniformOnFinset S hS).exponentialTilt score).guardMass
          (guardSubtype S G) < 1,
      |(((uniformOnFinset S hS).exponentialTilt score).deleteGuards
          (guardSubtype S G) hsmall).covariance F H -
        ((uniformOnFinset S hS).exponentialTilt score).covariance F H| ≤
        12 * KF * KH *
          (Real.exp (2 * K) * (G.card : ℝ) / (S.card : ℝ)) := by
  let mu := (uniformOnFinset S hS).exponentialTilt score
  let guards := guardSubtype S G
  let delta := Real.exp (2 * K) * (G.card : ℝ) / (S.card : ℝ)
  have hmass : mu.guardMass guards ≤ delta := by
    simpa only [mu, guards, delta] using
      tilted_uniform_guardMass_le S G hS score K hscore
  have hhalf : mu.guardMass guards ≤ (1 : ℝ) / 2 :=
    hmass.trans hsmallCensus
  have hsmall : mu.guardMass guards < 1 := by linarith
  refine ⟨hsmall, ?_⟩
  have hperturb := mu.guardPerturbation_le_four_mul_guardMass guards hhalf
  have hmass0 : 0 ≤ mu.guardMass guards := mu.guardMass_nonneg guards
  have hdelta0 : 0 ≤ delta := by
    dsimp only [delta]
    positivity
  calc
    |(mu.deleteGuards guards hsmall).covariance F H -
        mu.covariance F H| ≤
        3 * KF * KH * mu.guardPerturbation guards :=
      mu.abs_deleteGuards_covariance_sub_le guards hsmall F H
        hKF hKH hF hH
    _ ≤ 3 * KF * KH * (4 * mu.guardMass guards) := by
      exact mul_le_mul_of_nonneg_left hperturb
        (mul_nonneg (mul_nonneg (by norm_num) hKF) hKH)
    _ ≤ 3 * KF * KH * (4 * delta) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hmass (by norm_num)
      · exact mul_nonneg (mul_nonneg (by norm_num) hKF) hKH
    _ = 12 * KF * KH * delta := by ring
    _ = 12 * KF * KH *
          (Real.exp (2 * K) * (G.card : ℝ) / (S.card : ℝ)) := rfl

end GuardedUniformCell

end

end Erdos390.Full
