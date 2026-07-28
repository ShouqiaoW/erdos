import Mathlib

/-!
# Finite exponential families

This file develops the exact finite exponential family used by the smooth-row
bridge.  The sample space is finite, the base weights are nonnegative with
positive total mass, and every score is a continuous linear functional on a
finite-dimensional real parameter space.  All normalization, positivity,
smoothness, and covariance-Jacobian statements are proved from these data.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

/-- A probability mass function on a finite sample type. -/
structure FiniteProbability (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  mass_nonneg : ∀ ω, 0 ≤ mass ω
  mass_sum : ∑ ω, mass ω = 1

namespace FiniteProbability

variable {Ω : Type*} [Fintype Ω]

/-- Expectation with respect to a finite probability mass function. -/
def expect (μ : FiniteProbability Ω) (F : Ω → ℝ) : ℝ :=
  ∑ ω, μ.mass ω * F ω

/-- Covariance with respect to a finite probability mass function. -/
def covariance (μ : FiniteProbability Ω) (F G : Ω → ℝ) : ℝ :=
  μ.expect (fun ω => F ω * G ω) - μ.expect F * μ.expect G

end FiniteProbability

/-- Raw data for a finite exponential family.  `scale` is the paper's `L`,
and `baseMass` below is the paper's active mass `q_n`. -/
structure FiniteExponentialFamily
    (Ω Param : Type*) [Fintype Ω]
    [NormedAddCommGroup Param] [NormedSpace ℝ Param]
    [FiniteDimensional ℝ Param] where
  baseWeight : Ω → ℝ
  baseWeight_nonneg : ∀ ω, 0 ≤ baseWeight ω
  baseMass_pos : 0 < ∑ ω, baseWeight ω
  scale : ℝ
  scale_pos : 0 < scale
  score : Ω → Param →L[ℝ] ℝ

namespace FiniteExponentialFamily

variable {Ω Param : Type*} [Fintype Ω]
  [NormedAddCommGroup Param] [NormedSpace ℝ Param]
  [FiniteDimensional ℝ Param]

/-- Total active mass of the baseline family. -/
def baseMass (fam : FiniteExponentialFamily Ω Param) : ℝ :=
  ∑ ω, fam.baseWeight ω

theorem baseMass_positive (fam : FiniteExponentialFamily Ω Param) : 0 < fam.baseMass := by
  exact fam.baseMass_pos

theorem baseMass_ne_zero (fam : FiniteExponentialFamily Ω Param) : fam.baseMass ≠ 0 :=
  ne_of_gt fam.baseMass_pos

theorem scale_ne_zero (fam : FiniteExponentialFamily Ω Param) : fam.scale ≠ 0 :=
  ne_of_gt fam.scale_pos

/-- The unnormalized tilted mass at a sample point. -/
def unnormalizedWeight (fam : FiniteExponentialFamily Ω Param)
    (ξ : Param) (ω : Ω) : ℝ :=
  fam.baseWeight ω * Real.exp (fam.score ω ξ / fam.scale)

theorem unnormalizedWeight_nonneg (fam : FiniteExponentialFamily Ω Param)
    (ξ : Param) (ω : Ω) : 0 ≤ fam.unnormalizedWeight ξ ω :=
  mul_nonneg (fam.baseWeight_nonneg ω) (le_of_lt (Real.exp_pos _))

/-- The exact finite partition function. -/
def partition (fam : FiniteExponentialFamily Ω Param) (ξ : Param) : ℝ :=
  ∑ ω, fam.unnormalizedWeight ξ ω

theorem partition_pos (fam : FiniteExponentialFamily Ω Param) (ξ : Param) :
    0 < fam.partition ξ := by
  have hex : ∃ ω : Ω, 0 < fam.baseWeight ω := by
    have hsum : 0 < ∑ ω, fam.baseWeight ω := fam.baseMass_pos
    rw [Finset.sum_pos_iff_of_nonneg
      (fun ω (_ : ω ∈ (Finset.univ : Finset Ω)) => fam.baseWeight_nonneg ω)] at hsum
    exact hsum.imp fun _ hω => hω.2
  obtain ⟨ω, hω⟩ := hex
  rw [partition, Finset.sum_pos_iff_of_nonneg
    (fun η (_ : η ∈ (Finset.univ : Finset Ω)) => fam.unnormalizedWeight_nonneg ξ η)]
  exact ⟨ω, Finset.mem_univ ω, mul_pos hω (Real.exp_pos _)⟩

theorem partition_ne_zero (fam : FiniteExponentialFamily Ω Param) (ξ : Param) :
    fam.partition ξ ≠ 0 :=
  ne_of_gt (fam.partition_pos ξ)

/-- The normalized tilted probability mass. -/
def probabilityMass (fam : FiniteExponentialFamily Ω Param)
    (ξ : Param) (ω : Ω) : ℝ :=
  fam.unnormalizedWeight ξ ω / fam.partition ξ

theorem probabilityMass_nonneg (fam : FiniteExponentialFamily Ω Param)
    (ξ : Param) (ω : Ω) : 0 ≤ fam.probabilityMass ξ ω :=
  div_nonneg (fam.unnormalizedWeight_nonneg ξ ω) (le_of_lt (fam.partition_pos ξ))

theorem probabilityMass_sum (fam : FiniteExponentialFamily Ω Param) (ξ : Param) :
    ∑ ω, fam.probabilityMass ξ ω = 1 := by
  simp only [FiniteExponentialFamily.probabilityMass]
  rw [← Finset.sum_div, partition]
  exact div_self (fam.partition_ne_zero ξ)

/-- The tilted probability as an actual finite probability object. -/
def tiltedProbability (fam : FiniteExponentialFamily Ω Param)
    (ξ : Param) : FiniteProbability Ω where
  mass := fam.probabilityMass ξ
  mass_nonneg := fam.probabilityMass_nonneg ξ
  mass_sum := fam.probabilityMass_sum ξ

/-- Active coordinate weights.  Their total mass remains `baseMass`. -/
def activeWeight (fam : FiniteExponentialFamily Ω Param)
    (ξ : Param) (ω : Ω) : ℝ :=
  fam.baseMass * fam.probabilityMass ξ ω

theorem activeWeight_nonneg (fam : FiniteExponentialFamily Ω Param)
    (ξ : Param) (ω : Ω) : 0 ≤ fam.activeWeight ξ ω :=
  mul_nonneg (le_of_lt fam.baseMass_pos) (fam.probabilityMass_nonneg ξ ω)

theorem activeWeight_sum (fam : FiniteExponentialFamily Ω Param) (ξ : Param) :
    ∑ ω, fam.activeWeight ξ ω = fam.baseMass := by
  simp only [FiniteExponentialFamily.activeWeight]
  rw [← Finset.mul_sum, fam.probabilityMass_sum ξ, mul_one]

/-- Expectation under the normalized tilted law. -/
def expectation (fam : FiniteExponentialFamily Ω Param)
    (F : Ω → ℝ) (ξ : Param) : ℝ :=
  (fam.tiltedProbability ξ).expect F

/-- An active (unnormalized) moment. -/
def moment (fam : FiniteExponentialFamily Ω Param)
    (F : Ω → ℝ) (ξ : Param) : ℝ :=
  ∑ ω, fam.activeWeight ξ ω * F ω

/-- The unnormalized numerator of a tilted moment. -/
def rawMoment (fam : FiniteExponentialFamily Ω Param)
    (F : Ω → ℝ) (ξ : Param) : ℝ :=
  ∑ ω, fam.unnormalizedWeight ξ ω * F ω

theorem moment_eq_normalizedRawMoment
    (fam : FiniteExponentialFamily Ω Param) (F : Ω → ℝ) (ξ : Param) :
    fam.moment F ξ = fam.baseMass * fam.rawMoment F ξ / fam.partition ξ := by
  simp only [moment, activeWeight, probabilityMass, rawMoment]
  calc
    (∑ ω, fam.baseMass * (fam.unnormalizedWeight ξ ω / fam.partition ξ) * F ω)
        = ∑ ω, (fam.baseMass / fam.partition ξ) *
            (fam.unnormalizedWeight ξ ω * F ω) := by
              apply Finset.sum_congr rfl
              intro ω _
              ring
    _ = (fam.baseMass / fam.partition ξ) *
          ∑ ω, fam.unnormalizedWeight ξ ω * F ω := by rw [Finset.mul_sum]
    _ = fam.baseMass * (∑ ω, fam.unnormalizedWeight ξ ω * F ω) /
          fam.partition ξ := by ring

theorem moment_eq_baseMass_mul_expectation
    (fam : FiniteExponentialFamily Ω Param) (F : Ω → ℝ) (ξ : Param) :
    fam.moment F ξ = fam.baseMass * fam.expectation F ξ := by
  simp only [moment, expectation, FiniteProbability.expect,
    FiniteExponentialFamily.activeWeight, tiltedProbability]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem expectation_eq_rawMoment_div_partition
    (fam : FiniteExponentialFamily Ω Param) (F : Ω → ℝ) (ξ : Param) :
    fam.expectation F ξ = fam.rawMoment F ξ / fam.partition ξ := by
  simp only [expectation, tiltedProbability, FiniteProbability.expect,
    probabilityMass, rawMoment]
  calc
    (∑ ω, fam.unnormalizedWeight ξ ω / fam.partition ξ * F ω)
        = ∑ ω, (fam.unnormalizedWeight ξ ω * F ω) / fam.partition ξ := by
            apply Finset.sum_congr rfl
            intro ω _
            ring
    _ = (∑ ω, fam.unnormalizedWeight ξ ω * F ω) / fam.partition ξ := by
          rw [Finset.sum_div]

/-- Fréchet derivative of one unnormalized exponential weight. -/
def unnormalizedWeightFDeriv (fam : FiniteExponentialFamily Ω Param)
    (ξ : Param) (ω : Ω) : Param →L[ℝ] ℝ :=
  fam.baseWeight ω •
    (Real.exp (fam.score ω ξ / fam.scale) •
      ((fam.scale)⁻¹ • fam.score ω))

theorem hasFDerivAt_unnormalizedWeight
    (fam : FiniteExponentialFamily Ω Param) (ξ : Param) (ω : Ω) :
    HasFDerivAt (fun η => fam.unnormalizedWeight η ω)
      (fam.unnormalizedWeightFDeriv ξ ω) ξ := by
  have hs : HasFDerivAt (fun η => fam.score ω η / fam.scale)
      ((fam.scale)⁻¹ • fam.score ω) ξ := by
    simpa only [div_eq_mul_inv, mul_comm] using
      ((fam.score ω).hasFDerivAt.const_mul (fam.scale)⁻¹)
  simpa only [unnormalizedWeight, unnormalizedWeightFDeriv] using
    hs.exp.const_mul (fam.baseWeight ω)

theorem unnormalizedWeightFDeriv_apply
    (fam : FiniteExponentialFamily Ω Param) (ξ direction : Param) (ω : Ω) :
    fam.unnormalizedWeightFDeriv ξ ω direction =
      fam.unnormalizedWeight ξ ω / fam.scale * fam.score ω direction := by
  simp only [unnormalizedWeightFDeriv, ContinuousLinearMap.smul_apply,
    smul_eq_mul, unnormalizedWeight]
  field_simp

/-- Fréchet derivative of the partition function. -/
def partitionFDeriv (fam : FiniteExponentialFamily Ω Param)
    (ξ : Param) : Param →L[ℝ] ℝ :=
  ∑ ω, fam.unnormalizedWeightFDeriv ξ ω

theorem hasFDerivAt_partition
    (fam : FiniteExponentialFamily Ω Param) (ξ : Param) :
    HasFDerivAt fam.partition (fam.partitionFDeriv ξ) ξ := by
  have h := HasFDerivAt.sum (u := (Finset.univ : Finset Ω))
    (fun ω (_ : ω ∈ (Finset.univ : Finset Ω)) =>
      fam.hasFDerivAt_unnormalizedWeight ξ ω)
  have hfun : fam.partition =
      ∑ ω, fun η => fam.unnormalizedWeight η ω := by
    funext η
    simp only [partition, Finset.sum_apply]
  rw [hfun]
  simpa only [partitionFDeriv] using h

theorem partitionFDeriv_apply
    (fam : FiniteExponentialFamily Ω Param) (ξ direction : Param) :
    fam.partitionFDeriv ξ direction =
      (1 / fam.scale) *
        ∑ ω, fam.unnormalizedWeight ξ ω * fam.score ω direction := by
  simp only [partitionFDeriv, ContinuousLinearMap.sum_apply,
    fam.unnormalizedWeightFDeriv_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- Fréchet derivative of an unnormalized moment numerator. -/
def rawMomentFDeriv (fam : FiniteExponentialFamily Ω Param)
    (F : Ω → ℝ) (ξ : Param) : Param →L[ℝ] ℝ :=
  ∑ ω, F ω • fam.unnormalizedWeightFDeriv ξ ω

theorem hasFDerivAt_rawMoment
    (fam : FiniteExponentialFamily Ω Param) (F : Ω → ℝ) (ξ : Param) :
    HasFDerivAt (fam.rawMoment F) (fam.rawMomentFDeriv F ξ) ξ := by
  have h := HasFDerivAt.sum (u := (Finset.univ : Finset Ω))
    (fun ω (_ : ω ∈ (Finset.univ : Finset Ω)) =>
      (fam.hasFDerivAt_unnormalizedWeight ξ ω).mul_const (F ω))
  have hfun : fam.rawMoment F =
      ∑ ω, fun η => fam.unnormalizedWeight η ω * F ω := by
    funext η
    simp only [rawMoment, Finset.sum_apply]
  rw [hfun]
  simpa only [rawMomentFDeriv] using h

theorem rawMomentFDeriv_apply
    (fam : FiniteExponentialFamily Ω Param) (F : Ω → ℝ)
    (ξ direction : Param) :
    fam.rawMomentFDeriv F ξ direction =
      (1 / fam.scale) *
        ∑ ω, fam.unnormalizedWeight ξ ω * F ω * fam.score ω direction := by
  simp only [rawMomentFDeriv, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul,
    fam.unnormalizedWeightFDeriv_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- The derivative furnished directly by the quotient rule. -/
def quotientMomentFDeriv (fam : FiniteExponentialFamily Ω Param)
    (F : Ω → ℝ) (ξ : Param) : Param →L[ℝ] ℝ :=
  fam.baseMass •
    (fam.rawMoment F ξ •
        (-((fam.partition ξ) ^ 2)⁻¹ • fam.partitionFDeriv ξ) +
      (fam.partition ξ)⁻¹ • fam.rawMomentFDeriv F ξ)

theorem hasFDerivAt_moment_quotient
    (fam : FiniteExponentialFamily Ω Param) (F : Ω → ℝ) (ξ : Param) :
    HasFDerivAt (fam.moment F) (fam.quotientMomentFDeriv F ξ) ξ := by
  have hpart := fam.hasFDerivAt_partition ξ
  have hinv : HasFDerivAt (fun η => (fam.partition η)⁻¹)
      (-((fam.partition ξ) ^ 2)⁻¹ • fam.partitionFDeriv ξ) ξ := by
    exact (hasDerivAt_inv (fam.partition_ne_zero ξ)).comp_hasFDerivAt ξ hpart
  have hproduct := (fam.hasFDerivAt_rawMoment F ξ).mul hinv
  have hscaled := hproduct.const_mul fam.baseMass
  have heq : fam.moment F = fun η =>
      fam.baseMass * (fam.rawMoment F η * (fam.partition η)⁻¹) := by
    funext η
    rw [fam.moment_eq_normalizedRawMoment F η]
    simp only [div_eq_mul_inv]
    ring
  rw [heq]
  simpa only [quotientMomentFDeriv, div_eq_mul_inv, Pi.mul_apply] using hscaled

/-- Covariance under the normalized tilted law. -/
def covariance (fam : FiniteExponentialFamily Ω Param)
    (F G : Ω → ℝ) (ξ : Param) : ℝ :=
  (fam.tiltedProbability ξ).covariance F G

theorem partition_contDiff (fam : FiniteExponentialFamily Ω Param) :
    ContDiff ℝ ⊤ fam.partition := by
  apply ContDiff.sum
  intro ω _
  exact (contDiff_const.mul (((fam.score ω).contDiff.div_const fam.scale).exp))

theorem probabilityMass_contDiff (fam : FiniteExponentialFamily Ω Param) (ω : Ω) :
    ContDiff ℝ ⊤ (fun ξ => fam.probabilityMass ξ ω) := by
  apply ContDiff.div
  · exact contDiff_const.mul (((fam.score ω).contDiff.div_const fam.scale).exp)
  · exact fam.partition_contDiff
  · exact fam.partition_ne_zero

theorem activeWeight_contDiff (fam : FiniteExponentialFamily Ω Param) (ω : Ω) :
    ContDiff ℝ ⊤ (fun ξ => fam.activeWeight ξ ω) := by
  exact contDiff_const.mul (fam.probabilityMass_contDiff ω)

/-- Every finite active moment is smooth in the parameter. -/
theorem moment_contDiff (fam : FiniteExponentialFamily Ω Param) (F : Ω → ℝ) :
    ContDiff ℝ ⊤ (fam.moment F) := by
  apply ContDiff.sum
  intro ω _
  exact (fam.activeWeight_contDiff ω).mul contDiff_const

/-- The covariance with the score, as a continuous linear functional of
the parameter direction. -/
def covarianceScore (fam : FiniteExponentialFamily Ω Param)
    (F : Ω → ℝ) (ξ : Param) : Param →L[ℝ] ℝ :=
  ∑ ω, (fam.probabilityMass ξ ω *
      (F ω - fam.expectation F ξ)) • fam.score ω

theorem covarianceScore_apply (fam : FiniteExponentialFamily Ω Param)
    (F : Ω → ℝ) (ξ direction : Param) :
    fam.covarianceScore F ξ direction =
      fam.covariance F (fun ω => fam.score ω direction) ξ := by
  simp only [covarianceScore, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [covariance, FiniteProbability.covariance, expectation,
    FiniteProbability.expect, FiniteProbability.expect]
  simp only [FiniteProbability.expect]
  calc
    (∑ ω, fam.probabilityMass ξ ω * (F ω -
        ∑ η, fam.probabilityMass ξ η * F η) * fam.score ω direction)
        = (∑ ω, fam.probabilityMass ξ ω * (F ω * fam.score ω direction)) -
          (∑ η, fam.probabilityMass ξ η * F η) *
            (∑ ω, fam.probabilityMass ξ ω * fam.score ω direction) := by
              rw [Finset.mul_sum]
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro ω _
              ring
    _ = (∑ ω, fam.probabilityMass ξ ω * (F ω * fam.score ω direction)) -
          (∑ η, fam.probabilityMass ξ η * F η) *
            (∑ ω, fam.probabilityMass ξ ω * fam.score ω direction) := rfl

theorem covariance_eq_rawMoments
    (fam : FiniteExponentialFamily Ω Param) (F G : Ω → ℝ) (ξ : Param) :
    fam.covariance F G ξ =
      fam.rawMoment (fun ω => F ω * G ω) ξ / fam.partition ξ -
        (fam.rawMoment F ξ / fam.partition ξ) *
          (fam.rawMoment G ξ / fam.partition ξ) := by
  rw [covariance, FiniteProbability.covariance]
  change fam.expectation (fun ω => F ω * G ω) ξ -
      fam.expectation F ξ * fam.expectation G ξ = _
  rw [fam.expectation_eq_rawMoment_div_partition,
    fam.expectation_eq_rawMoment_div_partition,
    fam.expectation_eq_rawMoment_div_partition]

theorem quotientMomentFDeriv_apply
    (fam : FiniteExponentialFamily Ω Param) (F : Ω → ℝ)
    (ξ direction : Param) :
    fam.quotientMomentFDeriv F ξ direction =
      (fam.baseMass / fam.scale) *
        fam.covariance F (fun ω => fam.score ω direction) ξ := by
  simp only [quotientMomentFDeriv, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, smul_eq_mul]
  rw [fam.partitionFDeriv_apply ξ direction,
    fam.rawMomentFDeriv_apply F ξ direction,
    fam.covariance_eq_rawMoments F (fun ω => fam.score ω direction) ξ]
  simp only [rawMoment]
  field_simp [fam.partition_ne_zero ξ, fam.scale_ne_zero]
  ring

theorem quotientMomentFDeriv_eq_covarianceScore
    (fam : FiniteExponentialFamily Ω Param) (F : Ω → ℝ) (ξ : Param) :
    fam.quotientMomentFDeriv F ξ =
      (fam.baseMass / fam.scale) • fam.covarianceScore F ξ := by
  ext direction
  rw [fam.quotientMomentFDeriv_apply F ξ direction,
    ContinuousLinearMap.smul_apply, smul_eq_mul,
    fam.covarianceScore_apply F ξ direction]

/-- Exact covariance-Jacobian identity for a finite active moment. -/
theorem hasFDerivAt_moment_covariance
    (fam : FiniteExponentialFamily Ω Param) (F : Ω → ℝ) (ξ : Param) :
    HasFDerivAt (fam.moment F)
      ((fam.baseMass / fam.scale) • fam.covarianceScore F ξ) ξ := by
  rw [← fam.quotientMomentFDeriv_eq_covarianceScore F ξ]
  exact fam.hasFDerivAt_moment_quotient F ξ

/-- Evaluation form of the Jacobian identity:
`D moment_F(ξ)[direction] = q/L * Cov(F, score direction)`. -/
theorem fderiv_moment_apply
    (fam : FiniteExponentialFamily Ω Param) (F : Ω → ℝ)
    (ξ direction : Param) :
    fderiv ℝ (fam.moment F) ξ direction =
      (fam.baseMass / fam.scale) *
        fam.covariance F (fun ω => fam.score ω direction) ξ := by
  rw [(fam.hasFDerivAt_moment_covariance F ξ).fderiv,
    ContinuousLinearMap.smul_apply, smul_eq_mul,
    fam.covarianceScore_apply F ξ direction]

end FiniteExponentialFamily

end

end Erdos390.Full
