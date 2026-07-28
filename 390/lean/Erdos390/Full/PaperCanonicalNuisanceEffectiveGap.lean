import Erdos390.Full.PaperCanonicalBaselineBridge
import Erdos390.Full.PaperPhysicalIntervalNuisanceGap
import Erdos390.Full.PaperEffectiveBallCovarianceGap
import Erdos390.Full.FixedFiniteMixtureFullUniform

/-!
# Canonical finite nuisance gap on a preselected effective box

This file keeps the baseline covariance at the actual finite `n`.  It first
uses the positive barycentric cell masses and the two separated physical
pools to obtain a literal baseline nuisance gap, and then transfers that gap
to a bounded effective tilt by the exact finite density-ratio inequality.
No limiting mixture is selected or assumed to exist.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel PaperGuardCensus

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The quadratic form of the literal nuisance operator is the scalar
variance of the corresponding nuisance linear statistic under the actual
finite tilted law. -/
theorem tiltedLaw_covariance_nuisanceStatistic [Nonempty Head]
    (xi : B.ParamSpace) (z : B.NuisanceSpace) :
    (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m))
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) =
      inner ℝ z (B.nuisanceCovarianceOperator xi z) := by
  rw [B.nuisanceCovarianceOperator_quadratic]
  rfl

/-- The explicit nuisance gap used on an effective box of radius `a`. -/
def canonicalEffectiveNuisanceGamma [Nonempty Head]
    (I : PhysicalIntervals) (U a : ℝ)
    (T : BarycentricTarget B.sampleData) : ℝ :=
  Real.exp (-2 *
      ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
        B.nuisanceStatisticCoefficient U) * a)) *
    B.uniformNuisanceGap T.cellMassMargin
      (Real.log (I.lower .plus) - Real.log (I.upper .minus))
      (Real.log U)

theorem canonicalEffectiveNuisanceGamma_pos [Nonempty Head]
    (I : PhysicalIntervals) (U a : ℝ)
    (T : BarycentricTarget B.sampleData) :
    0 < B.canonicalEffectiveNuisanceGamma I U a T := by
  unfold canonicalEffectiveNuisanceGamma
  exact mul_pos (Real.exp_pos _)
    (B.uniformNuisanceGap_pos T.cellMassMargin_pos
      (fixedInterval_separation_pos I))

/-- Uniform nuisance gap on a preselected effective box, specialized to the
actual canonical barycentric baseline.  The gap is finite-`n` and explicit;
its positive density-ratio factor may depend on the already selected box
radius `a`, but there is no convergence hypothesis on the baseline weights.
-/
theorem nuisanceCovarianceOperator_effectiveBox_canonicalBaseline
    [Nonempty Head]
    (I : PhysicalIntervals) {U a : ℝ}
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (T : BarycentricTarget B.sampleData)
    (hbaseline : B.baseline = T.baseline)
    (hW : 1 < B.sampleData.W)
    (xi : B.ParamSpace) (hxi : B.paperEffectiveSize xi ≤ a)
    (z : B.NuisanceSpace) :
    (Real.exp (-2 *
          ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
            B.nuisanceStatisticCoefficient U) * a)) *
        B.uniformNuisanceGap T.cellMassMargin
          (Real.log (I.lower .plus) - Real.log (I.upper .minus))
          (Real.log U)) * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z) := by
  let gamma : ℝ := B.uniformNuisanceGap T.cellMassMargin
    (Real.log (I.lower .plus) - Real.log (I.upper .minus))
    (Real.log U)
  let K : ℝ :=
    (PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
      B.nuisanceStatisticCoefficient U) * a
  let F : B.sampleData.Sample → ℝ :=
    fun m ↦ inner ℝ z (B.nuisanceStatistic m)
  have hweight : ∀ c : Cell Head,
      T.cellMassMargin ≤ B.baseline.normalizedCellMass c := by
    intro c
    rw [hbaseline]
    exact T.cellMassMargin_le c
  have hbaseOperator : gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator 0 z) := by
    exact B.nuisanceCovarianceOperator_zero_fixedIntervals I
      T.cellMassMargin_pos hlowerOne hupperU hlo hhi hweight z
  have hbase : gamma * ‖z‖ ^ 2 ≤
      B.baselineSigmaProbability.covariance F F := by
    rw [B.baselineSigmaProbability_eq_tiltedLaw_zero]
    dsimp only [F]
    rw [B.tiltedLaw_covariance_nuisanceStatistic 0 z]
    exact hbaseOperator
  have hscore : ∀ m : B.sampleData.Sample,
      |B.scaledBridgeScore xi m| ≤ K := by
    intro m
    exact B.effectiveScoreBound_of_paperEffectiveSize
      hU hW (fun sigma ↦ (hhi sigma).trans_le
        (FixedFiniteMixtureFullUniform.physicalBound_mono
          (hupperU sigma) B.sampleData.n)) xi hxi m
  have hdom :=
    B.baselineSigmaProbability.exp_neg_two_mul_covariance_self_le_exponentialTilt
      F (B.scaledBridgeScore xi) K hscore
  have hfactor : 0 ≤ Real.exp (-2 * K) := (Real.exp_pos _).le
  have hchain : Real.exp (-2 * K) * (gamma * ‖z‖ ^ 2) ≤
      ((B.baselineSigmaProbability).exponentialTilt
        (B.scaledBridgeScore xi)).covariance F F :=
    (mul_le_mul_of_nonneg_left hbase hfactor).trans hdom
  rw [← B.tiltedLaw_eq_exponentialTilt_baseline] at hchain
  rw [B.tiltedLaw_covariance_nuisanceStatistic xi z] at hchain
  simpa only [gamma, K, mul_assoc] using hchain

/-- Named-gap form of
`nuisanceCovarianceOperator_effectiveBox_canonicalBaseline`, convenient for
the exact Schur regression constructors. -/
theorem canonicalEffectiveNuisanceGapProof
    [Nonempty Head]
    (I : PhysicalIntervals) {U a : ℝ}
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (T : BarycentricTarget B.sampleData)
    (hbaseline : B.baseline = T.baseline)
    (hW : 1 < B.sampleData.W)
    (xi : B.ParamSpace) (hxi : B.paperEffectiveSize xi ≤ a) :
    ∀ z : B.NuisanceSpace,
      B.canonicalEffectiveNuisanceGamma I U a T * ‖z‖ ^ 2 ≤
        inner ℝ z (B.nuisanceCovarianceOperator xi z) := by
  intro z
  simpa only [canonicalEffectiveNuisanceGamma, mul_assoc] using
    B.nuisanceCovarianceOperator_effectiveBox_canonicalBaseline I hU
      hlowerOne hupperU hlo hhi T hbaseline hW xi hxi z

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
