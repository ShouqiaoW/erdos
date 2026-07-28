import Erdos390.Full.PaperMainRawGaugeCoordinates

/-!
# Exact raw-gauge/slow form of the finite Schur regression

This file identifies the nuisance regression occurring in the actual Schur
operator with the regression of the literal raw-gauge/slow score.  It is an
exact finite-dimensional identity, and is the first attachment needed to
turn the two-stage estimates of Lemma 8.6 into bounds for the Proposition
8.7 vector field.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The exponential-family score of a pure nuisance parameter is exactly
the Euclidean pairing with the literal physical/head statistic. -/
theorem vectorScore_nuisanceEmbed_eq_nuisanceStatistic [Nonempty Head]
    (z : B.NuisanceSpace) (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.score m (B.nuisanceEmbed z) =
      inner ℝ z (B.nuisanceStatistic m) := by
  rw [B.vectorScore_eq_effectivePrime_add_nuisance]
  have hnuisance : B.nuisanceParameter (B.nuisanceEmbed z) = z := by
    apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
    funext c
    cases c <;> rfl
  simp_rw [B.nuisanceEmbed_effectivePrimeCoefficient]
  rw [hnuisance]
  simp

/-- The main-to-nuisance covariance block is the covariance vector of the
literal main score. -/
theorem crossCovarianceOperator_eq_nuisanceCovarianceVector_mainScore
    [Nonempty Head]
    (xi : B.ParamSpace) (u : B.MainSpace) :
    B.crossCovarianceOperator xi u =
      B.nuisanceCovarianceVector xi
        (fun m ↦ B.vectorFamily.scalarFamily.score m (B.mainEmbed u)) := by
  apply ext_inner_left ℝ
  intro z
  have hcross :
      inner ℝ z (B.crossCovarianceOperator xi u) =
        inner ℝ (B.nuisanceEmbed z)
          (B.covarianceOperator xi (B.mainEmbed u)) := by
    simpa only [crossCovarianceOperator,
      ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.adjoint_inner_right
        B.nuisanceEmbeddingCLM z
        (B.covarianceOperator xi (B.mainEmbeddingCLM u)))
  rw [hcross, B.inner_covarianceOperator,
    B.inner_nuisanceCovarianceVector]
  congr 1
  funext m
  calc
    inner ℝ (B.nuisanceEmbed z) (B.statistic m) =
        inner ℝ (B.statistic m) (B.nuisanceEmbed z) :=
      real_inner_comm _ _
    _ = inner ℝ z (B.nuisanceStatistic m) := by
      simpa only [VectorExponentialFamily.scalarFamily,
        innerSL_apply_apply] using
          B.vectorScore_nuisanceEmbed_eq_nuisanceStatistic z m
  funext m
  simpa only [VectorExponentialFamily.scalarFamily,
    innerSL_apply_apply] using
      (real_inner_comm (B.mainEmbed u) (B.statistic m)).symm

/-- The nuisance component of the exact Schur residual is the actual finite
regression coefficient of the literal main score. -/
theorem exactNuisanceRegression_eq_nuisanceCoefficient_mainScore
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    B.exactNuisanceRegression xi hgamma hgap u =
      B.nuisanceCoefficientOfScore xi hgamma hgap
        (fun m ↦ B.vectorFamily.scalarFamily.score m (B.mainEmbed u)) := by
  apply B.nuisanceCovarianceOperator_injective xi hgamma hgap
  rw [B.exactNuisanceRegression_solve,
    B.nuisanceCoefficientOfScore_solve]
  exact B.crossCovarianceOperator_eq_nuisanceCovarianceVector_mainScore xi u

/-- Consequently the score of the exact Schur residual is literally the
nuisance residual of the raw main score. -/
theorem vectorScore_exactSchurResidual_eq_nuisanceResidual_mainScore
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    (fun m ↦ B.vectorFamily.scalarFamily.score m
      (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) u)) =
      B.nuisanceResidualScore xi hgamma hgap
        (fun m ↦ B.vectorFamily.scalarFamily.score m (B.mainEmbed u)) := by
  funext m
  rw [B.vectorScore_schurResidual_eq_rawGauge_slow_nuisance]
  unfold nuisanceResidualScore
  rw [← B.exactNuisanceRegression_eq_nuisanceCoefficient_mainScore]
  change _ =
    B.vectorFamily.scalarFamily.score m (B.mainEmbed u) -
      inner ℝ (B.exactNuisanceRegression xi hgamma hgap u)
        (B.nuisanceStatistic m)
  rw [B.vectorScore_mainEmbed_eq_rawGauge_add_slow]

/-- Exact fast/slow score decomposition used by the full block inverse.  If
the raw gauge coordinate has the algebraic form

`q_fast - lambda * q_reg`

and the stored slow coordinate is `w * lambda`, then the Schur-residual
score is the nuisance-projected fast score plus `lambda` times the literal
two-stage compensated score.  This is the finite identity behind the marked
row integration in Proposition 8.7. -/
theorem vectorScore_exactSchurResidual_fast_add_compensated
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) (qFast qReg : B.RawBandGauge) (lambda : ℝ)
    (hq : B.rawGaugeOfMain u = qFast - lambda • qReg)
    (hslow : u MainCoord.slow = B.w * lambda) :
    (fun m ↦ B.vectorFamily.scalarFamily.score m
      (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) u)) =
      fun m ↦
        B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore qFast) m +
          lambda * B.actualCompensatedScore xi hgamma hgap qReg m := by
  rw [B.vectorScore_exactSchurResidual_eq_nuisanceResidual_mainScore]
  have hinput :
      (fun m ↦ B.vectorFamily.scalarFamily.score m (B.mainEmbed u)) =
        fun m ↦ B.bandRegressionScore qFast m +
          lambda * B.postBandPrimeScore qReg m := by
    funext m
    rw [B.vectorScore_mainEmbed_eq_rawGauge_add_slow, hq,
      B.bandRegressionScore_sub,
      B.bandRegressionScore_smul, hslow,
      mul_div_cancel_left₀ lambda (ne_of_gt B.w_pos),
      B.postBandPrimeScore_eq_slow_sub_bandRegression]
    ring
  rw [hinput, B.nuisanceResidualScore_add,
    B.nuisanceResidualScore_smul]
  rfl

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
