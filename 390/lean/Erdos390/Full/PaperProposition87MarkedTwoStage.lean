import Erdos390.Full.PaperVectorFieldEffectiveBound
import Erdos390.Full.PaperExactTwoStageTargetSolve

/-!
# Marked rows for the literal two-stage Proposition 8.7 solve

This file removes the last algebraic indirection between the two rows
estimated in the paper and the marked row of the actual ODE vector field.
The fast row is evaluated at the inverse solution of the projected target;
the slow row is evaluated at the compensated regression score.  The exact
Schur equation supplies their coefficients, and the proved compensated
variance bound controls the slow coefficient.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Assemble the marked row of the actual vector field from the literal
fast and compensated-slow rows.

There is no assumed vector-field row in this theorem.  The identity of the
fast coordinate, the coefficient of the compensated score, and the bound
on that coefficient are all consequences of the exact Schur solve. -/
theorem vectorField_markedRow_le_of_twoStage_rows
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (Delta : Band → ℝ)
    {gammaFull gammaNuisance : ℝ}
    (hgammaFull : 0 < gammaFull)
    (hFull : B.vectorFamily.HasCovarianceGap gammaFull xi)
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q =
      B.actualBandSchurLinearMap xi hgammaNuisance hGamma q)
    (p : ℕ) {Vlower Tslow Cfast Cslow rho : ℝ}
    (hVlower : 0 < Vlower) (hTslow : 0 ≤ Tslow)
    (hvariance : Vlower ≤
      B.actualTwoStageCompensatedVariance
        xi hgammaNuisance hGamma e)
    (htarget : |B.compensatedNormalizedTarget
      xi hgammaNuisance hGamma e Delta| ≤ Tslow)
    (hfast :
      |(B.tiltedLaw xi).covariance (B.markedValuation p)
        (B.nuisanceResidualScore xi hgammaNuisance hGamma
          (B.bandRegressionScore
            (e.symm (B.projectedNormalizedTargetBand Delta))))| ≤
        Cfast * rho)
    (hcompensated :
      |(B.tiltedLaw xi).covariance (B.markedValuation p)
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e)| ≤
        (Cslow * rho) * B.w) :
    |B.vectorFamily.scalarFamily.covariance
        (B.markedValuation p)
        (fun m ↦ B.vectorFamily.scalarFamily.score m
          (B.vectorFamily.vectorField (B.targetVector Delta) xi)) xi| ≤
      (Cfast + (Tslow / Vlower) * (Cslow * B.w)) * rho := by
  let v := B.vectorFamily.vectorField (B.targetVector Delta) xi
  let u := B.mainPart v
  let qFast := e.symm (B.projectedNormalizedTargetBand Delta)
  let qReg := B.actualBandRegression xi hgammaNuisance hGamma e
  let lambda := u MainCoord.slow / B.w
  have hu : B.exactSchurCovarianceOperator xi hgammaNuisance hGamma u =
      B.mainPart (B.normalizedTarget Delta) := by
    simpa only [u, v] using
      (B.vectorField_eq_schurResidual_and_mainEquation
        xi Delta hgammaFull hFull hgammaNuisance hGamma).2
  have hfastEq : B.fastGaugeOfMain
      xi hgammaNuisance hGamma e u = qFast := by
    simpa only [qFast] using
      B.fastGauge_eq_inverse_projectedTarget
        xi hgammaNuisance hGamma e he Delta u hu
  have hq : B.rawGaugeOfMain u = qFast - lambda • qReg := by
    rw [← hfastEq]
    simpa only [lambda, qReg] using
      B.rawGauge_eq_fastGauge_sub_regression
        xi hgammaNuisance hGamma e u
  have hstored : u MainCoord.slow = B.w * lambda := by
    simpa only [lambda] using B.slow_eq_w_mul_slow_div u
  have hlambda : |lambda| ≤ Tslow / Vlower := by
    simpa only [lambda] using
      B.abs_slow_div_le_of_variance_target_bounds
        xi hgammaNuisance hGamma e he Delta u hu
          hVlower hvariance hTslow htarget
  have hstoredNonneg : 0 ≤ B.w * (Tslow / Vlower) := by
    exact mul_nonneg B.w_pos.le (div_nonneg hTslow hVlower.le)
  have hlambdaStored :
      |lambda| ≤ (B.w * (Tslow / Vlower)) / B.w := by
    convert hlambda using 1
    field_simp [B.w_pos.ne']
  have hcompensated' :
      |(B.tiltedLaw xi).covariance (B.markedValuation p)
        (B.actualCompensatedScore
          xi hgammaNuisance hGamma qReg)| ≤
        (Cslow * rho) * B.w := by
    simpa only [qReg, actualTwoStageCompensatedScore] using hcompensated
  have hrow :=
    B.vectorField_markedRow_le_of_fast_compensated
      xi Delta hgammaFull hFull hgammaNuisance hGamma
      p qFast qReg lambda hstoredNonneg hq hstored hfast
      hcompensated' hlambdaStored
  have hrow' := hrow.trans_eq (show
      (Cfast + (B.w * (Tslow / Vlower)) * Cslow) * rho =
        (Cfast + (Tslow / Vlower) * (Cslow * B.w)) * rho by ring)
  simpa only [qFast, qReg, lambda, v, u] using hrow'

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
