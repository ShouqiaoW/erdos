import Erdos390.Full.PaperExactSchurRawSlow
import Erdos390.Full.PaperBridgePrimewiseRate

/-!
# Effective-norm bound for the literal paper vector field

The ODE continuation argument uses the effective max norm, not the ambient
Euclidean norm.  This file proves the exact finite identity which converts
the Schur solution into its three paper components:

* the prime-by-prime effective fugacity;
* the nuisance regression coefficient;
* the stored slow coordinate `w * lambda`.

It then shows that uniform bounds for those three components of every
solution of the *actual* Schur equation imply the required effective
velocity bound.  Thus Proposition 8.7 can consume the literal quantitative
outputs of Lemmas 8.4--8.6 without assuming a norm bound for the already
assembled vector field.
-/

open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Exact effective norm of a Schur residual.  In particular, the nuisance
term enters with the norm of the genuine finite regression `R u`; no
coordinate comparison or asymptotic estimate occurs in this identity. -/
theorem norm_effectiveParamEquiv_symm_schurResidual
    (R : B.MainSpace → B.NuisanceSpace) (u : B.MainSpace) :
    ‖B.effectiveParamEquiv.symm (B.schurResidual R u)‖ =
      max
        (max
          ‖fun p : ArithmeticBandGeometry.BandPrime
              B.sampleData.n B.sampleData.W ↦
            (B.rawGaugeOfMain u).1 (B.partition.band p) +
              (u MainCoord.slow / B.w) * B.primeDeviation p‖
          ‖R u‖)
        |u MainCoord.slow| := by
  rw [B.norm_effectiveParamEquiv_symm,
    B.norm_effectiveCoordinateCLM_eq,
    B.nuisanceParameter_schurResidual,
    B.schurResidual_slow, norm_neg]
  have hprime :
      (fun p : ArithmeticBandGeometry.BandPrime
          B.sampleData.n B.sampleData.W ↦
        B.effectivePrimeCoefficient (B.schurResidual R u) p) =
      (fun p ↦
        (B.rawGaugeOfMain u).1 (B.partition.band p) +
          (u MainCoord.slow / B.w) * B.primeDeviation p) := by
    funext p
    exact B.schurResidual_effectivePrimeCoefficient R u p
  rw [hprime]

/-- The effective velocity follows from componentwise bounds on the unique
solution of the literal Schur equation.  The hypotheses are deliberately
formulated for an arbitrary `u` satisfying that equation, rather than for
the vector field itself.  This is the exact interface exported by the
weighted inverse, compensated slow, and nuisance-regression estimates. -/
theorem effectiveVelocity_le_of_exactSchur_solution_component_bounds
    [Nonempty Head]
    (xi : B.ParamSpace) (Delta : Band → ℝ)
    {gammaFull gammaNuisance speed : ℝ}
    (hgammaFull : 0 < gammaFull)
    (hFull : B.vectorFamily.HasCovarianceGap gammaFull xi)
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hprime : ∀ u,
      B.exactSchurCovarianceOperator xi hgammaNuisance hGamma u =
          B.mainPart (B.normalizedTarget Delta) →
        ‖fun p : ArithmeticBandGeometry.BandPrime
              B.sampleData.n B.sampleData.W ↦
            (B.rawGaugeOfMain u).1 (B.partition.band p) +
              (u MainCoord.slow / B.w) * B.primeDeviation p‖ ≤ speed)
    (hnuisance : ∀ u,
      B.exactSchurCovarianceOperator xi hgammaNuisance hGamma u =
          B.mainPart (B.normalizedTarget Delta) →
        ‖B.exactNuisanceRegression xi hgammaNuisance hGamma u‖ ≤ speed)
    (hslow : ∀ u,
      B.exactSchurCovarianceOperator xi hgammaNuisance hGamma u =
          B.mainPart (B.normalizedTarget Delta) →
        |u MainCoord.slow| ≤ speed) :
    ‖B.effectiveParamEquiv.symm
        (B.vectorFamily.vectorField (B.targetVector Delta) xi)‖ ≤ speed := by
  let v := B.vectorFamily.vectorField (B.targetVector Delta) xi
  let u := B.mainPart v
  let R := B.exactNuisanceRegression xi hgammaNuisance hGamma
  have hsolve :=
    B.vectorField_eq_schurResidual_and_mainEquation xi Delta
      hgammaFull hFull hgammaNuisance hGamma
  have hv : v = B.schurResidual R u := by
    simpa only [v, u, R] using hsolve.1
  have hu : B.exactSchurCovarianceOperator xi hgammaNuisance hGamma u =
      B.mainPart (B.normalizedTarget Delta) := by
    simpa only [u, v] using hsolve.2
  rw [show B.vectorFamily.vectorField (B.targetVector Delta) xi = v by rfl,
    hv, B.norm_effectiveParamEquiv_symm_schurResidual]
  exact max_le (max_le (hprime u hu) (hnuisance u hu)) (hslow u hu)

/-- Primewise marked-row transfer for the literal vector field.  The fast
Schur residual and the compensated slow score are kept separate, exactly as
in the proof of Proposition 8.7.  A `O(w rho)` compensated row multiplied by
the proved `O(1/w)` slow velocity contributes only `O(rho)`; no endpoint
estimate is assumed here. -/
theorem vectorField_markedRow_le_of_fast_compensated
    [Nonempty Head]
    (xi : B.ParamSpace) (Delta : Band → ℝ)
    {gammaFull gammaNuisance : ℝ}
    (hgammaFull : 0 < gammaFull)
    (hFull : B.vectorFamily.HasCovarianceGap gammaFull xi)
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (p : ℕ) (qFast qReg : B.RawBandGauge) (lambda : ℝ)
    {Cfast Ccomp Cslow rho : ℝ}
    (hCslow : 0 ≤ Cslow)
    (hq : B.rawGaugeOfMain
        (B.mainPart (B.vectorFamily.vectorField
          (B.targetVector Delta) xi)) = qFast - lambda • qReg)
    (hslowCoord :
      B.mainPart (B.vectorFamily.vectorField
          (B.targetVector Delta) xi) MainCoord.slow = B.w * lambda)
    (hfast :
      |(B.tiltedLaw xi).covariance (B.markedValuation p)
        (B.nuisanceResidualScore xi hgammaNuisance hGamma
          (B.bandRegressionScore qFast))| ≤ Cfast * rho)
    (hcompensated :
      |(B.tiltedLaw xi).covariance (B.markedValuation p)
        (B.actualCompensatedScore xi hgammaNuisance hGamma qReg)| ≤
          (Ccomp * rho) * B.w)
    (hlambda : |lambda| ≤ Cslow / B.w) :
    |B.vectorFamily.scalarFamily.covariance
        (B.markedValuation p)
        (fun m ↦ B.vectorFamily.scalarFamily.score m
          (B.vectorFamily.vectorField (B.targetVector Delta) xi)) xi| ≤
      (Cfast + Cslow * Ccomp) * rho := by
  let v := B.vectorFamily.vectorField (B.targetVector Delta) xi
  let u := B.mainPart v
  let R := B.exactNuisanceRegression xi hgammaNuisance hGamma
  have hv :=
    (B.vectorField_eq_schurResidual_and_mainEquation xi Delta
      hgammaFull hFull hgammaNuisance hGamma).1
  have hscore :=
    B.vectorScore_exactSchurResidual_fast_add_compensated
      xi hgammaNuisance hGamma u qFast qReg lambda
      (by simpa only [u, v] using hq)
      (by simpa only [u, v] using hslowCoord)
  change |(B.tiltedLaw xi).covariance (B.markedValuation p)
    (fun m ↦ B.vectorFamily.scalarFamily.score m v)| ≤ _
  have hv' : v = B.schurResidual R u := by
    simpa only [v, u, R] using hv
  rw [hv']
  change |(B.tiltedLaw xi).covariance (B.markedValuation p)
    (fun m ↦ B.vectorFamily.scalarFamily.score m
      (B.schurResidual R u))| ≤ _
  have hscore' :
      (fun m ↦ B.vectorFamily.scalarFamily.score m
        (B.schurResidual R u)) =
      fun m ↦
        B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore qFast) m +
          lambda *
            B.actualCompensatedScore xi hgammaNuisance hGamma qReg m := by
    simpa only [R] using hscore
  rw [hscore', FiniteProbability.covariance_add_right,
    FiniteProbability.covariance_smul_right]
  exact Erdos390.effective_prime_velocity_bound
    ((B.tiltedLaw xi).covariance (B.markedValuation p)
      (B.nuisanceResidualScore xi hgammaNuisance hGamma
        (B.bandRegressionScore qFast)))
    ((B.tiltedLaw xi).covariance (B.markedValuation p)
      (B.actualCompensatedScore xi hgammaNuisance hGamma qReg))
    lambda B.w (Cfast * rho) (Ccomp * rho) Cslow
    B.w_pos hCslow hfast hcompensated hlambda |>.trans_eq (by ring)

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
