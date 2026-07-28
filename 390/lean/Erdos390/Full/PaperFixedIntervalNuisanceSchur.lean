import Erdos390.Full.PaperPhysicalIntervalNuisanceGap

/-!
# Fixed-interval nuisance regression and full Schur gap

This file replaces the earlier sample-cardinality diameter in the Schur
attachment by the fixed physical-interval geometry.  At an arbitrary finite
tilt, a concrete `l1` estimate gives the nuisance half-gap.  The exact
`Gamma^{-1} B` regression, its norm bound, and the full covariance gap then
follow from the already proved finite block algebra.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel PaperGuardCensus

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Half of the explicit fixed-interval baseline nuisance gap. -/
def fixedIntervalNuisanceGamma [Nonempty Head]
    (I : PhysicalIntervals) (U lambda : ℝ) : ℝ :=
  B.uniformNuisanceGap lambda
    (Real.log (I.lower .plus) - Real.log (I.upper .minus))
    (Real.log U) / 2

theorem fixedIntervalNuisanceGamma_pos [Nonempty Head]
    (I : PhysicalIntervals) {U lambda : ℝ} (hlambda : 0 < lambda) :
    0 < B.fixedIntervalNuisanceGamma I U lambda := by
  unfold fixedIntervalNuisanceGamma
  exact div_pos
    (B.uniformNuisanceGap_pos hlambda (fixedInterval_separation_pos I))
    (by norm_num)

/-- Canonical proof term for the fixed-interval nuisance half-gap at the
actual finite tilt. -/
def fixedIntervalNuisanceGapProof [Nonempty Head]
    (I : PhysicalIntervals) {U lambda epsilon : ℝ}
    (hlambda : 0 < lambda)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hweight : ∀ c : Cell Head,
      lambda ≤ B.baseline.normalizedCellMass c)
    (xi : B.ParamSpace)
    (hl1 : B.nuisanceFineBaseline.weightL1Distance
      (B.vectorFamily.probabilityMass xi) ≤ epsilon)
    (hsmall : epsilon * B.fixedIntervalNuisanceDiameter U ^ 2 ≤
      B.fixedIntervalNuisanceGamma I U lambda) :
    ∀ z,
      B.fixedIntervalNuisanceGamma I U lambda * ‖z‖ ^ 2 ≤
        inner ℝ z (B.nuisanceCovarianceOperator xi z) :=
  fun z ↦ B.nuisanceCovarianceOperator_fixedIntervals_half_gap_of_l1
    I hlambda hlowerOne hupperU hlo hhi hweight xi hl1
      (by simpa only [fixedIntervalNuisanceGamma] using hsmall) z

/-- The actual finite nuisance regression using the fixed-interval gap. -/
def fixedIntervalNuisanceRegression [Nonempty Head]
    (I : PhysicalIntervals) {U lambda epsilon : ℝ}
    (hlambda : 0 < lambda)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hweight : ∀ c : Cell Head,
      lambda ≤ B.baseline.normalizedCellMass c)
    (xi : B.ParamSpace)
    (hl1 : B.nuisanceFineBaseline.weightL1Distance
      (B.vectorFamily.probabilityMass xi) ≤ epsilon)
    (hsmall : epsilon * B.fixedIntervalNuisanceDiameter U ^ 2 ≤
      B.fixedIntervalNuisanceGamma I U lambda) :
    B.MainSpace → B.NuisanceSpace :=
  B.exactNuisanceRegression xi
    (B.fixedIntervalNuisanceGamma_pos I hlambda)
    (B.fixedIntervalNuisanceGapProof I hlambda hlowerOne hupperU
      hlo hhi hweight xi hl1 hsmall)

/-- Full covariance gap from the fixed-interval nuisance block and the
remaining main/slow Schur lower bound.  The cross-block constant is the
already proved canonical finite bound and is independent of a later box. -/
theorem hasCovarianceGap_of_fixedIntervals_schur_and_l1
    [Nonempty Head]
    (I : PhysicalIntervals) {U lambda epsilon gammaMain : ℝ}
    (hlambda : 0 < lambda) (hMain : 0 < gammaMain)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hweight : ∀ c : Cell Head,
      lambda ≤ B.baseline.normalizedCellMass c)
    (xi : B.ParamSpace)
    (hl1 : B.nuisanceFineBaseline.weightL1Distance
      (B.vectorFamily.probabilityMass xi) ≤ epsilon)
    (hsmall : epsilon * B.fixedIntervalNuisanceDiameter U ^ 2 ≤
      B.fixedIntervalNuisanceGamma I U lambda)
    (hSchur : ∀ u,
      gammaMain * ‖u‖ ^ 2 ≤
        inner ℝ
          (B.schurResidual
            (B.fixedIntervalNuisanceRegression I hlambda hlowerOne
              hupperU hlo hhi hweight xi hl1 hsmall) u)
          (B.covarianceOperator xi
            (B.schurResidual
              (B.fixedIntervalNuisanceRegression I hlambda hlowerOne
                hupperU hlo hhi hweight xi hl1 hsmall) u))) :
    B.vectorFamily.HasCovarianceGap
      (min gammaMain (B.fixedIntervalNuisanceGamma I U lambda) /
        (3 + 2 * (B.canonicalCrossBound /
          B.fixedIntervalNuisanceGamma I U lambda) ^ 2)) xi := by
  let gammaN := B.fixedIntervalNuisanceGamma I U lambda
  have hgammaN : 0 < gammaN := B.fixedIntervalNuisanceGamma_pos I hlambda
  let hGamma := B.fixedIntervalNuisanceGapProof I hlambda hlowerOne
    hupperU hlo hhi hweight xi hl1 hsmall
  let R := B.fixedIntervalNuisanceRegression I hlambda hlowerOne
    hupperU hlo hhi hweight xi hl1 hsmall
  have hRdef : R = B.exactNuisanceRegression xi hgammaN hGamma := by rfl
  apply B.hasCovarianceGap_of_schur xi R
    (B.canonicalCrossBound / gammaN) gammaMain gammaN
    (div_nonneg B.canonicalCrossBound_nonneg hgammaN.le)
    hMain hgammaN
  · intro u
    rw [hRdef]
    calc
      ‖B.exactNuisanceRegression xi hgammaN hGamma u‖ ≤
          (‖B.crossCovarianceOperator xi‖ / gammaN) * ‖u‖ :=
        B.exactNuisanceRegression_norm_le xi hgammaN hGamma u
      _ ≤ (B.canonicalCrossBound / gammaN) * ‖u‖ := by
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right
            (B.crossCovarianceOperator_norm_le_canonicalCrossBound xi)
            hgammaN.le) (norm_nonneg u)
  · rw [hRdef]
    exact B.exactNuisanceRegression_isRegression xi hgammaN hGamma
  · exact hSchur
  · intro z
    simpa only [nuisanceCovarianceOperator,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right] using hGamma z

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
