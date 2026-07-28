import Erdos390.Full.PaperExactSchurTwoStageQuadratic
import Erdos390.Full.PaperVectorFieldEffectiveBound

/-!
# Exact two-stage solution of the finite Schur target equation

This file performs the algebraic block solve which is used, but usually
left implicit, in Proposition 8.7.  The right side is the literal normalized
paper target.  Its fast band component and compensated slow component are
defined below from the actual finite arithmetic data.  No asymptotic
estimate, continuum operator, or covariance lower bound is asserted here.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport
  MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

private theorem sum_mainCoord_target {Gauge : Type*} [Fintype Gauge]
    (f : MainCoord Gauge → ℝ) :
    (∑ c : MainCoord Gauge, f c) =
      (∑ j : Gauge, f (.gauge j)) + f .slow := by
  let e : MainCoord Gauge ≃ Gauge ⊕ Unit :=
    { toFun := fun c => match c with
        | .gauge j => Sum.inl j
        | .slow => Sum.inr ()
      invFun := fun s => match s with
        | Sum.inl j => .gauge j
        | Sum.inr _ => .slow
      left_inv := by intro c; cases c <;> rfl
      right_inv := by intro s; cases s <;> rfl }
  calc
    (∑ c : MainCoord Gauge, f c) =
        ∑ s : Gauge ⊕ Unit, f (e.symm s) := by
      exact Fintype.sum_equiv e f (fun s => f (e.symm s))
        (fun c => by simp)
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp [e]

/-- Unprojected normalized band row represented by the paper target.  The
factor `1/H_j` is forced by the exact arithmetic `D` pairing. -/
def normalizedTargetBandRow [Nonempty Head]
    (Delta : Band → ℝ) (j : Band) : ℝ :=
  (B.L / B.q) * Delta j / B.harmonicMass j

/-- The literal arithmetic-gauge projection of the normalized target row. -/
def projectedNormalizedTargetBand [Nonempty Head] [Nonempty Band]
    (Delta : Band → ℝ) : B.RawBandGauge :=
  B.projectRawBandVector (B.normalizedTargetBandRow Delta)

/-- The `D` pairing is positive definite on the actual raw arithmetic
gauge.  This is a finite statement using only positivity of the actual
harmonic masses. -/
theorem eq_zero_of_bandDPairing_self_eq_zero
    (q : B.RawBandGauge) (hzero : B.bandDPairing q q = 0) : q = 0 := by
  apply Subtype.ext
  funext j
  have hterm :
      B.harmonicMass j * q.1 j * q.1 j ≤
        ∑ k : Band, B.harmonicMass k * q.1 k * q.1 k := by
    have h := Finset.single_le_sum
      (s := (Finset.univ : Finset Band))
      (f := fun k => B.harmonicMass k * q.1 k * q.1 k)
      (fun k hk => by
        change 0 ≤ B.harmonicMass k * q.1 k * q.1 k
        calc
          0 ≤ B.harmonicMass k * (q.1 k * q.1 k) :=
            mul_nonneg (B.harmonicMass_pos k).le
              (mul_self_nonneg (q.1 k))
          _ = B.harmonicMass k * q.1 k * q.1 k := by ring)
      (Finset.mem_univ j)
    simpa using h
  unfold bandDPairing at hzero
  rw [hzero] at hterm
  have hmass := B.harmonicMass_pos j
  have hprod : B.harmonicMass j * (q.1 j) ^ 2 = 0 := by
    apply le_antisymm
    · simpa [pow_two, mul_assoc] using hterm
    · positivity
  have hsq : (q.1 j) ^ 2 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hmass)
  exact sq_eq_zero_iff.mp hsq

/-- The projected target row represents exactly the gauge part of the
normalized paper target under the finite arithmetic `D` pairing. -/
theorem bandDPairing_projectedNormalizedTargetBand
    [Nonempty Head] [Nonempty Band]
    (Delta : Band → ℝ) (r : B.RawBandGauge) :
    B.bandDPairing r (B.projectedNormalizedTargetBand Delta) =
      inner ℝ (B.mainRawSlowLinearEquiv.symm (r, 0))
        (B.mainPart (B.normalizedTarget Delta)) := by
  rw [PiLp.inner_apply]
  change B.bandDPairing r (B.projectedNormalizedTargetBand Delta) =
    ∑ c : MainCoord B.GaugeIndex,
      B.mainPart (B.normalizedTarget Delta) c *
        B.mainRawSlowLinearEquiv.symm (r, 0) c
  rw [sum_mainCoord_target]
  simp only [B.mainRawSlowLinearEquiv_symm_gauge,
    B.mainRawSlowLinearEquiv_symm_slow, mul_zero, add_zero,
    B.mainPart_gauge]
  rw [show B.bandDPairing r (B.projectedNormalizedTargetBand Delta) =
      ∑ j : Band, B.harmonicMass j * r.1 j *
        B.normalizedTargetBandRow Delta j by
    unfold projectedNormalizedTargetBand bandDPairing
    exact B.weighted_pairing_projectRawBandVector r
      (B.normalizedTargetBandRow Delta)]
  unfold normalizedTargetBandRow
  have hmass (j : Band) : B.harmonicMass j ≠ 0 :=
    ne_of_gt (B.harmonicMass_pos j)
  have hcancel (j : Band) :
      B.harmonicMass j * r.1 j *
          ((B.L / B.q) * Delta j / B.harmonicMass j) =
        r.1 j * ((B.L / B.q) * Delta j) := by
    field_simp [hmass j]
  simp_rw [hcancel]
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun j : Band => r.1 j * ((B.L / B.q) * Delta j)) B.lowBand]
  rw [B.rawBandGauge_low_eq]
  simp only [B.normalizedTarget_apply, unscaledTarget, coordScale,
    div_one]
  have hrhs :
      (∑ x : B.GaugeIndex,
        (B.L / B.q) *
            (Delta x.1 - B.lowRatio x * Delta B.lowBand) * r.1 x.1) =
        (∑ x : B.GaugeIndex,
          r.1 x.1 * ((B.L / B.q) * Delta x.1)) -
          (∑ x : B.GaugeIndex, B.lowRatio x * r.1 x.1) *
            ((B.L / B.q) * Delta B.lowBand) := by
    calc
      (∑ x : B.GaugeIndex,
        (B.L / B.q) *
            (Delta x.1 - B.lowRatio x * Delta B.lowBand) * r.1 x.1) =
          ∑ x : B.GaugeIndex,
            (r.1 x.1 * ((B.L / B.q) * Delta x.1) -
              (B.lowRatio x * r.1 x.1) *
                ((B.L / B.q) * Delta B.lowBand)) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_mul]
  rw [hrhs]
  ring

/-- Full raw/slow pairing with the normalized target.  This extends the
preceding gauge identity by the literal stored slow coordinate. -/
theorem inner_mainRawSlow_symm_normalizedTarget
    [Nonempty Head] [Nonempty Band]
    (Delta : Band → ℝ) (q : B.RawBandGauge) (s : ℝ) :
    inner ℝ (B.mainRawSlowLinearEquiv.symm (q, s))
        (B.mainPart (B.normalizedTarget Delta)) =
      B.bandDPairing q (B.projectedNormalizedTargetBand Delta) +
        s * B.mainPart (B.normalizedTarget Delta) MainCoord.slow := by
  have hband := B.bandDPairing_projectedNormalizedTargetBand Delta q
  rw [PiLp.inner_apply] at hband ⊢
  change
    (∑ c : MainCoord B.GaugeIndex,
      B.mainPart (B.normalizedTarget Delta) c *
        B.mainRawSlowLinearEquiv.symm (q, s) c) = _
  change B.bandDPairing q (B.projectedNormalizedTargetBand Delta) =
    ∑ c : MainCoord B.GaugeIndex,
      B.mainPart (B.normalizedTarget Delta) c *
        B.mainRawSlowLinearEquiv.symm (q, 0) c at hband
  rw [sum_mainCoord_target] at hband ⊢
  simp only [B.mainRawSlowLinearEquiv_symm_gauge,
    B.mainRawSlowLinearEquiv_symm_slow, mul_zero, add_zero] at hband ⊢
  rw [hband]
  ring

/-- Bilinear form of the literal exact Schur operator.  Both arguments are
the genuine finite nuisance-regression residuals. -/
theorem inner_exactSchurCovarianceOperator_bilinear
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (v u : B.MainSpace) :
    inner ℝ v (B.exactSchurCovarianceOperator xi hgamma hgap u) =
      inner ℝ
        (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) v)
        (B.covarianceOperator xi
          (B.schurResidual
            (B.exactNuisanceRegression xi hgamma hgap) u)) := by
  let R := B.exactNuisanceRegression xi hgamma hgap
  let rv := B.schurResidual R v
  let ru := B.schurResidual R u
  have hleft :
      inner ℝ v (B.exactSchurCovarianceOperator xi hgamma hgap u) =
        inner ℝ (B.mainEmbed v) (B.covarianceOperator xi ru) := by
    simpa only [exactSchurCovarianceOperator,
      ContinuousLinearMap.comp_apply,
      B.exactSchurEmbeddingCLM_apply, R, ru] using
      (ContinuousLinearMap.adjoint_inner_right B.mainEmbeddingCLM v
        (B.covarianceOperator xi ru))
  have hv : B.mainEmbed v = rv + B.nuisanceEmbed (R v) := by
    rw [show rv = B.mainEmbed v - B.nuisanceEmbed (R v) from
      B.schurResidual_eq_sub R v]
    abel
  have horth :=
    (B.exactNuisanceRegression_isRegression xi hgamma hgap u (R v)).2
  have horth' : inner ℝ (B.nuisanceEmbed (R v))
      (B.covarianceOperator xi ru) = 0 := by
    simpa only [R, ru] using horth
  calc
    inner ℝ v (B.exactSchurCovarianceOperator xi hgamma hgap u) =
        inner ℝ (B.mainEmbed v) (B.covarianceOperator xi ru) := hleft
    _ = inner ℝ rv (B.covarianceOperator xi ru) := by
      rw [hv, inner_add_left]
      rw [horth', add_zero]

/-- Main vector carrying only a raw arithmetic-gauge coefficient. -/
def rawOnlyMain (q : B.RawBandGauge) : B.MainSpace :=
  B.mainRawSlowLinearEquiv.symm (q, 0)

@[simp] theorem rawGaugeOfMain_rawOnlyMain (q : B.RawBandGauge) :
    B.rawGaugeOfMain (B.rawOnlyMain q) = q := by
  have h := B.mainRawSlowLinearEquiv.apply_symm_apply (q, 0)
  exact congrArg Prod.fst h

@[simp] theorem rawOnlyMain_slow (q : B.RawBandGauge) :
    B.rawOnlyMain q MainCoord.slow = 0 :=
  B.mainRawSlowLinearEquiv_symm_slow q 0

/-- The exact Schur residual of a raw-only main vector has precisely the
nuisance-residual band score. -/
theorem vectorScore_exactSchurResidual_rawOnly
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) :
    (fun m => B.vectorFamily.scalarFamily.score m
      (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap)
        (B.rawOnlyMain q))) =
      B.nuisanceResidualScore xi hgamma hgap
        (B.bandRegressionScore q) := by
  rw [B.vectorScore_exactSchurResidual_eq_nuisanceResidual_mainScore]
  congr 1
  funext m
  rw [B.vectorScore_mainEmbed_eq_rawGauge_add_slow]
  simp

/-- The fast raw gauge associated with a main vector after the first-stage
slow-column regression. -/
def fastGaugeOfMain [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (u : B.MainSpace) : B.RawBandGauge :=
  B.rawGaugeOfMain u +
    (u MainCoord.slow / B.w) •
      B.actualBandRegression xi hgamma hgap e

theorem rawGauge_eq_fastGauge_sub_regression
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (u : B.MainSpace) :
    B.rawGaugeOfMain u =
      B.fastGaugeOfMain xi hgamma hgap e u -
        (u MainCoord.slow / B.w) •
          B.actualBandRegression xi hgamma hgap e := by
  unfold fastGaugeOfMain
  abel

theorem slow_eq_w_mul_slow_div (u : B.MainSpace) :
    u MainCoord.slow = B.w * (u MainCoord.slow / B.w) := by
  field_simp [ne_of_gt B.w_pos]

/-- Every solution of the literal main Schur equation has fast band
coordinate equal to the inverse solution of the literal projected target
row.  This is an exact finite identity, not an inverse estimate. -/
theorem actualBandSchur_fastGauge_eq_projectedTarget
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta)) :
    B.actualBandSchurLinearMap xi hgamma hgap
        (B.fastGaugeOfMain xi hgamma hgap e u) =
      B.projectedNormalizedTargetBand Delta := by
  let qReg := B.actualBandRegression xi hgamma hgap e
  let lambda := u MainCoord.slow / B.w
  let qFast := B.fastGaugeOfMain xi hgamma hgap e u
  have hq : B.rawGaugeOfMain u = qFast - lambda • qReg := by
    simpa only [qFast, lambda, qReg] using
      B.rawGauge_eq_fastGauge_sub_regression xi hgamma hgap e u
  have hs : u MainCoord.slow = B.w * lambda := by
    simpa only [lambda] using B.slow_eq_w_mul_slow_div u
  have hscoreU := B.vectorScore_exactSchurResidual_fast_add_compensated
    xi hgamma hgap u qFast qReg lambda hq hs
  have hpair : ∀ r : B.RawBandGauge,
      B.bandDPairing r
          (B.actualBandSchurLinearMap xi hgamma hgap qFast) =
        B.bandDPairing r (B.projectedNormalizedTargetBand Delta) := by
    intro r
    let vr := B.rawOnlyMain r
    have hscoreR := B.vectorScore_exactSchurResidual_rawOnly
      xi hgamma hgap r
    have horth := B.fastResidual_covariance_twoStageCompensated_eq_zero
      xi hgamma hgap e he r
    have horth' :
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore r))
          (B.actualCompensatedScore xi hgamma hgap qReg) = 0 := by
      simpa only [actualTwoStageCompensatedScore, qReg] using horth
    calc
      B.bandDPairing r
          (B.actualBandSchurLinearMap xi hgamma hgap qFast) =
          (B.tiltedLaw xi).covariance
            (B.nuisanceResidualScore xi hgamma hgap
              (B.bandRegressionScore r))
            (B.nuisanceResidualScore xi hgamma hgap
              (B.bandRegressionScore qFast)) :=
        B.actualBandSchur_bilinear_eq_residualCovariance
          xi hgamma hgap r qFast
      _ = (B.tiltedLaw xi).covariance
          (fun m => B.vectorFamily.scalarFamily.score m
            (B.schurResidual
              (B.exactNuisanceRegression xi hgamma hgap) vr))
          (fun m => B.vectorFamily.scalarFamily.score m
            (B.schurResidual
              (B.exactNuisanceRegression xi hgamma hgap) u)) := by
        rw [hscoreR, hscoreU,
          FiniteProbability.covariance_add_right,
          FiniteProbability.covariance_smul_right, horth']
        ring
      _ = inner ℝ vr
          (B.exactSchurCovarianceOperator xi hgamma hgap u) := by
        rw [B.inner_exactSchurCovarianceOperator_bilinear]
        rw [B.inner_covarianceOperator]
        congr 1 <;> funext m <;>
          simp only [VectorExponentialFamily.scalarFamily,
            innerSL_apply_apply] <;> exact real_inner_comm _ _
      _ = inner ℝ vr (B.mainPart (B.normalizedTarget Delta)) := by
        rw [hu]
      _ = B.bandDPairing r
          (B.projectedNormalizedTargetBand Delta) :=
        (B.bandDPairing_projectedNormalizedTargetBand Delta r).symm
  let d : B.RawBandGauge :=
    B.actualBandSchurLinearMap xi hgamma hgap qFast -
      B.projectedNormalizedTargetBand Delta
  have hdPair : B.bandDPairing d d = 0 := by
    have hd := hpair d
    unfold d bandDPairing at hd ⊢
    simp only [Submodule.coe_sub, Pi.sub_apply]
    calc
      (∑ j : Band,
        B.harmonicMass j *
          ((B.actualBandSchurLinearMap xi hgamma hgap qFast).1 j -
            (B.projectedNormalizedTargetBand Delta).1 j) *
          ((B.actualBandSchurLinearMap xi hgamma hgap qFast).1 j -
            (B.projectedNormalizedTargetBand Delta).1 j)) =
          (∑ j : Band,
            B.harmonicMass j *
              ((B.actualBandSchurLinearMap xi hgamma hgap qFast).1 j -
                (B.projectedNormalizedTargetBand Delta).1 j) *
              (B.actualBandSchurLinearMap xi hgamma hgap qFast).1 j) -
          (∑ j : Band,
            B.harmonicMass j *
              ((B.actualBandSchurLinearMap xi hgamma hgap qFast).1 j -
                (B.projectedNormalizedTargetBand Delta).1 j) *
              (B.projectedNormalizedTargetBand Delta).1 j) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := sub_eq_zero.mpr hd
  have hdZero := B.eq_zero_of_bandDPairing_self_eq_zero d hdPair
  simpa only [d, qFast] using sub_eq_zero.mp hdZero

/-- Consequently the fast coordinate is literally the inverse image of the
projected normalized target row. -/
theorem fastGauge_eq_inverse_projectedTarget
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta)) :
    B.fastGaugeOfMain xi hgamma hgap e u =
      e.symm (B.projectedNormalizedTargetBand Delta) := by
  apply e.injective
  rw [e.apply_symm_apply, he]
  exact B.actualBandSchur_fastGauge_eq_projectedTarget
    xi hgamma hgap e he Delta u hu

/-- Main direction whose exact Schur residual is the fully compensated
two-stage slow score.  Its raw coordinate is `-qReg` and its stored slow
coordinate is exactly `w`. -/
def compensatedMainDirection [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge) : B.MainSpace :=
  B.mainRawSlowLinearEquiv.symm
    (-B.actualBandRegression xi hgamma hgap e, B.w)

@[simp] theorem rawGaugeOfMain_compensatedMainDirection
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge) :
    B.rawGaugeOfMain
        (B.compensatedMainDirection xi hgamma hgap e) =
      -B.actualBandRegression xi hgamma hgap e := by
  have h := B.mainRawSlowLinearEquiv.apply_symm_apply
    (-B.actualBandRegression xi hgamma hgap e, B.w)
  exact congrArg Prod.fst h

@[simp] theorem compensatedMainDirection_slow
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge) :
    B.compensatedMainDirection xi hgamma hgap e MainCoord.slow = B.w :=
  B.mainRawSlowLinearEquiv_symm_slow
    (-B.actualBandRegression xi hgamma hgap e) B.w

/-- The exact Schur score of the compensated main direction is the literal
two-stage compensated score. -/
theorem vectorScore_exactSchurResidual_compensatedMainDirection
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge) :
    (fun m => B.vectorFamily.scalarFamily.score m
      (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap)
        (B.compensatedMainDirection xi hgamma hgap e))) =
      B.actualTwoStageCompensatedScore xi hgamma hgap e := by
  rw [B.vectorScore_exactSchurResidual_eq_nuisanceResidual_mainScore]
  change B.nuisanceResidualScore xi hgamma hgap
      (fun m => B.vectorFamily.scalarFamily.score m
        (B.mainEmbed
          (B.compensatedMainDirection xi hgamma hgap e))) =
    B.nuisanceResidualScore xi hgamma hgap
      (B.postBandPrimeScore
        (B.actualBandRegression xi hgamma hgap e))
  congr 1
  funext m
  rw [B.vectorScore_mainEmbed_eq_rawGauge_add_slow,
    B.rawGaugeOfMain_compensatedMainDirection,
    B.compensatedMainDirection_slow]
  have hneg :
      B.bandRegressionScore
          (-B.actualBandRegression xi hgamma hgap e) m =
        -B.bandRegressionScore
          (B.actualBandRegression xi hgamma hgap e) m := by
    have hnegArg :
        -B.actualBandRegression xi hgamma hgap e =
          (-1 : ℝ) • B.actualBandRegression xi hgamma hgap e := by
      apply Subtype.ext
      funext j
      simp
    rw [hnegArg]
    have h := congrFun (B.bandRegressionScore_smul (-1)
      (B.actualBandRegression xi hgamma hgap e)) m
    simpa only [neg_mul, one_mul] using h
  rw [hneg, B.postBandPrimeScore_eq_slow_sub_bandRegression]
  have hw : B.w / B.w = 1 := div_self (ne_of_gt B.w_pos)
  rw [hw]
  ring

/-- Literal right side in the compensated slow equation. -/
def compensatedNormalizedTarget [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (Delta : Band → ℝ) : ℝ :=
  inner ℝ (B.compensatedMainDirection xi hgamma hgap e)
    (B.mainPart (B.normalizedTarget Delta))

/-- Exact target-only formula for the compensated scalar.  All dependence
on the tilted law occurs through the already constructed first-stage
regression vector. -/
theorem compensatedNormalizedTarget_eq_slow_sub_bandDPairing
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (Delta : Band → ℝ) :
    B.compensatedNormalizedTarget xi hgamma hgap e Delta =
      -B.bandDPairing
          (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta) +
        B.w * B.mainPart (B.normalizedTarget Delta) MainCoord.slow := by
  unfold compensatedNormalizedTarget compensatedMainDirection
  rw [B.inner_mainRawSlow_symm_normalizedTarget]
  have hneg :
      B.bandDPairing (-B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta) =
        -B.bandDPairing (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta) := by
    unfold bandDPairing
    simp only [Submodule.coe_neg, Pi.neg_apply]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hneg]

/-- Target-only envelope obtained after inserting a sharp first-stage
regression bound into the exact compensated-target identity. -/
def twoStageCompensatedTargetBound
    (Creg Tband TslowCoord : ℝ) : ℝ :=
  sharpWeightTotal B.harmonicMass B.bandCenter *
      (Creg * B.w) * Tband +
    B.w * TslowCoord

/-- A first-stage regression bound, a projected target bound, and the raw
slow target coordinate bound imply the compensated-target estimate.  Thus
the latter need not be retained as an independent analytic hypothesis. -/
theorem abs_compensatedNormalizedTarget_le_of_regression_target
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (Delta : Band → ℝ)
    {Creg Tband TslowCoord : ℝ}
    (hCreg : 0 ≤ Creg)
    (hreg : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.actualBandRegression xi hgamma hgap e) ≤ Creg * B.w)
    (htargetBand : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.projectedNormalizedTargetBand Delta) ≤ Tband)
    (htargetSlowCoord :
      |B.mainPart (B.normalizedTarget Delta) MainCoord.slow| ≤
        TslowCoord) :
    |B.compensatedNormalizedTarget xi hgamma hgap e Delta| ≤
      B.twoStageCompensatedTargetBound Creg Tband TslowCoord := by
  unfold twoStageCompensatedTargetBound
  rw [B.compensatedNormalizedTarget_eq_slow_sub_bandDPairing]
  have hD := abs_rawDPairing_le_sharpWeightTotal_mul
    B.harmonicMass B.bandCenter B.harmonicMass_pos
    (B.partition.center_ne_zero B.n_gt_one)
    (B.actualBandRegression xi hgamma hgap e)
    (B.projectedNormalizedTargetBand Delta)
  have hD' :
      |B.bandDPairing (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta)| ≤
        sharpWeightTotal B.harmonicMass B.bandCenter *
          (Creg * B.w) * Tband := by
    calc
      |B.bandDPairing (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta)| ≤
        sharpWeightTotal B.harmonicMass B.bandCenter *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one)
            (B.actualBandRegression xi hgamma hgap e) *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one)
            (B.projectedNormalizedTargetBand Delta) := by
        simpa only [bandDPairing, rawDPairing] using hD
      _ ≤ sharpWeightTotal B.harmonicMass B.bandCenter *
          (Creg * B.w) * Tband := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hreg
            B.sharpBandWeightTotal_pos.le)
          htargetBand (norm_nonneg _)
          (mul_nonneg
            B.sharpBandWeightTotal_pos.le
            (mul_nonneg hCreg B.w_pos.le))
  calc
    |-B.bandDPairing (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta) +
        B.w * B.mainPart (B.normalizedTarget Delta) MainCoord.slow| ≤
      |B.bandDPairing (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta)| +
        B.w * |B.mainPart (B.normalizedTarget Delta) MainCoord.slow| := by
      calc
        _ ≤ |-B.bandDPairing
              (B.actualBandRegression xi hgamma hgap e)
              (B.projectedNormalizedTargetBand Delta)| +
            |B.w * B.mainPart (B.normalizedTarget Delta)
              MainCoord.slow| := abs_add_le _ _
        _ = _ := by rw [abs_neg, abs_mul, abs_of_pos B.w_pos]
    _ ≤ sharpWeightTotal B.harmonicMass B.bandCenter *
          (Creg * B.w) * Tband + B.w * TslowCoord :=
      add_le_add hD'
        (mul_le_mul_of_nonneg_left htargetSlowCoord B.w_pos.le)

/-- Literal finite variance in the compensated slow denominator. -/
def actualTwoStageCompensatedVariance
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge) : ℝ :=
  (B.tiltedLaw xi).covariance
    (B.actualTwoStageCompensatedScore xi hgamma hgap e)
    (B.actualTwoStageCompensatedScore xi hgamma hgap e)

/-- The slow coefficient of every literal Schur solution satisfies one
exact scalar equation.  Fast/slow and nuisance cross terms vanish by the
two proved normal equations. -/
theorem slow_div_mul_actualTwoStageCompensatedVariance
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta)) :
    (u MainCoord.slow / B.w) *
        B.actualTwoStageCompensatedVariance xi hgamma hgap e =
      B.compensatedNormalizedTarget xi hgamma hgap e Delta := by
  let qReg := B.actualBandRegression xi hgamma hgap e
  let lambda := u MainCoord.slow / B.w
  let qFast := B.fastGaugeOfMain xi hgamma hgap e u
  let vc := B.compensatedMainDirection xi hgamma hgap e
  have hq : B.rawGaugeOfMain u = qFast - lambda • qReg := by
    simpa only [qFast, lambda, qReg] using
      B.rawGauge_eq_fastGauge_sub_regression xi hgamma hgap e u
  have hs : u MainCoord.slow = B.w * lambda := by
    simpa only [lambda] using B.slow_eq_w_mul_slow_div u
  have hscoreU := B.vectorScore_exactSchurResidual_fast_add_compensated
    xi hgamma hgap u qFast qReg lambda hq hs
  have hscoreC :=
    B.vectorScore_exactSchurResidual_compensatedMainDirection
      xi hgamma hgap e
  have horth := B.fastResidual_covariance_twoStageCompensated_eq_zero
    xi hgamma hgap e he qFast
  have hscalar :
      inner ℝ vc (B.exactSchurCovarianceOperator xi hgamma hgap u) =
        lambda * B.actualTwoStageCompensatedVariance
          xi hgamma hgap e := by
    rw [B.inner_exactSchurCovarianceOperator_bilinear]
    rw [B.inner_covarianceOperator]
    have hleft :
        (fun m => inner ℝ
          (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) vc)
          (B.statistic m)) =
          B.actualTwoStageCompensatedScore xi hgamma hgap e := by
      funext m
      calc
        inner ℝ
            (B.schurResidual
              (B.exactNuisanceRegression xi hgamma hgap) vc)
            (B.statistic m) =
            B.vectorFamily.scalarFamily.score m
              (B.schurResidual
                (B.exactNuisanceRegression xi hgamma hgap) vc) := by
          simp only [VectorExponentialFamily.scalarFamily,
            innerSL_apply_apply]
          exact real_inner_comm _ _
        _ = B.actualTwoStageCompensatedScore xi hgamma hgap e m := by
          exact congrFun hscoreC m
    have hright :
        (fun m => inner ℝ
          (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) u)
          (B.statistic m)) =
          fun m =>
            B.nuisanceResidualScore xi hgamma hgap
                (B.bandRegressionScore qFast) m +
              lambda *
                B.actualTwoStageCompensatedScore xi hgamma hgap e m := by
      funext m
      calc
        inner ℝ
            (B.schurResidual
              (B.exactNuisanceRegression xi hgamma hgap) u)
            (B.statistic m) =
            B.vectorFamily.scalarFamily.score m
              (B.schurResidual
                (B.exactNuisanceRegression xi hgamma hgap) u) := by
          simp only [VectorExponentialFamily.scalarFamily,
            innerSL_apply_apply]
          exact real_inner_comm _ _
        _ = _ := congrFun hscoreU m
    rw [hleft, hright]
    change (B.tiltedLaw xi).covariance
      (B.actualTwoStageCompensatedScore xi hgamma hgap e)
      (fun m =>
        B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore qFast) m +
          lambda *
            B.actualTwoStageCompensatedScore xi hgamma hgap e m) =
      lambda * B.actualTwoStageCompensatedVariance
        xi hgamma hgap e
    rw [FiniteProbability.covariance_add_right,
      FiniteProbability.covariance_smul_right]
    have horth' :
        (B.tiltedLaw xi).covariance
          (B.actualTwoStageCompensatedScore xi hgamma hgap e)
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore qFast)) = 0 := by
      rw [(B.tiltedLaw xi).covariance_comm]
      exact horth
    rw [horth']
    unfold actualTwoStageCompensatedVariance
    ring
  unfold compensatedNormalizedTarget
  rw [← hu]
  simpa only [lambda, vc] using hscalar.symm

/-- Division form of the exact slow solve. -/
theorem slow_div_eq_compensatedTarget_div_variance
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta))
    (hvariance : B.actualTwoStageCompensatedVariance
      xi hgamma hgap e ≠ 0) :
    u MainCoord.slow / B.w =
      B.compensatedNormalizedTarget xi hgamma hgap e Delta /
        B.actualTwoStageCompensatedVariance xi hgamma hgap e := by
  apply (eq_div_iff hvariance).2
  exact B.slow_div_mul_actualTwoStageCompensatedVariance
    xi hgamma hgap e he Delta u hu

/-- Weighted fast-coordinate bound obtained directly from the literal band
inverse and the literal projected target. -/
theorem fastGauge_paperSharpNorm_le_of_inverse
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    {Cinv : ℝ}
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta)) :
    paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.fastGaugeOfMain xi hgamma hgap e u) ≤
      Cinv * paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.projectedNormalizedTargetBand Delta) := by
  rw [B.fastGauge_eq_inverse_projectedTarget
    xi hgamma hgap e he Delta u hu]
  exact hinv _

/-- A lower bound for the literal compensated variance and an upper bound
for its literal target give the exact slow-velocity estimate. -/
theorem abs_slow_div_le_of_variance_target_bounds
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta))
    {Vlower Tbound : ℝ} (hVlower : 0 < Vlower)
    (hvariance : Vlower ≤ B.actualTwoStageCompensatedVariance
      xi hgamma hgap e)
    (hTbound : 0 ≤ Tbound)
    (htarget : |B.compensatedNormalizedTarget
      xi hgamma hgap e Delta| ≤ Tbound) :
    |u MainCoord.slow / B.w| ≤ Tbound / Vlower := by
  have hVpos : 0 < B.actualTwoStageCompensatedVariance
      xi hgamma hgap e := hVlower.trans_le hvariance
  have hformula := B.slow_div_eq_compensatedTarget_div_variance
    xi hgamma hgap e he Delta u hu (ne_of_gt hVpos)
  rw [hformula, abs_div, abs_of_pos hVpos]
  calc
    |B.compensatedNormalizedTarget xi hgamma hgap e Delta| /
        B.actualTwoStageCompensatedVariance xi hgamma hgap e ≤
      Tbound / B.actualTwoStageCompensatedVariance
        xi hgamma hgap e :=
      div_le_div_of_nonneg_right htarget hVpos.le
    _ ≤ Tbound / Vlower :=
      div_le_div_of_nonneg_left hTbound hVlower hvariance

/-- Stored-slow form of the preceding estimate. -/
theorem abs_slow_le_of_variance_target_bounds
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta))
    {Vlower Tbound : ℝ} (hVlower : 0 < Vlower)
    (hvariance : Vlower ≤ B.actualTwoStageCompensatedVariance
      xi hgamma hgap e)
    (hTbound : 0 ≤ Tbound)
    (htarget : |B.compensatedNormalizedTarget
      xi hgamma hgap e Delta| ≤ Tbound) :
    |u MainCoord.slow| ≤ B.w * (Tbound / Vlower) := by
  have hlambda := B.abs_slow_div_le_of_variance_target_bounds
    xi hgamma hgap e he Delta u hu hVlower hvariance hTbound htarget
  have hs := B.slow_eq_w_mul_slow_div u
  rw [hs, abs_mul, abs_of_pos B.w_pos]
  exact mul_le_mul_of_nonneg_left hlambda B.w_pos.le

/-- Exact prime-coefficient identity for the two-stage decomposition of an
arbitrary main vector. -/
theorem effectivePrimeCoefficient_fast_compensated
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (u : B.MainSpace)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    (B.rawGaugeOfMain u).1 (B.partition.band p) +
        (u MainCoord.slow / B.w) * B.primeDeviation p =
      (B.fastGaugeOfMain xi hgamma hgap e u).1
          (B.partition.band p) +
        (u MainCoord.slow / B.w) *
          B.actualCompensatedCoefficient
            (B.actualBandRegression xi hgamma hgap e) p := by
  have hq := B.rawGauge_eq_fastGauge_sub_regression
    xi hgamma hgap e u
  have hp := congrArg
    (fun q : B.RawBandGauge => q.1 (B.partition.band p)) hq
  simp only [Submodule.coe_sub, Pi.sub_apply, SetLike.val_smul,
    Pi.smul_apply, smul_eq_mul] at hp
  unfold actualCompensatedCoefficient bandRegressionCoefficient
  rw [hp]
  ring

/-- Dimension-free prime-fugacity bound from a sharp fast bound and the
literal pointwise compensated-coefficient bound. -/
theorem effectivePrimeVelocity_norm_le_of_fast_compensated
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (u : B.MainSpace)
    {Cfast Clambda Ccomp : ℝ}
    (hCfast : 0 ≤ Cfast) (hClambda : 0 ≤ Clambda)
    (hCcomp : 0 ≤ Ccomp)
    (hfast : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.fastGaugeOfMain xi hgamma hgap e u) ≤ Cfast)
    (hlambda : |u MainCoord.slow / B.w| ≤ Clambda)
    (hcomp : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.actualCompensatedCoefficient
        (B.actualBandRegression xi hgamma hgap e) p| ≤ Ccomp) :
    ‖fun p : BandPrime B.sampleData.n B.sampleData.W =>
        (B.rawGaugeOfMain u).1 (B.partition.band p) +
          (u MainCoord.slow / B.w) * B.primeDeviation p‖ ≤
      Cfast + Clambda * Ccomp := by
  have hbound : 0 ≤ Cfast + Clambda * Ccomp :=
    add_nonneg hCfast (mul_nonneg hClambda hCcomp)
  rw [pi_norm_le_iff_of_nonneg hbound]
  intro p
  rw [Real.norm_eq_abs,
    B.effectivePrimeCoefficient_fast_compensated xi hgamma hgap e u p]
  have hq :
      |(B.fastGaugeOfMain xi hgamma hgap e u).1
          (B.partition.band p)| ≤ Cfast := by
    have hcoord := abs_raw_coordinate_le_paperSharpNorm
      B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.fastGaugeOfMain xi hgamma hgap e u)
      (B.partition.band p)
    have hc := B.partition.center_mem_zero_one B.n_gt_one
      (B.partition.band p)
    have habs : |B.bandCenter (B.partition.band p)| ≤ 1 := by
      change |B.partition.center (B.partition.band p)| ≤ 1
      rw [abs_of_nonneg hc.1]
      exact hc.2
    calc
      |(B.fastGaugeOfMain xi hgamma hgap e u).1
          (B.partition.band p)| ≤
          |B.bandCenter (B.partition.band p)| *
            paperSharpNorm B.harmonicMass B.bandCenter
              (B.partition.center_ne_zero B.n_gt_one)
              (B.fastGaugeOfMain xi hgamma hgap e u) := hcoord
      _ ≤ 1 * paperSharpNorm B.harmonicMass B.bandCenter
              (B.partition.center_ne_zero B.n_gt_one)
              (B.fastGaugeOfMain xi hgamma hgap e u) :=
        mul_le_mul_of_nonneg_right habs (norm_nonneg _)
      _ ≤ Cfast := by simpa using hfast
  calc
    |(B.fastGaugeOfMain xi hgamma hgap e u).1
          (B.partition.band p) +
        (u MainCoord.slow / B.w) *
          B.actualCompensatedCoefficient
            (B.actualBandRegression xi hgamma hgap e) p| ≤
      |(B.fastGaugeOfMain xi hgamma hgap e u).1
          (B.partition.band p)| +
        |u MainCoord.slow / B.w| *
          |B.actualCompensatedCoefficient
            (B.actualBandRegression xi hgamma hgap e) p| := by
      simpa only [abs_mul] using
        abs_add_le
          ((B.fastGaugeOfMain xi hgamma hgap e u).1
            (B.partition.band p))
          ((u MainCoord.slow / B.w) *
            B.actualCompensatedCoefficient
              (B.actualBandRegression xi hgamma hgap e) p)
    _ ≤ Cfast + Clambda * Ccomp :=
      add_le_add hq
        (mul_le_mul hlambda (hcomp p) (abs_nonneg _) hClambda)

/-- Exact nuisance component of the two-stage main solve before inserting
the target identities. -/
theorem exactNuisanceRegression_eq_fast_add_twoStage
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (u : B.MainSpace) :
    B.exactNuisanceRegression xi hgamma hgap u =
      B.nuisanceCoefficientOfScore xi hgamma hgap
          (B.bandRegressionScore
            (B.fastGaugeOfMain xi hgamma hgap e u)) +
        (u MainCoord.slow / B.w) •
          B.actualTwoStageNuisanceCoefficient xi hgamma hgap e := by
  let qReg := B.actualBandRegression xi hgamma hgap e
  let lambda := u MainCoord.slow / B.w
  let qFast := B.fastGaugeOfMain xi hgamma hgap e u
  have hq : B.rawGaugeOfMain u = qFast - lambda • qReg := by
    simpa only [qFast, lambda, qReg] using
      B.rawGauge_eq_fastGauge_sub_regression xi hgamma hgap e u
  have hs : u MainCoord.slow = B.w * lambda := by
    simpa only [lambda] using B.slow_eq_w_mul_slow_div u
  have hinput :
      (fun m => B.vectorFamily.scalarFamily.score m (B.mainEmbed u)) =
        fun m => B.bandRegressionScore qFast m +
          lambda * B.postBandPrimeScore qReg m := by
    funext m
    rw [B.vectorScore_mainEmbed_eq_rawGauge_add_slow, hq,
      B.bandRegressionScore_sub, B.bandRegressionScore_smul, hs,
      mul_div_cancel_left₀ lambda (ne_of_gt B.w_pos),
      B.postBandPrimeScore_eq_slow_sub_bandRegression]
    ring
  rw [B.exactNuisanceRegression_eq_nuisanceCoefficient_mainScore,
    hinput, B.nuisanceCoefficientOfScore_add,
    B.nuisanceCoefficientOfScore_smul]
  rfl

/-- Literal fast nuisance coefficient attached to the normalized target. -/
def targetFastNuisanceCoefficient
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (Delta : Band → ℝ) : B.NuisanceSpace :=
  B.nuisanceCoefficientOfScore xi hgamma hgap
    (B.bandRegressionScore
      (e.symm (B.projectedNormalizedTargetBand Delta)))

/-- A literal covariance-vector row bounded by `gamma * C` gives the
corresponding target-fast nuisance coefficient bound `C`.  Thus the
coefficient estimate is a consequence of the nuisance covariance gap, not
an additional analytic input. -/
theorem targetFastNuisanceCoefficient_norm_le_of_covarianceVector
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (Delta : Band → ℝ) {C : ℝ}
    (hcov : ‖B.nuisanceCovarianceVector xi
      (B.bandRegressionScore
        (e.symm (B.projectedNormalizedTargetBand Delta)))‖ ≤
          gamma * C) :
    ‖B.targetFastNuisanceCoefficient xi hgamma hgap e Delta‖ ≤ C := by
  unfold targetFastNuisanceCoefficient
  calc
    ‖B.nuisanceCoefficientOfScore xi hgamma hgap
        (B.bandRegressionScore
          (e.symm (B.projectedNormalizedTargetBand Delta)))‖ ≤
      ‖B.nuisanceCovarianceVector xi
        (B.bandRegressionScore
          (e.symm (B.projectedNormalizedTargetBand Delta)))‖ / gamma :=
        B.nuisanceCoefficientOfScore_norm_le xi hgamma hgap _
    _ ≤ (gamma * C) / gamma :=
      div_le_div_of_nonneg_right hcov hgamma.le
    _ = C := by field_simp [ne_of_gt hgamma]

/-- The same gap reduction for the literal post-band slow row. -/
theorem actualTwoStageNuisanceCoefficient_norm_le_of_covarianceVector
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {C : ℝ}
    (hcov : ‖B.nuisanceCovarianceVector xi
      (B.postBandPrimeScore
        (B.actualBandRegression xi hgamma hgap e))‖ ≤ gamma * C) :
    ‖B.actualTwoStageNuisanceCoefficient xi hgamma hgap e‖ ≤ C := by
  unfold actualTwoStageNuisanceCoefficient actualNuisanceCoefficient
  calc
    ‖B.nuisanceCoefficientOfScore xi hgamma hgap
        (B.postBandPrimeScore
          (B.actualBandRegression xi hgamma hgap e))‖ ≤
      ‖B.nuisanceCovarianceVector xi
        (B.postBandPrimeScore
          (B.actualBandRegression xi hgamma hgap e))‖ / gamma :=
        B.nuisanceCoefficientOfScore_norm_le xi hgamma hgap _
    _ ≤ (gamma * C) / gamma :=
      div_le_div_of_nonneg_right hcov hgamma.le
    _ = C := by field_simp [ne_of_gt hgamma]

/-- After imposing the Schur equation, the nuisance component is the sum
of the literal target-fast coefficient and the literal compensated-slow
coefficient. -/
theorem exactNuisanceRegression_eq_targetFast_add_twoStage
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta)) :
    B.exactNuisanceRegression xi hgamma hgap u =
      B.targetFastNuisanceCoefficient xi hgamma hgap e Delta +
        (u MainCoord.slow / B.w) •
          B.actualTwoStageNuisanceCoefficient xi hgamma hgap e := by
  rw [B.exactNuisanceRegression_eq_fast_add_twoStage]
  unfold targetFastNuisanceCoefficient
  rw [B.fastGauge_eq_inverse_projectedTarget
    xi hgamma hgap e he Delta u hu]

/-- Nuisance-velocity estimate from the two explicit coefficients and the
already solved slow scalar. -/
theorem exactNuisanceRegression_norm_le_of_twoStage
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta))
    {CfastNuisance Clambda CslowNuisance : ℝ}
    (hClambda : 0 ≤ Clambda)
    (hfast : ‖B.targetFastNuisanceCoefficient
      xi hgamma hgap e Delta‖ ≤ CfastNuisance)
    (hlambda : |u MainCoord.slow / B.w| ≤ Clambda)
    (hslow : ‖B.actualTwoStageNuisanceCoefficient
      xi hgamma hgap e‖ ≤ CslowNuisance) :
    ‖B.exactNuisanceRegression xi hgamma hgap u‖ ≤
      CfastNuisance + Clambda * CslowNuisance := by
  rw [B.exactNuisanceRegression_eq_targetFast_add_twoStage
    xi hgamma hgap e he Delta u hu]
  calc
    ‖B.targetFastNuisanceCoefficient xi hgamma hgap e Delta +
        (u MainCoord.slow / B.w) •
          B.actualTwoStageNuisanceCoefficient xi hgamma hgap e‖ ≤
      ‖B.targetFastNuisanceCoefficient xi hgamma hgap e Delta‖ +
        ‖(u MainCoord.slow / B.w) •
          B.actualTwoStageNuisanceCoefficient xi hgamma hgap e‖ :=
      norm_add_le _ _
    _ = ‖B.targetFastNuisanceCoefficient xi hgamma hgap e Delta‖ +
        |u MainCoord.slow / B.w| *
          ‖B.actualTwoStageNuisanceCoefficient xi hgamma hgap e‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ CfastNuisance + Clambda * CslowNuisance :=
      add_le_add hfast
        (mul_le_mul hlambda hslow (norm_nonneg _) hClambda)

/-- The three component estimates required by Proposition 8.7, derived
from explicit two-stage target quantities.  In particular, the conclusion
is not assumed for arbitrary solutions of the Schur equation. -/
theorem exactSchur_solution_component_bounds_of_twoStageTargets
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ)
    {Cinv Tband Vlower Tslow Ccomp
      CfastNuisance CslowNuisance : ℝ}
    (hCinv : 0 ≤ Cinv) (hTband : 0 ≤ Tband)
    (hVlower : 0 < Vlower) (hTslow : 0 ≤ Tslow)
    (hCcomp : 0 ≤ Ccomp)
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (htargetBand : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.projectedNormalizedTargetBand Delta) ≤ Tband)
    (hvariance : Vlower ≤ B.actualTwoStageCompensatedVariance
      xi hgamma hgap e)
    (htargetSlow : |B.compensatedNormalizedTarget
      xi hgamma hgap e Delta| ≤ Tslow)
    (hcomp : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.actualCompensatedCoefficient
        (B.actualBandRegression xi hgamma hgap e) p| ≤ Ccomp)
    (hfastNuisance : ‖B.targetFastNuisanceCoefficient
      xi hgamma hgap e Delta‖ ≤ CfastNuisance)
    (hslowNuisance : ‖B.actualTwoStageNuisanceCoefficient
      xi hgamma hgap e‖ ≤ CslowNuisance)
    (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta)) :
    ‖fun p : BandPrime B.sampleData.n B.sampleData.W =>
        (B.rawGaugeOfMain u).1 (B.partition.band p) +
          (u MainCoord.slow / B.w) * B.primeDeviation p‖ ≤
        Cinv * Tband + (Tslow / Vlower) * Ccomp ∧
      ‖B.exactNuisanceRegression xi hgamma hgap u‖ ≤
        CfastNuisance + (Tslow / Vlower) * CslowNuisance ∧
      |u MainCoord.slow| ≤ B.w * (Tslow / Vlower) := by
  have hfast : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.fastGaugeOfMain xi hgamma hgap e u) ≤ Cinv * Tband := by
    calc
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one)
          (B.fastGaugeOfMain xi hgamma hgap e u) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one)
          (B.projectedNormalizedTargetBand Delta) :=
        B.fastGauge_paperSharpNorm_le_of_inverse
          xi hgamma hgap e he hinv Delta u hu
      _ ≤ Cinv * Tband :=
        mul_le_mul_of_nonneg_left htargetBand hCinv
  have hlambda : |u MainCoord.slow / B.w| ≤ Tslow / Vlower :=
    B.abs_slow_div_le_of_variance_target_bounds
      xi hgamma hgap e he Delta u hu hVlower hvariance
      hTslow htargetSlow
  have hClambda : 0 ≤ Tslow / Vlower :=
    div_nonneg hTslow hVlower.le
  have hprime := B.effectivePrimeVelocity_norm_le_of_fast_compensated
    xi hgamma hgap e u
    (mul_nonneg hCinv hTband) hClambda hCcomp hfast hlambda hcomp
  have hnuisance := B.exactNuisanceRegression_norm_le_of_twoStage
    xi hgamma hgap e he Delta u hu hClambda
      hfastNuisance hlambda hslowNuisance
  have hslow := B.abs_slow_le_of_variance_target_bounds
    xi hgamma hgap e he Delta u hu hVlower hvariance
      hTslow htargetSlow
  exact ⟨hprime, hnuisance, hslow⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
