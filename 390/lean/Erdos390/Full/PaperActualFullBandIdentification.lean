import Erdos390.Full.PaperExactSchurRawSlow
import Erdos390.Full.PaperActualSquarefreeReference

/-!
# Exact identification of the actual full-valuation band operator

The full-valuation sharp operator produced by Lemmas 7.5 and 8.4 is defined
through the bounded valuation law.  The nonlinear bridge is written through
covariance rows of the actual tilted sample.  This file proves that these
are the same finite operator before nuisance regression, and records the
exact sharp/raw gauge conjugacy.  No asymptotic estimate is used.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The bounded-law full band row is literally the normalized covariance row
of the actual tilted bridge law. -/
theorem fullBandRow_actualValuationLaw_eq_normalizedBandCovarianceRow
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) (i : Band) :
    PrimePowerSharpBandTransfer.fullBandRow
        (B.actualValuationLaw xi) B.partition q.1 i =
      B.normalizedBandCovarianceRow xi
        (B.bandRegressionScore q) i := by
  have hscore : B.bandRegressionScore q =
      fun m ↦ ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.bandRegressionCoefficient q p *
          ArithmeticModel.valuation p.1 (B.sampleData.value m) := by
    funext m
    exact B.bandRegressionScore_eq_primeSum q m
  rw [hscore]
  unfold PrimePowerSharpBandTransfer.fullBandRow
    normalizedBandCovarianceRow bandScore
    PrimePowerCovariance.BoundedValuationLaw.covVV
    PrimePowerCovariance.BoundedValuationLaw.V
    actualValuationLaw
  rw [FiniteProbability.covariance_sum_left]
  simp_rw [FiniteProbability.covariance_sum_right,
    FiniteProbability.covariance_smul_right]
  simp only [bandRegressionCoefficient]
  change (1 / B.harmonicMass i) * _ = _ / B.harmonicMass i
  ring

/-- The actual full-valuation operator on the paper's raw arithmetic gauge,
before the finite nuisance regression. -/
def actualBandFullLinearMap [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) : B.RawBandGauge →ₗ[ℝ] B.RawBandGauge where
  toFun q := B.projectRawBandVector
    (B.normalizedBandCovarianceRow xi (B.bandRegressionScore q))
  map_add' q r := by
    rw [B.bandRegressionScore_add,
      B.normalizedBandCovarianceRow_add,
      B.projectRawBandVector_add]
  map_smul' c q := by
    rw [B.bandRegressionScore_smul,
      B.normalizedBandCovarianceRow_smul,
      B.projectRawBandVector_smul]
    rfl

/-- Scaling the literal full sharp operator back to raw coordinates gives
exactly `actualBandFullLinearMap`. -/
theorem scale_actualFullProjected_eq_actualBandFull
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace)
    (q : PaperWeightedInverseExport.SharpGaugeSpace
      B.harmonicMass B.bandCenter) :
    scaleGaugeLinearEquiv B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualFullProjectedCLM xi q) =
      B.actualBandFullLinearMap xi
        (scaleGaugeLinearEquiv B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q) := by
  apply Subtype.ext
  funext i
  let S := scaleGaugeLinearEquiv B.harmonicMass B.bandCenter
    (B.partition.center_ne_zero B.n_gt_one)
  change B.bandCenter i *
      FiniteGraphQuotientInverse.meanProjection
        (MovingLowGaugeTransfer.sharpWeight
          B.harmonicMass B.bandCenter)
        (fun j ↦ PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q.1 j) i =
    MovingLowGaugeTransfer.weightedGaugeProjection
      B.harmonicMass B.bandCenter
      (B.normalizedBandCovarianceRow xi
        (B.bandRegressionScore (S q))) i
  have hrow :
      B.normalizedBandCovarianceRow xi
        (B.bandRegressionScore (S q)) =
      MovingLowGaugeTransfer.scaleByCenter B.bandCenter
        (fun j ↦ PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q.1 j) := by
    funext j
    rw [← B.fullBandRow_actualValuationLaw_eq_normalizedBandCovarianceRow]
    unfold PrimePowerSharpBandTransfer.fullSharpRow
    change PrimePowerSharpBandTransfer.fullBandRow
        (B.actualValuationLaw xi) B.partition (S q).1 j =
      B.bandCenter j *
        (PrimePowerSharpBandTransfer.fullBandRow
          (B.actualValuationLaw xi) B.partition
            (fun k ↦ B.bandCenter k * q.1 k) j / B.bandCenter j)
    have hscaled : (S q).1 =
        fun k ↦ B.bandCenter k * q.1 k := by
      funext k
      exact scaleGaugeLinearEquiv_apply
        B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one) q k
    rw [hscaled]
    exact (mul_div_cancel₀ _
      (B.partition.center_ne_zero B.n_gt_one j)).symm
  rw [hrow]
  exact (PaperWeightedInverseExport.weightedGaugeProjection_scale_eq
    B.harmonicMass B.bandCenter
    (fun j ↦ PrimePowerSharpBandTransfer.fullSharpRow
      (B.actualValuationLaw xi) B.partition q.1 j)
    (B.partition.center_ne_zero B.n_gt_one)
    (ne_of_gt B.sharpBandWeightTotal_pos) i).symm

/-- Exact finite nuisance-Schur correction.  The correction is displayed as
the projected normalized row of the actual regression coefficient; it is not
discarded as a generic `o(1)` perturbation. -/
theorem actualBandSchurLinearMap_eq_full_sub_nuisanceCorrection
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) :
    B.actualBandSchurLinearMap xi hgamma hgap q =
      B.actualBandFullLinearMap xi q -
        B.projectRawBandVector
          (B.normalizedBandCovarianceRow xi
            (fun m ↦ inner ℝ
              (B.nuisanceCoefficientOfScore xi hgamma hgap
                (B.bandRegressionScore q))
              (B.nuisanceStatistic m))) := by
  change B.projectRawBandVector
      (B.normalizedBandCovarianceRow xi
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))) =
    B.projectRawBandVector
        (B.normalizedBandCovarianceRow xi (B.bandRegressionScore q)) -
      B.projectRawBandVector
        (B.normalizedBandCovarianceRow xi
          (fun m ↦ inner ℝ
            (B.nuisanceCoefficientOfScore xi hgamma hgap
              (B.bandRegressionScore q))
            (B.nuisanceStatistic m)))
  unfold nuisanceResidualScore
  rw [B.normalizedBandCovarianceRow_sub]
  exact B.projectRawBandVector_sub _ _

/-- The literal nuisance-Schur operator transported to the sharp gauge in
which Lemma 8.4 supplies its inverse. -/
def actualSchurProjectedLinearMap [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    SharpGaugeSpace B.partition.mass B.partition.center →ₗ[ℝ]
      SharpGaugeSpace B.partition.mass B.partition.center :=
  let S := scaleGaugeLinearEquiv B.partition.mass B.partition.center
    (B.partition.center_ne_zero B.n_gt_one)
  S.symm.toLinearMap.comp
    ((B.actualBandSchurLinearMap xi hgamma hgap).comp S.toLinearMap)

def actualSchurProjectedCLM [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    SharpGaugeSpace B.partition.mass B.partition.center →L[ℝ]
      SharpGaugeSpace B.partition.mass B.partition.center :=
  (B.actualSchurProjectedLinearMap xi hgamma hgap).toContinuousLinearMap

@[simp] theorem actualSchurProjectedCLM_apply
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : SharpGaugeSpace B.partition.mass B.partition.center) :
    B.actualSchurProjectedCLM xi hgamma hgap q =
      (scaleGaugeLinearEquiv B.partition.mass B.partition.center
        (B.partition.center_ne_zero B.n_gt_one)).symm
        (B.actualBandSchurLinearMap xi hgamma hgap
          (scaleGaugeLinearEquiv B.partition.mass B.partition.center
            (B.partition.center_ne_zero B.n_gt_one) q)) := rfl

/-- Transport a sharp-gauge equivalence back to the paper's raw arithmetic
gauge by the exact centre scaling. -/
def rawBandEquivOfSharpEquiv [Nonempty Band]
    (e : SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
      SharpGaugeSpace B.partition.mass B.partition.center) :
    RawGaugeSpace B.partition.mass B.partition.center ≃ₗ[ℝ]
      RawGaugeSpace B.partition.mass B.partition.center :=
  let S := scaleGaugeLinearEquiv B.partition.mass B.partition.center
    (B.partition.center_ne_zero B.n_gt_one)
  S.symm.trans (e.toLinearEquiv.trans S)

/-- If the sharp equivalence represents the actual Schur operator, its raw
transport is literally `actualBandSchurLinearMap`. -/
theorem rawBandEquivOfSharpEquiv_eq_actualBandSchurLinearMap
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
      SharpGaugeSpace B.partition.mass B.partition.center)
    (he : ∀ q, e q = B.actualSchurProjectedCLM xi hgamma hgap q)
    (b : RawGaugeSpace B.partition.mass B.partition.center) :
    B.rawBandEquivOfSharpEquiv e b =
      B.actualBandSchurLinearMap xi hgamma hgap b := by
  let S := scaleGaugeLinearEquiv B.partition.mass B.partition.center
    (B.partition.center_ne_zero B.n_gt_one)
  change S (e (S.symm b)) = B.actualBandSchurLinearMap xi hgamma hgap b
  rw [he]
  change S (S.symm
    (B.actualBandSchurLinearMap xi hgamma hgap (S (S.symm b)))) = _
  rw [S.apply_symm_apply, S.apply_symm_apply]

/-- The sharp inverse estimate is exactly the paper's weighted raw-gauge
inverse estimate after transport. -/
theorem rawBandEquivOfSharpEquiv_symm_paperSharpNorm_le
    [Nonempty Band]
    (e : SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
      SharpGaugeSpace B.partition.mass B.partition.center)
    {C : ℝ} (hinv : ∀ v, ‖e.symm v‖ ≤ C * ‖v‖)
    (u : RawGaugeSpace B.partition.mass B.partition.center) :
    paperSharpNorm B.partition.mass B.partition.center
        (B.partition.center_ne_zero B.n_gt_one)
        ((B.rawBandEquivOfSharpEquiv e).symm u) ≤
      C * paperSharpNorm B.partition.mass B.partition.center
        (B.partition.center_ne_zero B.n_gt_one) u := by
  let S := scaleGaugeLinearEquiv B.partition.mass B.partition.center
    (B.partition.center_ne_zero B.n_gt_one)
  let Eraw := B.rawBandEquivOfSharpEquiv e
  change ‖S.symm (Eraw.symm u)‖ ≤ C * ‖S.symm u‖
  have hinvEq : Eraw.symm u = S (e.symm (S.symm u)) := by
    apply Eraw.injective
    rw [Eraw.apply_symm_apply]
    change u = S (e (S.symm (S (e.symm (S.symm u)))))
    rw [S.symm_apply_apply, e.apply_symm_apply, S.apply_symm_apply]
  rw [hinvEq, S.symm_apply_apply]
  exact hinv (S.symm u)

/-- A literal row-relative estimate for the finite nuisance correction gives
the sharp operator-norm perturbation used in the Schur step.  This theorem
contains no asymptotic input: the application must supply the displayed
row estimate, uniformly in the preselected tilt box. -/
theorem actualSchurProjectedCLM_sub_full_le_of_nuisanceCorrectionRow
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    {r : ℝ} (hr : 0 ≤ r)
    (hrow : ∀
      (q : SharpGaugeSpace B.partition.mass B.partition.center) (i : Band),
      |B.normalizedBandCovarianceRow xi
          (fun m ↦ inner ℝ
            (B.nuisanceCoefficientOfScore xi hgamma hgap
              (B.bandRegressionScore
                (scaleGaugeLinearEquiv B.partition.mass B.partition.center
                  (B.partition.center_ne_zero B.n_gt_one) q)))
            (B.nuisanceStatistic m)) i| ≤
        (r * ‖q‖) * B.bandCenter i)
    (q : SharpGaugeSpace B.partition.mass B.partition.center) :
    ‖(B.actualSchurProjectedCLM xi hgamma hgap -
        B.actualFullProjectedCLM xi) q‖ ≤
      (2 * r) * ‖q‖ := by
  let S := scaleGaugeLinearEquiv B.partition.mass B.partition.center
    (B.partition.center_ne_zero B.n_gt_one)
  let correction : Band → ℝ := fun i ↦
    B.normalizedBandCovarianceRow xi
      (fun m ↦ inner ℝ
        (B.nuisanceCoefficientOfScore xi hgamma hgap
          (B.bandRegressionScore (S q)))
        (B.nuisanceStatistic m)) i
  have hcorrection (i : Band) :
      |correction i| ≤ (r * ‖q‖) * B.bandCenter i := by
    exact hrow q i
  have hC : 0 ≤ r * ‖q‖ := mul_nonneg hr (norm_nonneg q)
  have hproject :
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one)
          (B.projectRawBandVector correction) ≤
        2 * (r * ‖q‖) :=
    B.projectRawBandVector_paperSharpNorm_le_two
      correction hC hcorrection
  have hfull :
      S.symm (B.actualBandFullLinearMap xi (S q)) =
        B.actualFullProjectedCLM xi q := by
    apply S.injective
    rw [S.apply_symm_apply]
    exact (B.scale_actualFullProjected_eq_actualBandFull xi q).symm
  have hschur :
      S.symm (B.actualBandSchurLinearMap xi hgamma hgap (S q)) =
        B.actualSchurProjectedCLM xi hgamma hgap q := by
    rfl
  rw [ContinuousLinearMap.sub_apply, ← hschur, ← hfull]
  rw [← map_sub]
  have hraw := B.actualBandSchurLinearMap_eq_full_sub_nuisanceCorrection
    xi hgamma hgap (S q)
  change ‖S.symm
      (B.actualBandSchurLinearMap xi hgamma hgap (S q) -
        B.actualBandFullLinearMap xi (S q))‖ ≤ (2 * r) * ‖q‖
  rw [hraw]
  simp only [sub_sub_cancel_left, map_neg, norm_neg]
  exact hproject.trans_eq (by ring)

/-- Two literal covariance-vector estimates imply the relative nuisance
correction row.  This is the exact finite aggregation needed to attach an
analytic marked-row theorem: `hsource` controls the nuisance coefficient,
while `hband` controls the marked output band.  The factor `1 / amin` is
kept visible, so at the moving low cell an application must prove a rate
strong enough to dominate the vanishing minimum centre. -/
theorem actualSchurProjectedCLM_sub_full_le_of_nuisanceCovarianceBounds
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    {Csource Crow amin : ℝ}
    (hCsource : 0 ≤ Csource) (hCrow : 0 ≤ Crow) (hamin : 0 < amin)
    (hcenter : ∀ i : Band, amin ≤ B.bandCenter i)
    (hsource : ∀ q :
      SharpGaugeSpace B.partition.mass B.partition.center,
      ‖B.nuisanceCovarianceVector xi
          (B.bandRegressionScore
            (scaleGaugeLinearEquiv B.partition.mass B.partition.center
              (B.partition.center_ne_zero B.n_gt_one) q))‖ ≤
        Csource * ‖q‖)
    (hband : ∀ i : Band,
      ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖ ≤
        Crow * B.harmonicMass i)
    (q : SharpGaugeSpace B.partition.mass B.partition.center) :
    ‖(B.actualSchurProjectedCLM xi hgamma hgap -
        B.actualFullProjectedCLM xi) q‖ ≤
      (2 * (((Csource / gamma) * Crow) / amin)) * ‖q‖ := by
  let A : ℝ := (Csource / gamma) * Crow
  have hA : 0 ≤ A := by
    exact mul_nonneg (div_nonneg hCsource hgamma.le) hCrow
  have hrow : ∀
      (q' : SharpGaugeSpace B.partition.mass B.partition.center) (i : Band),
      |B.normalizedBandCovarianceRow xi
          (fun m ↦ inner ℝ
            (B.nuisanceCoefficientOfScore xi hgamma hgap
              (B.bandRegressionScore
                (scaleGaugeLinearEquiv B.partition.mass B.partition.center
                  (B.partition.center_ne_zero B.n_gt_one) q')))
            (B.nuisanceStatistic m)) i| ≤
        ((A / amin) * ‖q'‖) * B.bandCenter i := by
    intro q' i
    let S' := scaleGaugeLinearEquiv B.partition.mass B.partition.center
      (B.partition.center_ne_zero B.n_gt_one)
    let z' := B.nuisanceCoefficientOfScore xi hgamma hgap
      (B.bandRegressionScore (S' q'))
    change |B.normalizedBandCovarianceRow xi
        (fun m ↦ inner ℝ z' (B.nuisanceStatistic m)) i| ≤ _
    have hz' : ‖z'‖ ≤ (Csource / gamma) * ‖q'‖ := by
      calc
        ‖z'‖ ≤
            ‖B.nuisanceCovarianceVector xi
              (B.bandRegressionScore (S' q'))‖ / gamma :=
          B.nuisanceCoefficientOfScore_norm_le xi hgamma hgap _
        _ ≤ (Csource * ‖q'‖) / gamma :=
          div_le_div_of_nonneg_right (hsource q') hgamma.le
        _ = (Csource / gamma) * ‖q'‖ := by ring
    have hH : 0 < B.harmonicMass i := B.harmonicMass_pos i
    unfold normalizedBandCovarianceRow
    rw [B.covariance_marked_nuisanceScore_eq_inner,
      abs_div, abs_of_pos hH]
    have hinner := abs_real_inner_le_norm z'
      (B.nuisanceCovarianceVector xi (B.bandScore i))
    calc
      |inner ℝ z' (B.nuisanceCovarianceVector xi (B.bandScore i))| /
            B.harmonicMass i ≤
          (‖z'‖ * ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖) /
            B.harmonicMass i :=
        div_le_div_of_nonneg_right hinner hH.le
      _ ≤ (((Csource / gamma) * ‖q'‖) *
            (Crow * B.harmonicMass i)) / B.harmonicMass i := by
        apply div_le_div_of_nonneg_right _ hH.le
        exact mul_le_mul hz' (hband i) (norm_nonneg _)
          (mul_nonneg (div_nonneg hCsource hgamma.le) (norm_nonneg q'))
      _ = A * ‖q'‖ := by
        dsimp only [A]
        field_simp [ne_of_gt hH]
      _ = ((A / amin) * ‖q'‖) * amin := by
        field_simp [ne_of_gt hamin]
      _ ≤ ((A / amin) * ‖q'‖) * B.bandCenter i :=
        mul_le_mul_of_nonneg_left (hcenter i)
          (mul_nonneg (div_nonneg hA hamin.le) (norm_nonneg q'))
  exact B.actualSchurProjectedCLM_sub_full_le_of_nuisanceCorrectionRow
    xi hgamma hgap (div_nonneg hA hamin.le) hrow q

/-- Stable inversion of the actual nuisance-Schur operator from the actual
full-valuation inverse.  The sole new analytic input is the explicit
`hrow` bound on the nuisance correction, in the same sharp relative scale
as the moving-low cell. -/
theorem exists_actualSchurProjectedEquiv_of_full_of_nuisanceCorrectionRow
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace)
    (fullEquiv :
      SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
        SharpGaugeSpace B.partition.mass B.partition.center)
    (hfull : ∀ q, fullEquiv q = B.actualFullProjectedCLM xi q)
    {gamma C r : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hinv : ∀ v, ‖fullEquiv.symm v‖ ≤ C * ‖v‖)
    (hsmall : C * (2 * r) < 1)
    (hrow : ∀
      (q : SharpGaugeSpace B.partition.mass B.partition.center) (i : Band),
      |B.normalizedBandCovarianceRow xi
          (fun m ↦ inner ℝ
            (B.nuisanceCoefficientOfScore xi hgamma hgap
              (B.bandRegressionScore
                (scaleGaugeLinearEquiv B.partition.mass B.partition.center
                  (B.partition.center_ne_zero B.n_gt_one) q)))
            (B.nuisanceStatistic m)) i| ≤
        (r * ‖q‖) * B.bandCenter i) :
    ∃ schurEquiv :
      SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
        SharpGaugeSpace B.partition.mass B.partition.center,
      (∀ q, schurEquiv q =
        B.actualSchurProjectedCLM xi hgamma hgap q) ∧
      ∀ v, ‖schurEquiv.symm v‖ ≤
        (C / (1 - C * (2 * r))) * ‖v‖ := by
  let A := B.actualFullProjectedCLM xi
  let Ainv : SharpGaugeSpace B.partition.mass B.partition.center →L[ℝ]
      SharpGaugeSpace B.partition.mass B.partition.center := fullEquiv.symm
  let E := B.actualSchurProjectedCLM xi hgamma hgap - A
  have hleft (q : SharpGaugeSpace B.partition.mass B.partition.center) :
      Ainv (A q) = q := by
    dsimp only [Ainv, A]
    rw [← hfull q]
    exact fullEquiv.symm_apply_apply q
  have hinv' (v : SharpGaugeSpace B.partition.mass B.partition.center) :
      ‖Ainv v‖ ≤ C * ‖v‖ := hinv v
  have herror (q : SharpGaugeSpace B.partition.mass B.partition.center) :
      ‖E q‖ ≤ (2 * r) * ‖q‖ := by
    dsimp only [E, A]
    exact B.actualSchurProjectedCLM_sub_full_le_of_nuisanceCorrectionRow
      xi hgamma hgap hr hrow q
  let schurEquiv := StableInverse.perturbedEquiv
    A Ainv E C (2 * r) hC hsmall hleft hinv' herror
  refine ⟨schurEquiv, ?_, ?_⟩
  · intro q
    rw [StableInverse.perturbedEquiv_apply]
    dsimp only [schurEquiv, E]
    simp only [add_sub_cancel]
  · intro v
    exact StableInverse.perturbed_inverse_bound
      A Ainv E C (2 * r) hC hsmall hleft hinv' herror v

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
