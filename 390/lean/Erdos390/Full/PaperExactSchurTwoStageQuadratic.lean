import Erdos390.Full.FiniteProbabilityCovarianceCauchySchwarz
import Erdos390.Full.PaperActualTwoStageRegression
import Erdos390.Full.PaperExactSchurRawSlow
import Erdos390.Full.PaperWeightedGaugeDGeometry

/-!
# Exact quadratic attachment for the two-stage Schur regression

This file supplies the finite-dimensional algebra between the arithmetic
band inverse of Lemma 8.4 and the compensated slow score of Lemma 8.6.  In
particular, no limiting operator, mesh estimate, or covariance lower bound
is assumed here.

The first identity identifies the quadratic form of the literal projected
band Schur operator with the variance of the nuisance-residual band score.
The second identity proves that the fast band residual and the fitted slow
score are exactly covariance-orthogonal.  Combining them gives the exact
fast/slow quadratic decomposition of the main Schur block used in
Proposition 8.7.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The exact arithmetic `D` pairing on raw band rows. -/
def bandDPairing (q r : B.RawBandGauge) : ℝ :=
  ∑ j : Band, B.harmonicMass j * q.1 j * r.1 j

/-- Projecting a normalized band row does not change its pairing with an
arithmetic-gauge vector.  This is the exact finite arithmetic centering
identity; in particular it does not replace the arithmetic centres by
continuum cell centres. -/
theorem weighted_pairing_projectRawBandVector
    [Nonempty Band]
    (q : B.RawBandGauge) (x : Band → ℝ) :
    (∑ j : Band, B.harmonicMass j * q.1 j *
        (B.projectRawBandVector x).1 j) =
      ∑ j : Band, B.harmonicMass j * q.1 j * x j := by
  let mu : ℝ :=
    (∑ k : Band, B.harmonicMass k * B.bandCenter k * x k) /
      sharpWeightTotal B.harmonicMass B.bandCenter
  have hcoord (j : Band) :
      (B.projectRawBandVector x).1 j = x j - B.bandCenter j * mu := by
    change weightedGaugeProjection B.harmonicMass B.bandCenter x j = _
    unfold weightedGaugeProjection
    rfl
  rw [show (∑ j : Band, B.harmonicMass j * q.1 j *
      (B.projectRawBandVector x).1 j) =
      (∑ j : Band, B.harmonicMass j * q.1 j * x j) -
        mu * (∑ j : Band,
          rawGaugeWeight B.harmonicMass B.bandCenter j * q.1 j) by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcoord]
    unfold rawGaugeWeight
    ring]
  have hq := q.2
  change (∑ j : Band,
    rawGaugeWeight B.harmonicMass B.bandCenter j * q.1 j) = 0 at hq
  rw [hq, mul_zero, sub_zero]

/-- The quadratic form of the literal arithmetic band Schur map is exactly
the variance of the band score after the actual finite nuisance regression.
This is an equality at finite `n`, in the arithmetic `D`-pairing. -/
theorem actualBandSchur_quadratic_eq_residualVariance
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) :
    (∑ j : Band, B.harmonicMass j * q.1 j *
        (B.actualBandSchurLinearMap xi hgamma hgap q).1 j) =
      (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q)) := by
  let F : B.sampleData.Sample → ℝ := B.bandRegressionScore q
  let a : B.NuisanceSpace :=
    B.nuisanceCoefficientOfScore xi hgamma hgap F
  let Z : B.sampleData.Sample → ℝ :=
    fun m ↦ inner ℝ a (B.nuisanceStatistic m)
  let R : B.sampleData.Sample → ℝ :=
    B.nuisanceResidualScore xi hgamma hgap F
  have hF : F = fun m ↦ R m + Z m := by
    funext m
    simp only [F, R, Z, a]
    unfold nuisanceResidualScore
    ring
  have horth : (B.tiltedLaw xi).covariance Z R = 0 := by
    simpa only [Z, R, a] using
      B.nuisanceResidualScore_covariance_zero
        xi hgamma hgap F a
  calc
    (∑ j : Band, B.harmonicMass j * q.1 j *
        (B.actualBandSchurLinearMap xi hgamma hgap q).1 j) =
        ∑ j : Band, B.harmonicMass j * q.1 j *
          B.normalizedBandCovarianceRow xi R j := by
      exact B.weighted_pairing_projectRawBandVector q
        (B.normalizedBandCovarianceRow xi R)
    _ = (B.tiltedLaw xi).covariance F R := by
      exact (B.covariance_bandRegressionScore_eq_weightedRow
        xi q R).symm
    _ = (B.tiltedLaw xi).covariance R R := by
      rw [hF, FiniteProbability.covariance_add_left, horth, add_zero]

/-- Bilinear form of the preceding identity.  It is needed for the
covariance Cauchy--Schwarz conversion from a sharp inverse bound to a
positive `D`-quadratic gap. -/
theorem actualBandSchur_bilinear_eq_residualCovariance
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q r : B.RawBandGauge) :
    B.bandDPairing q (B.actualBandSchurLinearMap xi hgamma hgap r) =
      (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore r)) := by
  let Fq : B.sampleData.Sample → ℝ := B.bandRegressionScore q
  let Fr : B.sampleData.Sample → ℝ := B.bandRegressionScore r
  let aq : B.NuisanceSpace :=
    B.nuisanceCoefficientOfScore xi hgamma hgap Fq
  let Zq : B.sampleData.Sample → ℝ :=
    fun m ↦ inner ℝ aq (B.nuisanceStatistic m)
  let Rq : B.sampleData.Sample → ℝ :=
    B.nuisanceResidualScore xi hgamma hgap Fq
  let Rr : B.sampleData.Sample → ℝ :=
    B.nuisanceResidualScore xi hgamma hgap Fr
  have hFq : Fq = fun m ↦ Rq m + Zq m := by
    funext m
    simp only [Fq, Rq, Zq, aq]
    unfold nuisanceResidualScore
    ring
  have horth : (B.tiltedLaw xi).covariance Zq Rr = 0 := by
    simpa only [Zq, Rr, aq] using
      B.nuisanceResidualScore_covariance_zero
        xi hgamma hgap Fr aq
  calc
    B.bandDPairing q (B.actualBandSchurLinearMap xi hgamma hgap r) =
        ∑ j : Band, B.harmonicMass j * q.1 j *
          B.normalizedBandCovarianceRow xi Rr j := by
      unfold bandDPairing
      exact B.weighted_pairing_projectRawBandVector q
        (B.normalizedBandCovarianceRow xi Rr)
    _ = (B.tiltedLaw xi).covariance Fq Rr := by
      exact (B.covariance_bandRegressionScore_eq_weightedRow
        xi q Rr).symm
    _ = (B.tiltedLaw xi).covariance Rq Rr := by
      rw [hFq, FiniteProbability.covariance_add_left, horth, add_zero]

/-- Covariance Cauchy--Schwarz converts an inverse bound for the literal
band Schur map into a quantitative `D`-quadratic estimate.  The two displayed
`D` comparisons are pure finite weighted-gauge geometry; they are kept as
arguments here so this analytic attachment cannot silently change norms. -/
theorem actualBandSchur_quadratic_mul_bound_of_inverse
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    {Cinv Dlower Dupper : ℝ}
    (hCinv : 0 ≤ Cinv) (hDlower : 0 ≤ Dlower)
    (hDupper : 0 ≤ Dupper)
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (hDdiag : ∀ v,
      Dlower *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) v ^ 2 ≤
        B.bandDPairing v v)
    (hDbilin : ∀ v u,
      |B.bandDPairing v u| ≤
        Dupper *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) v *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) u)
    (q : B.RawBandGauge) :
    Dlower ^ 2 *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
      (Dupper * Cinv) *
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore q))
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore q)) := by
  let S : B.RawBandGauge → ℝ := fun v ↦
    paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) v
  let R : B.RawBandGauge → B.sampleData.Sample → ℝ := fun v ↦
    B.nuisanceResidualScore xi hgamma hgap (B.bandRegressionScore v)
  let Q : B.RawBandGauge → ℝ := fun v ↦
    (B.tiltedLaw xi).covariance (R v) (R v)
  let y : B.RawBandGauge := e.symm q
  have hey : B.actualBandSchurLinearMap xi hgamma hgap y = q := by
    rw [← he, LinearEquiv.apply_symm_apply]
  have hDqq : Dlower * S q ^ 2 ≤ B.bandDPairing q q := hDdiag q
  have hDqq0 : 0 ≤ B.bandDPairing q q :=
    (mul_nonneg hDlower (sq_nonneg _)).trans hDqq
  have hcross : B.bandDPairing q q =
      (B.tiltedLaw xi).covariance (R q) (R y) := by
    calc
      B.bandDPairing q q =
          B.bandDPairing q
            (B.actualBandSchurLinearMap xi hgamma hgap y) := by rw [hey]
      _ = (B.tiltedLaw xi).covariance (R q) (R y) :=
        B.actualBandSchur_bilinear_eq_residualCovariance
          xi hgamma hgap q y
  have hcs : (B.bandDPairing q q) ^ 2 ≤ Q q * Q y := by
    rw [hcross]
    exact (B.tiltedLaw xi).covariance_sq_le_mul_self (R q) (R y)
  have hQy : Q y = B.bandDPairing y q := by
    calc
      Q y = B.bandDPairing y
          (B.actualBandSchurLinearMap xi hgamma hgap y) :=
        (B.actualBandSchur_quadratic_eq_residualVariance
          xi hgamma hgap y).symm
      _ = B.bandDPairing y q := by rw [hey]
  have hSy : S y ≤ Cinv * S q := hinv q
  have hS0 (v : B.RawBandGauge) : 0 ≤ S v := by
    exact norm_nonneg _
  have hQy0 : 0 ≤ Q y :=
    (B.tiltedLaw xi).covariance_self_nonneg (R y)
  have hQq0 : 0 ≤ Q q :=
    (B.tiltedLaw xi).covariance_self_nonneg (R q)
  have hQyUpper : Q y ≤ Dupper * Cinv * S q ^ 2 := by
    rw [hQy]
    calc
      B.bandDPairing y q ≤ |B.bandDPairing y q| := le_abs_self _
      _ ≤ Dupper * S y * S q := hDbilin y q
      _ ≤ Dupper * (Cinv * S q) * S q := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hSy hDupper) (hS0 q)
      _ = Dupper * Cinv * S q ^ 2 := by ring
  by_cases hSq : S q = 0
  · change Dlower ^ 2 * S q ^ 2 ≤ (Dupper * Cinv) * Q q
    rw [hSq]
    norm_num
    exact mul_nonneg (mul_nonneg hDupper hCinv) hQq0
  · have hSqPos : 0 < S q := lt_of_le_of_ne (hS0 q) (Ne.symm hSq)
    have hDsq : (Dlower * S q ^ 2) ^ 2 ≤
        (B.bandDPairing q q) ^ 2 := by
      exact sq_le_sq₀ (mul_nonneg hDlower (sq_nonneg _)) hDqq0 |>.2 hDqq
    have hmaster : (Dlower * S q ^ 2) ^ 2 ≤
        Q q * (Dupper * Cinv * S q ^ 2) := by
      exact hDsq.trans (hcs.trans
        (mul_le_mul_of_nonneg_left hQyUpper hQq0))
    nlinarith [sq_pos_of_pos hSqPos]

/-- Division form of the preceding quantitative gap. -/
theorem actualBandSchur_quadratic_lower_of_inverse
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    {Cinv Dlower Dupper : ℝ}
    (hCinv : 0 < Cinv) (hDlower : 0 ≤ Dlower)
    (hDupper : 0 < Dupper)
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (hDdiag : ∀ v,
      Dlower *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) v ^ 2 ≤
        B.bandDPairing v v)
    (hDbilin : ∀ v u,
      |B.bandDPairing v u| ≤
        Dupper *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) v *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) u)
    (q : B.RawBandGauge) :
    (Dlower ^ 2 / (Dupper * Cinv)) *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q)) := by
  have hmul := B.actualBandSchur_quadratic_mul_bound_of_inverse
    xi hgamma hgap e he hCinv.le hDlower hDupper.le
    hinv hDdiag hDbilin q
  have hden : 0 < Dupper * Cinv := mul_pos hDupper hCinv
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).2
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Literal arithmetic specialization of the inverse-to-quadratic theorem.
The two `D` constants and both weighted inequalities are now conclusions of
the finite positive harmonic masses and centres. -/
theorem actualBandSchur_quadratic_lower_of_inverse_arithmetic
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    {Cinv : ℝ} (hCinv : 0 < Cinv)
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (q : B.RawBandGauge) :
    (rawDLowerWeight B.harmonicMass B.bandCenter ^ 2 /
        (sharpWeightTotal B.harmonicMass B.bandCenter * Cinv)) *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q)) := by
  apply B.actualBandSchur_quadratic_lower_of_inverse
    xi hgamma hgap e he hCinv
    (rawDLowerWeight_pos B.harmonicMass B.bandCenter
      B.harmonicMass_pos
      (B.partition.center_ne_zero B.n_gt_one)).le
    B.sharpBandWeightTotal_pos
    hinv
  · intro v
    simpa only [bandDPairing, rawDPairing] using
      rawDLowerWeight_mul_paperSharpNorm_sq_le
        B.harmonicMass B.bandCenter B.harmonicMass_pos
        (B.partition.center_ne_zero B.n_gt_one) v
  · intro v u
    simpa only [bandDPairing, rawDPairing] using
      abs_rawDPairing_le_sharpWeightTotal_mul
        B.harmonicMass B.bandCenter B.harmonicMass_pos
        (B.partition.center_ne_zero B.n_gt_one) v u

/-- The nuisance-residual fast band score is exactly orthogonal to the
two-stage compensated slow score.  Both the band normal equation and the
nuisance normal equation are used; neither orthogonality is postulated. -/
theorem fastResidual_covariance_twoStageCompensated_eq_zero
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (qFast : B.RawBandGauge) :
    (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore qFast))
        (B.actualTwoStageCompensatedScore xi hgamma hgap e) = 0 := by
  let a : B.NuisanceSpace := B.nuisanceCoefficientOfScore xi hgamma hgap
    (B.bandRegressionScore qFast)
  have hband : (B.tiltedLaw xi).covariance
      (B.bandRegressionScore qFast)
      (B.actualTwoStageCompensatedScore xi hgamma hgap e) = 0 :=
    (B.actualTwoStageCompensatedScore_orthogonal
      xi hgamma hgap e he).2 qFast
  have hnuisance : (B.tiltedLaw xi).covariance
      (fun m ↦ inner ℝ a (B.nuisanceStatistic m))
      (B.actualTwoStageCompensatedScore xi hgamma hgap e) = 0 :=
    (B.actualTwoStageCompensatedScore_orthogonal
      xi hgamma hgap e he).1 a
  have hresidual :
      B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore qFast) =
        fun m ↦ B.bandRegressionScore qFast m -
          inner ℝ a (B.nuisanceStatistic m) := by
    rfl
  rw [hresidual]
  have hsub : (fun m ↦ B.bandRegressionScore qFast m -
      inner ℝ a (B.nuisanceStatistic m)) =
      fun m ↦ B.bandRegressionScore qFast m +
        (-1 : ℝ) * inner ℝ a (B.nuisanceStatistic m) := by
    funext m
    ring
  rw [hsub, FiniteProbability.covariance_add_left,
    FiniteProbability.covariance_smul_left, hband, hnuisance]
  ring

/-- Exact Pythagorean identity for the finite two-stage regression. -/
theorem covariance_fast_add_slow_twoStage
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (qFast : B.RawBandGauge) (lambda : ℝ) :
    (B.tiltedLaw xi).covariance
        (fun m ↦
          B.nuisanceResidualScore xi hgamma hgap
              (B.bandRegressionScore qFast) m +
            lambda * B.actualTwoStageCompensatedScore
              xi hgamma hgap e m)
        (fun m ↦
          B.nuisanceResidualScore xi hgamma hgap
              (B.bandRegressionScore qFast) m +
            lambda * B.actualTwoStageCompensatedScore
              xi hgamma hgap e m) =
      (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore qFast))
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore qFast)) +
        lambda ^ 2 * (B.tiltedLaw xi).covariance
          (B.actualTwoStageCompensatedScore xi hgamma hgap e)
          (B.actualTwoStageCompensatedScore xi hgamma hgap e) := by
  let F := B.nuisanceResidualScore xi hgamma hgap
    (B.bandRegressionScore qFast)
  let C := B.actualTwoStageCompensatedScore xi hgamma hgap e
  have hFC : (B.tiltedLaw xi).covariance F C = 0 := by
    exact B.fastResidual_covariance_twoStageCompensated_eq_zero
      xi hgamma hgap e he qFast
  have hCF : (B.tiltedLaw xi).covariance C F = 0 := by
    rw [(B.tiltedLaw xi).covariance_comm]
    exact hFC
  rw [FiniteProbability.covariance_add_left,
    FiniteProbability.covariance_add_right,
    FiniteProbability.covariance_add_right,
    FiniteProbability.covariance_smul_left,
    FiniteProbability.covariance_smul_right,
    FiniteProbability.covariance_smul_right,
    hFC, hCF]
  rw [FiniteProbability.covariance_smul_left]
  ring

/-- Exact quadratic decomposition of the actual main Schur block.  For the
canonical first-stage regression `qReg`, every main vector is written with
raw coordinate `qFast - lambda qReg` and stored slow coordinate
`w * lambda`.  The resulting Schur quadratic form is the sum of the fast
band residual variance and `lambda^2` times the fully compensated slow
variance. -/
theorem exactSchur_quadratic_eq_fast_add_slow_twoStage
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (u : B.MainSpace) (qFast : B.RawBandGauge) (lambda : ℝ)
    (hq : B.rawGaugeOfMain u = qFast - lambda •
      B.actualBandRegression xi hgamma hgap e)
    (hslow : u MainCoord.slow = B.w * lambda) :
    inner ℝ u (B.exactSchurCovarianceOperator xi hgamma hgap u) =
      (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore qFast))
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore qFast)) +
        lambda ^ 2 * (B.tiltedLaw xi).covariance
          (B.actualTwoStageCompensatedScore xi hgamma hgap e)
          (B.actualTwoStageCompensatedScore xi hgamma hgap e) := by
  rw [B.exactSchurCovarianceOperator_quadratic,
    B.inner_covarianceOperator]
  have hscore := B.vectorScore_exactSchurResidual_fast_add_compensated
    xi hgamma hgap u qFast
      (B.actualBandRegression xi hgamma hgap e) lambda hq hslow
  have hinnerScore :
      (fun m ↦ inner ℝ
        (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) u)
        (B.statistic m)) =
      fun m ↦ B.vectorFamily.scalarFamily.score m
        (B.schurResidual
          (B.exactNuisanceRegression xi hgamma hgap) u) := by
    funext m
    simp only [VectorExponentialFamily.scalarFamily, innerSL_apply_apply]
    exact real_inner_comm _ _
  rw [hinnerScore, hscore]
  exact B.covariance_fast_add_slow_twoStage
    xi hgamma hgap e he qFast lambda

/-- Deterministic fast/slow coercivity assembly.  The only coordinate input
is the displayed comparison between the concrete Euclidean `MainSpace` norm
and the intrinsic sharp-fast/stored-slow coordinates.  The analytic inputs
are exactly the fast band variance lower bound and the compensated slow
variance lower bound; an undischarged Schur-gap hypothesis is not used. -/
theorem exactSchurGap_of_fastSlow
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gammaNuisance : ℝ}
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q,
      e q = B.actualBandSchurLinearMap
        xi hgammaNuisance hGamma q)
    {gammaFast gammaSlow Ccoord : ℝ}
    (hgammaFast : 0 < gammaFast)
    (hgammaSlow : 0 < gammaSlow)
    (hCcoord : 0 < Ccoord)
    (hfast : ∀ q,
      gammaFast *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore q))
          (B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore q)))
    (hslow : gammaSlow * B.w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e)
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e))
    (hcoordinate : ∀ (u : B.MainSpace) (qFast : B.RawBandGauge)
        (lambda : ℝ),
      B.rawGaugeOfMain u = qFast - lambda •
          B.actualBandRegression xi hgammaNuisance hGamma e →
      u MainCoord.slow = B.w * lambda →
      ‖u‖ ^ 2 ≤ Ccoord *
        (paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) qFast ^ 2 +
          (B.w * lambda) ^ 2)) :
    ∀ u,
      (min gammaFast gammaSlow / Ccoord) * ‖u‖ ^ 2 ≤
        inner ℝ
          (B.schurResidual
            (B.exactNuisanceRegression
              xi hgammaNuisance hGamma) u)
          (B.covarianceOperator xi
            (B.schurResidual
              (B.exactNuisanceRegression
                xi hgammaNuisance hGamma) u)) := by
  intro u
  let lambda : ℝ := u MainCoord.slow / B.w
  let qReg : B.RawBandGauge :=
    B.actualBandRegression xi hgammaNuisance hGamma e
  let qFast : B.RawBandGauge := B.rawGaugeOfMain u + lambda • qReg
  have hq : B.rawGaugeOfMain u = qFast - lambda • qReg := by
    simp only [qFast]
    abel
  have hstored : u MainCoord.slow = B.w * lambda := by
    dsimp only [lambda]
    field_simp [ne_of_gt B.w_pos]
  have hcoord := hcoordinate u qFast lambda hq (by
    simpa only [qReg] using hstored)
  have hdecomp := B.exactSchur_quadratic_eq_fast_add_slow_twoStage
    xi hgammaNuisance hGamma e he u qFast lambda hq
      (by simpa only [qReg] using hstored)
  let S : ℝ := paperSharpNorm B.harmonicMass B.bandCenter
    (B.partition.center_ne_zero B.n_gt_one) qFast
  let Vfast : ℝ := (B.tiltedLaw xi).covariance
    (B.nuisanceResidualScore xi hgammaNuisance hGamma
      (B.bandRegressionScore qFast))
    (B.nuisanceResidualScore xi hgammaNuisance hGamma
      (B.bandRegressionScore qFast))
  let Vslow : ℝ := (B.tiltedLaw xi).covariance
    (B.actualTwoStageCompensatedScore xi hgammaNuisance hGamma e)
    (B.actualTwoStageCompensatedScore xi hgammaNuisance hGamma e)
  have hfast' : gammaFast * S ^ 2 ≤ Vfast := hfast qFast
  have hslow' : gammaSlow * B.w ^ 2 ≤ Vslow := hslow
  have hlambdaSq : 0 ≤ lambda ^ 2 := sq_nonneg _
  have hslowScaled : gammaSlow * (B.w * lambda) ^ 2 ≤
      lambda ^ 2 * Vslow := by
    have := mul_le_mul_of_nonneg_left hslow' hlambdaSq
    nlinarith
  have hminFast : min gammaFast gammaSlow * S ^ 2 ≤ Vfast :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg S)).trans
      hfast'
  have hminSlow : min gammaFast gammaSlow * (B.w * lambda) ^ 2 ≤
      lambda ^ 2 * Vslow :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _)
      (sq_nonneg (B.w * lambda))).trans hslowScaled
  have hsum : min gammaFast gammaSlow *
      (S ^ 2 + (B.w * lambda) ^ 2) ≤
      Vfast + lambda ^ 2 * Vslow := by
    nlinarith
  have hminPos : 0 < min gammaFast gammaSlow :=
    lt_min hgammaFast hgammaSlow
  have hscaledCoord :
      (min gammaFast gammaSlow / Ccoord) * ‖u‖ ^ 2 ≤
        min gammaFast gammaSlow *
          (S ^ 2 + (B.w * lambda) ^ 2) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hCcoord).2
    have hmul := mul_le_mul_of_nonneg_left hcoord hminPos.le
    dsimp only [S] at hmul ⊢
    nlinarith
  rw [← B.exactSchurCovarianceOperator_quadratic]
  rw [hdecomp]
  exact hscaledCoord.trans hsum

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
