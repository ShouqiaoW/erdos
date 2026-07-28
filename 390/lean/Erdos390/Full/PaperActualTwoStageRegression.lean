import Erdos390.Full.PaperActualPrimePowerRelative

/-!
# The literal two-stage band/nuisance solve of Lemma 8.6

This file defines the actual Schur-projected band operator on the exact raw
arithmetic gauge.  The first regression vector is obtained by inverting this
literal operator on the literal Schur-projected raw slow-score column.  The
second regression is then the actual nuisance inverse already constructed in
`PaperActualCompensatedRegression`.

No covariance matrix, inverse, or regression conclusion is stored in bridge
data.  The equivalence argument of the first-stage constructor is intended to
be supplied by the actual projected inverse conclusion of Lemma 8.4.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport
open CompressedArithmeticOperator
open MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Positivity of the exact projection denominator
`sum_j H_j alpha_j^2`. -/
theorem sharpBandWeightTotal_pos [Nonempty Band] :
    0 < sharpWeightTotal B.harmonicMass B.bandCenter := by
  unfold sharpWeightTotal sharpWeight
  apply Finset.sum_pos
  · intro j hj
    exact mul_pos (B.harmonicMass_pos j)
      (sq_pos_of_pos (B.bandCenter_pos j))
  · exact Finset.univ_nonempty

/-- Exact arithmetic projection of a raw band row to
`sum_j H_j alpha_j b_j = 0`. -/
def projectRawBandVector [Nonempty Band]
    (x : Band → ℝ) : B.RawBandGauge :=
  ⟨weightedGaugeProjection B.harmonicMass B.bandCenter x,
    weightedGaugeProjection_mem_rawGauge
      B.harmonicMass B.bandCenter x
      (ne_of_gt B.sharpBandWeightTotal_pos)⟩

theorem projectRawBandVector_add [Nonempty Band]
    (x y : Band → ℝ) :
    B.projectRawBandVector (x + y) =
      B.projectRawBandVector x + B.projectRawBandVector y := by
  apply Subtype.ext
  change weightedGaugeProjection B.harmonicMass B.bandCenter (x + y) =
    weightedGaugeProjection B.harmonicMass B.bandCenter x +
      weightedGaugeProjection B.harmonicMass B.bandCenter y
  exact weightedGaugeProjection_add
    B.harmonicMass B.bandCenter x y

theorem projectRawBandVector_smul [Nonempty Band]
    (a : ℝ) (x : Band → ℝ) :
    B.projectRawBandVector (a • x) =
      a • B.projectRawBandVector x := by
  apply Subtype.ext
  change weightedGaugeProjection B.harmonicMass B.bandCenter (a • x) =
    a • weightedGaugeProjection B.harmonicMass B.bandCenter x
  exact weightedGaugeProjection_smul
    B.harmonicMass B.bandCenter a x

theorem projectRawBandVector_sub [Nonempty Band]
    (x y : Band → ℝ) :
    B.projectRawBandVector (x - y) =
      B.projectRawBandVector x - B.projectRawBandVector y := by
  apply Subtype.ext
  funext j
  change weightedGaugeProjection B.harmonicMass B.bandCenter (x - y) j =
    weightedGaugeProjection B.harmonicMass B.bandCenter x j -
      weightedGaugeProjection B.harmonicMass B.bandCenter y j
  have hsum :
      (∑ k : Band,
        B.harmonicMass k * B.bandCenter k * (x k - y k)) =
      (∑ k : Band, B.harmonicMass k * B.bandCenter k * x k) -
        ∑ k : Band, B.harmonicMass k * B.bandCenter k * y k := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  unfold weightedGaugeProjection
  simp only [Pi.sub_apply, hsum]
  ring

/-- The kernel of the exact arithmetic projection is orthogonal to every
raw-gauge vector in the `D` pairing. -/
theorem weighted_sum_eq_zero_of_projectRawBandVector_eq_zero
    [Nonempty Band]
    (x : Band → ℝ) (q : B.RawBandGauge)
    (hx : B.projectRawBandVector x = 0) :
    (∑ j : Band, B.harmonicMass j * q.1 j * x j) = 0 := by
  let mu : ℝ :=
    (∑ k : Band, B.harmonicMass k * B.bandCenter k * x k) /
      sharpWeightTotal B.harmonicMass B.bandCenter
  have hxcoord (j : Band) : x j = B.bandCenter j * mu := by
    have hzero := congrArg (fun v : B.RawBandGauge ↦ v.1 j) hx
    change weightedGaugeProjection B.harmonicMass B.bandCenter x j = 0 at hzero
    unfold weightedGaugeProjection at hzero
    dsimp only [mu]
    linarith
  calc
    (∑ j : Band, B.harmonicMass j * q.1 j * x j) =
        mu * ∑ j : Band,
          rawGaugeWeight B.harmonicMass B.bandCenter j * q.1 j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hxcoord j]
      unfold rawGaugeWeight
      ring
    _ = 0 := by
      have hq := q.2
      change (∑ j : Band,
        rawGaugeWeight B.harmonicMass B.bandCenter j * q.1 j) = 0 at hq
      rw [hq, mul_zero]

/-- The literal normalized covariance row `D^{-1} Cov(Omega,F)`. -/
def normalizedBandCovarianceRow [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ) (j : Band) : ℝ :=
  (B.tiltedLaw xi).covariance (B.bandScore j) F /
    B.harmonicMass j

theorem normalizedBandCovarianceRow_add [Nonempty Head]
    (xi : B.ParamSpace) (F G : B.sampleData.Sample → ℝ) :
    B.normalizedBandCovarianceRow xi (fun m ↦ F m + G m) =
      B.normalizedBandCovarianceRow xi F +
        B.normalizedBandCovarianceRow xi G := by
  funext j
  unfold normalizedBandCovarianceRow
  rw [FiniteProbability.covariance_add_right]
  simp only [Pi.add_apply]
  ring

theorem normalizedBandCovarianceRow_smul [Nonempty Head]
    (xi : B.ParamSpace) (a : ℝ) (F : B.sampleData.Sample → ℝ) :
    B.normalizedBandCovarianceRow xi (fun m ↦ a * F m) =
      a • B.normalizedBandCovarianceRow xi F := by
  funext j
  unfold normalizedBandCovarianceRow
  rw [FiniteProbability.covariance_smul_right]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem normalizedBandCovarianceRow_sub [Nonempty Head]
    (xi : B.ParamSpace) (F G : B.sampleData.Sample → ℝ) :
    B.normalizedBandCovarianceRow xi (fun m ↦ F m - G m) =
      B.normalizedBandCovarianceRow xi F -
        B.normalizedBandCovarianceRow xi G := by
  have hsub : (fun m ↦ F m - G m) =
      fun m ↦ F m + (-1 : ℝ) * G m := by
    funext m
    ring
  rw [hsub, B.normalizedBandCovarianceRow_add,
    B.normalizedBandCovarianceRow_smul]
  funext j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem nuisanceCovarianceVector_add [Nonempty Head]
    (xi : B.ParamSpace) (F G : B.sampleData.Sample → ℝ) :
    B.nuisanceCovarianceVector xi (fun m ↦ F m + G m) =
      B.nuisanceCovarianceVector xi F +
        B.nuisanceCovarianceVector xi G := by
  apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
  funext c
  change (B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m c) (fun m ↦ F m + G m) = _
  rw [FiniteProbability.covariance_add_right]
  rfl

theorem nuisanceCovarianceVector_smul [Nonempty Head]
    (xi : B.ParamSpace) (a : ℝ) (F : B.sampleData.Sample → ℝ) :
    B.nuisanceCovarianceVector xi (fun m ↦ a * F m) =
      a • B.nuisanceCovarianceVector xi F := by
  apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
  funext c
  change (B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m c) (fun m ↦ a * F m) = _
  rw [FiniteProbability.covariance_smul_right]
  rfl

theorem nuisanceCoefficientOfScore_add [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F G : B.sampleData.Sample → ℝ) :
    B.nuisanceCoefficientOfScore xi hgamma hgap
        (fun m ↦ F m + G m) =
      B.nuisanceCoefficientOfScore xi hgamma hgap F +
        B.nuisanceCoefficientOfScore xi hgamma hgap G := by
  unfold nuisanceCoefficientOfScore
  rw [B.nuisanceCovarianceVector_add xi F G]
  exact (B.nuisanceCovarianceEquiv xi hgamma hgap).symm.map_add _ _

theorem nuisanceCoefficientOfScore_smul [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (a : ℝ) (F : B.sampleData.Sample → ℝ) :
    B.nuisanceCoefficientOfScore xi hgamma hgap (fun m ↦ a * F m) =
      a • B.nuisanceCoefficientOfScore xi hgamma hgap F := by
  unfold nuisanceCoefficientOfScore
  rw [B.nuisanceCovarianceVector_smul xi a F]
  exact (B.nuisanceCovarianceEquiv xi hgamma hgap).symm.map_smul a _

theorem nuisanceResidualScore_add [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F G : B.sampleData.Sample → ℝ) :
    B.nuisanceResidualScore xi hgamma hgap (fun m ↦ F m + G m) =
      fun m ↦ B.nuisanceResidualScore xi hgamma hgap F m +
        B.nuisanceResidualScore xi hgamma hgap G m := by
  funext m
  unfold nuisanceResidualScore
  rw [B.nuisanceCoefficientOfScore_add xi hgamma hgap F G,
    inner_add_left]
  ring

theorem nuisanceResidualScore_smul [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (a : ℝ) (F : B.sampleData.Sample → ℝ) :
    B.nuisanceResidualScore xi hgamma hgap (fun m ↦ a * F m) =
      fun m ↦ a * B.nuisanceResidualScore xi hgamma hgap F m := by
  funext m
  unfold nuisanceResidualScore
  rw [B.nuisanceCoefficientOfScore_smul xi hgamma hgap a F,
    inner_smul_left]
  simp only [conj_trivial]
  ring

theorem nuisanceResidualScore_sub [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F G : B.sampleData.Sample → ℝ) :
    B.nuisanceResidualScore xi hgamma hgap (fun m ↦ F m - G m) =
      fun m ↦ B.nuisanceResidualScore xi hgamma hgap F m -
        B.nuisanceResidualScore xi hgamma hgap G m := by
  have hsub : (fun m ↦ F m - G m) =
      fun m ↦ F m + (-1 : ℝ) * G m := by
    funext m
    ring
  rw [hsub, B.nuisanceResidualScore_add xi hgamma hgap,
    B.nuisanceResidualScore_smul xi hgamma hgap]
  funext m
  ring

theorem bandRegressionScore_add
    (q r : B.RawBandGauge) :
    B.bandRegressionScore (q + r) =
      fun m ↦ B.bandRegressionScore q m + B.bandRegressionScore r m := by
  funext m
  unfold bandRegressionScore
  simp only [Submodule.coe_add, Pi.add_apply, add_mul]
  rw [Finset.sum_add_distrib]

theorem bandRegressionScore_smul
    (a : ℝ) (q : B.RawBandGauge) :
    B.bandRegressionScore (a • q) =
      fun m ↦ a * B.bandRegressionScore q m := by
  funext m
  unfold bandRegressionScore
  simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem bandRegressionScore_sub
    (q r : B.RawBandGauge) :
    B.bandRegressionScore (q - r) =
      fun m ↦ B.bandRegressionScore q m - B.bandRegressionScore r m := by
  have hneg : -r = (-1 : ℝ) • r := (neg_one_smul ℝ r).symm
  rw [sub_eq_add_neg, B.bandRegressionScore_add, hneg,
    B.bandRegressionScore_smul]
  funext m
  ring

/-- Actual Schur-projected normalized band row of a raw gauge score. -/
def schurBandRow [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) : Band → ℝ :=
  B.normalizedBandCovarianceRow xi
    (B.nuisanceResidualScore xi hgamma hgap (B.bandRegressionScore q))

theorem schurBandRow_add [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q r : B.RawBandGauge) :
    B.schurBandRow xi hgamma hgap (q + r) =
      B.schurBandRow xi hgamma hgap q +
        B.schurBandRow xi hgamma hgap r := by
  unfold schurBandRow
  rw [B.bandRegressionScore_add q r,
    B.nuisanceResidualScore_add xi hgamma hgap,
    B.normalizedBandCovarianceRow_add xi]

theorem schurBandRow_smul [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (a : ℝ) (q : B.RawBandGauge) :
    B.schurBandRow xi hgamma hgap (a • q) =
      a • B.schurBandRow xi hgamma hgap q := by
  unfold schurBandRow
  rw [B.bandRegressionScore_smul a q,
    B.nuisanceResidualScore_smul xi hgamma hgap,
    B.normalizedBandCovarianceRow_smul xi]

/-- The exact projected operator
`P_{alpha,n} D^{-1} C^Z_{xi} P_{alpha,n}` on the arithmetic gauge. -/
def actualBandSchurLinearMap [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    B.RawBandGauge →ₗ[ℝ] B.RawBandGauge where
  toFun q := B.projectRawBandVector (B.schurBandRow xi hgamma hgap q)
  map_add' q r := by
    rw [B.schurBandRow_add xi hgamma hgap q r,
      B.projectRawBandVector_add]
  map_smul' a q := by
    rw [B.schurBandRow_smul xi hgamma hgap a q,
      B.projectRawBandVector_smul]
    rfl

/-- Literal Schur-projected right side
`P_{alpha,n}D^{-1}b^Z`. -/
def actualBandRegressionTarget [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) : B.RawBandGauge :=
  B.projectRawBandVector
    (B.normalizedBandCovarianceRow xi
      (B.nuisanceResidualScore xi hgamma hgap B.slowScore))

/-- First-stage actual regression obtained from an inverse of the literal
operator just defined. -/
def actualBandRegression [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge) :
    B.RawBandGauge :=
  e.symm (B.actualBandRegressionTarget xi hgamma hgap)

theorem actualBandRegression_normalEquation [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q) :
    B.actualBandSchurLinearMap xi hgamma hgap
        (B.actualBandRegression xi hgamma hgap e) =
      B.actualBandRegressionTarget xi hgamma hgap := by
  rw [← he]
  exact e.apply_symm_apply _

/-- The constructed first-stage regression makes the literal normalized
band row of the fully nuisance-projected score vanish after arithmetic gauge
projection. -/
theorem actualBandRegression_projectedResidual_zero
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q) :
    B.projectRawBandVector
      (B.normalizedBandCovarianceRow xi
        (B.actualCompensatedScore xi hgamma hgap
          (B.actualBandRegression xi hgamma hgap e))) = 0 := by
  let q := B.actualBandRegression xi hgamma hgap e
  have hnormal := B.actualBandRegression_normalEquation
    xi hgamma hgap e he
  have hpost : B.postBandPrimeScore q =
      fun m ↦ B.slowScore m - B.bandRegressionScore q m := by
    funext m
    exact B.postBandPrimeScore_eq_slow_sub_bandRegression q m
  have hresidual :
      B.actualCompensatedScore xi hgamma hgap q =
        fun m ↦
          B.nuisanceResidualScore xi hgamma hgap B.slowScore m -
          B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore q) m := by
    unfold actualCompensatedScore
    rw [hpost, B.nuisanceResidualScore_sub xi hgamma hgap]
  rw [hresidual, B.normalizedBandCovarianceRow_sub,
    B.projectRawBandVector_sub]
  change B.actualBandRegressionTarget xi hgamma hgap -
      B.actualBandSchurLinearMap xi hgamma hgap q = 0
  rw [← hnormal]
  exact sub_self _

/-- Exact covariance of a raw gauge score with an arbitrary finite score,
written in the normalized band-row coordinates. -/
theorem covariance_bandRegressionScore_eq_weightedRow [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    (F : B.sampleData.Sample → ℝ) :
    (B.tiltedLaw xi).covariance (B.bandRegressionScore q) F =
      ∑ j : Band, B.harmonicMass j * q.1 j *
        B.normalizedBandCovarianceRow xi F j := by
  unfold bandRegressionScore normalizedBandCovarianceRow
  rw [FiniteProbability.covariance_sum_left]
  apply Finset.sum_congr rfl
  intro j hj
  rw [FiniteProbability.covariance_smul_left]
  have hH := B.harmonicMass_pos j
  field_simp [ne_of_gt hH]

/-- The first-stage normal equation is genuine covariance orthogonality to
every arithmetic gauge score. -/
theorem actualBandRegression_covariance_gauge_zero
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (r : B.RawBandGauge) :
    (B.tiltedLaw xi).covariance (B.bandRegressionScore r)
      (B.actualCompensatedScore xi hgamma hgap
        (B.actualBandRegression xi hgamma hgap e)) = 0 := by
  rw [B.covariance_bandRegressionScore_eq_weightedRow]
  exact B.weighted_sum_eq_zero_of_projectRawBandVector_eq_zero
    (B.normalizedBandCovarianceRow xi
      (B.actualCompensatedScore xi hgamma hgap
        (B.actualBandRegression xi hgamma hgap e))) r
    (B.actualBandRegression_projectedResidual_zero
      xi hgamma hgap e he)

/-- Arithmetic gauge projection costs at most a factor two in the paper's
sharp norm.  This is the exact finite form of the rowwise step used on the
right side of the regression equation: a bound
`|x_j| <= C * alpha_j` remains a sharp bound after applying
`P_{alpha,n}`.  Positivity of the actual harmonic masses and centers proves
the weighted-mean estimate; no operator bound is assumed. -/
theorem projectRawBandVector_paperSharpNorm_le_two
    [Nonempty Band]
    (x : Band → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hx : ∀ j, |x j| ≤ C * B.bandCenter j) :
    paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.projectRawBandVector x) ≤ 2 * C := by
  let u : Band → ℝ := fun j ↦ x j / B.bandCenter j
  let omega : Band → ℝ :=
    sharpWeight B.harmonicMass B.bandCenter
  let total : ℝ := sharpWeightTotal B.harmonicMass B.bandCenter
  have hAlpha (j : Band) : B.bandCenter j ≠ 0 :=
    B.partition.center_ne_zero B.n_gt_one j
  have hAlphaPos (j : Band) : 0 < B.bandCenter j :=
    B.bandCenter_pos j
  have hTotal : 0 < total := by
    simpa only [total] using B.sharpBandWeightTotal_pos
  have hu (j : Band) : |u j| ≤ C := by
    dsimp only [u]
    rw [abs_div, abs_of_pos (hAlphaPos j)]
    exact (div_le_iff₀ (hAlphaPos j)).2 (by
      simpa only [mul_comm] using hx j)
  have hOmega (j : Band) : 0 ≤ omega j := by
    dsimp only [omega]
    exact sharpWeight_nonneg_of_mass_nonneg
      B.harmonicMass B.bandCenter
      (fun k ↦ (B.harmonicMass_pos k).le) j
  have hMean :
      |(∑ j, omega j * u j) / total| ≤ C := by
    rw [abs_div, abs_of_pos hTotal]
    calc
      |∑ j, omega j * u j| / total ≤
          (∑ j, |omega j * u j|) / total :=
        div_le_div_of_nonneg_right
          (Finset.abs_sum_le_sum_abs _ _) hTotal.le
      _ ≤ (∑ j, omega j * C) / total := by
        apply div_le_div_of_nonneg_right _ hTotal.le
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_of_nonneg (hOmega j)]
        exact mul_le_mul_of_nonneg_left (hu j) (hOmega j)
      _ = C := by
        rw [← Finset.sum_mul]
        change total * C / total = C
        field_simp [ne_of_gt hTotal]
  have hScale : scaleByCenter B.bandCenter u = x := by
    funext j
    unfold scaleByCenter u
    field_simp [hAlpha j]
  have hProjected (j : Band) :
      (B.projectRawBandVector x).1 j / B.bandCenter j =
        u j - (∑ k, omega k * u k) / total := by
    have hconj := congrFun
      (unscale_weightedGaugeProjection_scale_eq
        B.harmonicMass B.bandCenter u hAlpha (ne_of_gt hTotal)) j
    change weightedGaugeProjection B.harmonicMass B.bandCenter
        (scaleByCenter B.bandCenter u) j / B.bandCenter j = _ at hconj
    rw [hScale] at hconj
    simpa only [BridgeData.projectRawBandVector, omega, total] using hconj
  rw [paperSharpNorm_eq_piNorm]
  have hTwoC : 0 ≤ 2 * C := mul_nonneg (by norm_num) hC
  rw [pi_norm_le_iff_of_nonneg hTwoC]
  intro j
  rw [Real.norm_eq_abs, hProjected]
  exact (abs_sub _ _).trans (by linarith [hu j, hMean])

/-- A literal row-relative estimate for the Schur-projected slow-score
column implies the sharp bound on the actual regression target.  This removes
the target-norm contract from later Lemma 8.6 assembly: applications need
only prove the paper's natural row estimate before arithmetic gauge
projection. -/
theorem actualBandRegressionTarget_sharpNorm_le_of_row
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    {C w : ℝ} (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hrow : ∀ j,
      |B.normalizedBandCovarianceRow xi
          (B.nuisanceResidualScore xi hgamma hgap B.slowScore) j| ≤
        (C * w) * B.bandCenter j) :
    paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegressionTarget xi hgamma hgap) ≤
      (2 * C) * w := by
  have hproject := B.projectRawBandVector_paperSharpNorm_le_two
    (B.normalizedBandCovarianceRow xi
      (B.nuisanceResidualScore xi hgamma hgap B.slowScore))
    (mul_nonneg hC hw) hrow
  simpa only [actualBandRegressionTarget, mul_assoc] using hproject

/-- The inverse bound and actual target bound imply the sharp estimate for
the constructed first-stage regression; it is not an independent input. -/
theorem actualBandRegression_sharpNorm_le [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {Cinv Cright w : ℝ}
    (hCinv : 0 ≤ Cinv)
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (hright : paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegressionTarget xi hgamma hgap) ≤ Cright * w) :
    paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegression xi hgamma hgap e) ≤
      (Cinv * Cright) * w := by
  calc
    paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegression xi hgamma hgap e) ≤
      Cinv * paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegressionTarget xi hgamma hgap) :=
      hinv _
    _ ≤ Cinv * (Cright * w) :=
      mul_le_mul_of_nonneg_left hright hCinv
    _ = (Cinv * Cright) * w := by ring

/-- The three displayed coefficient bounds of Lemma 8.6 for the regression
vector constructed above.  They are derived from the actual inverse/target
outputs and the actual canonical-mesh moment bounds. -/
theorem actualBandRegression_compensatedCoefficient_three_bounds
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {Cinv Cright K w : ℝ}
    (hCinv : 0 ≤ Cinv) (hCright : 0 ≤ Cright)
    (hw : 0 ≤ w)
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (hright : paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegressionTarget xi hgamma hgap) ≤ Cright * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2) :
    (∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.actualCompensatedCoefficient
        (B.actualBandRegression xi hgamma hgap e) p| ≤
          (1 + Cinv * Cright) * w) ∧
    B.partition.compensatedL1
        (B.actualBandRegression xi hgamma hgap e) ≤
      (7 + (Cinv * Cright) * K) * w ∧
    B.partition.compensatedL2Sq
        (B.actualBandRegression xi hgamma hgap e) ≤
      2 * (4 + (Cinv * Cright) ^ 2 * K) * w ^ 2 := by
  have hsharp := B.actualBandRegression_sharpNorm_le
    xi hgamma hgap e hCinv hinv hright
  have hC : 0 ≤ Cinv * Cright := mul_nonneg hCinv hCright
  obtain ⟨hsup, hL1, hL2⟩ :=
    B.partition.compensatedCoefficient_three_bounds B.n_gt_one
      (B.actualBandRegression xi hgamma hgap e)
      hC hw hsharp hbandT hdevSup hdevL1 hdevL2
  refine ⟨?_, hL1, hL2⟩
  intro p
  rw [← B.partition_compensatedCoefficient_eq
    (B.actualBandRegression xi hgamma hgap e) p]
  exact hsup p

/-- The first and third displays of paper Lemma 8.6, specialized to the
literal canonical regular-mesh partition.  Unlike
`actualBandRegression_compensatedCoefficient_three_bounds`, this theorem
does not receive any prime-deviation moment estimate as a hypothesis: the
pointwise, `L¹`, and quadratic estimates are consequences of the proved PNT
quadratures packaged by `MomentReady` and of the exact endpoint
certificate.  The equality `hscale` identifies the scale stored in the
actual bridge data with the paper scale `delta + eta`.

The only remaining inputs in this statement are the inverse and right-row
bounds supplied by the preceding weighted-inverse lemma; no conclusion of
Lemma 8.6 is among them. -/
theorem actualBandRegression_regularMesh_moment_and_coefficient_bounds
    {delta : ℝ}
    (M : RegularRelativeMesh.Mesh delta delta)
    [Nonempty Head]
    (B : BridgeData Head (Fin (M.cellCount + 1)))
    (E : PositiveCellTransfer.IntervalCertificate B.partition)
    (hLower : ∀ j, E.lower j =
      RegularMeshPrimeCutoffs.fullCutoff M B.sampleData.n
        B.sampleData.W j.1)
    (hUpper : ∀ j, E.upper j =
      RegularMeshPrimeCutoffs.fullCutoff M B.sampleData.n
        B.sampleData.W (j.1 + 1))
    (hdelta : 0 < delta)
    (hscale : B.w = delta + M.ratio)
    (R : RegularMeshPrimeCutoffs.Mesh.MomentReady M B.partition)
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {Cinv Crow K : ℝ}
    (hCinv : 0 ≤ Cinv) (hCrow : 0 ≤ Crow)
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (hrightRow : ∀ j,
      |B.normalizedBandCovarianceRow xi
          (B.nuisanceResidualScore xi hgamma hgap B.slowScore) j| ≤
        (Crow * B.w) * B.bandCenter j)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K) :
    B.partition.totalL1 ≤ 7 * B.w ∧
    B.w ^ 2 / 16 ≤ B.partition.variance ∧
    B.partition.variance ≤ 4 * B.w ^ 2 ∧
    (forall p : BandPrime B.sampleData.n B.sampleData.W,
      |B.actualCompensatedCoefficient
        (B.actualBandRegression xi hgamma hgap e) p| ≤
          (1 + Cinv * (2 * Crow)) * B.w) ∧
    B.partition.compensatedL1
      (B.actualBandRegression xi hgamma hgap e) ≤
      (7 + (Cinv * (2 * Crow)) * K) * B.w ∧
    B.partition.compensatedL2Sq
      (B.actualBandRegression xi hgamma hgap e) ≤
      2 * (4 + (Cinv * (2 * Crow)) ^ 2 * K) * B.w ^ 2 := by
  obtain ⟨hL1, hVarLower, hVarUpper⟩ :=
    RegularMeshPrimeCutoffs.Mesh.actual_moment_bounds_of_ready
      M B.partition E hLower hUpper hdelta M.ratio_le_eta B.n_gt_one R
  have hSup :=
    RegularMeshPrimeCutoffs.Mesh.actual_deviation_sup_le_scale
      M B.partition E hLower hUpper hdelta B.n_gt_one
  have hL1' : B.partition.totalL1 ≤ 7 * B.w := by
    rw [hscale]
    exact hL1
  have hVarLower' : B.w ^ 2 / 16 ≤ B.partition.variance := by
    rw [hscale]
    exact hVarLower
  have hVarUpper' : B.partition.variance ≤ 4 * B.w ^ 2 := by
    rw [hscale]
    exact hVarUpper
  have hSup' : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ B.w := by
    intro p
    rw [hscale]
    exact hSup p
  have hright := B.actualBandRegressionTarget_sharpNorm_le_of_row
    xi hgamma hgap hCrow B.w_pos.le hrightRow
  have hTwoCrow : 0 ≤ 2 * Crow := mul_nonneg (by norm_num) hCrow
  obtain ⟨hcSup, hcL1, hcL2⟩ :=
    B.actualBandRegression_compensatedCoefficient_three_bounds
      xi hgamma hgap e hCinv hTwoCrow B.w_pos.le hinv hright hbandT
      hSup' hL1' hVarUpper'
  exact ⟨hL1', hVarLower', hVarUpper', hcSup, hcL1, hcL2⟩

/-- The exact second-stage coefficient attached to the first-stage solve. -/
def actualTwoStageNuisanceCoefficient [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge) :
    B.NuisanceSpace :=
  B.actualNuisanceCoefficient xi hgamma hgap
    (B.actualBandRegression xi hgamma hgap e)

/-- The literal fully fitted `C_g` after the two displayed regression stages. -/
def actualTwoStageCompensatedScore [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge) :
    B.sampleData.Sample → ℝ :=
  B.actualCompensatedScore xi hgamma hgap
    (B.actualBandRegression xi hgamma hgap e)

/-- The second-stage coefficient is bounded by the literal post-band
covariance vector divided by the proved nuisance gap. -/
theorem actualTwoStageNuisanceCoefficient_norm_le
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {Cz w : ℝ}
    (hcov : ‖B.nuisanceCovarianceVector xi
      (B.postBandPrimeScore
        (B.actualBandRegression xi hgamma hgap e))‖ ≤ Cz * w) :
    ‖B.actualTwoStageNuisanceCoefficient xi hgamma hgap e‖ ≤
      (Cz / gamma) * w := by
  unfold actualTwoStageNuisanceCoefficient actualNuisanceCoefficient
  calc
    ‖B.nuisanceCoefficientOfScore xi hgamma hgap
        (B.postBandPrimeScore
          (B.actualBandRegression xi hgamma hgap e))‖ ≤
        ‖B.nuisanceCovarianceVector xi
          (B.postBandPrimeScore
            (B.actualBandRegression xi hgamma hgap e))‖ / gamma :=
      B.nuisanceCoefficientOfScore_norm_le xi hgamma hgap _
    _ ≤ (Cz * w) / gamma :=
      div_le_div_of_nonneg_right hcov (le_of_lt hgamma)
    _ = (Cz / gamma) * w := by ring

/-- The fully fitted literal score is orthogonal both to every nuisance
score and to every raw arithmetic-gauge band score. -/
theorem actualTwoStageCompensatedScore_orthogonal
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q) :
    (∀ z : B.NuisanceSpace,
      (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m))
        (B.actualTwoStageCompensatedScore xi hgamma hgap e) = 0) ∧
    ∀ r : B.RawBandGauge,
      (B.tiltedLaw xi).covariance (B.bandRegressionScore r)
        (B.actualTwoStageCompensatedScore xi hgamma hgap e) = 0 := by
  constructor
  · intro z
    exact B.actualCompensatedScore_covariance_nuisance_zero
      xi hgamma hgap (B.actualBandRegression xi hgamma hgap e) z
  · intro r
    exact B.actualBandRegression_covariance_gauge_zero
      xi hgamma hgap e he r

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
