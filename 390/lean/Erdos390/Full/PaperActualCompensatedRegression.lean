import Erdos390.Full.PaperBridgeFit
import Erdos390.Full.PaperCompensatedCoefficientBounds
import Erdos390.Full.PrimePowerCovariance

/-!
# The actual two-stage compensated regression in Lemma 8.6

The objects in this file live on the genuine guard-deleted, tilted finite
probability space from `PaperBridgeFit`.  In particular, the nuisance
coefficient is not an abstract vector satisfying a normal equation: it is
defined by applying the inverse of the proved actual nuisance covariance
operator to the literal covariance vector of the post-band-regression score.

This file proves the exact finite identities used before the analytic
`w^2` comparison: the prime-coefficient expansion, nuisance normal equation,
orthogonality, Schur variance identity, and marked-row decomposition.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport
open PrimePowerCovariance

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The paper's exact raw arithmetic gauge for the actual bridge partition. -/
abbrev RawBandGauge :=
  RawGaugeSpace B.harmonicMass B.bandCenter

/-- A raw gauge coefficient evaluated at the band of an actual prime. -/
def bandRegressionCoefficient
    (q : B.RawBandGauge) (p : BandPrime B.sampleData.n B.sampleData.W) : ℝ :=
  q.1 (B.partition.band p)

/-- The literal band regression score `sum_j q_j Omega_j`. -/
def bandRegressionScore
    (q : B.RawBandGauge) (m : B.sampleData.Sample) : ℝ :=
  ∑ j : Band, q.1 j * B.bandScore j m

/-- The literal post-band-regression prime coefficient
`c_p = g_p - q_{j(p)}`. -/
def actualCompensatedCoefficient
    (q : B.RawBandGauge) (p : BandPrime B.sampleData.n B.sampleData.W) : ℝ :=
  B.primeDeviation p - B.bandRegressionCoefficient q p

/-- The prime part of the compensated score, before nuisance regression. -/
def postBandPrimeScore
    (q : B.RawBandGauge) (m : B.sampleData.Sample) : ℝ :=
  ∑ p : BandPrime B.sampleData.n B.sampleData.W,
    B.actualCompensatedCoefficient q p *
      valuation p.1 (B.sampleData.value m)

theorem partition_deviation_eq_primeDeviation
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    B.partition.deviation p = B.primeDeviation p := rfl

theorem partition_regressionCoefficient_eq
    (q : B.RawBandGauge)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    B.partition.regressionCoefficient q p =
      B.bandRegressionCoefficient q p := rfl

theorem partition_compensatedCoefficient_eq
    (q : B.RawBandGauge)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    B.partition.compensatedCoefficient q p =
      B.actualCompensatedCoefficient q p := rfl

/-- Reindexing over the actual partition identifies the raw band score with
the corresponding primewise coefficient sum. -/
theorem bandRegressionScore_eq_primeSum
    (q : B.RawBandGauge) (m : B.sampleData.Sample) :
    B.bandRegressionScore q m =
      ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.bandRegressionCoefficient q p *
          valuation p.1 (B.sampleData.value m) := by
  unfold bandRegressionScore bandScore bandRegressionCoefficient
  rw [← Finset.sum_fiberwise Finset.univ B.partition.band
    (fun p : BandPrime B.sampleData.n B.sampleData.W ↦
      q.1 (B.partition.band p) *
        valuation p.1 (B.sampleData.value m))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpj : B.partition.band p = j :=
    (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff
      B.partition.data).mp hp
  rw [hpj]

/-- The first-stage residual is exactly `S_g - sum_j q_j Omega_j`. -/
theorem postBandPrimeScore_eq_slow_sub_bandRegression
    (q : B.RawBandGauge) (m : B.sampleData.Sample) :
    B.postBandPrimeScore q m =
      B.slowScore m - B.bandRegressionScore q m := by
  rw [B.bandRegressionScore_eq_primeSum q m]
  unfold postBandPrimeScore actualCompensatedCoefficient
    slowScore primeDeviation bandRegressionCoefficient
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- The actual normalized tilted law `ν_{n,ξ}`. -/
abbrev tiltedLaw [Nonempty Head] (xi : B.ParamSpace) :
    FiniteProbability B.sampleData.Sample :=
  B.vectorFamily.scalarFamily.tiltedProbability xi

/-- Coordinatewise covariance of the literal nuisance statistic with an
arbitrary actual finite score. -/
def nuisanceCovarianceVector [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ) : B.NuisanceSpace :=
  (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).symm
    (fun c ↦ (B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m c) F)

@[simp]
theorem nuisanceCovarianceVector_apply [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    (c : NuisanceCoord B.HeadIndex) :
    B.nuisanceCovarianceVector xi F c =
      (B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c) F := rfl

theorem inner_nuisanceCovarianceVector [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    (z : B.NuisanceSpace) :
    inner ℝ z (B.nuisanceCovarianceVector xi F) =
      (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) F := by
  rw [PiLp.inner_apply]
  change (∑ c : NuisanceCoord B.HeadIndex,
      B.nuisanceCovarianceVector xi F c * z c) = _
  rw [show (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) =
      fun m ↦ ∑ c : NuisanceCoord B.HeadIndex,
        z c * B.nuisanceStatistic m c by
    funext m
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro c hc
    rw [RCLike.inner_apply]
    simp only [starRingEnd_apply, star_trivial]
    ring]
  rw [FiniteProbability.covariance_sum_left]
  apply Finset.sum_congr rfl
  intro c hc
  rw [FiniteProbability.covariance_smul_left]
  simp only [B.nuisanceCovarianceVector_apply]
  ring

/-- Bilinear form of the actual nuisance covariance block. -/
theorem inner_nuisanceCovarianceOperator_bilinear [Nonempty Head]
    (xi : B.ParamSpace) (z a : B.NuisanceSpace) :
    inner ℝ z (B.nuisanceCovarianceOperator xi a) =
      (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m))
        (fun m ↦ inner ℝ a (B.nuisanceStatistic m)) := by
  have hadjoint :
      inner ℝ z (B.nuisanceCovarianceOperator xi a) =
        inner ℝ (B.nuisanceEmbed z)
          (B.covarianceOperator xi (B.nuisanceEmbed a)) := by
    simpa only [nuisanceCovarianceOperator,
      ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.adjoint_inner_right B.nuisanceEmbeddingCLM z
        (B.covarianceOperator xi (B.nuisanceEmbeddingCLM a)))
  rw [hadjoint, B.inner_covarianceOperator]
  congr 1
  · funext m
    rw [B.statistic_eq_combine m,
      B.inner_nuisanceEmbed_combine z (B.nuisanceStatistic m)
        (B.mainStatistic m)]
  · funext m
    rw [B.statistic_eq_combine m,
      B.inner_nuisanceEmbed_combine a (B.nuisanceStatistic m)
        (B.mainStatistic m)]

/-- The second-stage nuisance coefficient, defined by the actual inverse
`Γ_{ξ,n}^{-1}` and the literal covariance vector. -/
def nuisanceCoefficientOfScore [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) : B.NuisanceSpace :=
  (B.nuisanceCovarianceEquiv xi hgamma hgap).symm
    (B.nuisanceCovarianceVector xi F)

theorem nuisanceCoefficientOfScore_solve [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) :
    B.nuisanceCovarianceOperator xi
        (B.nuisanceCoefficientOfScore xi hgamma hgap F) =
      B.nuisanceCovarianceVector xi F := by
  rw [← B.nuisanceCovarianceEquiv_apply xi hgamma hgap]
  exact (B.nuisanceCovarianceEquiv xi hgamma hgap).apply_symm_apply _

/-- Coercivity of the literal nuisance covariance block bounds the actual
regression coefficient by the norm of its literal covariance vector. -/
theorem nuisanceCoefficientOfScore_norm_le [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) :
    ‖B.nuisanceCoefficientOfScore xi hgamma hgap F‖ ≤
      ‖B.nuisanceCovarianceVector xi F‖ / gamma := by
  let a := B.nuisanceCoefficientOfScore xi hgamma hgap F
  have hcoer := hgap a
  rw [B.nuisanceCoefficientOfScore_solve xi hgamma hgap F] at hcoer
  have hinner : inner ℝ a (B.nuisanceCovarianceVector xi F) ≤
      ‖a‖ * ‖B.nuisanceCovarianceVector xi F‖ :=
    real_inner_le_norm _ _
  by_cases ha : ‖a‖ = 0
  · change ‖a‖ ≤ ‖B.nuisanceCovarianceVector xi F‖ / gamma
    rw [ha]
    exact div_nonneg (norm_nonneg _) (le_of_lt hgamma)
  · have hapos : 0 < ‖a‖ :=
      lt_of_le_of_ne (norm_nonneg a) (Ne.symm ha)
    have hcancel : gamma * ‖a‖ ≤
        ‖B.nuisanceCovarianceVector xi F‖ := by
      have hmul : (gamma * ‖a‖) * ‖a‖ ≤
          ‖B.nuisanceCovarianceVector xi F‖ * ‖a‖ := by
        calc
          (gamma * ‖a‖) * ‖a‖ = gamma * ‖a‖ ^ 2 := by ring
          _ ≤ inner ℝ a (B.nuisanceCovarianceVector xi F) := hcoer
          _ ≤ ‖B.nuisanceCovarianceVector xi F‖ * ‖a‖ := by
            simpa [mul_comm] using hinner
      exact (mul_le_mul_iff_right₀ hapos).mp (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmul)
    change ‖a‖ ≤ ‖B.nuisanceCovarianceVector xi F‖ / gamma
    exact (le_div_iff₀ hgamma).2 (by simpa [mul_comm] using hcancel)

/-- The exact Schur loss is nonnegative and is bounded by the squared norm
of the literal nuisance covariance vector divided by the nuisance gap. -/
theorem nuisanceRegressionLoss_bounds [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) :
    0 ≤ inner ℝ (B.nuisanceCoefficientOfScore xi hgamma hgap F)
        (B.nuisanceCovarianceVector xi F) ∧
    inner ℝ (B.nuisanceCoefficientOfScore xi hgamma hgap F)
        (B.nuisanceCovarianceVector xi F) ≤
      ‖B.nuisanceCovarianceVector xi F‖ ^ 2 / gamma := by
  let a := B.nuisanceCoefficientOfScore xi hgamma hgap F
  have hsolve := B.nuisanceCoefficientOfScore_solve xi hgamma hgap F
  have hcoer := hgap a
  rw [hsolve] at hcoer
  have hlower : 0 ≤ inner ℝ a (B.nuisanceCovarianceVector xi F) := by
    exact le_trans
      (mul_nonneg (le_of_lt hgamma) (sq_nonneg ‖a‖)) hcoer
  have hnorm := B.nuisanceCoefficientOfScore_norm_le xi hgamma hgap F
  have hinner : inner ℝ a (B.nuisanceCovarianceVector xi F) ≤
      ‖a‖ * ‖B.nuisanceCovarianceVector xi F‖ :=
    real_inner_le_norm _ _
  refine ⟨hlower, hinner.trans ?_⟩
  calc
    ‖a‖ * ‖B.nuisanceCovarianceVector xi F‖ ≤
        (‖B.nuisanceCovarianceVector xi F‖ / gamma) *
          ‖B.nuisanceCovarianceVector xi F‖ :=
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = ‖B.nuisanceCovarianceVector xi F‖ ^ 2 / gamma := by ring

/-- Residual after the actual finite nuisance regression. -/
def nuisanceResidualScore [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) (m : B.sampleData.Sample) : ℝ :=
  F m - inner ℝ (B.nuisanceCoefficientOfScore xi hgamma hgap F)
    (B.nuisanceStatistic m)

private theorem covariance_sub_right
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (F G H : Omega → ℝ) :
    mu.covariance F (fun omega ↦ G omega - H omega) =
      mu.covariance F G - mu.covariance F H := by
  have hfun : (fun omega ↦ G omega - H omega) =
      fun omega ↦ G omega + (-1 : ℝ) * H omega := by
    funext omega
    ring
  rw [hfun, mu.covariance_add_right, mu.covariance_smul_right]
  ring

/-- Exact Schur orthogonality of the actual nuisance residual. -/
theorem nuisanceResidualScore_covariance_zero [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) (z : B.NuisanceSpace) :
    (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m))
        (B.nuisanceResidualScore xi hgamma hgap F) = 0 := by
  let a := B.nuisanceCoefficientOfScore xi hgamma hgap F
  unfold nuisanceResidualScore
  rw [covariance_sub_right]
  have hfirst := B.inner_nuisanceCovarianceVector xi F z
  have hsecond := B.inner_nuisanceCovarianceOperator_bilinear xi z a
  have hsolve := congrArg (fun v : B.NuisanceSpace ↦ inner ℝ z v)
    (B.nuisanceCoefficientOfScore_solve xi hgamma hgap F)
  change inner ℝ z (B.nuisanceCovarianceOperator xi a) =
    inner ℝ z (B.nuisanceCovarianceVector xi F) at hsolve
  rw [hfirst, hsecond] at hsolve
  exact sub_eq_zero.mpr hsolve.symm

/-- The actual paper nuisance coefficient `a_Z` after the band regression. -/
def actualNuisanceCoefficient [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) : B.NuisanceSpace :=
  B.nuisanceCoefficientOfScore xi hgamma hgap (B.postBandPrimeScore q)

/-- The fully compensated score `C_g` from the paper. -/
def actualCompensatedScore [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) : B.sampleData.Sample → ℝ :=
  B.nuisanceResidualScore xi hgamma hgap (B.postBandPrimeScore q)

theorem actualCompensatedScore_covariance_nuisance_zero [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) (z : B.NuisanceSpace) :
    (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m))
        (B.actualCompensatedScore xi hgamma hgap q) = 0 := by
  exact B.nuisanceResidualScore_covariance_zero xi hgamma hgap
    (B.postBandPrimeScore q) z

/-- Exact Schur-variance identity.  This is an equality at finite `n`; the
subsequent continuum and prime-power arguments only estimate its two terms. -/
theorem nuisanceResidualScore_variance_identity [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) :
    (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap F)
        (B.nuisanceResidualScore xi hgamma hgap F) =
      (B.tiltedLaw xi).covariance F F -
        inner ℝ (B.nuisanceCoefficientOfScore xi hgamma hgap F)
          (B.nuisanceCovarianceVector xi F) := by
  let a := B.nuisanceCoefficientOfScore xi hgamma hgap F
  let Zscore : B.sampleData.Sample → ℝ :=
    fun m ↦ inner ℝ a (B.nuisanceStatistic m)
  have horth := B.nuisanceResidualScore_covariance_zero
    xi hgamma hgap F a
  have hcomm : (B.tiltedLaw xi).covariance
      (B.nuisanceResidualScore xi hgamma hgap F) Zscore = 0 := by
    simpa only [Zscore] using
      ((B.tiltedLaw xi).covariance_comm
        (B.nuisanceResidualScore xi hgamma hgap F) Zscore).trans horth
  have hF : F = fun m ↦
      B.nuisanceResidualScore xi hgamma hgap F m + Zscore m := by
    funext m
    unfold nuisanceResidualScore
    simp only [a, Zscore]
    ring
  have hvarZ := B.inner_nuisanceCovarianceOperator_bilinear xi a a
  have hsolve := congrArg (fun v : B.NuisanceSpace ↦ inner ℝ a v)
    (B.nuisanceCoefficientOfScore_solve xi hgamma hgap F)
  change inner ℝ a (B.nuisanceCovarianceOperator xi a) =
    inner ℝ a (B.nuisanceCovarianceVector xi F) at hsolve
  rw [hvarZ] at hsolve
  rw [show (B.tiltedLaw xi).covariance F F =
      (B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceResidualScore xi hgamma hgap F m + Zscore m)
        (fun m ↦ B.nuisanceResidualScore xi hgamma hgap F m + Zscore m) by
    rw [← hF]]
  rw [FiniteProbability.covariance_add_left,
    FiniteProbability.covariance_add_right,
    FiniteProbability.covariance_add_right]
  rw [horth, hcomm, zero_add, add_zero]
  linarith

/-- Exact marked-row identity for an arbitrary nuisance coefficient.  The
vector on the right is the literal covariance vector of the marked score,
so a Euclidean row estimate can be used without introducing a
coordinate-counting loss. -/
theorem covariance_marked_nuisanceScore_eq_inner [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    (z : B.NuisanceSpace) :
    (B.tiltedLaw xi).covariance F
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) =
      inner ℝ z (B.nuisanceCovarianceVector xi F) := by
  rw [(B.tiltedLaw xi).covariance_comm]
  exact (B.inner_nuisanceCovarianceVector xi F z).symm

/-- A coordinatewise nuisance-row estimate gives the Euclidean estimate used
in the second regression.  The only loss is the square root of the fixed
nuisance dimension.  Keeping this conversion explicit is useful in the
marked-row argument: the analytic input is naturally proved one physical or
head coordinate at a time, whereas the regression coefficient is controlled
in Euclidean norm. -/
theorem nuisanceCovarianceVector_norm_le_sqrt_card_mul [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hcoord : ∀ c : NuisanceCoord B.HeadIndex,
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c) F| ≤ K) :
    ‖B.nuisanceCovarianceVector xi F‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K := by
  have hsq : ‖B.nuisanceCovarianceVector xi F‖ ^ 2 ≤
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, B.nuisanceCovarianceVector_apply]
    calc
      (∑ c : NuisanceCoord B.HeadIndex,
          |(B.tiltedLaw xi).covariance
            (fun m ↦ B.nuisanceStatistic m c) F| ^ 2) ≤
          ∑ _c : NuisanceCoord B.HeadIndex, K ^ 2 := by
        apply Finset.sum_le_sum
        intro c hc
        exact pow_le_pow_left₀ (abs_nonneg _) (hcoord c) 2
      _ = (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K ^ 2 := by
        simp
  have hcard : 0 ≤
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) := by positivity
  have hsqrt :
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)) ^ 2 =
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) :=
    Real.sq_sqrt hcard
  have hrhs0 : 0 ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K :=
    mul_nonneg (Real.sqrt_nonneg _) hK
  have hrhsSq :
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K) ^ 2 =
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K ^ 2 := by
    rw [mul_pow, hsqrt]
  rw [← hrhsSq] at hsq
  nlinarith [norm_nonneg (B.nuisanceCovarianceVector xi F)]

/-- A reciprocal marked row controls the covariance with the entire literal
post-band prime score by the actual compensated weighted `L¹` norm.  This is
the finite summation step used twice in Lemma 8.6: once for the nuisance
coefficient and once for a marked valuation row. -/
theorem abs_covariance_nuisance_postBandPrimeScore_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    (c : NuisanceCoord B.HeadIndex) {Cmarked : ℝ}
    (hmarked : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ))) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m c)
      (B.postBandPrimeScore q)| ≤
        Cmarked * B.partition.compensatedL1 q := by
  let mu := B.tiltedLaw xi
  let Z : B.sampleData.Sample → ℝ :=
    fun m ↦ B.nuisanceStatistic m c
  have hsum :
      mu.covariance Z (B.postBandPrimeScore q) =
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.actualCompensatedCoefficient q p *
            mu.covariance Z
              (fun m ↦ valuation p.1 (B.sampleData.value m)) := by
    unfold postBandPrimeScore
    rw [show (fun m ↦ ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.actualCompensatedCoefficient q p *
          valuation p.1 (B.sampleData.value m)) =
      fun m ↦ ∑ p ∈ (Finset.univ :
          Finset (BandPrime B.sampleData.n B.sampleData.W)),
        B.actualCompensatedCoefficient q p *
          valuation p.1 (B.sampleData.value m) by simp]
    rw [mu.covariance_sum_right]
    apply Finset.sum_congr rfl
    intro p hp
    rw [mu.covariance_smul_right]
  change |mu.covariance Z (B.postBandPrimeScore q)| ≤ _
  rw [hsum]
  calc
    |∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.actualCompensatedCoefficient q p *
          mu.covariance Z
            (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          |B.actualCompensatedCoefficient q p *
            mu.covariance Z
              (fun m ↦ valuation p.1 (B.sampleData.value m))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        |B.actualCompensatedCoefficient q p| *
          (Cmarked * (1 / (p.1 : ℝ))) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hmarked p) (abs_nonneg _)
    _ = Cmarked * B.partition.compensatedL1 q := by
      unfold ArithmeticBandGeometry.Partition.compensatedL1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [B.partition_compensatedCoefficient_eq q p]
      ring

/-- Vector form of the reciprocal-row summation.  Thus the covariance vector
needed for the nuisance regression is a consequence of the same componentwise
marked estimates and of the already established coefficient `L¹` bound; it is
not a second independent analytic assumption. -/
theorem nuisanceCovarianceVector_postBand_norm_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {Cmarked : ℝ} (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ))) :
    ‖B.nuisanceCovarianceVector xi (B.postBandPrimeScore q)‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked * B.partition.compensatedL1 q) := by
  have hL1nonneg : 0 ≤ B.partition.compensatedL1 q := by
    unfold ArithmeticBandGeometry.Partition.compensatedL1
    apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg (by positivity) (abs_nonneg _)
  apply B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
    xi (B.postBandPrimeScore q) (mul_nonneg hCmarked hL1nonneg)
  intro c
  exact B.abs_covariance_nuisance_postBandPrimeScore_le_of_marked
    xi q c (fun p ↦ hmarked c p)

/-- Scaled form used in the final `w²` assembly. -/
theorem nuisanceCovarianceVector_postBand_norm_le_of_marked_and_l1
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {Cmarked CL1 w : ℝ} (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ)))
    (hL1 : B.partition.compensatedL1 q ≤ CL1 * w) :
    ‖B.nuisanceCovarianceVector xi (B.postBandPrimeScore q)‖ ≤
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked * CL1)) * w := by
  have hraw := B.nuisanceCovarianceVector_postBand_norm_le_of_marked
    xi q hCmarked hmarked
  calc
    ‖B.nuisanceCovarianceVector xi (B.postBandPrimeScore q)‖ ≤
        Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * B.partition.compensatedL1 q) := hraw
    _ ≤ Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * (CL1 * w)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hL1 hCmarked)
        (Real.sqrt_nonneg _)
    _ = (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * CL1)) * w := by ring

/-- The explicit nuisance contribution to a marked row is derived from the
two natural covariance-vector bounds and nuisance coercivity.  In
particular, later assembly need not assume the scalar marked nuisance row
itself. -/
theorem actualNuisanceCoefficient_markedRow_bound [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) (F : B.sampleData.Sample → ℝ)
    {Cz Cmarked w rho : ℝ}
    (hCz : 0 ≤ Cz) (hw : 0 ≤ w)
    (hscore : ‖B.nuisanceCovarianceVector xi
        (B.postBandPrimeScore q)‖ ≤ Cz * w)
    (hmarked : ‖B.nuisanceCovarianceVector xi F‖ ≤
      Cmarked * rho) :
    |(B.tiltedLaw xi).covariance F
        (fun m ↦ inner ℝ
          (B.actualNuisanceCoefficient xi hgamma hgap q)
          (B.nuisanceStatistic m))| ≤
      ((Cz / gamma) * Cmarked) * w * rho := by
  have ha : ‖B.actualNuisanceCoefficient xi hgamma hgap q‖ ≤
      (Cz / gamma) * w := by
    unfold actualNuisanceCoefficient
    calc
      ‖B.nuisanceCoefficientOfScore xi hgamma hgap
          (B.postBandPrimeScore q)‖ ≤
          ‖B.nuisanceCovarianceVector xi
            (B.postBandPrimeScore q)‖ / gamma :=
        B.nuisanceCoefficientOfScore_norm_le xi hgamma hgap _
      _ ≤ (Cz * w) / gamma :=
        div_le_div_of_nonneg_right hscore (le_of_lt hgamma)
      _ = (Cz / gamma) * w := by ring
  rw [B.covariance_marked_nuisanceScore_eq_inner]
  calc
    |inner ℝ (B.actualNuisanceCoefficient xi hgamma hgap q)
        (B.nuisanceCovarianceVector xi F)| ≤
        ‖B.actualNuisanceCoefficient xi hgamma hgap q‖ *
          ‖B.nuisanceCovarianceVector xi F‖ := abs_real_inner_le_norm _ _
    _ ≤ ((Cz / gamma) * w) * (Cmarked * rho) :=
      mul_le_mul ha hmarked (norm_nonneg _) (by
        exact mul_nonneg
          (div_nonneg hCz (le_of_lt hgamma)) hw)
    _ = ((Cz / gamma) * Cmarked) * w * rho := by ring

/-- Exact marked-row decomposition after nuisance regression. -/
theorem actualCompensatedScore_markedRow_decomposition [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) (p : ℕ) :
    (B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (B.actualCompensatedScore xi hgamma hgap q) =
      (B.tiltedLaw xi).covariance
          (fun m ↦ valuation p (B.sampleData.value m))
          (B.postBandPrimeScore q) -
        (B.tiltedLaw xi).covariance
          (fun m ↦ valuation p (B.sampleData.value m))
          (fun m ↦ inner ℝ
            (B.actualNuisanceCoefficient xi hgamma hgap q)
            (B.nuisanceStatistic m)) := by
  exact covariance_sub_right _ _ _ _

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
