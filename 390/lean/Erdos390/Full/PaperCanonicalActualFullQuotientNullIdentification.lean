import Erdos390.Full.PaperCanonicalActualBandQuadraticTransfer
import Erdos390.Full.PaperNuisancePrimeLogRows
import Erdos390.Full.FiniteTiltCovarianceDomination

/-!
# Exact prime-log null identification for the fixed-kappa quotient gap

The arithmetic quotient lower bound is naturally proved after minimizing the
coefficient `b_{j(p)} - mu t_p` over the physical logarithmic direction.  The
actual main score, however, carries a prescribed value of `mu` coming from
the stored slow coordinate.  This file proves at finite `n` that the two
scores have exactly the same nuisance-Schur quadratic form: their difference
is a multiple of `primeLogScore`, and the latter is an affine nuisance score.

No continuum limit or covariance approximation occurs here.  In particular,
the arbitrary band vector is retained throughout; the slow/`alpha` direction
is not discarded by restricting to the raw gauge.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperCanonicalSlowKappa
open PaperCanonicalActualBandQuadraticTransfer
open PaperPrimePowerChamberError
open PaperWeightedInverseExport
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open PaperSquarefreeSlowQuadraticLower
open FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference
open OmittedTiltPairChamber

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The nuisance vector whose physical coordinate is `a` and whose centered
head coordinates represent `phi` modulo the reference head. -/
def physicalHeadNuisanceVector [Nonempty Head]
    (a : ℝ) (phi : Head → ℝ) : B.NuisanceSpace :=
  (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).symm
    (fun c => match c with
      | .physical => a
      | .head h => phi h.1 - phi B.referenceHead)

@[simp] theorem physicalHeadNuisanceVector_physical [Nonempty Head]
    (a : ℝ) (phi : Head → ℝ) :
    B.physicalHeadNuisanceVector a phi NuisanceCoord.physical = a := rfl

@[simp] theorem physicalHeadNuisanceVector_head [Nonempty Head]
    (a : ℝ) (phi : Head → ℝ) (h : B.HeadIndex) :
    B.physicalHeadNuisanceVector a phi (NuisanceCoord.head h) =
      phi h.1 - phi B.referenceHead := rfl

/-- The deterministic term created when ordinary head indicators are
rewritten as the centered nuisance head indicators. -/
def physicalHeadAffineConstant [Nonempty Head]
    (phi : Head → ℝ) : ℝ :=
  phi B.referenceHead +
    ∑ h : B.HeadIndex,
      (phi h.1 - phi B.referenceHead) * B.headBaselineMass h.1

/-- Exact affine realization of a physical score plus an arbitrary tagged
head function inside the nuisance coordinates. -/
theorem physical_mul_add_headFunction_eq_inner_add_constant
    [Nonempty Head]
    (a : ℝ) (phi : Head → ℝ) (m : B.sampleData.Sample) :
    a * B.physicalScore m + B.headFunctionScore phi m =
      inner ℝ (B.physicalHeadNuisanceVector a phi)
          (B.nuisanceStatistic m) +
        B.physicalHeadAffineConstant phi := by
  rw [B.inner_nuisanceStatistic_eq_physical_add_headFunction]
  rw [B.headFunctionScore_decomposition phi m]
  unfold physicalHeadAffineConstant nuisanceHeadFunction headFunctionScore
  simp only [B.physicalHeadNuisanceVector_physical,
    B.physicalHeadNuisanceVector_head]
  change
    a * B.physicalScore m +
        (phi B.referenceHead +
          ∑ h : B.HeadIndex,
            (phi h.1 - phi B.referenceHead) * B.headIndicator h.1 m) =
      a * B.physicalScore m +
          ∑ h : B.HeadIndex,
            (phi h.1 - phi B.referenceHead) *
              (B.headIndicator h.1 m - B.headBaselineMass h.1) +
        (phi B.referenceHead +
          ∑ h : B.HeadIndex,
            (phi h.1 - phi B.referenceHead) * B.headBaselineMass h.1)
  have hsum :
      (∑ h : B.HeadIndex,
          (phi h.1 - phi B.referenceHead) *
            (B.headIndicator h.1 m - B.headBaselineMass h.1)) +
        ∑ h : B.HeadIndex,
          (phi h.1 - phi B.referenceHead) * B.headBaselineMass h.1 =
      ∑ h : B.HeadIndex,
        (phi h.1 - phi B.referenceHead) * B.headIndicator h.1 m := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  rw [show
      a * B.physicalScore m +
            (∑ h : B.HeadIndex,
              (phi h.1 - phi B.referenceHead) *
                (B.headIndicator h.1 m - B.headBaselineMass h.1)) +
          (phi B.referenceHead +
            ∑ h : B.HeadIndex,
              (phi h.1 - phi B.referenceHead) * B.headBaselineMass h.1) =
        a * B.physicalScore m + phi B.referenceHead +
          ((∑ h : B.HeadIndex,
              (phi h.1 - phi B.referenceHead) *
                (B.headIndicator h.1 m - B.headBaselineMass h.1)) +
            ∑ h : B.HeadIndex,
              (phi h.1 - phi B.referenceHead) * B.headBaselineMass h.1) by
    ring, hsum]
  ring

/-- The covariance vector of a nuisance linear functional is the nuisance
covariance operator applied to its coefficient. -/
theorem nuisanceCovarianceVector_inner_nuisanceStatistic
    [Nonempty Head]
    (xi : B.ParamSpace) (z : B.NuisanceSpace) :
    B.nuisanceCovarianceVector xi
        (fun m => inner ℝ z (B.nuisanceStatistic m)) =
      B.nuisanceCovarianceOperator xi z := by
  apply ext_inner_left ℝ
  intro v
  rw [B.inner_nuisanceCovarianceVector,
    B.inner_nuisanceCovarianceOperator_bilinear]

/-- Regression recovers an exact nuisance linear functional. -/
theorem nuisanceCoefficientOfScore_inner_nuisanceStatistic
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (z : B.NuisanceSpace) :
    B.nuisanceCoefficientOfScore xi hgamma hgap
        (fun m => inner ℝ z (B.nuisanceStatistic m)) = z := by
  apply B.nuisanceCovarianceOperator_injective xi hgamma hgap
  rw [B.nuisanceCoefficientOfScore_solve,
    B.nuisanceCovarianceVector_inner_nuisanceStatistic]

/-- Hence the nuisance residual of a nuisance linear functional vanishes
pointwise, not merely in covariance. -/
theorem nuisanceResidualScore_inner_nuisanceStatistic
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (z : B.NuisanceSpace) :
    B.nuisanceResidualScore xi hgamma hgap
        (fun m => inner ℝ z (B.nuisanceStatistic m)) =
      fun _ => 0 := by
  funext m
  unfold nuisanceResidualScore
  rw [B.nuisanceCoefficientOfScore_inner_nuisanceStatistic]
  ring

/-- A deterministic score has zero nuisance covariance vector. -/
theorem nuisanceCovarianceVector_const
    [Nonempty Head]
    (xi : B.ParamSpace) (c : ℝ) :
    B.nuisanceCovarianceVector xi (fun _ => c) = 0 := by
  apply ext_inner_left ℝ
  intro z
  rw [B.inner_nuisanceCovarianceVector, inner_zero_right]
  unfold FiniteProbability.covariance
  rw [show (fun m => inner ℝ z (B.nuisanceStatistic m) * c) =
      fun m => c * inner ℝ z (B.nuisanceStatistic m) by
    funext m
    ring]
  rw [(B.tiltedLaw xi).expect_smul,
    (B.tiltedLaw xi).expect_const]
  ring

/-- The nuisance regression coefficient of a deterministic score is zero. -/
theorem nuisanceCoefficientOfScore_const
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (c : ℝ) :
    B.nuisanceCoefficientOfScore xi hgamma hgap (fun _ => c) = 0 := by
  apply B.nuisanceCovarianceOperator_injective xi hgamma hgap
  rw [B.nuisanceCoefficientOfScore_solve,
    B.nuisanceCovarianceVector_const, map_zero]

/-- Constants survive nuisance regression unchanged. -/
theorem nuisanceResidualScore_const
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (c : ℝ) :
    B.nuisanceResidualScore xi hgamma hgap (fun _ => c) = fun _ => c := by
  funext m
  unfold nuisanceResidualScore
  rw [B.nuisanceCoefficientOfScore_const]
  simp

/-- The nuisance residual of an affine nuisance score is precisely its
deterministic affine part. -/
theorem nuisanceResidualScore_inner_add_const
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (z : B.NuisanceSpace) (c : ℝ) :
    B.nuisanceResidualScore xi hgamma hgap
        (fun m => inner ℝ z (B.nuisanceStatistic m) + c) =
      fun _ => c := by
  rw [B.nuisanceResidualScore_add,
    B.nuisanceResidualScore_inner_nuisanceStatistic,
    B.nuisanceResidualScore_const]
  funext m
  simp

/-- Under the literal finite head-prime condition, `primeLogScore` has only
an affine nuisance residual. -/
theorem nuisanceResidualScore_primeLogScore_eq_const
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W) :
    B.nuisanceResidualScore xi hgamma hgap B.primeLogScore =
      fun _ => B.physicalHeadAffineConstant B.exactPrimeLogHeadFunction := by
  have hscore : B.primeLogScore = fun m =>
      inner ℝ
          (B.physicalHeadNuisanceVector
            (1 / Real.log (ArithmeticModel.y B.sampleData.n))
            B.exactPrimeLogHeadFunction)
          (B.nuisanceStatistic m) +
        B.physicalHeadAffineConstant B.exactPrimeLogHeadFunction := by
    funext m
    rw [B.primeLogScore_eq_explicit_physical_add_head hhead m]
    exact B.physical_mul_add_headFunction_eq_inner_add_constant
      (1 / Real.log (ArithmeticModel.y B.sampleData.n))
      B.exactPrimeLogHeadFunction m
  rw [hscore, B.nuisanceResidualScore_inner_add_const]

/-- Primewise form of the arithmetic physical residual score. -/
theorem primeValuationScore_residual_eq_band_sub_primeLog
    (b : Band → ℝ) (mu : ℝ) (m : B.sampleData.Sample) :
    B.primeValuationScore (B.partition.data.residual b mu) m =
      (∑ j : Band, b j * B.bandScore j m) - mu * B.primeLogScore m := by
  have hband :
      (∑ j : Band, b j * B.bandScore j m) =
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          b (B.partition.band p) *
            valuation p.1 (B.sampleData.value m) := by
    unfold bandScore
    rw [← Finset.sum_fiberwise Finset.univ B.partition.band
      (fun p : BandPrime B.sampleData.n B.sampleData.W =>
        b (B.partition.band p) *
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
  rw [hband]
  unfold primeValuationScore Erdos390.Lemma84.WeightedBandData.residual
    Erdos390.Lemma84.WeightedBandData.lift
    Erdos390.Lemma84.WeightedBandData.coord
    primeLogScore ArithmeticModel.tPrime ArithmeticBandGeometry.Partition.data
  simp only [ArithmeticModel.tPrime, div_eq_mul_inv]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Changing the physical subtraction parameter changes the prime score by
exactly a multiple of the prime-log nuisance direction. -/
theorem primeValuationScore_residual_change_mu
    (b : Band → ℝ) (mu nu : ℝ) :
    B.primeValuationScore (B.partition.data.residual b nu) =
      fun m =>
        B.primeValuationScore (B.partition.data.residual b mu) m +
          (mu - nu) * B.primeLogScore m := by
  funext m
  rw [B.primeValuationScore_residual_eq_band_sub_primeLog,
    B.primeValuationScore_residual_eq_band_sub_primeLog]
  ring

/-- The arbitrary band vector represented by an actual main parameter before
subtracting its physical logarithmic coordinate. -/
def mainBandVector (u : B.MainSpace) (j : Band) : ℝ :=
  (B.rawGaugeOfMain u).1 j +
    (u MainCoord.slow / B.w) * B.bandCenter j

/-- At the stored slow parameter, the physical residual score of
`mainBandVector` is exactly the literal exponential-family main score. -/
theorem primeValuationScore_mainBandVector_residual_eq_mainScore
    [Nonempty Head]
    (u : B.MainSpace) :
    B.primeValuationScore
        (B.partition.data.residual (B.mainBandVector u)
          (u MainCoord.slow / B.w)) =
      fun m => B.vectorFamily.scalarFamily.score m (B.mainEmbed u) := by
  funext m
  rw [B.primeValuationScore_residual_eq_band_sub_primeLog]
  rw [B.vectorScore_mainEmbed_eq_rawGauge_add_slow]
  rw [B.slowScore_eq_bandScore_sub_primeLogScore]
  unfold mainBandVector bandRegressionScore
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  have hsum :
      (∑ j : Band,
          (u MainCoord.slow / B.w) * B.bandCenter j * B.bandScore j m) =
        (u MainCoord.slow / B.w) *
          ∑ j : Band, B.bandCenter j * B.bandScore j m := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]
  ring

/-- The exact gauge part of `mainBandVector` is the original raw arithmetic
gauge.  Thus the slow/center direction is retained in `b` and only removed
by the literal quotient projection. -/
theorem gaugePart_mainBandVector_eq_rawGauge
    [Nonempty Band]
    (u : B.MainSpace) :
    B.partition.data.gaugePart (B.mainBandVector u) =
      (B.rawGaugeOfMain u).1 := by
  let q : B.RawBandGauge := B.rawGaugeOfMain u
  let lambda : ℝ := u MainCoord.slow / B.w
  have hq : B.partition.data.inGauge q.1 :=
    B.partition.rawGauge_inGauge q
  have henergy : B.partition.data.centerEnergy ≠ 0 :=
    (B.partition.centerEnergy_pos B.n_gt_one).ne'
  have hinner :
      B.partition.data.bandInner B.partition.data.center
          B.partition.data.center ≠ 0 := by
    simpa [Erdos390.Lemma84.WeightedBandData.centerEnergy,
      Erdos390.Lemma84.WeightedBandData.bandNormSq] using henergy
  have hcoef :
      B.partition.data.gaugeCoefficient (B.mainBandVector u) = lambda := by
    unfold Erdos390.Lemma84.WeightedBandData.gaugeCoefficient
    change B.partition.data.bandInner B.partition.data.center
        (fun j => q.1 j + lambda * B.partition.data.center j) /
          B.partition.data.centerEnergy = lambda
    rw [B.partition.data.bandInner_add_right,
      B.partition.data.bandInner_smul_right]
    change B.partition.data.bandInner B.partition.data.center q.1 = 0 at hq
    rw [hq, zero_add]
    unfold Erdos390.Lemma84.WeightedBandData.centerEnergy
      Erdos390.Lemma84.WeightedBandData.bandNormSq
    field_simp [hinner]
  apply funext
  intro j
  unfold Erdos390.Lemma84.WeightedBandData.gaugePart mainBandVector
  change q.1 j + lambda * B.partition.data.center j -
      B.partition.data.gaugeCoefficient (B.mainBandVector u) *
        B.partition.data.center j = q.1 j
  rw [hcoef]
  ring

/-- Exact null relation needed by the full quotient gap: after nuisance
regression, changing `mu` adds only a deterministic constant. -/
theorem nuisanceResidualScore_residual_change_mu
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W)
    (b : Band → ℝ) (mu nu : ℝ) :
    B.nuisanceResidualScore xi hgamma hgap
        (B.primeValuationScore (B.partition.data.residual b nu)) =
      fun m =>
        B.nuisanceResidualScore xi hgamma hgap
            (B.primeValuationScore (B.partition.data.residual b mu)) m +
          (mu - nu) *
            B.physicalHeadAffineConstant B.exactPrimeLogHeadFunction := by
  rw [B.primeValuationScore_residual_change_mu,
    B.nuisanceResidualScore_add, B.nuisanceResidualScore_smul,
    B.nuisanceResidualScore_primeLogScore_eq_const
      xi hgamma hgap hhead]

/-- Adding a deterministic constant to the right statistic leaves a finite
covariance unchanged.  This is stated separately because the slow-row
identification below needs equality of the literal normalized rows, not only
equality of the corresponding quadratic forms. -/
theorem covariance_add_const_right
    {Omega : Type*} [Fintype Omega]
    (law : Erdos390.Full.FiniteProbability Omega)
    (F G : Omega → ℝ) (c : ℝ) :
    law.covariance F (fun omega => G omega + c) = law.covariance F G := by
  have hconstLeft : law.covariance (fun _ => c) F = 0 := by
    unfold Erdos390.Full.FiniteProbability.covariance
    rw [law.expect_smul, law.expect_const]
    ring
  have hconstRight : law.covariance F (fun _ => c) = 0 := by
    rw [law.covariance_comm]
    exact hconstLeft
  rw [law.covariance_add_right, hconstRight, add_zero]

/-- Exact normalized-row version of the finite prime-log null relation.
After nuisance regression, the literal slow score and the arithmetic
band-centre valuation score differ only by a deterministic constant.
Consequently every normalized band covariance row is identical.  No lower
bound on a band centre and no limiting argument is used. -/
theorem normalizedBandCovarianceRow_nuisanceResidual_slow_eq_bandCenterScore
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W) :
    B.normalizedBandCovarianceRow xi
        (B.nuisanceResidualScore xi hgamma hgap B.slowScore) =
      B.normalizedBandCovarianceRow xi
        (B.nuisanceResidualScore xi hgamma hgap
          (fun m => ∑ j : Band, B.bandCenter j * B.bandScore j m)) := by
  have hslow : B.slowScore =
      B.primeValuationScore
        (B.partition.data.residual B.bandCenter 1) := by
    funext m
    rw [B.primeValuationScore_residual_eq_band_sub_primeLog]
    simpa only [one_mul] using B.slowScore_eq_bandScore_sub_primeLogScore m
  have hcenter :
      (fun m => ∑ j : Band, B.bandCenter j * B.bandScore j m) =
        B.primeValuationScore
          (B.partition.data.residual B.bandCenter 0) := by
    funext m
    rw [B.primeValuationScore_residual_eq_band_sub_primeLog]
    ring
  rw [hslow, hcenter]
  have hchange := B.nuisanceResidualScore_residual_change_mu
    xi hgamma hgap hhead B.bandCenter 0 1
  funext i
  unfold normalizedBandCovarianceRow
  rw [hchange]
  exact congrArg (fun x : ℝ => x / B.harmonicMass i)
    (covariance_add_const_right
      (B.tiltedLaw xi) (B.bandScore i)
      (B.nuisanceResidualScore xi hgamma hgap
        (B.primeValuationScore
          (B.partition.data.residual B.bandCenter 0)))
      ((0 - 1) *
        B.physicalHeadAffineConstant B.exactPrimeLogHeadFunction))

/-- Covariance is unchanged when a deterministic constant is added to both
copies of a score. -/
theorem covariance_add_const_self
    {Omega : Type*} [Fintype Omega]
    (law : Erdos390.Full.FiniteProbability Omega)
    (F : Omega → ℝ) (c : ℝ) :
    law.covariance (fun omega => F omega + c)
        (fun omega => F omega + c) = law.covariance F F := by
  have hconstLeft (G : Omega → ℝ) :
      law.covariance (fun _ => c) G = 0 := by
    unfold Erdos390.Full.FiniteProbability.covariance
    rw [law.expect_smul, law.expect_const]
    ring
  have hconstRight (G : Omega → ℝ) :
      law.covariance G (fun _ => c) = 0 := by
    rw [law.covariance_comm]
    exact hconstLeft G
  rw [law.covariance_add_left, law.covariance_add_right,
    law.covariance_add_right, hconstRight, hconstLeft, hconstLeft]
  ring

/-- The nuisance-Schur variance of the physical residual is independent of
the subtraction parameter `mu`.  This is the finite exact-null statement,
with no asymptotic hypothesis. -/
theorem nuisanceResidualVariance_residual_independent_mu
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W)
    (b : Band → ℝ) (mu nu : ℝ) :
    (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.primeValuationScore (B.partition.data.residual b nu)))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.primeValuationScore (B.partition.data.residual b nu))) =
      (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.primeValuationScore (B.partition.data.residual b mu)))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.primeValuationScore (B.partition.data.residual b mu))) := by
  rw [B.nuisanceResidualScore_residual_change_mu
    xi hgamma hgap hhead b mu nu]
  exact covariance_add_const_self
    (B.tiltedLaw xi)
    (B.nuisanceResidualScore xi hgamma hgap
      (B.primeValuationScore (B.partition.data.residual b mu)))
    ((mu - nu) *
      B.physicalHeadAffineConstant B.exactPrimeLogHeadFunction)

/-- Fixed-kappa full quotient gap for every arithmetic band vector and every
choice of the physical subtraction parameter.  The production lower bound is
proved at the exact arithmetic minimizer; `nuisanceResidualVariance_residual_independent_mu`
then transfers it by an equality, not an estimate, to the parameter carried
by the actual main/slow score. -/
theorem actualResidualSchur_fullQuotient_Dgap_canonicalKappa_independent_mu
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma Cmarked : ℝ}
    (hgamma : 0 < gamma) (hCmarked : 0 ≤ Cmarked)
    (hgapNuisance : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Set.Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    {rowError Eprofile CKernel totalWeight invW R : ℝ}
    (hEprofile : 0 ≤ Eprofile) (hCKernel : 0 ≤ CKernel)
    (hW : 0 < B.sampleData.W)
    (hTotal : (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        reciprocalWeight p) ≤ totalWeight)
    (hInvW : (1 / (B.sampleData.W : ℝ)) ≤ invW)
    (hrowReference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hpair : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p r 1 1)| ≤
        Eprofile * pairWeight p r 1 1)
    (hsingle : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel)
    (hrowPower : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) * ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV p.1 r.1 -
          (B.actualValuationLaw xi).covII p.1 r.1| ≤ R)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (hsmall : rowError +
          ((4 * pairCovarianceScale Eprofile) * totalWeight +
            2 * Eprofile +
            ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
              CKernel) * invW) +
          R +
          ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked ^ 2 * totalWeight / gamma) ≤
        (canonicalSlowKappa / 2) *
          anchorMass (primeWeight B.sampleData.n) anchor) :
    ∀ (b : Band → ℝ) (mu : ℝ),
      let c := B.partition.data.residual b mu
      let F := B.primeValuationScore c
      ((canonicalSlowKappa / 2) *
                anchorMass (primeWeight B.sampleData.n) anchor -
              rowError -
              ((4 * pairCovarianceScale Eprofile) * totalWeight +
                2 * Eprofile +
                ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                  CKernel) * invW) -
              R -
              ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
                Cmarked ^ 2 * totalWeight / gamma)) *
            B.partition.data.bandNormSq (B.partition.data.gaugePart b) ≤
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgapNuisance F)
          (B.nuisanceResidualScore xi hgamma hgapNuisance F) := by
  intro b mu
  dsimp only
  have hbase :=
    B.actualPhysicalResidualSchur_fullQuotient_Dgap_canonicalKappa
      xi hgamma hCmarked hgapNuisance anchor hinterior hmass
      hEprofile hCKernel hW hTotal hInvW hrowReference hpair hsingle
      hKernel hrowPower hmarked hsmall b
  have hnull := B.nuisanceResidualVariance_residual_independent_mu
    xi hgamma hgapNuisance hhead b
      (B.partition.data.physicalMinimizer b) mu
  rw [hnull]
  exact hbase

/-- Literal `MainSpace` form of the fixed-kappa quotient gap.  The left side
is the arithmetic `D`-norm of the raw gauge represented by `u`; the right side
is the actual nuisance-Schur variance of the exponential-family main score.
The stored slow coordinate is present in that score and is removed from the
left side only through the exact quotient projection proved above. -/
theorem actualMainScoreSchur_rawGauge_Dgap_canonicalKappa
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma Cmarked : ℝ}
    (hgamma : 0 < gamma) (hCmarked : 0 ≤ Cmarked)
    (hgapNuisance : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Set.Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    {rowError Eprofile CKernel totalWeight invW R : ℝ}
    (hEprofile : 0 ≤ Eprofile) (hCKernel : 0 ≤ CKernel)
    (hW : 0 < B.sampleData.W)
    (hTotal : (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        reciprocalWeight p) ≤ totalWeight)
    (hInvW : (1 / (B.sampleData.W : ℝ)) ≤ invW)
    (hrowReference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hpair : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p r 1 1)| ≤
        Eprofile * pairWeight p r 1 1)
    (hsingle : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel)
    (hrowPower : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) * ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV p.1 r.1 -
          (B.actualValuationLaw xi).covII p.1 r.1| ≤ R)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (hsmall : rowError +
          ((4 * pairCovarianceScale Eprofile) * totalWeight +
            2 * Eprofile +
            ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
              CKernel) * invW) +
          R +
          ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked ^ 2 * totalWeight / gamma) ≤
        (canonicalSlowKappa / 2) *
          anchorMass (primeWeight B.sampleData.n) anchor) :
    ∀ u : B.MainSpace,
      ((canonicalSlowKappa / 2) *
                anchorMass (primeWeight B.sampleData.n) anchor -
              rowError -
              ((4 * pairCovarianceScale Eprofile) * totalWeight +
                2 * Eprofile +
                ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                  CKernel) * invW) -
              R -
              ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
                Cmarked ^ 2 * totalWeight / gamma)) *
            B.partition.data.bandNormSq (B.rawGaugeOfMain u).1 ≤
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgapNuisance
            (fun m =>
              B.vectorFamily.scalarFamily.score m (B.mainEmbed u)))
          (B.nuisanceResidualScore xi hgamma hgapNuisance
            (fun m =>
              B.vectorFamily.scalarFamily.score m (B.mainEmbed u))) := by
  intro u
  have hbound :=
    B.actualResidualSchur_fullQuotient_Dgap_canonicalKappa_independent_mu
      xi hgamma hCmarked hgapNuisance hhead anchor hinterior hmass
      hEprofile hCKernel hW hTotal hInvW hrowReference hpair hsingle
      hKernel hrowPower hmarked hsmall
      (B.mainBandVector u) (u MainCoord.slow / B.w)
  dsimp only at hbound
  rw [B.gaugePart_mainBandVector_eq_rawGauge] at hbound
  rw [B.primeValuationScore_mainBandVector_residual_eq_mainScore] at hbound
  exact hbound

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
