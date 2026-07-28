import Erdos390.Full.NuisanceCovariance
import Erdos390.Proposition87

/-!
# The finite nonlinear moment lift

This file turns the scalar covariance--Jacobian identity for a finite
exponential family into the vector Jacobian used by the nonlinear fitting
argument.  A quantitative covariance gap is then used to construct the
inverse Jacobian (rather than assuming a right inverse), define the actual
ODE vector field, and prove its exact solve and velocity estimates.

The final section records a non-circular continuation theorem.  Its input is
an explicit covariance gap on a ball chosen before solving the ODE; local
Lipschitz continuity is derived from the finite exponential formulas and
operator inversion.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full

noncomputable section

/-- A self-dual finite exponential family.  The tilt score of a sample is the
inner product with its statistic. -/
structure VectorExponentialFamily
    (Omega E : Type*) [Fintype Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] where
  baseWeight : Omega → ℝ
  baseWeight_nonneg : ∀ omega, 0 ≤ baseWeight omega
  baseMass_pos : 0 < ∑ omega, baseWeight omega
  scale : ℝ
  scale_pos : 0 < scale
  statistic : Omega → E

namespace VectorExponentialFamily

variable {Omega E : Type*} [Fintype Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The scalar family underlying a vector exponential family. -/
def scalarFamily (vf : VectorExponentialFamily Omega E) :
    FiniteExponentialFamily Omega E where
  baseWeight := vf.baseWeight
  baseWeight_nonneg := vf.baseWeight_nonneg
  baseMass_pos := vf.baseMass_pos
  scale := vf.scale
  scale_pos := vf.scale_pos
  score := fun omega => (innerSL ℝ) (vf.statistic omega)

/-- Total active mass. -/
def baseMass (vf : VectorExponentialFamily Omega E) : ℝ :=
  vf.scalarFamily.baseMass

theorem baseMass_positive (vf : VectorExponentialFamily Omega E) :
    0 < vf.baseMass :=
  vf.scalarFamily.baseMass_positive

/-- The exact normalized tilted probability mass. -/
def probabilityMass (vf : VectorExponentialFamily Omega E)
    (xi : E) (omega : Omega) : ℝ :=
  vf.scalarFamily.probabilityMass xi omega

/-- The active vector moment map. -/
def vectorMoment (vf : VectorExponentialFamily Omega E) (xi : E) : E :=
  ∑ omega, vf.scalarFamily.activeWeight xi omega • vf.statistic omega

/-- Kronecker test function used to differentiate one active weight. -/
def delta (omega : Omega) (eta : Omega) : ℝ := by
  classical
  exact if eta = omega then 1 else 0

@[simp]
theorem moment_delta (vf : VectorExponentialFamily Omega E)
    (xi : E) (omega : Omega) :
    vf.scalarFamily.moment (delta omega) xi =
      vf.scalarFamily.activeWeight xi omega := by
  classical
  simp [FiniteExponentialFamily.moment, delta]

/-- Derivative of one active coordinate, obtained from the already proved
finite covariance identity. -/
def activeWeightFDeriv (vf : VectorExponentialFamily Omega E)
    (xi : E) (omega : Omega) : E →L[ℝ] ℝ :=
  (vf.baseMass / vf.scale) •
    vf.scalarFamily.covarianceScore (delta omega) xi

theorem hasFDerivAt_activeWeight (vf : VectorExponentialFamily Omega E)
    (xi : E) (omega : Omega) :
    HasFDerivAt (fun eta => vf.scalarFamily.activeWeight eta omega)
      (vf.activeWeightFDeriv xi omega) xi := by
  have h := vf.scalarFamily.hasFDerivAt_moment_covariance
    (delta omega) xi
  have hfun : vf.scalarFamily.moment (delta omega) =
      fun eta => vf.scalarFamily.activeWeight eta omega := by
    funext eta
    exact vf.moment_delta eta omega
  rw [hfun] at h
  simpa only [activeWeightFDeriv, baseMass] using h

/-- The concrete vector Jacobian.  It is a finite sum of the derivatives of
the active weights, each multiplied by its statistic vector. -/
def jacobian (vf : VectorExponentialFamily Omega E) (xi : E) : E →L[ℝ] E :=
  ∑ omega, (vf.activeWeightFDeriv xi omega).smulRight (vf.statistic omega)

/-- Exact Fréchet derivative of the vector moment map. -/
theorem hasFDerivAt_vectorMoment (vf : VectorExponentialFamily Omega E)
    (xi : E) :
    HasFDerivAt vf.vectorMoment (vf.jacobian xi) xi := by
  have h := HasFDerivAt.sum (u := (Finset.univ : Finset Omega))
    (fun omega (_ : omega ∈ (Finset.univ : Finset Omega)) =>
      (vf.hasFDerivAt_activeWeight xi omega).smul_const
        (vf.statistic omega))
  have hfun : vf.vectorMoment =
      ∑ omega, fun eta =>
        vf.scalarFamily.activeWeight eta omega • vf.statistic omega := by
    funext eta
    simp only [vectorMoment, Finset.sum_apply]
  rw [hfun]
  simpa only [jacobian] using h

/-- Pairing the vector moment with a direction gives the corresponding
scalar active moment. -/
theorem inner_vectorMoment (vf : VectorExponentialFamily Omega E)
    (x xi : E) :
    inner ℝ x (vf.vectorMoment xi) =
      vf.scalarFamily.moment (fun omega => inner ℝ x (vf.statistic omega)) xi := by
  simp only [vectorMoment, FiniteExponentialFamily.moment, inner_sum,
    real_inner_smul_right]

/-- The tilted statistics as an actual finite pattern mixture. -/
def tiltedMixture (vf : VectorExponentialFamily Omega E) (xi : E) :
    PatternMixture Omega E where
  weight := vf.probabilityMass xi
  weight_nonneg := vf.scalarFamily.probabilityMass_nonneg xi
  weight_sum := vf.scalarFamily.probabilityMass_sum xi
  pattern := vf.statistic

/-- Exact quadratic covariance identity for the vector Jacobian. -/
theorem inner_jacobian_self (vf : VectorExponentialFamily Omega E)
    (xi x : E) :
    inner ℝ x (vf.jacobian xi x) =
      (vf.baseMass / vf.scale) * (vf.tiltedMixture xi).covarianceForm x := by
  let F : Omega → ℝ := fun omega => inner ℝ x (vf.statistic omega)
  have hleft : HasFDerivAt
      (fun eta => inner ℝ x (vf.vectorMoment eta))
      (((innerSL ℝ) x).comp (vf.jacobian xi)) xi := by
    exact ((innerSL ℝ) x).hasFDerivAt.comp xi
      (vf.hasFDerivAt_vectorMoment xi)
  have hright : HasFDerivAt
      (vf.scalarFamily.moment F)
      ((vf.baseMass / vf.scale) •
        vf.scalarFamily.covarianceScore F xi) xi :=
    vf.scalarFamily.hasFDerivAt_moment_covariance F xi
  have hfun : (fun eta => inner ℝ x (vf.vectorMoment eta)) =
      vf.scalarFamily.moment F := by
    funext eta
    exact vf.inner_vectorMoment x eta
  have hmaps : ((innerSL ℝ) x).comp (vf.jacobian xi) =
      (vf.baseMass / vf.scale) •
        vf.scalarFamily.covarianceScore F xi := by
    exact hleft.unique (hfun ▸ hright)
  have happ := congrArg (fun T : E →L[ℝ] ℝ => T x) hmaps
  change inner ℝ x (vf.jacobian xi x) =
    (vf.baseMass / vf.scale) *
      vf.scalarFamily.covarianceScore F xi x at happ
  rw [vf.scalarFamily.covarianceScore_apply F xi x] at happ
  have hscore : (fun omega => vf.scalarFamily.score omega x) = F := by
    funext omega
    simp only [scalarFamily, innerSL_apply_apply, F]
    exact real_inner_comm _ _
  rw [hscore] at happ
  simpa only [tiltedMixture, PatternMixture.covarianceForm,
    PatternMixture.probability, FiniteExponentialFamily.covariance,
    FiniteExponentialFamily.tiltedProbability, probabilityMass, smul_eq_mul]
    using happ

/-- A pointwise spectral-gap hypothesis for the actual tilted finite law. -/
def HasCovarianceGap (vf : VectorExponentialFamily Omega E)
    (gamma : ℝ) (xi : E) : Prop :=
  ∀ x, gamma * ‖x‖ ^ 2 ≤ (vf.tiltedMixture xi).covarianceForm x

theorem jacobian_coercive (vf : VectorExponentialFamily Omega E)
    {gamma : ℝ} {xi : E}
    (hgap : vf.HasCovarianceGap gamma xi) (x : E) :
    ((vf.baseMass / vf.scale) * gamma) * ‖x‖ ^ 2 ≤
      inner ℝ x (vf.jacobian xi x) := by
  rw [vf.inner_jacobian_self xi x]
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left (hgap x)
      (div_nonneg (le_of_lt vf.baseMass_positive)
        (le_of_lt vf.scale_pos)))

theorem jacobian_injective (vf : VectorExponentialFamily Omega E)
    {gamma : ℝ} (hgamma : 0 < gamma) {xi : E}
    (hgap : vf.HasCovarianceGap gamma xi) :
    Function.Injective (vf.jacobian xi) := by
  intro x y hxy
  have hzero : vf.jacobian xi (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hcoer := vf.jacobian_coercive hgap (x - y)
  rw [hzero, inner_zero_right] at hcoer
  have hcpos : 0 < (vf.baseMass / vf.scale) * gamma :=
    mul_pos (div_pos vf.baseMass_positive vf.scale_pos) hgamma
  have hnorm : ‖x - y‖ = 0 := by
    by_contra hn
    have hnormpos : 0 < ‖x - y‖ :=
      lt_of_le_of_ne (norm_nonneg (x - y)) (Ne.symm hn)
    have hprodpos : 0 <
        ((vf.baseMass / vf.scale) * gamma) * ‖x - y‖ ^ 2 :=
      mul_pos hcpos (sq_pos_of_pos hnormpos)
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- The Jacobian as a continuous linear equivalence, constructed from the
proved covariance gap. -/
def jacobianEquiv [CompleteSpace E]
    (vf : VectorExponentialFamily Omega E)
    {gamma : ℝ} (hgamma : 0 < gamma) {xi : E}
    (hgap : vf.HasCovarianceGap gamma xi) : E ≃L[ℝ] E := by
  let J := vf.jacobian xi
  have hinj : Function.Injective J := vf.jacobian_injective hgamma hgap
  have hsurj : Function.Surjective J :=
    LinearMap.surjective_of_injective hinj
  exact ContinuousLinearEquiv.ofBijective J
    (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj)

theorem jacobian_isInvertible [CompleteSpace E]
    (vf : VectorExponentialFamily Omega E)
    {gamma : ℝ} (hgamma : 0 < gamma) {xi : E}
    (hgap : vf.HasCovarianceGap gamma xi) :
    (vf.jacobian xi).IsInvertible := by
  exact ⟨vf.jacobianEquiv hgamma hgap, rfl⟩

/-- The actual globally defined vector field.  At a point with a covariance
gap this is the genuine inverse-Jacobian lift of `target`. -/
def vectorField (vf : VectorExponentialFamily Omega E) (target : E)
    (xi : E) : E :=
  (vf.jacobian xi).inverse target

theorem jacobian_vectorField [CompleteSpace E]
    (vf : VectorExponentialFamily Omega E) (target : E)
    {gamma : ℝ} (hgamma : 0 < gamma) {xi : E}
    (hgap : vf.HasCovarianceGap gamma xi) :
    vf.jacobian xi (vf.vectorField target xi) = target := by
  exact (vf.jacobian_isInvertible hgamma hgap).self_apply_inverse target

/-- Quantitative inverse bound derived from coercivity and Cauchy--Schwarz. -/
theorem norm_vectorField_le [CompleteSpace E]
    (vf : VectorExponentialFamily Omega E) (target : E)
    {gamma : ℝ} (hgamma : 0 < gamma) {xi : E}
    (hgap : vf.HasCovarianceGap gamma xi) :
    ‖vf.vectorField target xi‖ ≤
      ‖target‖ / ((vf.baseMass / vf.scale) * gamma) := by
  let v := vf.vectorField target xi
  have hsolve : vf.jacobian xi v = target :=
    vf.jacobian_vectorField target hgamma hgap
  have hcoer := vf.jacobian_coercive hgap v
  rw [hsolve] at hcoer
  have hinner : inner ℝ v target ≤ ‖v‖ * ‖target‖ :=
    real_inner_le_norm _ _
  have hcpos : 0 < (vf.baseMass / vf.scale) * gamma :=
    mul_pos (div_pos vf.baseMass_positive vf.scale_pos) hgamma
  by_cases hv : ‖v‖ = 0
  · have hleft : ‖vf.vectorField target xi‖ = 0 := by simpa [v] using hv
    rw [hleft]
    exact div_nonneg (norm_nonneg target) (le_of_lt hcpos)
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    have hprod : ((vf.baseMass / vf.scale) * gamma) * ‖v‖ ≤ ‖target‖ := by
      have hcancel :
          (((vf.baseMass / vf.scale) * gamma) * ‖v‖) * ‖v‖ ≤
            ‖target‖ * ‖v‖ := by
        calc
          (((vf.baseMass / vf.scale) * gamma) * ‖v‖) * ‖v‖
              = ((vf.baseMass / vf.scale) * gamma) * ‖v‖ ^ 2 := by ring
          _ ≤ inner ℝ v target := hcoer
          _ ≤ ‖target‖ * ‖v‖ := by simpa [mul_comm] using hinner
      exact (mul_le_mul_iff_left₀ hvpos).mp hcancel
    apply (le_div_iff₀ hcpos).2
    simpa [v, mul_comm] using hprod

/-! ## Smoothness and non-circular continuation -/

theorem expectation_contDiff (vf : VectorExponentialFamily Omega E)
    (F : Omega → ℝ) :
    ContDiff ℝ ⊤ (vf.scalarFamily.expectation F) := by
  change ContDiff ℝ ⊤ (fun xi =>
    ∑ omega, vf.scalarFamily.probabilityMass xi omega * F omega)
  apply ContDiff.sum
  intro omega _
  exact (vf.scalarFamily.probabilityMass_contDiff omega).mul contDiff_const

theorem covarianceScore_contDiff (vf : VectorExponentialFamily Omega E)
    (F : Omega → ℝ) :
    ContDiff ℝ ⊤ (fun xi => vf.scalarFamily.covarianceScore F xi) := by
  simp only [FiniteExponentialFamily.covarianceScore]
  apply ContDiff.sum
  intro omega _
  have hscalar : ContDiff ℝ ⊤ (fun xi =>
      vf.scalarFamily.probabilityMass xi omega *
        (F omega - vf.scalarFamily.expectation F xi)) :=
    (vf.scalarFamily.probabilityMass_contDiff omega).mul
      (contDiff_const.sub (vf.expectation_contDiff F))
  have hscore : ContDiff ℝ ⊤
      (fun _ : E => vf.scalarFamily.score omega) := contDiff_const
  simpa only [Pi.smul_apply] using hscalar.smul hscore

theorem activeWeightFDeriv_contDiff
    (vf : VectorExponentialFamily Omega E) (omega : Omega) :
    ContDiff ℝ ⊤ (fun xi => vf.activeWeightFDeriv xi omega) := by
  simpa only [activeWeightFDeriv] using
    (ContDiff.const_smul (vf.baseMass / vf.scale)
      (vf.covarianceScore_contDiff (delta omega)))

/-- The finite covariance Jacobian varies smoothly on the whole parameter
space. -/
theorem jacobian_contDiff (vf : VectorExponentialFamily Omega E) :
    ContDiff ℝ ⊤ vf.jacobian := by
  change ContDiff ℝ ⊤ (fun xi =>
    ∑ omega, (vf.activeWeightFDeriv xi omega).smulRight
      (vf.statistic omega))
  apply ContDiff.sum
  intro omega _
  exact (vf.activeWeightFDeriv_contDiff omega).smulRight contDiff_const

/-- At every point where the explicit covariance gap holds, the actual
inverse-Jacobian vector field is `C^1`.  This is derived from smooth operator
inversion, not supplied as an ODE regularity hypothesis. -/
theorem vectorField_contDiffAt [CompleteSpace E]
    (vf : VectorExponentialFamily Omega E) (target : E)
    {gamma : ℝ} (hgamma : 0 < gamma) {xi : E}
    (hgap : vf.HasCovarianceGap gamma xi) :
    ContDiffAt ℝ 1 (vf.vectorField target) xi := by
  have hinv : ContDiffAt ℝ 1
      (fun eta => (vf.jacobian eta).inverse) xi :=
    (vf.jacobian_isInvertible hgamma hgap).contDiffAt_map_inverse.comp xi
      (vf.jacobian_contDiff.contDiffAt.of_le (by simp))
  have happ := hinv.clm_apply (contDiffAt_const (x := xi) (c := target))
  simpa only [vectorField] using happ

theorem vectorField_contDiffOn [CompleteSpace E]
    (vf : VectorExponentialFamily Omega E) (target : E)
    {gamma : ℝ} (hgamma : 0 < gamma) (s : Set E)
    (hgap : ∀ xi ∈ s, vf.HasCovarianceGap gamma xi) :
    ContDiffOn ℝ 1 (vf.vectorField target) s := by
  intro xi hxi
  exact (vf.vectorField_contDiffAt target hgamma (hgap xi hxi)).contDiffWithinAt

/-- Convert the explicit finite baseline/coarsening certificate of
`NuisanceCovariance` into the precise gap predicate needed by the Jacobian.
This theorem uses the actual finite baseline weights at `x0`; no limiting
covariance object occurs. -/
theorem hasCovarianceGap_of_coarseBaseline
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (vf : VectorExponentialFamily Omega E) (x0 xi : E)
    (coarse : PatternMixture Cell E)
    (coarseMean : PatternMixture.CoarseMeanCertificate
      (vf.tiltedMixture x0) coarse)
    (cert : PatternMixture.AffineSpanningCertificate coarse)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hweight : ∀ c, lambda ≤ coarse.weight c)
    (diameter epsilon : ℝ)
    (hdiam : ∀ i j,
      ‖(vf.tiltedMixture x0).pattern i -
        (vf.tiltedMixture x0).pattern j‖ ≤ diameter)
    (hl1 : (vf.tiltedMixture x0).weightL1Distance
      (vf.probabilityMass xi) ≤ epsilon)
    (hsmall : epsilon * diameter ^ 2 ≤
      PatternMixture.baselineGap lambda cert / 2) :
    vf.HasCovarianceGap
      (PatternMixture.baselineGap lambda cert / 2) xi := by
  intro x
  have h := PatternMixture.actualCovarianceForm_reweight_half_gap_of_coarsening
    (vf.tiltedMixture x0) coarse coarseMean cert lambda hlambda hweight
    (vf.probabilityMass xi)
    (vf.scalarFamily.probabilityMass_nonneg xi)
    (vf.scalarFamily.probabilityMass_sum xi)
    diameter epsilon hdiam hl1 hsmall x
  exact h

/-- Straight-target lift on a box fixed before the ODE is solved.

The only analytic input is the actual covariance gap at every point of the
prechosen closed ball.  The inverse Jacobian, solve identity, speed bound,
and a Lipschitz constant for the vector field are all derived above.  The
displayed margin is checked before invoking Picard--Lindelöf, so confinement
in the same ball is non-circular. -/
theorem exists_straightTargetLift_on_preselectedBall [CompleteSpace E]
    (vf : VectorExponentialFamily Omega E)
    (x0 target : E) (a : NNReal)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ xi ∈ closedBall x0 (a : ℝ),
      vf.HasCovarianceGap gamma xi)
    (hmargin : ‖target‖ / ((vf.baseMass / vf.scale) * gamma) ≤ (a : ℝ)) :
    ∃ path : ℝ → E, path 0 = x0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, path t ∈ closedBall x0 (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path (vf.vectorField target (path t))
          (Icc (0 : ℝ) 1) t) ∧
      vf.vectorMoment (path 1) = vf.vectorMoment x0 + target := by
  have hcpos : 0 < (vf.baseMass / vf.scale) * gamma :=
    mul_pos (div_pos vf.baseMass_positive vf.scale_pos) hgamma
  let speed : NNReal :=
    ⟨‖target‖ / ((vf.baseMass / vf.scale) * gamma),
      div_nonneg (norm_nonneg target) (le_of_lt hcpos)⟩
  have hspeed : ∀ xi ∈ closedBall x0 (a : ℝ),
      ‖vf.vectorField target xi‖ ≤ (speed : ℝ) := by
    intro xi hxi
    simpa only [speed] using
      (vf.norm_vectorField_le target hgamma (hgap xi hxi))
  have hsmooth : ContDiffOn ℝ 1 (vf.vectorField target)
      (closedBall x0 (a : ℝ)) :=
    vf.vectorField_contDiffOn target hgamma _ hgap
  obtain ⟨K, hK⟩ := hsmooth.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall x0 (a : ℝ)) (isCompact_closedBall x0 (a : ℝ))
  have hspeed_le_a : speed ≤ a := by
    apply NNReal.coe_le_coe.mp
    simpa only [speed] using hmargin
  exact Erdos390.straight_target_fit_of_lipschitz
    (vf.vectorField target) vf.vectorMoment vf.jacobian
    x0 target a speed K hspeed hK hspeed_le_a
    (fun xi _ => vf.hasFDerivAt_vectorMoment xi)
    (fun xi hxi => vf.jacobian_vectorField target hgamma (hgap xi hxi))

/-- Fully finite certificate form of the preselected-box theorem.  Instead of
assuming a covariance or inverse-Jacobian bound, it accepts:

* actual baseline and coarse pattern mixtures;
* exact conditional-mean and affine-spanning certificates;
* a uniform positive lower bound for the coarse cell masses;
* an explicit diameter bound and an `ell^1` tilt bound on the chosen ball.

These data imply the half-gap via the finite law of total variance and the
weight-perturbation theorem, after which the nonlinear lift is automatic. -/
theorem exists_straightTargetLift_of_coarseBaseline
    [CompleteSpace E]
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (vf : VectorExponentialFamily Omega E)
    (x0 target : E) (a : NNReal)
    (coarse : PatternMixture Cell E)
    (coarseMean : PatternMixture.CoarseMeanCertificate
      (vf.tiltedMixture x0) coarse)
    (cert : PatternMixture.AffineSpanningCertificate coarse)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hweight : ∀ c, lambda ≤ coarse.weight c)
    (diameter epsilon : ℝ)
    (hdiam : ∀ i j,
      ‖(vf.tiltedMixture x0).pattern i -
        (vf.tiltedMixture x0).pattern j‖ ≤ diameter)
    (hl1 : ∀ xi ∈ closedBall x0 (a : ℝ),
      (vf.tiltedMixture x0).weightL1Distance
        (vf.probabilityMass xi) ≤ epsilon)
    (hsmall : epsilon * diameter ^ 2 ≤
      PatternMixture.baselineGap lambda cert / 2)
    (hmargin : ‖target‖ /
      ((vf.baseMass / vf.scale) *
        (PatternMixture.baselineGap lambda cert / 2)) ≤ (a : ℝ)) :
    ∃ path : ℝ → E, path 0 = x0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, path t ∈ closedBall x0 (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path (vf.vectorField target (path t))
          (Icc (0 : ℝ) 1) t) ∧
      vf.vectorMoment (path 1) = vf.vectorMoment x0 + target := by
  have hgamma : 0 < PatternMixture.baselineGap lambda cert / 2 :=
    div_pos (PatternMixture.baselineGap_pos lambda hlambda cert) (by norm_num)
  apply vf.exists_straightTargetLift_on_preselectedBall
    x0 target a hgamma _ hmargin
  intro xi hxi
  exact vf.hasCovarianceGap_of_coarseBaseline x0 xi coarse coarseMean cert
    lambda hlambda hweight diameter epsilon hdiam (hl1 xi hxi) hsmall

end VectorExponentialFamily

end

end Erdos390.Full
