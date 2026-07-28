import Erdos390.Full.FiniteExponentialFamily

/-!
# Uniform finite nuisance-covariance gaps

This file isolates the finite-dimensional argument used for the actual
finite-`n` nuisance covariance `Γ_{0,n}`.  There is no limiting mixture.
The hypotheses are explicit pattern vectors, explicit probability weights,
a positive lower bound for those weights, and a checkable affine-spanning
certificate (a continuous linear reconstruction from pair differences).

The second part controls a perturbation of the mixture weights in `ℓ¹` and
shows that a sufficiently small bounded tilt preserves half of the baseline
gap.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

/-- A finite probability mixture of explicit nuisance-pattern vectors. -/
structure PatternMixture
    (Cell Nuisance : Type*) [Fintype Cell]
    [NormedAddCommGroup Nuisance] [InnerProductSpace ℝ Nuisance] where
  weight : Cell → ℝ
  weight_nonneg : ∀ c, 0 ≤ weight c
  weight_sum : ∑ c, weight c = 1
  pattern : Cell → Nuisance

namespace PatternMixture

variable {Cell Nuisance : Type*} [Fintype Cell]
  [NormedAddCommGroup Nuisance] [InnerProductSpace ℝ Nuisance]

/-- The mixture weights as an actual finite probability law. -/
def probability (mix : PatternMixture Cell Nuisance) : FiniteProbability Cell where
  mass := mix.weight
  mass_nonneg := mix.weight_nonneg
  mass_sum := mix.weight_sum

/-- The scalar quadratic form of the nuisance covariance matrix in direction
`x`. -/
def covarianceForm (mix : PatternMixture Cell Nuisance) (x : Nuisance) : ℝ :=
  mix.probability.covariance
    (fun c => inner ℝ x (mix.pattern c))
    (fun c => inner ℝ x (mix.pattern c))

/-- All ordered pair differences, equipped with the Euclidean norm. -/
def pairDifferenceAnalysis (mix : PatternMixture Cell Nuisance) :
    Nuisance →L[ℝ] EuclideanSpace ℝ (Cell × Cell) :=
  (EuclideanSpace.equiv (Cell × Cell) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun ij : Cell × Cell =>
      (innerSL ℝ) (mix.pattern ij.1 - mix.pattern ij.2))

theorem pairDifferenceAnalysis_apply
    (mix : PatternMixture Cell Nuisance) (x : Nuisance) (ij : Cell × Cell) :
    (mix.pairDifferenceAnalysis x : (Cell × Cell) → ℝ) ij =
      inner ℝ (mix.pattern ij.1 - mix.pattern ij.2) x := by
  rfl

theorem pairDifferenceAnalysis_norm_sq
    (mix : PatternMixture Cell Nuisance) (x : Nuisance) :
    ‖mix.pairDifferenceAnalysis x‖ ^ 2 =
      ∑ ij : Cell × Cell,
        (inner ℝ x (mix.pattern ij.1 - mix.pattern ij.2)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  apply Finset.sum_congr rfl
  intro ij _
  rw [mix.pairDifferenceAnalysis_apply x ij, real_inner_comm]

/-- A directly checkable affine-spanning certificate.  It asks for explicit
linear reconstruction from the complete list of pairwise pattern
differences; it does not assume a covariance inequality. -/
structure AffineSpanningCertificate (mix : PatternMixture Cell Nuisance) where
  reconstruct : EuclideanSpace ℝ (Cell × Cell) →L[ℝ] Nuisance
  left_inverse : reconstruct.comp mix.pairDifferenceAnalysis =
    ContinuousLinearMap.id ℝ Nuisance

namespace AffineSpanningCertificate

variable {mix : PatternMixture Cell Nuisance}

/-- A positive explicit reconstruction constant. -/
def bound (cert : AffineSpanningCertificate mix) : ℝ :=
  max 1 ‖cert.reconstruct‖

theorem bound_pos (cert : AffineSpanningCertificate mix) : 0 < cert.bound := by
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem bound_ne_zero (cert : AffineSpanningCertificate mix) : cert.bound ≠ 0 :=
  ne_of_gt cert.bound_pos

theorem norm_le_bound_mul_analysis
    (cert : AffineSpanningCertificate mix) (x : Nuisance) :
    ‖x‖ ≤ cert.bound * ‖mix.pairDifferenceAnalysis x‖ := by
  have hleft := congrArg (fun T : Nuisance →L[ℝ] Nuisance => T x) cert.left_inverse
  have hreconstruct : cert.reconstruct (mix.pairDifferenceAnalysis x) = x := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hleft
  calc
    ‖x‖ = ‖cert.reconstruct (mix.pairDifferenceAnalysis x)‖ := by rw [hreconstruct]
    _ ≤ ‖cert.reconstruct‖ * ‖mix.pairDifferenceAnalysis x‖ :=
      cert.reconstruct.le_opNorm _
    _ ≤ cert.bound * ‖mix.pairDifferenceAnalysis x‖ := by
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

theorem norm_sq_le_bound_sq_mul_analysis_sq
    (cert : AffineSpanningCertificate mix) (x : Nuisance) :
    ‖x‖ ^ 2 ≤ cert.bound ^ 2 * ‖mix.pairDifferenceAnalysis x‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg x)
    (cert.norm_le_bound_mul_analysis x) 2
  calc
    ‖x‖ ^ 2 ≤ (cert.bound * ‖mix.pairDifferenceAnalysis x‖) ^ 2 := h
    _ = cert.bound ^ 2 * ‖mix.pairDifferenceAnalysis x‖ ^ 2 := by ring

end AffineSpanningCertificate

theorem weightedVariance_pairDifference
    (w X : Cell → ℝ) (hsum : ∑ c, w c = 1) :
    (∑ c, w c * X c ^ 2) - (∑ c, w c * X c) ^ 2 =
      (1 / 2 : ℝ) *
        ∑ i, ∑ j, w i * w j * (X i - X j) ^ 2 := by
  have hA : (∑ i, ∑ j, w i * w j * X i ^ 2) = ∑ i, w i * X i ^ 2 := by
    calc
      (∑ i, ∑ j, w i * w j * X i ^ 2)
          = ∑ i, (w i * X i ^ 2) * ∑ j, w j := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = ∑ i, w i * X i ^ 2 := by rw [hsum]; simp
  have hB : (∑ i, ∑ j, w i * w j * X j ^ 2) = ∑ j, w j * X j ^ 2 := by
    rw [Finset.sum_comm]
    calc
      (∑ j, ∑ i, w i * w j * X j ^ 2)
          = ∑ j, (w j * X j ^ 2) * ∑ i, w i := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = ∑ j, w j * X j ^ 2 := by rw [hsum]; simp
  have hC : (∑ i, ∑ j, w i * w j * (X i * X j)) =
      (∑ i, w i * X i) ^ 2 := by
    calc
      (∑ i, ∑ j, w i * w j * (X i * X j))
          = (∑ i, w i * X i) * ∑ j, w j * X j := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = (∑ i, w i * X i) ^ 2 := by ring
  calc
    (∑ i, w i * X i ^ 2) - (∑ i, w i * X i) ^ 2
        = (1 / 2 : ℝ) * ((∑ i, w i * X i ^ 2) +
            (∑ j, w j * X j ^ 2) - 2 * (∑ i, w i * X i) ^ 2) := by ring
    _ = (1 / 2 : ℝ) * ((∑ i, ∑ j, w i * w j * X i ^ 2) +
          (∑ i, ∑ j, w i * w j * X j ^ 2) -
          2 * (∑ i, ∑ j, w i * w j * (X i * X j))) := by rw [hA, hB, hC]
    _ = (1 / 2 : ℝ) * ∑ i, ∑ j, w i * w j * (X i - X j) ^ 2 := by
      congr 1
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem covarianceForm_pairDifference
    (mix : PatternMixture Cell Nuisance) (x : Nuisance) :
    mix.covarianceForm x =
      (1 / 2 : ℝ) * ∑ i, ∑ j, mix.weight i * mix.weight j *
        (inner ℝ x (mix.pattern i - mix.pattern j)) ^ 2 := by
  simp only [covarianceForm, probability, FiniteProbability.covariance,
    FiniteProbability.expect]
  simpa only [pow_two, inner_sub_right] using
    (weightedVariance_pairDifference
      mix.weight (fun c => inner ℝ x (mix.pattern c)) mix.weight_sum)

/-- Explicit gap supplied by a positive cell-mass lower bound and an affine
spanning certificate. -/
def baselineGap (lambda : ℝ) {mix : PatternMixture Cell Nuisance}
    (cert : AffineSpanningCertificate mix) : ℝ :=
  lambda ^ 2 / (2 * cert.bound ^ 2)

theorem baselineGap_pos (lambda : ℝ) (hlambda : 0 < lambda)
    {mix : PatternMixture Cell Nuisance}
    (cert : AffineSpanningCertificate mix) :
    0 < baselineGap lambda cert := by
  exact div_pos (sq_pos_of_pos hlambda)
    (mul_pos (by norm_num) (sq_pos_of_pos cert.bound_pos))

/-- Uniform positive spectral gap for the actual finite baseline mixture.
No convergence of the weights is used. -/
theorem covarianceForm_uniform_gap
    (mix : PatternMixture Cell Nuisance)
    (cert : AffineSpanningCertificate mix)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hweight : ∀ c, lambda ≤ mix.weight c)
    (x : Nuisance) :
    baselineGap lambda cert * ‖x‖ ^ 2 ≤ mix.covarianceForm x := by
  have hpair : lambda ^ 2 *
      (∑ i, ∑ j, (inner ℝ x (mix.pattern i - mix.pattern j)) ^ 2) ≤
      ∑ i, ∑ j, mix.weight i * mix.weight j *
        (inner ℝ x (mix.pattern i - mix.pattern j)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hprod : lambda ^ 2 ≤ mix.weight i * mix.weight j := by
      nlinarith [hweight i, hweight j, mix.weight_nonneg i,
        mix.weight_nonneg j, le_of_lt hlambda]
    exact mul_le_mul_of_nonneg_right hprod (sq_nonneg _)
  have hvariance : (lambda ^ 2 / 2) *
      ‖mix.pairDifferenceAnalysis x‖ ^ 2 ≤ mix.covarianceForm x := by
    rw [mix.covarianceForm_pairDifference x,
      mix.pairDifferenceAnalysis_norm_sq x]
    calc
      (lambda ^ 2 / 2) *
          (∑ ij : Cell × Cell,
            (inner ℝ x (mix.pattern ij.1 - mix.pattern ij.2)) ^ 2)
          = (1 / 2 : ℝ) * (lambda ^ 2 *
              ∑ i, ∑ j,
                (inner ℝ x (mix.pattern i - mix.pattern j)) ^ 2) := by
              simp only [Fintype.sum_prod_type]
              ring
      _ ≤ (1 / 2 : ℝ) * ∑ i, ∑ j, mix.weight i * mix.weight j *
          (inner ℝ x (mix.pattern i - mix.pattern j)) ^ 2 := by
            exact mul_le_mul_of_nonneg_left hpair (by norm_num)
  calc
    baselineGap lambda cert * ‖x‖ ^ 2
        ≤ baselineGap lambda cert *
            (cert.bound ^ 2 * ‖mix.pairDifferenceAnalysis x‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_left
            (cert.norm_sq_le_bound_sq_mul_analysis_sq x)
            (le_of_lt (baselineGap_pos lambda hlambda cert))
    _ = (lambda ^ 2 / 2) * ‖mix.pairDifferenceAnalysis x‖ ^ 2 := by
          simp only [baselineGap]
          field_simp [cert.bound_ne_zero]
    _ ≤ mix.covarianceForm x := hvariance

/-- Concrete certificate that a coarse pattern vector is the conditional
mean of an actual finer finite distribution on each cell. -/
structure CoarseMeanCertificate
    {Fine : Type*} [Fintype Fine]
    [DecidableEq Cell]
    (fine : PatternMixture Fine Nuisance)
    (coarse : PatternMixture Cell Nuisance) where
  cell : Fine → Cell
  cell_mass : ∀ c,
    ∑ f ∈ (Finset.univ : Finset Fine) with cell f = c, fine.weight f =
      coarse.weight c
  cell_firstMoment : ∀ c x,
    ∑ f ∈ (Finset.univ : Finset Fine) with cell f = c,
      fine.weight f * inner ℝ x (fine.pattern f) =
        coarse.weight c * inner ℝ x (coarse.pattern c)

namespace CoarseMeanCertificate

variable {Fine : Type*} [Fintype Fine]
  [DecidableEq Cell]
  {fine : PatternMixture Fine Nuisance}
  {coarse : PatternMixture Cell Nuisance}

theorem global_firstMoment (cert : CoarseMeanCertificate fine coarse)
    (x : Nuisance) :
    ∑ f, fine.weight f * inner ℝ x (fine.pattern f) =
      ∑ c, coarse.weight c * inner ℝ x (coarse.pattern c) := by
  classical
  rw [← Finset.sum_fiberwise (Finset.univ : Finset Fine) cert.cell
    (fun f => fine.weight f * inner ℝ x (fine.pattern f))]
  apply Finset.sum_congr rfl
  intro c _
  exact cert.cell_firstMoment c x

theorem global_cellPatternSq (cert : CoarseMeanCertificate fine coarse)
    (x : Nuisance) :
    ∑ f, fine.weight f *
        (inner ℝ x (coarse.pattern (cert.cell f))) ^ 2 =
      ∑ c, coarse.weight c * (inner ℝ x (coarse.pattern c)) ^ 2 := by
  classical
  rw [← Finset.sum_fiberwise (Finset.univ : Finset Fine) cert.cell
    (fun f => fine.weight f *
      (inner ℝ x (coarse.pattern (cert.cell f))) ^ 2)]
  apply Finset.sum_congr rfl
  intro c _
  calc
    (∑ f ∈ (Finset.univ : Finset Fine) with cert.cell f = c,
        fine.weight f * (inner ℝ x (coarse.pattern (cert.cell f))) ^ 2)
        = (∑ f ∈ (Finset.univ : Finset Fine) with cert.cell f = c,
            fine.weight f) * (inner ℝ x (coarse.pattern c)) ^ 2 := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro f hf
              rw [(Finset.mem_filter.mp hf).2]
    _ = coarse.weight c * (inner ℝ x (coarse.pattern c)) ^ 2 := by
          rw [cert.cell_mass c]

theorem global_crossMoment (cert : CoarseMeanCertificate fine coarse)
    (x : Nuisance) :
    ∑ f, fine.weight f * inner ℝ x (fine.pattern f) *
        inner ℝ x (coarse.pattern (cert.cell f)) =
      ∑ c, coarse.weight c * (inner ℝ x (coarse.pattern c)) ^ 2 := by
  classical
  rw [← Finset.sum_fiberwise (Finset.univ : Finset Fine) cert.cell
    (fun f => fine.weight f * inner ℝ x (fine.pattern f) *
      inner ℝ x (coarse.pattern (cert.cell f)))]
  apply Finset.sum_congr rfl
  intro c _
  calc
    (∑ f ∈ (Finset.univ : Finset Fine) with cert.cell f = c,
      fine.weight f * inner ℝ x (fine.pattern f) *
        inner ℝ x (coarse.pattern (cert.cell f)))
        = (∑ f ∈ (Finset.univ : Finset Fine) with cert.cell f = c,
            fine.weight f * inner ℝ x (fine.pattern f)) *
              inner ℝ x (coarse.pattern c) := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro f hf
                rw [(Finset.mem_filter.mp hf).2]
    _ = coarse.weight c * (inner ℝ x (coarse.pattern c)) ^ 2 := by
          rw [cert.cell_firstMoment c x]
          ring

/-- Exact finite law-of-total-variance identity. -/
theorem covarianceForm_decomposition
    (cert : CoarseMeanCertificate fine coarse) (x : Nuisance) :
    fine.covarianceForm x = coarse.covarianceForm x +
      ∑ f, fine.weight f *
        (inner ℝ x (fine.pattern f) -
          inner ℝ x (coarse.pattern (cert.cell f))) ^ 2 := by
  have hfirst := cert.global_firstMoment x
  have hcellSq := cert.global_cellPatternSq x
  have hcross := cert.global_crossMoment x
  simp only [covarianceForm, probability, FiniteProbability.covariance,
    FiniteProbability.expect]
  rw [show (∑ f, fine.weight f *
      (inner ℝ x (fine.pattern f) * inner ℝ x (fine.pattern f))) =
      ∑ f, fine.weight f * (inner ℝ x (fine.pattern f)) ^ 2 by
        apply Finset.sum_congr rfl
        intro f _
        ring]
  rw [show (∑ c, coarse.weight c *
      (inner ℝ x (coarse.pattern c) * inner ℝ x (coarse.pattern c))) =
      ∑ c, coarse.weight c * (inner ℝ x (coarse.pattern c)) ^ 2 by
        apply Finset.sum_congr rfl
        intro c _
        ring]
  have hwithin : (∑ f, fine.weight f *
      (inner ℝ x (fine.pattern f) -
        inner ℝ x (coarse.pattern (cert.cell f))) ^ 2) =
      (∑ f, fine.weight f * (inner ℝ x (fine.pattern f)) ^ 2) -
        2 * (∑ f, fine.weight f * inner ℝ x (fine.pattern f) *
          inner ℝ x (coarse.pattern (cert.cell f))) +
        (∑ f, fine.weight f *
          (inner ℝ x (coarse.pattern (cert.cell f))) ^ 2) := by
    calc
      (∑ f, fine.weight f *
          (inner ℝ x (fine.pattern f) -
            inner ℝ x (coarse.pattern (cert.cell f))) ^ 2)
          = ∑ f, (fine.weight f * (inner ℝ x (fine.pattern f)) ^ 2 -
              2 * (fine.weight f * inner ℝ x (fine.pattern f) *
                inner ℝ x (coarse.pattern (cert.cell f))) +
              fine.weight f *
                (inner ℝ x (coarse.pattern (cert.cell f))) ^ 2) := by
                  apply Finset.sum_congr rfl
                  intro f _
                  ring
      _ = (∑ f, fine.weight f * (inner ℝ x (fine.pattern f)) ^ 2) -
          (∑ f, 2 * (fine.weight f * inner ℝ x (fine.pattern f) *
            inner ℝ x (coarse.pattern (cert.cell f)))) +
          (∑ f, fine.weight f *
            (inner ℝ x (coarse.pattern (cert.cell f))) ^ 2) := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (∑ f, fine.weight f * (inner ℝ x (fine.pattern f)) ^ 2) -
          2 * (∑ f, fine.weight f * inner ℝ x (fine.pattern f) *
            inner ℝ x (coarse.pattern (cert.cell f))) +
          (∑ f, fine.weight f *
            (inner ℝ x (coarse.pattern (cert.cell f))) ^ 2) := by
              rw [Finset.mul_sum]
  rw [hwithin, hfirst, hcellSq, hcross]
  ring

theorem coarse_covarianceForm_le_fine
    (cert : CoarseMeanCertificate fine coarse) (x : Nuisance) :
    coarse.covarianceForm x ≤ fine.covarianceForm x := by
  rw [cert.covarianceForm_decomposition x]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun f _ =>
    mul_nonneg (fine.weight_nonneg f) (sq_nonneg _))

end CoarseMeanCertificate

/-- The actual fine finite law inherits the explicit coarse-pattern gap. -/
theorem covarianceForm_uniform_gap_of_coarsening
    {Fine : Type*} [Fintype Fine]
    [DecidableEq Cell]
    (fine : PatternMixture Fine Nuisance)
    (coarse : PatternMixture Cell Nuisance)
    (coarseMean : CoarseMeanCertificate fine coarse)
    (cert : AffineSpanningCertificate coarse)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hweight : ∀ c, lambda ≤ coarse.weight c)
    (x : Nuisance) :
    baselineGap lambda cert * ‖x‖ ^ 2 ≤ fine.covarianceForm x := by
  exact (coarse.covarianceForm_uniform_gap cert lambda hlambda hweight x).trans
    (coarseMean.coarse_covarianceForm_le_fine x)

/-- Reweight a fixed finite list of nuisance patterns. -/
def reweight (mix : PatternMixture Cell Nuisance) (newWeight : Cell → ℝ)
    (h_nonneg : ∀ c, 0 ≤ newWeight c) (h_sum : ∑ c, newWeight c = 1) :
    PatternMixture Cell Nuisance where
  weight := newWeight
  weight_nonneg := h_nonneg
  weight_sum := h_sum
  pattern := mix.pattern

/-- `ℓ¹` distance between a new weight vector and the actual finite
baseline weights. -/
def weightL1Distance (mix : PatternMixture Cell Nuisance)
    (newWeight : Cell → ℝ) : ℝ :=
  ∑ c, |newWeight c - mix.weight c|

theorem productWeightL1_le_two
    (w v : Cell → ℝ)
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ c, 0 ≤ v c)
    (hwsum : ∑ c, w c = 1) (hvsum : ∑ c, v c = 1) :
    ∑ i, ∑ j, |v i * v j - w i * w j| ≤
      2 * ∑ i, |v i - w i| := by
  have hpoint : ∀ i j, |v i * v j - w i * w j| ≤
      |v i - w i| * v j + w i * |v j - w j| := by
    intro i j
    calc
      |v i * v j - w i * w j|
          = |(v i - w i) * v j + w i * (v j - w j)| := by
              congr 1
              ring
      _ ≤ |(v i - w i) * v j| + |w i * (v j - w j)| := abs_add_le _ _
      _ = |v i - w i| * v j + w i * |v j - w j| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (hv j), abs_of_nonneg (hw i)]
  calc
    (∑ i, ∑ j, |v i * v j - w i * w j|)
        ≤ ∑ i, ∑ j, (|v i - w i| * v j + w i * |v j - w j|) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          exact hpoint i j
    _ = 2 * ∑ i, |v i - w i| := by
      simp_rw [Finset.sum_add_distrib]
      calc
        (∑ i, ∑ j, |v i - w i| * v j) +
            (∑ i, ∑ j, w i * |v j - w j|)
            = (∑ i, |v i - w i| * (∑ j, v j)) +
                (∑ i, w i * (∑ j, |v j - w j|)) := by
                  congr 1
                  · apply Finset.sum_congr rfl
                    intro i _
                    rw [Finset.mul_sum]
                  · apply Finset.sum_congr rfl
                    intro i _
                    rw [Finset.mul_sum]
        _ = 2 * ∑ i, |v i - w i| := by
          rw [hvsum]
          simp only [mul_one]
          rw [← Finset.sum_mul, hwsum]
          ring

theorem projectedPairDifference_sq_le
    (mix : PatternMixture Cell Nuisance)
    (diameter : ℝ)
    (hdiam : ∀ i j, ‖mix.pattern i - mix.pattern j‖ ≤ diameter)
    (x : Nuisance) (i j : Cell) :
    (inner ℝ x (mix.pattern i - mix.pattern j)) ^ 2 ≤
      diameter ^ 2 * ‖x‖ ^ 2 := by
  have habs : |inner ℝ x (mix.pattern i - mix.pattern j)| ≤ ‖x‖ * diameter := by
    exact (abs_real_inner_le_norm x (mix.pattern i - mix.pattern j)).trans
      (mul_le_mul_of_nonneg_left (hdiam i j) (norm_nonneg x))
  have hsq := pow_le_pow_left₀ (abs_nonneg (inner ℝ x
    (mix.pattern i - mix.pattern j))) habs 2
  calc
    (inner ℝ x (mix.pattern i - mix.pattern j)) ^ 2
        ≤ (‖x‖ * diameter) ^ 2 := by simpa only [sq_abs] using hsq
    _ = diameter ^ 2 * ‖x‖ ^ 2 := by ring

/-- An `ℓ¹` perturbation of the finite mixture weights perturbs every
covariance quadratic form by at most `ε * diameter²`.  This is the finite
operator comparison used after the actual `Γ_{0,n}` baseline is fixed. -/
theorem abs_covarianceForm_reweight_sub_le
    (mix : PatternMixture Cell Nuisance)
    (newWeight : Cell → ℝ)
    (hnew_nonneg : ∀ c, 0 ≤ newWeight c)
    (hnew_sum : ∑ c, newWeight c = 1)
    (diameter epsilon : ℝ)
    (hdiam : ∀ i j, ‖mix.pattern i - mix.pattern j‖ ≤ diameter)
    (hl1 : mix.weightL1Distance newWeight ≤ epsilon)
    (x : Nuisance) :
    |(mix.reweight newWeight hnew_nonneg hnew_sum).covarianceForm x -
        mix.covarianceForm x| ≤
      epsilon * diameter ^ 2 * ‖x‖ ^ 2 := by
  let tilted := mix.reweight newWeight hnew_nonneg hnew_sum
  let pairTerm : Cell → Cell → ℝ := fun i j =>
    (newWeight i * newWeight j - mix.weight i * mix.weight j) *
      (inner ℝ x (mix.pattern i - mix.pattern j)) ^ 2
  have hrewrite : tilted.covarianceForm x - mix.covarianceForm x =
      (1 / 2 : ℝ) * ∑ i, ∑ j, pairTerm i j := by
    rw [tilted.covarianceForm_pairDifference x,
      mix.covarianceForm_pairDifference x]
    simp only [tilted, reweight]
    calc
      (1 / 2 : ℝ) *
            (∑ i, ∑ j, newWeight i * newWeight j *
              (inner ℝ x (mix.pattern i - mix.pattern j)) ^ 2) -
          (1 / 2 : ℝ) *
            (∑ i, ∑ j, mix.weight i * mix.weight j *
              (inner ℝ x (mix.pattern i - mix.pattern j)) ^ 2)
          = (1 / 2 : ℝ) *
              ((∑ i, ∑ j, newWeight i * newWeight j *
                (inner ℝ x (mix.pattern i - mix.pattern j)) ^ 2) -
              (∑ i, ∑ j, mix.weight i * mix.weight j *
                (inner ℝ x (mix.pattern i - mix.pattern j)) ^ 2)) := by ring
      _ = (1 / 2 : ℝ) * ∑ i, ∑ j, pairTerm i j := by
        congr 1
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        simp only [pairTerm]
        ring
  have habssum : |∑ i, ∑ j, pairTerm i j| ≤
      ∑ i, ∑ j, |pairTerm i j| := by
    calc
      |∑ i, ∑ j, pairTerm i j| ≤ ∑ i, |∑ j, pairTerm i j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |pairTerm i j| := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.abs_sum_le_sum_abs _ _
  have hterms : (∑ i, ∑ j, |pairTerm i j|) ≤
      (∑ i, ∑ j,
        |newWeight i * newWeight j - mix.weight i * mix.weight j|) *
          (diameter ^ 2 * ‖x‖ ^ 2) := by
    calc
      (∑ i, ∑ j, |pairTerm i j|)
          ≤ ∑ i, ∑ j,
              |newWeight i * newWeight j - mix.weight i * mix.weight j| *
                (diameter ^ 2 * ‖x‖ ^ 2) := by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j _
            simp only [pairTerm, abs_mul, abs_sq]
            exact mul_le_mul_of_nonneg_left
              (mix.projectedPairDifference_sq_le diameter hdiam x i j)
              (abs_nonneg _)
      _ = (∑ i, ∑ j,
            |newWeight i * newWeight j - mix.weight i * mix.weight j|) *
          (diameter ^ 2 * ‖x‖ ^ 2) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
  have hproduct := productWeightL1_le_two mix.weight newWeight
    mix.weight_nonneg hnew_nonneg mix.weight_sum hnew_sum
  rw [hrewrite, abs_mul, abs_of_nonneg (by norm_num)]
  calc
    (1 / 2 : ℝ) * |∑ i, ∑ j, pairTerm i j|
        ≤ (1 / 2 : ℝ) * ∑ i, ∑ j, |pairTerm i j| := by
          exact mul_le_mul_of_nonneg_left habssum (by norm_num)
    _ ≤ (1 / 2 : ℝ) *
        ((∑ i, ∑ j,
          |newWeight i * newWeight j - mix.weight i * mix.weight j|) *
            (diameter ^ 2 * ‖x‖ ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hterms (by norm_num)
    _ ≤ (1 / 2 : ℝ) *
        ((2 * mix.weightL1Distance newWeight) *
          (diameter ^ 2 * ‖x‖ ^ 2)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hproduct
              (mul_nonneg (sq_nonneg diameter) (sq_nonneg ‖x‖)))
            (by norm_num)
    _ ≤ epsilon * diameter ^ 2 * ‖x‖ ^ 2 := by
      have hscale : 0 ≤ diameter ^ 2 * ‖x‖ ^ 2 :=
        mul_nonneg (sq_nonneg diameter) (sq_nonneg ‖x‖)
      calc
        (1 / 2 : ℝ) *
            ((2 * mix.weightL1Distance newWeight) *
              (diameter ^ 2 * ‖x‖ ^ 2))
            = mix.weightL1Distance newWeight *
                (diameter ^ 2 * ‖x‖ ^ 2) := by ring
        _ ≤ epsilon * (diameter ^ 2 * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hl1 hscale
        _ = epsilon * diameter ^ 2 * ‖x‖ ^ 2 := by ring

/-- If the `ℓ¹` tilt error is small compared with the explicit finite
baseline gap, the tilted covariance retains half that gap. -/
theorem covarianceForm_reweight_half_gap
    (mix : PatternMixture Cell Nuisance)
    (cert : AffineSpanningCertificate mix)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hweight : ∀ c, lambda ≤ mix.weight c)
    (newWeight : Cell → ℝ)
    (hnew_nonneg : ∀ c, 0 ≤ newWeight c)
    (hnew_sum : ∑ c, newWeight c = 1)
    (diameter epsilon : ℝ)
    (hdiam : ∀ i j, ‖mix.pattern i - mix.pattern j‖ ≤ diameter)
    (hl1 : mix.weightL1Distance newWeight ≤ epsilon)
    (hsmall : epsilon * diameter ^ 2 ≤ baselineGap lambda cert / 2)
    (x : Nuisance) :
    (baselineGap lambda cert / 2) * ‖x‖ ^ 2 ≤
      (mix.reweight newWeight hnew_nonneg hnew_sum).covarianceForm x := by
  let tilted := mix.reweight newWeight hnew_nonneg hnew_sum
  have hbase := mix.covarianceForm_uniform_gap cert lambda hlambda hweight x
  have hperturb := mix.abs_covarianceForm_reweight_sub_le newWeight
    hnew_nonneg hnew_sum diameter epsilon hdiam hl1 x
  have hdrop : mix.covarianceForm x - tilted.covarianceForm x ≤
      epsilon * diameter ^ 2 * ‖x‖ ^ 2 := by
    calc
      mix.covarianceForm x - tilted.covarianceForm x
          ≤ |mix.covarianceForm x - tilted.covarianceForm x| := le_abs_self _
      _ = |tilted.covarianceForm x - mix.covarianceForm x| := abs_sub_comm _ _
      _ ≤ epsilon * diameter ^ 2 * ‖x‖ ^ 2 := hperturb
  have hscaledSmall : epsilon * diameter ^ 2 * ‖x‖ ^ 2 ≤
      (baselineGap lambda cert / 2) * ‖x‖ ^ 2 := by
    exact mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖x‖)
  dsimp only [tilted] at hdrop ⊢
  nlinarith

/-- Full finite-`n` version: an actual fine baseline law obtains its gap from
explicit coarse conditional means, and an `ℓ¹`-small tilt of the actual fine
weights preserves half of that gap. -/
theorem actualCovarianceForm_reweight_half_gap_of_coarsening
    {Fine : Type*} [Fintype Fine] [DecidableEq Cell]
    (fine : PatternMixture Fine Nuisance)
    (coarse : PatternMixture Cell Nuisance)
    (coarseMean : CoarseMeanCertificate fine coarse)
    (cert : AffineSpanningCertificate coarse)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hweight : ∀ c, lambda ≤ coarse.weight c)
    (newWeight : Fine → ℝ)
    (hnew_nonneg : ∀ f, 0 ≤ newWeight f)
    (hnew_sum : ∑ f, newWeight f = 1)
    (diameter epsilon : ℝ)
    (hdiam : ∀ i j, ‖fine.pattern i - fine.pattern j‖ ≤ diameter)
    (hl1 : fine.weightL1Distance newWeight ≤ epsilon)
    (hsmall : epsilon * diameter ^ 2 ≤ baselineGap lambda cert / 2)
    (x : Nuisance) :
    (baselineGap lambda cert / 2) * ‖x‖ ^ 2 ≤
      (fine.reweight newWeight hnew_nonneg hnew_sum).covarianceForm x := by
  let tilted := fine.reweight newWeight hnew_nonneg hnew_sum
  have hbase := covarianceForm_uniform_gap_of_coarsening fine coarse coarseMean
    cert lambda hlambda hweight x
  have hperturb := fine.abs_covarianceForm_reweight_sub_le newWeight
    hnew_nonneg hnew_sum diameter epsilon hdiam hl1 x
  have hdrop : fine.covarianceForm x - tilted.covarianceForm x ≤
      epsilon * diameter ^ 2 * ‖x‖ ^ 2 := by
    calc
      fine.covarianceForm x - tilted.covarianceForm x
          ≤ |fine.covarianceForm x - tilted.covarianceForm x| := le_abs_self _
      _ = |tilted.covarianceForm x - fine.covarianceForm x| := abs_sub_comm _ _
      _ ≤ epsilon * diameter ^ 2 * ‖x‖ ^ 2 := hperturb
  have hscaledSmall : epsilon * diameter ^ 2 * ‖x‖ ^ 2 ≤
      (baselineGap lambda cert / 2) * ‖x‖ ^ 2 := by
    exact mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖x‖)
  dsimp only [tilted] at hdrop ⊢
  nlinarith

end PatternMixture

end

end Erdos390.Full
