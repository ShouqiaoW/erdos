import Erdos390.Full.PaperActualFullBandIdentification
import Erdos390.Full.PaperNuisancePrimeLogRows

/-!
# Attaching reciprocal nuisance marked rows to the actual Schur operator

This file performs the finite summations that turn a coordinatewise bound
`|Cov(Z_c,v_p)| <= Cmarked / p` into the two covariance-vector bounds used
by the exact Schur perturbation theorem.  The analytic rate remains a
literal hypothesis; in particular the proof does not replace the required
`O(1/(pL))` estimate by a merely bounded `O(1/p)` row.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Summing a reciprocal marked-prime estimate over one literal band gives
exactly its harmonic mass. -/
theorem abs_covariance_nuisance_bandScore_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) (c : NuisanceCoord B.HeadIndex) (i : Band)
    {Cmarked : ℝ}
    (hmarked : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m c) (B.bandScore i)| ≤
        Cmarked * B.harmonicMass i := by
  let mu := B.tiltedLaw xi
  let Z : B.sampleData.Sample → ℝ :=
    fun m ↦ B.nuisanceStatistic m c
  have hsum :
      mu.covariance Z (B.bandScore i) =
        ∑ p ∈ B.partition.data.fiber i,
          mu.covariance Z
            (fun m ↦ ArithmeticModel.valuation p.1
              (B.sampleData.value m)) := by
    unfold bandScore
    rw [mu.covariance_sum_right]
  change |mu.covariance Z (B.bandScore i)| ≤ _
  rw [hsum]
  calc
    |∑ p ∈ B.partition.data.fiber i,
        mu.covariance Z
          (fun m ↦ ArithmeticModel.valuation p.1
            (B.sampleData.value m))| ≤
        ∑ p ∈ B.partition.data.fiber i,
          |mu.covariance Z
            (fun m ↦ ArithmeticModel.valuation p.1
              (B.sampleData.value m))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ B.partition.data.fiber i,
        Cmarked * (1 / (p.1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hmarked p
    _ = Cmarked * B.harmonicMass i := by
      change (∑ p ∈ B.partition.data.fiber i,
        Cmarked * (1 / (p.1 : ℝ))) =
          Cmarked * ∑ p ∈ B.partition.data.fiber i,
            (1 / (p.1 : ℝ))
      rw [Finset.mul_sum]

/-- Euclidean vector form of the preceding one-band summation. -/
theorem nuisanceCovarianceVector_bandScore_norm_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) (i : Band)
    {Cmarked : ℝ} (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked * B.harmonicMass i) := by
  have hK : 0 ≤ Cmarked * B.harmonicMass i :=
    mul_nonneg hCmarked (B.harmonicMass_pos i).le
  exact B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
    xi (B.bandScore i) hK (fun c ↦
      B.abs_covariance_nuisance_bandScore_le_of_marked
        xi c i (fun p ↦ hmarked c p))

/-- The same reciprocal marked family controls the nuisance covariance of
every sharp-gauge band score.  The finite factor is the exact arithmetic
first moment `sum_i H_i alpha_i`; no continuum replacement is made. -/
theorem abs_covariance_nuisance_scaledBandRegression_le_of_marked
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (c : NuisanceCoord B.HeadIndex)
    {Cmarked : ℝ}
    (hmarked : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (q : SharpGaugeSpace B.partition.mass B.partition.center) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m c)
      (B.bandRegressionScore
        (scaleGaugeLinearEquiv B.partition.mass B.partition.center
          (B.partition.center_ne_zero B.n_gt_one) q))| ≤
      (Cmarked *
        (∑ j : Band, B.harmonicMass j * B.bandCenter j)) * ‖q‖ := by
  let mu := B.tiltedLaw xi
  let Z : B.sampleData.Sample → ℝ :=
    fun m ↦ B.nuisanceStatistic m c
  let S := scaleGaugeLinearEquiv B.partition.mass B.partition.center
    (B.partition.center_ne_zero B.n_gt_one)
  have hsum :
      mu.covariance Z (B.bandRegressionScore (S q)) =
        ∑ j : Band, (S q).1 j *
          mu.covariance Z (B.bandScore j) := by
    unfold bandRegressionScore
    rw [show (fun m ↦ ∑ j : Band, (S q).1 j * B.bandScore j m) =
      fun m ↦ ∑ j ∈ (Finset.univ : Finset Band),
        (S q).1 j * B.bandScore j m by simp]
    rw [mu.covariance_sum_right]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mu.covariance_smul_right]
  have hcoeff (j : Band) : |(S q).1 j| ≤ B.bandCenter j * ‖q‖ := by
    rw [show (S q).1 j = B.bandCenter j * q.1 j by rfl,
      abs_mul, abs_of_pos (B.bandCenter_pos j)]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm q.1 j)
      (B.bandCenter_pos j).le
  change |mu.covariance Z (B.bandRegressionScore (S q))| ≤ _
  rw [hsum]
  calc
    |∑ j : Band, (S q).1 j * mu.covariance Z (B.bandScore j)| ≤
        ∑ j : Band, |(S q).1 j *
          mu.covariance Z (B.bandScore j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Band, (B.bandCenter j * ‖q‖) *
        (Cmarked * B.harmonicMass j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul (hcoeff j)
        (B.abs_covariance_nuisance_bandScore_le_of_marked
          xi c j (fun p ↦ hmarked p))
        (abs_nonneg _)
        (mul_nonneg (B.bandCenter_pos j).le (norm_nonneg q))
    _ = (Cmarked *
        (∑ j : Band, B.harmonicMass j * B.bandCenter j)) * ‖q‖ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Euclidean vector version of the sharp-gauge source estimate. -/
theorem nuisanceCovarianceVector_scaledBandRegression_norm_le_of_marked
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace)
    {Cmarked : ℝ} (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (q : SharpGaugeSpace B.partition.mass B.partition.center) :
    ‖B.nuisanceCovarianceVector xi
      (B.bandRegressionScore
        (scaleGaugeLinearEquiv B.partition.mass B.partition.center
          (B.partition.center_ne_zero B.n_gt_one) q))‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        ((Cmarked *
          (∑ j : Band, B.harmonicMass j * B.bandCenter j)) * ‖q‖) := by
  have hmoment : 0 ≤ ∑ j : Band,
      B.harmonicMass j * B.bandCenter j := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (B.harmonicMass_pos j).le (B.bandCenter_pos j).le
  have hK : 0 ≤ (Cmarked *
      (∑ j : Band, B.harmonicMass j * B.bandCenter j)) * ‖q‖ :=
    mul_nonneg (mul_nonneg hCmarked hmoment) (norm_nonneg q)
  exact B.nuisanceCovarianceVector_norm_le_sqrt_card_mul xi _ hK
    (fun c ↦ B.abs_covariance_nuisance_scaledBandRegression_le_of_marked
      xi c (fun p ↦ hmarked c p) q)

/-- The exact Schur perturbation rate supplied by a reciprocal marked family.
The explicit `1 / amin` records the moving-low-cell loss. -/
def nuisanceMarkedSchurRate (Cmarked gamma amin : ℝ) : ℝ :=
  let droot := Real.sqrt
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let moment := ∑ j : Band, B.harmonicMass j * B.bandCenter j
  (((droot * (Cmarked * moment)) / gamma) *
      (droot * Cmarked)) / amin

/-- A coordinatewise reciprocal nuisance marked row closes the finite Schur
operator perturbation with the completely explicit rate above.  Therefore an
application with `Cmarked = O(1/L)` and `amin` of order `1/log L` obtains the
required `O(log L/L^2)` sharp error, whereas an `O(1)` marked constant does
not suffice. -/
theorem actualSchurProjectedCLM_sub_full_le_of_marked
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    {Cmarked amin : ℝ} (hCmarked : 0 ≤ Cmarked) (hamin : 0 < amin)
    (hcenter : ∀ i : Band, amin ≤ B.bandCenter i)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (q : SharpGaugeSpace B.partition.mass B.partition.center) :
    ‖(B.actualSchurProjectedCLM xi hgamma hgap -
        B.actualFullProjectedCLM xi) q‖ ≤
      (2 * B.nuisanceMarkedSchurRate Cmarked gamma amin) * ‖q‖ := by
  let droot : ℝ := Real.sqrt
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let moment : ℝ := ∑ j : Band,
    B.harmonicMass j * B.bandCenter j
  let Csource : ℝ := droot * (Cmarked * moment)
  let Crow : ℝ := droot * Cmarked
  have hmoment : 0 ≤ moment := by
    dsimp only [moment]
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (B.harmonicMass_pos j).le (B.bandCenter_pos j).le
  have hdroot : 0 ≤ droot := by
    exact Real.sqrt_nonneg _
  have hCsource : 0 ≤ Csource :=
    mul_nonneg hdroot (mul_nonneg hCmarked hmoment)
  have hCrow : 0 ≤ Crow := mul_nonneg hdroot hCmarked
  have hsource : ∀ q' :
      SharpGaugeSpace B.partition.mass B.partition.center,
      ‖B.nuisanceCovarianceVector xi
          (B.bandRegressionScore
            (scaleGaugeLinearEquiv B.partition.mass B.partition.center
              (B.partition.center_ne_zero B.n_gt_one) q'))‖ ≤
        Csource * ‖q'‖ := by
    intro q'
    have h := B.nuisanceCovarianceVector_scaledBandRegression_norm_le_of_marked
      xi hCmarked hmarked q'
    simpa only [Csource, droot, moment, mul_assoc] using h
  have hband : ∀ i : Band,
      ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖ ≤
        Crow * B.harmonicMass i := by
    intro i
    have h := B.nuisanceCovarianceVector_bandScore_norm_le_of_marked
      xi i hCmarked hmarked
    simpa only [Crow, droot, mul_assoc] using h
  have h :=
    B.actualSchurProjectedCLM_sub_full_le_of_nuisanceCovarianceBounds
      xi hgamma hgap hCsource hCrow hamin hcenter hsource hband q
  simpa only [nuisanceMarkedSchurRate, Csource, Crow, droot, moment] using h

/-- Direct attachment of the paper's two `O(1/(pL))` analytic inputs: the
physical marked row and pairwise agreement of the exact-cell valuation
means.  All finite-mixture cancellation, band summation, Euclidean
conversion, sharp conjugation, and Schur algebra are conclusions. -/
theorem actualSchurProjectedCLM_sub_full_le_of_pairwiseCells
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    {Cscale Lscale amin : ℝ}
    (hCscale : 0 ≤ Cscale) (hLscale : 0 < Lscale) (hamin : 0 < amin)
    (hcenter : ∀ i : Band, amin ≤ B.bandCenter i)
    (hphysical : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m NuisanceCoord.physical)
          (fun m ↦ ArithmeticModel.valuation p.1
            (B.sampleData.value m))| ≤
        (Cscale / Lscale) * (1 / (p.1 : ℝ)))
    (hpair : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c c' : Cell Head),
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ ArithmeticModel.valuation p.1 (x : ℕ)) -
        ((B.guardedCellProbability c').exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c')).expect
          (fun x ↦ ArithmeticModel.valuation p.1 (x : ℕ))| ≤
        (Cscale / Lscale) * (1 / (p.1 : ℝ)))
    (q : SharpGaugeSpace B.partition.mass B.partition.center) :
    ‖(B.actualSchurProjectedCLM xi hgamma hgap -
        B.actualFullProjectedCLM xi) q‖ ≤
      (2 * B.nuisanceMarkedSchurRate
        (6 * Cscale / Lscale) gamma amin) * ‖q‖ := by
  have hCmarked : 0 ≤ 6 * Cscale / Lscale := by positivity
  have hmarked :=
    B.nuisanceMarkedRows_le_of_pairwise_cell_valuation_and_physical
      xi hCscale hLscale hphysical hpair
  exact B.actualSchurProjectedCLM_sub_full_le_of_marked
    xi hgamma hgap hCmarked hamin hcenter hmarked q

/-- Stable inverse for the literal nuisance-Schur operator, now consuming
only the already constructed full-valuation inverse and a coordinatewise
reciprocal nuisance marked family. -/
theorem exists_actualSchurProjectedEquiv_of_full_of_marked
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace)
    (fullEquiv :
      SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
        SharpGaugeSpace B.partition.mass B.partition.center)
    (hfull : ∀ q, fullEquiv q = B.actualFullProjectedCLM xi q)
    {gamma C Cmarked amin : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hC : 0 ≤ C) (hCmarked : 0 ≤ Cmarked) (hamin : 0 < amin)
    (hcenter : ∀ i : Band, amin ≤ B.bandCenter i)
    (hinv : ∀ v, ‖fullEquiv.symm v‖ ≤ C * ‖v‖)
    (hsmall : C *
      (2 * B.nuisanceMarkedSchurRate Cmarked gamma amin) < 1)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    ∃ schurEquiv :
      SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
        SharpGaugeSpace B.partition.mass B.partition.center,
      (∀ q, schurEquiv q =
        B.actualSchurProjectedCLM xi hgamma hgap q) ∧
      ∀ v, ‖schurEquiv.symm v‖ ≤
        (C / (1 - C *
          (2 * B.nuisanceMarkedSchurRate Cmarked gamma amin))) * ‖v‖ := by
  let A := B.actualFullProjectedCLM xi
  let Ainv : SharpGaugeSpace B.partition.mass B.partition.center →L[ℝ]
      SharpGaugeSpace B.partition.mass B.partition.center := fullEquiv.symm
  let delta : ℝ := 2 * B.nuisanceMarkedSchurRate Cmarked gamma amin
  let E := B.actualSchurProjectedCLM xi hgamma hgap - A
  have hleft (q : SharpGaugeSpace B.partition.mass B.partition.center) :
      Ainv (A q) = q := by
    dsimp only [Ainv, A]
    rw [← hfull q]
    exact fullEquiv.symm_apply_apply q
  have hinv' (v : SharpGaugeSpace B.partition.mass B.partition.center) :
      ‖Ainv v‖ ≤ C * ‖v‖ := hinv v
  have herror (q : SharpGaugeSpace B.partition.mass B.partition.center) :
      ‖E q‖ ≤ delta * ‖q‖ := by
    dsimp only [E, A, delta]
    exact B.actualSchurProjectedCLM_sub_full_le_of_marked
      xi hgamma hgap hCmarked hamin hcenter hmarked q
  have hsmall' : C * delta < 1 := by
    simpa only [delta] using hsmall
  let schurEquiv := StableInverse.perturbedEquiv
    A Ainv E C delta hC hsmall' hleft hinv' herror
  refine ⟨schurEquiv, ?_, ?_⟩
  · intro q
    rw [StableInverse.perturbedEquiv_apply]
    dsimp only [schurEquiv, E]
    simp only [add_sub_cancel]
  · intro v
    simpa only [delta] using StableInverse.perturbed_inverse_bound
      A Ainv E C delta hC hsmall' hleft hinv' herror v

/-- End-to-end raw-gauge form consumed by the paper's two-stage regression:
the sharp full inverse and the literal nuisance marked family construct an
actual linear equivalence whose map is exactly the finite Schur band matrix,
with the stated paper-sharp inverse bound. -/
theorem exists_actualBandSchurEquiv_of_full_of_marked
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace)
    (fullEquiv :
      SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
        SharpGaugeSpace B.partition.mass B.partition.center)
    (hfull : ∀ q, fullEquiv q = B.actualFullProjectedCLM xi q)
    {gamma C Cmarked amin : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hC : 0 ≤ C) (hCmarked : 0 ≤ Cmarked) (hamin : 0 < amin)
    (hcenter : ∀ i : Band, amin ≤ B.bandCenter i)
    (hinv : ∀ v, ‖fullEquiv.symm v‖ ≤ C * ‖v‖)
    (hsmall : C *
      (2 * B.nuisanceMarkedSchurRate Cmarked gamma amin) < 1)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    ∃ rawEquiv :
      RawGaugeSpace B.partition.mass B.partition.center ≃ₗ[ℝ]
        RawGaugeSpace B.partition.mass B.partition.center,
      (∀ b, rawEquiv b =
        B.actualBandSchurLinearMap xi hgamma hgap b) ∧
      ∀ u,
        paperSharpNorm B.partition.mass B.partition.center
            (B.partition.center_ne_zero B.n_gt_one) (rawEquiv.symm u) ≤
          (C / (1 - C *
            (2 * B.nuisanceMarkedSchurRate Cmarked gamma amin))) *
            paperSharpNorm B.partition.mass B.partition.center
              (B.partition.center_ne_zero B.n_gt_one) u := by
  obtain ⟨sharpEquiv, hsharp, hinvSharp⟩ :=
    B.exists_actualSchurProjectedEquiv_of_full_of_marked
      xi fullEquiv hfull hgamma hgap hC hCmarked hamin hcenter
      hinv hsmall hmarked
  let rawEquiv := B.rawBandEquivOfSharpEquiv sharpEquiv
  refine ⟨rawEquiv, ?_, ?_⟩
  · intro b
    exact B.rawBandEquivOfSharpEquiv_eq_actualBandSchurLinearMap
      xi hgamma hgap sharpEquiv hsharp b
  · intro u
    exact B.rawBandEquivOfSharpEquiv_symm_paperSharpNorm_le
      sharpEquiv hinvSharp u

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
