import Erdos390.Full.PaperActualTwoStageRegression

/-!
# Exact relative-error assembly for Lemma 8.6

This file combines the literal two-stage score with the already proved
prime-power row transfer.  Its hypotheses are only the two genuinely
analytic squarefree estimates and a norm bound for the finite nuisance
covariance vector.  The full-valuation Schur variance and marked-row bounds
are conclusions, with every relative error displayed at the `w^2` or `w/p`
scale.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport
open PrimePowerCovariance
open PaperPrimePowerRelativeQuadratic
open PaperPrimePowerLemma75

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Scalar triangle inequality used by the marked-row assembly. -/
private theorem markedRow_triangle
    {fitted full squarefree nuisance bpower bsquarefree bnuisance : ℝ}
    (hdecomp : fitted = full - nuisance)
    (hpower : |full - squarefree| ≤ bpower)
    (hsquarefree : |squarefree| ≤ bsquarefree)
    (hnuisance : |nuisance| ≤ bnuisance) :
    |fitted| ≤ bsquarefree + bpower + bnuisance := by
  have hfull : |full| ≤ |full - squarefree| + |squarefree| := by
    calc
      |full| = |(full - squarefree) + squarefree| := by ring_nf
      _ ≤ |full - squarefree| + |squarefree| := abs_add_le _ _
  calc
    |fitted| = |full - nuisance| := by rw [hdecomp]
    _ ≤ |full| + |nuisance| := abs_sub _ _
    _ ≤ (|full - squarefree| + |squarefree|) + |nuisance| :=
      add_le_add hfull (le_refl _)
    _ ≤ (bpower + bsquarefree) + bnuisance :=
      add_le_add (add_le_add hpower hsquarefree) hnuisance
    _ = bsquarefree + bpower + bnuisance := by ring

/-- Exact assembly of the relative full-valuation Schur-variance estimate.
The squarefree lower and upper estimates remain visible; the prime-power
term and the finite nuisance loss are derived rather than postulated. -/
theorem actualCompensatedScore_variance_bounds_of_squarefree
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w Cpow epsilon lower upper Cz : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w)
    (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon)
    (hCz : 0 ≤ Cz)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (h75 : PrimePowerTransferBounds (B.actualValuationLaw xi)
      B.sampleData.n B.sampleData.W Cpow epsilon)
    (hsfLower : lower * w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q))
    (hsfUpper :
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) ≤
          upper * w ^ 2)
    (hcovZ : ‖B.nuisanceCovarianceVector xi
      (B.postBandPrimeScore q)‖ ≤ Cz * w) :
    lower * w ^ 2 -
        (((1 + C) * (7 + C * K)) *
          (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon)) * w ^ 2 -
        (Cz ^ 2 / gamma) * w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.actualCompensatedScore xi hgamma hgap q)
        (B.actualCompensatedScore xi hgamma hgap q) ∧
    (B.tiltedLaw xi).covariance
        (B.actualCompensatedScore xi hgamma hgap q)
        (B.actualCompensatedScore xi hgamma hgap q) ≤
      upper * w ^ 2 +
        (((1 + C) * (7 + C * K)) *
          (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon)) * w ^ 2 := by
  let E : ℝ := ((1 + C) * (7 + C * K)) *
    (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon)
  let full : ℝ := (B.tiltedLaw xi).covariance
    (B.postBandPrimeScore q) (B.postBandPrimeScore q)
  let squarefree : ℝ := (B.tiltedLaw xi).covariance
    (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q)
  let loss : ℝ := inner ℝ
    (B.nuisanceCoefficientOfScore xi hgamma hgap
      (B.postBandPrimeScore q))
    (B.nuisanceCovarianceVector xi (B.postBandPrimeScore q))
  let residualVariance : ℝ := (B.tiltedLaw xi).covariance
    (B.actualCompensatedScore xi hgamma hgap q)
    (B.actualCompensatedScore xi hgamma hgap q)
  have hpow : |full - squarefree| ≤ E * w ^ 2 := by
    exact B.actual_primePower_relative_variance_bound xi q
      hC hK hw hCpow hepsilon hsharp hbandT hdevSup hdevL1 hdevL2 h75
  have hvar : residualVariance = full - loss := by
    exact B.nuisanceResidualScore_variance_identity
      xi hgamma hgap (B.postBandPrimeScore q)
  have hloss := B.nuisanceRegressionLoss_bounds
    xi hgamma hgap (B.postBandPrimeScore q)
  have hcovSq :
      ‖B.nuisanceCovarianceVector xi (B.postBandPrimeScore q)‖ ^ 2 ≤
        (Cz * w) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hCz hw)).2 hcovZ
  have hlossUpper : loss ≤ (Cz ^ 2 / gamma) * w ^ 2 := by
    calc
      loss ≤
          ‖B.nuisanceCovarianceVector xi (B.postBandPrimeScore q)‖ ^ 2 /
            gamma := hloss.2
      _ ≤ (Cz * w) ^ 2 / gamma :=
        div_le_div_of_nonneg_right hcovSq (le_of_lt hgamma)
      _ = (Cz ^ 2 / gamma) * w ^ 2 := by ring
  have hpowLower : -(E * w ^ 2) ≤ full - squarefree :=
    neg_le_of_abs_le hpow
  have hpowUpper : full - squarefree ≤ E * w ^ 2 :=
    le_of_abs_le hpow
  have hlossNonneg : 0 ≤ loss := hloss.1
  change lower * w ^ 2 ≤ squarefree at hsfLower
  change squarefree ≤ upper * w ^ 2 at hsfUpper
  change lower * w ^ 2 - E * w ^ 2 -
      (Cz ^ 2 / gamma) * w ^ 2 ≤ residualVariance ∧
    residualVariance ≤ upper * w ^ 2 + E * w ^ 2
  constructor
  · rw [hvar]
    linarith
  · rw [hvar]
    linarith

/-- Coordinatewise form of the preceding variance assembly.  This is the
form in which the physical and finitely many head rows arise from the marked
estimates.  The Euclidean nuisance-vector hypothesis is therefore not an
additional analytic contract; it follows with the displayed, fixed
square-root-of-dimension factor. -/
theorem actualCompensatedScore_variance_bounds_of_squarefree_and_coordinate_rows
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w Cpow epsilon lower upper Cz : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w)
    (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon)
    (hCz : 0 ≤ Cz)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (h75 : PrimePowerTransferBounds (B.actualValuationLaw xi)
      B.sampleData.n B.sampleData.W Cpow epsilon)
    (hsfLower : lower * w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q))
    (hsfUpper :
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) ≤
          upper * w ^ 2)
    (hcovCoord : ∀ c : NuisanceCoord B.HeadIndex,
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (B.postBandPrimeScore q)| ≤ Cz * w) :
    lower * w ^ 2 -
        (((1 + C) * (7 + C * K)) *
          (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon)) * w ^ 2 -
        ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * Cz) ^ 2 /
          gamma) * w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.actualCompensatedScore xi hgamma hgap q)
        (B.actualCompensatedScore xi hgamma hgap q) ∧
    (B.tiltedLaw xi).covariance
        (B.actualCompensatedScore xi hgamma hgap q)
        (B.actualCompensatedScore xi hgamma hgap q) ≤
      upper * w ^ 2 +
        (((1 + C) * (7 + C * K)) *
          (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon)) * w ^ 2 := by
  let d : ℝ := Real.sqrt
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  have hcoordK : 0 ≤ Cz * w := mul_nonneg hCz hw
  have hcovZ : ‖B.nuisanceCovarianceVector xi
      (B.postBandPrimeScore q)‖ ≤ (d * Cz) * w := by
    have hraw := B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
      xi (B.postBandPrimeScore q) hcoordK hcovCoord
    simpa only [d, mul_assoc] using hraw
  simpa only [d] using
    B.actualCompensatedScore_variance_bounds_of_squarefree xi q
      hC hK hw hCpow hepsilon
      (mul_nonneg (Real.sqrt_nonneg _) hCz)
      hsharp hbandT hdevSup hdevL1 hdevL2 hgamma hgap h75
      hsfLower hsfUpper hcovZ

/-- Variance assembly in terms of the single analytic nuisance marked-row
family.  The covariance vector of the complete post-band score is obtained by
summing those marked rows against the literal fitted coefficients.  Thus the
`O(w)` nuisance cross-column is not assumed separately. -/
theorem actualCompensatedScore_variance_bounds_of_squarefree_and_marked_nuisance_rows
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w Cpow epsilon lower upper Cmarked : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w)
    (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon)
    (hCmarked : 0 ≤ Cmarked)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (h75 : PrimePowerTransferBounds (B.actualValuationLaw xi)
      B.sampleData.n B.sampleData.W Cpow epsilon)
    (hsfLower : lower * w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q))
    (hsfUpper :
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) ≤
          upper * w ^ 2)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ))) :
    lower * w ^ 2 -
        (((1 + C) * (7 + C * K)) *
          (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon)) * w ^ 2 -
        ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * (7 + C * K))) ^ 2 / gamma) * w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.actualCompensatedScore xi hgamma hgap q)
        (B.actualCompensatedScore xi hgamma hgap q) ∧
    (B.tiltedLaw xi).covariance
        (B.actualCompensatedScore xi hgamma hgap q)
        (B.actualCompensatedScore xi hgamma hgap q) ≤
      upper * w ^ 2 +
        (((1 + C) * (7 + C * K)) *
          (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon)) * w ^ 2 := by
  have hL1 :=
    (B.partition.compensatedCoefficient_three_bounds B.n_gt_one q
      hC hw hsharp hbandT hdevSup hdevL1 hdevL2).2.1
  have hcovZ :=
    B.nuisanceCovarianceVector_postBand_norm_le_of_marked_and_l1
      xi q hCmarked hmarked hL1
  exact B.actualCompensatedScore_variance_bounds_of_squarefree xi q
    hC hK hw hCpow hepsilon
    (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg hCmarked (by positivity)))
    hsharp hbandT hdevSup hdevL1 hdevL2 hgamma hgap h75
    hsfLower hsfUpper hcovZ

set_option maxHeartbeats 1000000 in
/-- Exact assembly of the marked-prime row after both regression stages.
The first two hypotheses are the squarefree marked row and the explicit
finite-nuisance marked row; Lemma 7.5 supplies the intervening full-valuation
replacement at the relative `w/p` scale. -/
theorem actualCompensatedScore_markedRow_bound_of_squarefree
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w Cpow epsilon Csf CZrow : ℝ}
    (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation r| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (h75 : PrimePowerTransferBounds (B.actualValuationLaw xi)
      B.sampleData.n B.sampleData.W Cpow epsilon)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W)
    (hsquarefree :
      |(B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q)| ≤
          Csf * w * (1 / (p : ℝ)))
    (hnuisance :
      |(B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (fun m ↦ inner ℝ
          (B.actualNuisanceCoefficient xi hgamma hgap q)
          (B.nuisanceStatistic m))| ≤
        CZrow * w * (1 / (p : ℝ))) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ valuation p (B.sampleData.value m))
      (B.actualCompensatedScore xi hgamma hgap q)| ≤
      Csf * w * (1 / (p : ℝ)) +
        (1 + C) * w *
          (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon) *
          (1 / (p : ℝ)) +
        CZrow * w * (1 / (p : ℝ)) := by
  let fitted : ℝ := (B.tiltedLaw xi).covariance
    (fun m ↦ valuation p (B.sampleData.value m))
    (B.actualCompensatedScore xi hgamma hgap q)
  let full : ℝ := (B.tiltedLaw xi).covariance
    (fun m ↦ valuation p (B.sampleData.value m))
    (B.postBandPrimeScore q)
  let squarefree : ℝ := (B.tiltedLaw xi).covariance
    (fun m ↦ divInd p (B.sampleData.value m))
    (B.postBandSquarefreeScore q)
  let nuisance : ℝ := (B.tiltedLaw xi).covariance
    (fun m ↦ valuation p (B.sampleData.value m))
    (fun m ↦ inner ℝ
      (B.actualNuisanceCoefficient xi hgamma hgap q)
      (B.nuisanceStatistic m))
  have hpower : |full - squarefree| ≤
      (1 + C) * w *
        (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon) *
        (1 / (p : ℝ)) := by
    exact B.actual_primePower_relative_markedRow_bound xi q
      hC hw hsharp hbandT hdevSup hdevL1 hdevL2 h75 hp
  have hdecomp : fitted = full - nuisance := by
    exact B.actualCompensatedScore_markedRow_decomposition
      xi hgamma hgap q p
  exact markedRow_triangle hdecomp hpower hsquarefree hnuisance

/-- Marked-row assembly with the scalar nuisance-row contract removed.  The
nuisance term is a conclusion of the actual covariance-vector bounds and
the proved nuisance inverse.  These vector bounds are exactly the two
analytic rows estimated before the final Cauchy--Schwarz step in the paper. -/
theorem actualCompensatedScore_markedRow_bound_of_squarefree_and_vector_rows
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w Cpow epsilon Csf Cz Cmarked : ℝ}
    (hC : 0 ≤ C) (hw : 0 ≤ w) (hCz : 0 ≤ Cz)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation r| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (h75 : PrimePowerTransferBounds (B.actualValuationLaw xi)
      B.sampleData.n B.sampleData.W Cpow epsilon)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W)
    (hsquarefree :
      |(B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q)| ≤
          Csf * w * (1 / (p : ℝ)))
    (hcovZ : ‖B.nuisanceCovarianceVector xi
        (B.postBandPrimeScore q)‖ ≤ Cz * w)
    (hmarkedZ : ‖B.nuisanceCovarianceVector xi
        (fun m ↦ valuation p (B.sampleData.value m))‖ ≤
      Cmarked * (1 / (p : ℝ))) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ valuation p (B.sampleData.value m))
      (B.actualCompensatedScore xi hgamma hgap q)| ≤
      Csf * w * (1 / (p : ℝ)) +
        (1 + C) * w *
          (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon) *
          (1 / (p : ℝ)) +
        ((Cz / gamma) * Cmarked) * w * (1 / (p : ℝ)) := by
  have hnuisance := B.actualNuisanceCoefficient_markedRow_bound
    xi hgamma hgap q
      (fun m ↦ valuation p (B.sampleData.value m))
      hCz hw hcovZ hmarkedZ
  exact B.actualCompensatedScore_markedRow_bound_of_squarefree
    xi q hC hw hsharp hbandT hdevSup hdevL1 hdevL2
      hgamma hgap h75 hp hsquarefree hnuisance

/-- Fully coordinatewise version of the marked-row assembly.  Both nuisance
vector norms are discharged from the physical/head coordinate estimates.  As
the head set is fixed, the displayed square-root cardinality is a fixed
constant and introduces no dependence on the later tilt box or on `n`. -/
theorem actualCompensatedScore_markedRow_bound_of_squarefree_and_coordinate_rows
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w Cpow epsilon Csf Cz Cmarked : ℝ}
    (hC : 0 ≤ C) (hw : 0 ≤ w) (hCz : 0 ≤ Cz)
    (hCmarked : 0 ≤ Cmarked)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation r| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (h75 : PrimePowerTransferBounds (B.actualValuationLaw xi)
      B.sampleData.n B.sampleData.W Cpow epsilon)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W)
    (hsquarefree :
      |(B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q)| ≤
          Csf * w * (1 / (p : ℝ)))
    (hcovCoord : ∀ c : NuisanceCoord B.HeadIndex,
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (B.postBandPrimeScore q)| ≤ Cz * w)
    (hmarkedCoord : ∀ c : NuisanceCoord B.HeadIndex,
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p (B.sampleData.value m))| ≤
          Cmarked * (1 / (p : ℝ))) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ valuation p (B.sampleData.value m))
      (B.actualCompensatedScore xi hgamma hgap q)| ≤
      Csf * w * (1 / (p : ℝ)) +
        (1 + C) * w *
          (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon) *
          (1 / (p : ℝ)) +
        (((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * Cz) /
            gamma) *
          (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked)) * w * (1 / (p : ℝ)) := by
  let d : ℝ := Real.sqrt
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  have hscoreK : 0 ≤ Cz * w := mul_nonneg hCz hw
  have hmarkedK : 0 ≤ Cmarked * (1 / (p : ℝ)) :=
    mul_nonneg hCmarked (by positivity)
  have hcovZ : ‖B.nuisanceCovarianceVector xi
      (B.postBandPrimeScore q)‖ ≤ (d * Cz) * w := by
    have hraw := B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
      xi (B.postBandPrimeScore q) hscoreK hcovCoord
    simpa only [d, mul_assoc] using hraw
  have hmarkedZ : ‖B.nuisanceCovarianceVector xi
      (fun m ↦ valuation p (B.sampleData.value m))‖ ≤
        (d * Cmarked) * (1 / (p : ℝ)) := by
    have hraw := B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
      xi (fun m ↦ valuation p (B.sampleData.value m))
      hmarkedK hmarkedCoord
    simpa only [d, mul_assoc] using hraw
  simpa only [d] using
    B.actualCompensatedScore_markedRow_bound_of_squarefree_and_vector_rows
      xi q hC hw (mul_nonneg (Real.sqrt_nonneg _) hCz)
      hsharp hbandT hdevSup hdevL1 hdevL2 hgamma hgap h75 hp
      hsquarefree hcovZ hmarkedZ

/-- Marked-row assembly with one analytic nuisance-row family and no separate
post-band nuisance-column hypothesis.  The latter is the exact fitted-
coefficient summation proved above. -/
theorem actualCompensatedScore_markedRow_bound_of_squarefree_and_marked_nuisance_rows
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w Cpow epsilon Csf Cmarked : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w)
    (hCmarked : 0 ≤ Cmarked)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation r| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (h75 : PrimePowerTransferBounds (B.actualValuationLaw xi)
      B.sampleData.n B.sampleData.W Cpow epsilon)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W)
    (hsquarefree :
      |(B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q)| ≤
          Csf * w * (1 / (p : ℝ)))
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (r : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation r.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (r.1 : ℝ))) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ valuation p (B.sampleData.value m))
      (B.actualCompensatedScore xi hgamma hgap q)| ≤
      Csf * w * (1 / (p : ℝ)) +
        (1 + C) * w *
          (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon) *
          (1 / (p : ℝ)) +
        (((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              (Cmarked * (7 + C * K))) / gamma) *
          (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked)) * w * (1 / (p : ℝ)) := by
  have hL1 :=
    (B.partition.compensatedCoefficient_three_bounds B.n_gt_one q
      hC hw hsharp hbandT hdevSup hdevL1 hdevL2).2.1
  have hcovZ :=
    B.nuisanceCovarianceVector_postBand_norm_le_of_marked_and_l1
      xi q hCmarked hmarked hL1
  have hmarkedCoord : ∀ c : NuisanceCoord B.HeadIndex,
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p (B.sampleData.value m))| ≤
          Cmarked * (1 / (p : ℝ)) := by
    intro c
    exact hmarked c ⟨p, hp⟩
  have hmarkedZ : ‖B.nuisanceCovarianceVector xi
      (fun m ↦ valuation p (B.sampleData.value m))‖ ≤
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        Cmarked) * (1 / (p : ℝ)) := by
    have hraw := B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
      xi (fun m ↦ valuation p (B.sampleData.value m))
      (mul_nonneg hCmarked (by positivity)) hmarkedCoord
    simpa only [mul_assoc] using hraw
  exact B.actualCompensatedScore_markedRow_bound_of_squarefree_and_vector_rows
    xi q hC hw
    (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg hCmarked (by positivity)))
    hsharp hbandT hdevSup hdevL1 hdevL2 hgamma hgap h75 hp
    hsquarefree hcovZ hmarkedZ

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
