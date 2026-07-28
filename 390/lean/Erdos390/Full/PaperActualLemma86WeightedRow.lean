import Erdos390.Full.PaperActualSquarefreeSlowLower
import Erdos390.Full.PaperActualPrimePowerRowTransfer
import Erdos390.Full.PaperActualTwoStageRegression
import Erdos390.Full.PaperExactTwoStageTargetSolve
import Erdos390.Full.PaperCanonicalSlowKappa

/-!
# Lemma 8.6 from the literal actual weighted prime row

This is the slow-variance assembly in the form produced by the canonical
raw-reference comparison.  In contrast to the older interface, it does not
assume a five-field Lemma 7.5 package for the actual guarded law.  The sole
prime-power input is the weighted `VV-II` row, which is exactly what the
quadratic calculation uses.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperBridgeFit

open ArithmeticModel ArithmeticBandGeometry
open FiniteProbability OmittedTiltPairChamber
open PrimePowerCovariance
open PaperPrimePowerChamberError
open PaperSquarefreeSlowQuadraticLower
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The finite slow constant when the actual full-versus-squarefree error is
given by one weighted-row budget `R`. -/
def actualLemma86SlowConstantOfRow
    (kappa anchorFloor rowError Eprofile CKernel C K R
      Cmarked gamma : ℝ) : ℝ :=
  actualSquarefreeLowerConstant kappa anchorFloor rowError Eprofile
      CKernel C K (1 / (B.sampleData.W : ℝ)) -
    ((1 + C) * (7 + C * K)) * R -
    (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
      (Cmarked * (7 + C * K))) ^ 2 / gamma

/-- Exact two-stage variance comparison from the squarefree variance, a
literal actual weighted row, and the nuisance marked rows. -/
theorem actualCompensatedScore_variance_bounds_of_squarefree_and_weightedRow
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w R lower upper Cmarked : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w) (hR : 0 ≤ R)
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
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 r.1 -
            (B.actualValuationLaw xi).covII p.1 r.1| ≤ R)
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
        (((1 + C) * (7 + C * K)) * R) * w ^ 2 -
        ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * (7 + C * K))) ^ 2 / gamma) * w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.actualCompensatedScore xi hgamma hgap q)
        (B.actualCompensatedScore xi hgamma hgap q) ∧
    (B.tiltedLaw xi).covariance
        (B.actualCompensatedScore xi hgamma hgap q)
        (B.actualCompensatedScore xi hgamma hgap q) ≤
      upper * w ^ 2 +
        (((1 + C) * (7 + C * K)) * R) * w ^ 2 := by
  let E : ℝ := ((1 + C) * (7 + C * K)) * R
  let Cz : ℝ := Real.sqrt
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
      (Cmarked * (7 + C * K))
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
    exact B.actual_primePower_relative_variance_bound_of_row xi q
      hC hK hw hR hsharp hbandT hdevSup hdevL1 hdevL2 hrow
  have hL1 :=
    (B.partition.compensatedCoefficient_three_bounds B.n_gt_one q
      hC hw hsharp hbandT hdevSup hdevL1 hdevL2).2.1
  have hcovZRaw :=
    B.nuisanceCovarianceVector_postBand_norm_le_of_marked_and_l1
      xi q hCmarked hmarked hL1
  have hcovZ : ‖B.nuisanceCovarianceVector xi
      (B.postBandPrimeScore q)‖ ≤ Cz * w := by
    simpa only [Cz, mul_assoc] using hcovZRaw
  have hvar : residualVariance = full - loss := by
    exact B.nuisanceResidualScore_variance_identity
      xi hgamma hgap (B.postBandPrimeScore q)
  have hloss := B.nuisanceRegressionLoss_bounds
    xi hgamma hgap (B.postBandPrimeScore q)
  have hCz0 : 0 ≤ Cz := by
    dsimp only [Cz]
    positivity
  have hcovSq :
      ‖B.nuisanceCovarianceVector xi (B.postBandPrimeScore q)‖ ^ 2 ≤
        (Cz * w) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hCz0 hw)).2 hcovZ
  have hlossUpper : loss ≤ (Cz ^ 2 / gamma) * w ^ 2 := by
    calc
      loss ≤
          ‖B.nuisanceCovarianceVector xi (B.postBandPrimeScore q)‖ ^ 2 /
            gamma := hloss.2
      _ ≤ (Cz * w) ^ 2 / gamma :=
        div_le_div_of_nonneg_right hcovSq hgamma.le
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

/-- Lower-bound-only version of the preceding assembly.  It avoids an
irrelevant squarefree upper estimate and is the form used by the uniform
canonical wrapper. -/
theorem actualCompensatedScore_lower_of_squarefree_and_weightedRow
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w R lower Cmarked : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w) (hR : 0 ≤ R)
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
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 r.1 -
            (B.actualValuationLaw xi).covII p.1 r.1| ≤ R)
    (hsfLower : lower * w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q))
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ))) :
    lower * w ^ 2 -
        (((1 + C) * (7 + C * K)) * R) * w ^ 2 -
        ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * (7 + C * K))) ^ 2 / gamma) * w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.actualCompensatedScore xi hgamma hgap q)
        (B.actualCompensatedScore xi hgamma hgap q) := by
  let E : ℝ := ((1 + C) * (7 + C * K)) * R
  let Cz : ℝ := Real.sqrt
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
      (Cmarked * (7 + C * K))
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
  have hpow : |full - squarefree| ≤ E * w ^ 2 :=
    B.actual_primePower_relative_variance_bound_of_row xi q
      hC hK hw hR hsharp hbandT hdevSup hdevL1 hdevL2 hrow
  have hL1 :=
    (B.partition.compensatedCoefficient_three_bounds B.n_gt_one q
      hC hw hsharp hbandT hdevSup hdevL1 hdevL2).2.1
  have hcovZRaw :=
    B.nuisanceCovarianceVector_postBand_norm_le_of_marked_and_l1
      xi q hCmarked hmarked hL1
  have hcovZ : ‖B.nuisanceCovarianceVector xi
      (B.postBandPrimeScore q)‖ ≤ Cz * w := by
    simpa only [Cz, mul_assoc] using hcovZRaw
  have hvar : residualVariance = full - loss :=
    B.nuisanceResidualScore_variance_identity
      xi hgamma hgap (B.postBandPrimeScore q)
  have hloss := B.nuisanceRegressionLoss_bounds
    xi hgamma hgap (B.postBandPrimeScore q)
  have hCz0 : 0 ≤ Cz := by
    dsimp only [Cz]
    positivity
  have hcovSq :
      ‖B.nuisanceCovarianceVector xi (B.postBandPrimeScore q)‖ ^ 2 ≤
        (Cz * w) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hCz0 hw)).2 hcovZ
  have hlossUpper : loss ≤ (Cz ^ 2 / gamma) * w ^ 2 := by
    calc
      loss ≤
          ‖B.nuisanceCovarianceVector xi (B.postBandPrimeScore q)‖ ^ 2 /
            gamma := hloss.2
      _ ≤ (Cz * w) ^ 2 / gamma :=
        div_le_div_of_nonneg_right hcovSq hgamma.le
      _ = (Cz ^ 2 / gamma) * w ^ 2 := by ring
  have hpowLower : -(E * w ^ 2) ≤ full - squarefree :=
    neg_le_of_abs_le hpow
  change lower * w ^ 2 ≤ squarefree at hsfLower
  change lower * w ^ 2 - E * w ^ 2 -
      (Cz ^ 2 / gamma) * w ^ 2 ≤ residualVariance
  rw [hvar]
  linarith

/-- Fixed-`kappa` finite Lemma 8.6.  Every remaining hypothesis is a
literal finite arithmetic/probabilistic estimate; the slow coercivity
constant no longer sits under an `n`-dependent existential quantifier. -/
theorem actualTwoStageCompensatedVariance_lower_canonicalKappa_of_weightedRow
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {C K R rowError Eprofile CKernel anchorFloor Cmarked : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hrowError : 0 ≤ rowError) (hEprofile : 0 ≤ Eprofile)
    (hCKernel : 0 ≤ CKernel) (hCmarked : 0 ≤ Cmarked)
    (hW : 0 < B.sampleData.W)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.actualBandRegression xi hgamma hgap e) ≤ C * B.w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ B.w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * B.w)
    (hvarLower : B.w ^ 2 / 16 ≤ B.partition.variance)
    (hdevL2 : B.partition.variance ≤ 4 * B.w ^ 2)
    (hvariance : B.partition.variance ≤ B.partition.centerEnergy)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    (hAnchorMass : anchorFloor ≤
      anchorMass (primeWeight B.sampleData.n) anchor)
    (hrowResidual : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p r 1 1)| ≤
        Eprofile * pairWeight p r 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p r : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p.1) (tPrime B.sampleData.n r.1)| ≤
        CKernel)
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 r.1 -
            (B.actualValuationLaw xi).covII p.1 r.1| ≤ R)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ))) :
    B.actualLemma86SlowConstantOfRow
        PaperCanonicalSlowKappa.canonicalSlowKappa anchorFloor rowError
          Eprofile CKernel C K R Cmarked gamma * B.w ^ 2 ≤
      B.actualTwoStageCompensatedVariance xi hgamma hgap e := by
  let q := B.actualBandRegression xi hgamma hgap e
  let lower := actualSquarefreeLowerConstant
    PaperCanonicalSlowKappa.canonicalSlowKappa anchorFloor rowError
      Eprofile CKernel C K (1 / (B.sampleData.W : ℝ))
  have hsfLower :=
    B.actualSquarefree_relative_lower_canonicalKappa_of_profiles
      xi q hC hK B.w_pos.le hrowError hEprofile hCKernel hW
      (by simpa only [q] using hsharp) hbandT hdevSup hdevL1
      hvarLower hdevL2 hvariance anchor hinterior hmass hAnchorMass
      hrowResidual hpair hsingle hKernel
  have hlower :=
    B.actualCompensatedScore_lower_of_squarefree_and_weightedRow
      xi q hC hK B.w_pos.le hR hCmarked
      (by simpa only [q] using hsharp) hbandT hdevSup hdevL1 hdevL2
      hgamma hgap hrow (by simpa only [q, lower] using hsfLower) hmarked
  change B.actualLemma86SlowConstantOfRow
      PaperCanonicalSlowKappa.canonicalSlowKappa anchorFloor rowError
        Eprofile CKernel C K R Cmarked gamma * B.w ^ 2 ≤
    (B.tiltedLaw xi).covariance
      (B.actualCompensatedScore xi hgamma hgap q)
      (B.actualCompensatedScore xi hgamma hgap q)
  dsimp only [actualLemma86SlowConstantOfRow, lower] at hlower ⊢
  ring_nf at hlower ⊢
  exact hlower

set_option maxHeartbeats 2000000 in
/-- Paper-facing Lemma 8.6 slow lower with neither a squarefree-variance
contract nor an actual-law Lemma 7.5 contract. -/
theorem exists_actualTwoStageCompensatedVariance_lower_of_weightedRow
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {C K R rowError Eprofile CF CKernel anchorFloor Cmarked : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hrowError : 0 ≤ rowError) (hEprofile : 0 ≤ Eprofile)
    (hCF : 0 ≤ CF) (hCKernel : 0 ≤ CKernel)
    (hCmarked : 0 ≤ Cmarked)
    (hW : 0 < B.sampleData.W)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.actualBandRegression xi hgamma hgap e) ≤ C * B.w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ B.w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * B.w)
    (hvarLower : B.w ^ 2 / 16 ≤ B.partition.variance)
    (hdevL2 : B.partition.variance ≤ 4 * B.w ^ 2)
    (hvariance : B.partition.variance ≤ B.partition.centerEnergy)
    {epsilonMesh : ℝ} (hepsilonMesh : 0 < epsilonMesh)
    (hhalf : epsilonMesh < 1 / 2)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc epsilonMesh (1 - epsilonMesh))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    (hAnchorMass : anchorFloor ≤
      anchorMass (primeWeight B.sampleData.n) anchor)
    (hrowResidual : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p r 1 1)| ≤
        Eprofile * pairWeight p r 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hF : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n p.1)| ≤ CF)
    (hKernel : ∀ p r : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p.1) (tPrime B.sampleData.n r.1)| ≤
        CKernel)
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 r.1 -
            (B.actualValuationLaw xi).covII p.1 r.1| ≤ R)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ))) :
    ∃ kappa : ℝ, 0 < kappa ∧
      B.actualLemma86SlowConstantOfRow kappa anchorFloor rowError
          Eprofile CKernel C K R Cmarked gamma * B.w ^ 2 ≤
        B.actualTwoStageCompensatedVariance xi hgamma hgap e := by
  let q := B.actualBandRegression xi hgamma hgap e
  obtain ⟨kappa, hkappa, hsfLower, hsfUpper⟩ :=
    B.exists_actualSquarefree_compensated_bounds_of_profiles
      (C := C) (K := K) (w := B.w) (rowError := rowError)
      (Eprofile := Eprofile) (CF := CF) (CKernel := CKernel)
      (anchorFloor := anchorFloor) xi q hC hK B.w_pos.le hrowError
      hEprofile hCF hCKernel hW
      (by simpa only [q] using hsharp) hbandT hdevSup hdevL1
      hvarLower hdevL2 hvariance hepsilonMesh hhalf anchor hinterior
      hmass hAnchorMass hrowResidual hpair hsingle hF hKernel
  let lower := actualSquarefreeLowerConstant kappa anchorFloor rowError
    Eprofile CKernel C K (1 / (B.sampleData.W : ℝ))
  let upper := actualSquarefreeUpperConstant Eprofile CF CKernel C K
    (1 / (B.sampleData.W : ℝ))
  have hbounds :=
    B.actualCompensatedScore_variance_bounds_of_squarefree_and_weightedRow
      xi q hC hK B.w_pos.le hR hCmarked
      (by simpa only [q] using hsharp) hbandT hdevSup hdevL1 hdevL2
      hgamma hgap hrow
      (by simpa only [q, lower] using hsfLower)
      (by simpa only [q, upper] using hsfUpper) hmarked
  refine ⟨kappa, hkappa, ?_⟩
  change B.actualLemma86SlowConstantOfRow kappa anchorFloor rowError
      Eprofile CKernel C K R Cmarked gamma * B.w ^ 2 ≤
    (B.tiltedLaw xi).covariance
      (B.actualCompensatedScore xi hgamma hgap q)
      (B.actualCompensatedScore xi hgamma hgap q)
  have hlower := hbounds.1
  dsimp only [actualLemma86SlowConstantOfRow, lower] at hlower ⊢
  ring_nf at hlower ⊢
  exact hlower

end BridgeData

end Erdos390.Full.PaperBridgeFit
