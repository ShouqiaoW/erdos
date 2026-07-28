import Erdos390.Full.PaperActualLemma86WeightedRow

/-!
# Paper-scale finite slow-variance lower

The older relative lemma normalized the partition variance by the special
factor `1/16`.  A permitted two-parameter paper mesh instead supplies a
uniform factor depending only on the previously fixed regularity constant.
This file keeps that factor literal.  No comparison between `delta` and
`eta` is encoded in the finite statement.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperBridgeFit

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open OmittedTiltPairChamber PrimePowerCovariance
open PaperPrimePowerChamberError PaperSquarefreeSlowQuadraticLower
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open PaperWeightedInverseExport PaperCanonicalSlowKappa
open FiniteSignedQuadraticEntryTransfer SquarefreeCovarianceReference

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Squarefree lower constant with a literal relative variance factor. -/
def paperScaleSquarefreeSlowConstant
    (varianceFactor anchorFloor rowError Eprofile CKernel C K invW : ℝ) : ℝ :=
  (canonicalSlowKappa / 4) * anchorFloor * varianceFactor -
    rowError * slowL2Constant C K -
    (4 * pairCovarianceScale Eprofile) * slowL1Constant C K ^ 2 -
    (2 * Eprofile) * slowL2Constant C K -
    signedSecondConstant Eprofile CKernel * invW * slowL2Constant C K

/-- Final full-valuation/nuisance slow constant at the same paper scale. -/
def paperScaleLemma86SlowConstantOfRow
    (varianceFactor anchorFloor rowError Eprofile CKernel C K invW R
      Cmarked gamma : ℝ) : ℝ :=
  paperScaleSquarefreeSlowConstant varianceFactor anchorFloor rowError
      Eprofile CKernel C K invW -
    ((1 + C) * (7 + C * K)) * R -
    (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
      (Cmarked * (7 + C * K))) ^ 2 / gamma

/-- Matching squarefree upper constant at the literal paper scale. -/
def paperScaleSquarefreeSlowUpperConstant
    (Eprofile CF CKernel C K invW : ℝ) : ℝ :=
  CKernel * slowL1Constant C K ^ 2 +
    CF * slowL2Constant C K +
    (4 * pairCovarianceScale Eprofile) * slowL1Constant C K ^ 2 +
    (2 * Eprofile) * slowL2Constant C K +
    signedSecondConstant Eprofile CKernel * invW * slowL2Constant C K

/-- Matching full-valuation upper constant; nuisance regression can only
decrease the variance, so no nuisance loss appears here. -/
def paperScaleLemma86SlowUpperConstantOfRow
    (Eprofile CF CKernel C K invW R : ℝ) : ℝ :=
  paperScaleSquarefreeSlowUpperConstant Eprofile CF CKernel C K invW +
    ((1 + C) * (7 + C * K)) * R

/-- Exact relative squarefree lower for an arbitrary nonnegative variance
factor.  The proof retains the literal arithmetic anchor and does not
replace the two mesh parameters by one another. -/
theorem actualSquarefree_relative_lower_canonicalKappa_of_varianceFactor
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w varianceFactor rowError Eprofile CKernel anchorFloor : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w)
    (hvarianceFactor : 0 ≤ varianceFactor)
    (hrowError : 0 ≤ rowError) (hEprofile : 0 ≤ Eprofile)
    (hCKernel : 0 ≤ CKernel) (hW : 0 < B.sampleData.W)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hvarLower : varianceFactor * w ^ 2 ≤ B.partition.variance)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    (hvariance : B.partition.variance ≤ B.partition.centerEnergy)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    (hAnchorMass : anchorFloor ≤
      anchorMass (primeWeight B.sampleData.n) anchor)
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
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
          (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n r.1)| ≤ CKernel) :
    paperScaleSquarefreeSlowConstant varianceFactor anchorFloor rowError
        Eprofile CKernel C K (1 / (B.sampleData.W : ℝ)) * w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) := by
  let CL1 := slowL1Constant C K
  let CL2 := slowL2Constant C K
  let eOff := 4 * pairCovarianceScale Eprofile
  let eDiag := 2 * Eprofile
  let eSecond := signedSecondConstant Eprofile CKernel
  let invW := 1 / (B.sampleData.W : ℝ)
  have hthree := B.partition.compensatedCoefficient_three_bounds
    B.n_gt_one q hC hw hsharp hbandT hdevSup hdevL1 hdevL2
  have hL1 : B.partition.compensatedL1 q ≤ CL1 * w := by
    simpa only [CL1, slowL1Constant] using hthree.2.1
  have hL2 : B.partition.compensatedL2Sq q ≤ CL2 * w ^ 2 := by
    simpa only [CL2, slowL2Constant] using hthree.2.2
  have hCL1 : 0 ≤ CL1 := by
    dsimp only [CL1, slowL1Constant]
    positivity
  have hCL2 : 0 ≤ CL2 := by
    dsimp only [CL2, slowL2Constant]
    positivity
  have hL1nonneg : 0 ≤ B.partition.compensatedL1 q := by
    unfold ArithmeticBandGeometry.Partition.compensatedL1
    exact Finset.sum_nonneg fun p hp ↦
      mul_nonneg (by positivity) (abs_nonneg _)
  have hL1Sq : B.partition.compensatedL1 q ^ 2 ≤
      CL1 ^ 2 * w ^ 2 := by
    have hsquare := (sq_le_sq₀ hL1nonneg (mul_nonneg hCL1 hw)).2 hL1
    nlinarith
  have hSecondRaw :=
    weightedL2SqSecond_le_invCutoff_mul_weightedL2Sq
      (n := B.sampleData.n) hW
      (compensatedPrimeCoefficient B.partition q)
  have hInvW : 0 ≤ invW := by dsimp only [invW]; positivity
  have hSecond :
      weightedL2SqSecond reciprocalWeight
          (compensatedPrimeCoefficient B.partition q) ≤
        invW * CL2 * w ^ 2 := by
    rw [weightedL2Sq_compensated_eq] at hSecondRaw
    calc
      weightedL2SqSecond reciprocalWeight
          (compensatedPrimeCoefficient B.partition q) ≤
          invW * B.partition.compensatedL2Sq q := by
        simpa only [invW] using hSecondRaw
      _ ≤ invW * (CL2 * w ^ 2) :=
        mul_le_mul_of_nonneg_left hL2 hInvW
      _ = invW * CL2 * w ^ 2 := by ring
  have hlowerExact :=
    B.actualSquarefree_compensated_lower_canonicalKappa_of_profiles
      xi q anchor hinterior hmass hrow hvariance hEprofile
      hpair hsingle (fun p hp ↦ hKernel ⟨p, hp⟩ ⟨p, hp⟩)
  have hk4 : 0 ≤ canonicalSlowKappa / 4 :=
    div_nonneg canonicalSlowKappa_pos.le (by norm_num)
  have hmassvar :
      anchorFloor * (varianceFactor * w ^ 2) ≤
        anchorMass (primeWeight B.sampleData.n) anchor *
          B.partition.variance :=
    mul_le_mul hAnchorMass hvarLower
      (mul_nonneg hvarianceFactor (sq_nonneg _)) hmass.le
  have hmain := mul_le_mul_of_nonneg_left hmassvar hk4
  have hrowLoss := mul_le_mul_of_nonneg_left hL2 hrowError
  have heOff : 0 ≤ eOff := by
    dsimp only [eOff]
    exact mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hEprofile)
  have heDiag : 0 ≤ eDiag := by dsimp only [eDiag]; positivity
  have heSecond : 0 ≤ eSecond := by
    dsimp only [eSecond, signedSecondConstant]
    positivity
  have hoffLoss := mul_le_mul_of_nonneg_left hL1Sq heOff
  have hdiagLoss := mul_le_mul_of_nonneg_left hL2 heDiag
  have hsecondLoss := mul_le_mul_of_nonneg_left hSecond heSecond
  have htarget :
      paperScaleSquarefreeSlowConstant varianceFactor anchorFloor rowError
          Eprofile CKernel C K invW * w ^ 2 ≤
        (canonicalSlowKappa / 4) *
              anchorMass (primeWeight B.sampleData.n) anchor *
              B.partition.variance -
          rowError * B.partition.compensatedL2Sq q -
          (eOff * B.partition.compensatedL1 q ^ 2 +
            eDiag * B.partition.compensatedL2Sq q +
            eSecond * weightedL2SqSecond reciprocalWeight
              (compensatedPrimeCoefficient B.partition q)) := by
    dsimp only [paperScaleSquarefreeSlowConstant, CL1, CL2,
      eOff, eDiag, eSecond]
    nlinarith [hmain, hrowLoss, hoffLoss, hdiagLoss, hsecondLoss]
  simpa only [invW] using htarget.trans hlowerExact

/-- Exact two-stage finite lower at an arbitrary paper variance factor. -/
theorem actualTwoStageCompensatedVariance_lower_paperScale_of_weightedRow
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {C K R varianceFactor rowError Eprofile CKernel anchorFloor Cmarked : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hvarianceFactor : 0 ≤ varianceFactor)
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
    (hvarLower : varianceFactor * B.w ^ 2 ≤ B.partition.variance)
    (hdevL2 : B.partition.variance ≤ 4 * B.w ^ 2)
    (hvariance : B.partition.variance ≤ B.partition.centerEnergy)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    (hAnchorMass : anchorFloor ≤
      anchorMass (primeWeight B.sampleData.n) anchor)
    (hrowReference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
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
          (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n r.1)| ≤ CKernel)
    (hrowPower : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
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
    B.paperScaleLemma86SlowConstantOfRow varianceFactor anchorFloor
        rowError Eprofile CKernel C K (1 / (B.sampleData.W : ℝ)) R
        Cmarked gamma * B.w ^ 2 ≤
      B.actualTwoStageCompensatedVariance xi hgamma hgap e := by
  let q := B.actualBandRegression xi hgamma hgap e
  let lower := paperScaleSquarefreeSlowConstant varianceFactor
    anchorFloor rowError Eprofile CKernel C K
      (1 / (B.sampleData.W : ℝ))
  have hsfLower :=
    B.actualSquarefree_relative_lower_canonicalKappa_of_varianceFactor
      xi q hC hK B.w_pos.le hvarianceFactor hrowError hEprofile
      hCKernel hW (by simpa only [q] using hsharp) hbandT hdevSup
      hdevL1 hvarLower hdevL2 hvariance anchor hinterior hmass
      hAnchorMass hrowReference hpair hsingle hKernel
  have hlower :=
    B.actualCompensatedScore_lower_of_squarefree_and_weightedRow
      xi q hC hK B.w_pos.le hR hCmarked
      (by simpa only [q] using hsharp) hbandT hdevSup hdevL1 hdevL2
      hgamma hgap hrowPower (by simpa only [q, lower] using hsfLower)
      hmarked
  change B.paperScaleLemma86SlowConstantOfRow varianceFactor anchorFloor
      rowError Eprofile CKernel C K (1 / (B.sampleData.W : ℝ)) R
      Cmarked gamma * B.w ^ 2 ≤
    (B.tiltedLaw xi).covariance
      (B.actualCompensatedScore xi hgamma hgap q)
      (B.actualCompensatedScore xi hgamma hgap q)
  dsimp only [paperScaleLemma86SlowConstantOfRow, lower] at hlower ⊢
  ring_nf at hlower ⊢
  exact hlower

/-- Two-sided literal finite Lemma 8.6 variance estimate.  This exposes the
upper estimate used by the paper instead of retaining it only as an
intermediate squarefree calculation. -/
theorem actualTwoStageCompensatedVariance_bounds_paperScale_of_weightedRow
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {C K R varianceFactor rowError Eprofile CF CKernel anchorFloor
      Cmarked : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hvarianceFactor : 0 ≤ varianceFactor)
    (hrowError : 0 ≤ rowError) (hEprofile : 0 ≤ Eprofile)
    (hCF : 0 ≤ CF) (hCKernel : 0 ≤ CKernel)
    (hCmarked : 0 ≤ Cmarked) (hW : 0 < B.sampleData.W)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.actualBandRegression xi hgamma hgap e) ≤ C * B.w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ B.w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * B.w)
    (hvarLower : varianceFactor * B.w ^ 2 ≤ B.partition.variance)
    (hdevL2 : B.partition.variance ≤ 4 * B.w ^ 2)
    (hvariance : B.partition.variance ≤ B.partition.centerEnergy)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    (hAnchorMass : anchorFloor ≤
      anchorMass (primeWeight B.sampleData.n) anchor)
    (hrowReference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
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
          (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n r.1)| ≤ CKernel)
    (hrowPower : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
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
    B.paperScaleLemma86SlowConstantOfRow varianceFactor anchorFloor
          rowError Eprofile CKernel C K (1 / (B.sampleData.W : ℝ)) R
          Cmarked gamma * B.w ^ 2 ≤
        B.actualTwoStageCompensatedVariance xi hgamma hgap e ∧
      B.actualTwoStageCompensatedVariance xi hgamma hgap e ≤
        paperScaleLemma86SlowUpperConstantOfRow Eprofile CF CKernel C K
          (1 / (B.sampleData.W : ℝ)) R * B.w ^ 2 := by
  let q := B.actualBandRegression xi hgamma hgap e
  let lower := paperScaleSquarefreeSlowConstant varianceFactor
    anchorFloor rowError Eprofile CKernel C K
      (1 / (B.sampleData.W : ℝ))
  let upper := paperScaleSquarefreeSlowUpperConstant Eprofile CF CKernel
    C K (1 / (B.sampleData.W : ℝ))
  have hsfLower :=
    B.actualSquarefree_relative_lower_canonicalKappa_of_varianceFactor
      xi q hC hK B.w_pos.le hvarianceFactor hrowError hEprofile
      hCKernel hW (by simpa only [q] using hsharp) hbandT hdevSup
      hdevL1 hvarLower hdevL2 hvariance anchor hinterior hmass
      hAnchorMass hrowReference hpair hsingle hKernel
  have hthree := B.partition.compensatedCoefficient_three_bounds
    B.n_gt_one q hC B.w_pos.le (by simpa only [q] using hsharp)
      hbandT hdevSup hdevL1 hdevL2
  let CL1 := slowL1Constant C K
  let CL2 := slowL2Constant C K
  let invW := 1 / (B.sampleData.W : ℝ)
  have hL1 : B.partition.compensatedL1 q ≤ CL1 * B.w := by
    simpa only [CL1, slowL1Constant] using hthree.2.1
  have hL2 : B.partition.compensatedL2Sq q ≤ CL2 * B.w ^ 2 := by
    simpa only [CL2, slowL2Constant] using hthree.2.2
  have hCL1 : 0 ≤ CL1 := by
    dsimp only [CL1, slowL1Constant]
    positivity
  have hL1nonneg : 0 ≤ B.partition.compensatedL1 q := by
    unfold ArithmeticBandGeometry.Partition.compensatedL1
    exact Finset.sum_nonneg fun p hp ↦
      mul_nonneg (by positivity) (abs_nonneg _)
  have hL1Sq : B.partition.compensatedL1 q ^ 2 ≤
      CL1 ^ 2 * B.w ^ 2 := by
    have hsquare := (sq_le_sq₀ hL1nonneg
      (mul_nonneg hCL1 B.w_pos.le)).2 hL1
    nlinarith
  have hSecondRaw :=
    weightedL2SqSecond_le_invCutoff_mul_weightedL2Sq
      (n := B.sampleData.n) hW
      (compensatedPrimeCoefficient B.partition q)
  have hInvW : 0 ≤ invW := by dsimp only [invW]; positivity
  have hSecond : weightedL2SqSecond reciprocalWeight
      (compensatedPrimeCoefficient B.partition q) ≤
        invW * CL2 * B.w ^ 2 := by
    rw [weightedL2Sq_compensated_eq] at hSecondRaw
    calc
      _ ≤ invW * B.partition.compensatedL2Sq q := by
        simpa only [invW] using hSecondRaw
      _ ≤ invW * (CL2 * B.w ^ 2) :=
        mul_le_mul_of_nonneg_left hL2 hInvW
      _ = invW * CL2 * B.w ^ 2 := by ring
  have hsfUpperRaw := B.actualSquarefree_compensated_upper_of_profiles
    xi q hEprofile hpair hsingle hF hKernel
  have hsfUpper :
      (B.tiltedLaw xi).covariance
          (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) ≤
        upper * B.w ^ 2 := by
    have hKernelL1 := mul_le_mul_of_nonneg_left hL1Sq hCKernel
    have hFL2 := mul_le_mul_of_nonneg_left hL2 hCF
    have heOff : 0 ≤ 4 * pairCovarianceScale Eprofile :=
      mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hEprofile)
    have hOffL1 := mul_le_mul_of_nonneg_left hL1Sq heOff
    have heDiag : 0 ≤ 2 * Eprofile := mul_nonneg (by norm_num) hEprofile
    have hDiagL2 := mul_le_mul_of_nonneg_left hL2 heDiag
    have heSecond : 0 ≤ signedSecondConstant Eprofile CKernel := by
      dsimp only [signedSecondConstant]
      positivity
    have hSecondL2 := mul_le_mul_of_nonneg_left hSecond heSecond
    calc
      _ ≤ CKernel * B.partition.compensatedL1 q ^ 2 +
            CF * B.partition.compensatedL2Sq q +
            (4 * pairCovarianceScale Eprofile) *
              B.partition.compensatedL1 q ^ 2 +
            (2 * Eprofile) * B.partition.compensatedL2Sq q +
            signedSecondConstant Eprofile CKernel *
              weightedL2SqSecond reciprocalWeight
                (compensatedPrimeCoefficient B.partition q) := hsfUpperRaw
      _ ≤ upper * B.w ^ 2 := by
        dsimp only [upper, paperScaleSquarefreeSlowUpperConstant]
        dsimp only [CL1, CL2, invW] at hKernelL1 hFL2 hOffL1 hDiagL2 hSecondL2
        ring_nf at hKernelL1 hFL2 hOffL1 hDiagL2 hSecondL2 ⊢
        linarith
  have hbounds := B.actualCompensatedScore_variance_bounds_of_squarefree_and_weightedRow
    xi q hC hK B.w_pos.le hR hCmarked
      (by simpa only [q] using hsharp) hbandT hdevSup hdevL1 hdevL2
      hgamma hgap hrowPower (by simpa only [q, lower] using hsfLower)
      (by simpa only [q, upper] using hsfUpper) hmarked
  have hlowerFull :=
    B.actualTwoStageCompensatedVariance_lower_paperScale_of_weightedRow
      xi hgamma hgap e hC hK hR hvarianceFactor hrowError hEprofile
      hCKernel hCmarked hW hsharp hbandT hdevSup hdevL1 hvarLower
      hdevL2 hvariance anchor hinterior hmass hAnchorMass hrowReference
      hpair hsingle hKernel hrowPower hmarked
  refine ⟨hlowerFull, ?_⟩
  change (B.tiltedLaw xi).covariance
      (B.actualCompensatedScore xi hgamma hgap q)
      (B.actualCompensatedScore xi hgamma hgap q) ≤ _
  dsimp only [paperScaleLemma86SlowUpperConstantOfRow, upper] at hbounds ⊢
  ring_nf at hbounds ⊢
  exact hbounds.2

end BridgeData

end Erdos390.Full.PaperBridgeFit

end
