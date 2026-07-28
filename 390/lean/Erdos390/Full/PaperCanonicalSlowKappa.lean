import Erdos390.Full.PaperActualSquarefreeSlowLower

/-!
# A fixed slow-direction Dickman gap

The compact interior anchor is always taken in `[1/8,7/8]`.  Hence its
Dickman quotient gap must be selected once, before `n`, the arithmetic mesh,
and every tilt parameter.  This file exposes that fixed choice and threads
it through the exact prime Dirichlet and squarefree lower bounds.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperCanonicalSlowKappa

open ArithmeticModel ArithmeticBandGeometry
open ConditionedPoissonLimit PoissonDickmanWeightedInverse
open PoissonDickmanDirichlet OmittedTiltPairChamber
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open PaperSquarefreeSlowQuadraticLower
open PaperBridgeFit PaperBridgeFit.BridgeData
open PaperPrimePowerChamberError
open PaperWeightedInverseExport
open FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference
open PrimePowerCovariance

/-- The one compact Dickman quotient gap used by every canonical slow
estimate. -/
def canonicalSlowKappa : ℝ :=
  Classical.choose
    (exists_transposeQuotient_uniform_gap
      (epsilon := (1 / 8 : ℝ)) (by norm_num) (by norm_num))

theorem canonicalSlowKappa_pos : 0 < canonicalSlowKappa :=
  (Classical.choose_spec
    (exists_transposeQuotient_uniform_gap
      (epsilon := (1 / 8 : ℝ)) (by norm_num) (by norm_num))).1

theorem canonicalSlowKappa_gap :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8),
      canonicalSlowKappa ≤ -covarianceKernelQuotient t s :=
  (Classical.choose_spec
    (exists_transposeQuotient_uniform_gap
      (epsilon := (1 / 8 : ℝ)) (by norm_num) (by norm_num))).2

/-- Fixed-`kappa` version of the prime anchor Dirichlet lower. -/
theorem canonicalSlowKappa_primeDirichlet_anchor_lower
    {n W : ℕ} (hn : 1 < n)
    (anchor : Finset (PrimeIndex n W))
    (hinterior : ∀ q ∈ anchor,
      tPrime n q.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight n) anchor) :
    ∀ c : PrimeIndex n W → ℝ,
      (canonicalSlowKappa / 2) * anchorMass (primeWeight n) anchor *
          primePhysicalDistance n c (anchorMean n anchor c) ≤
        dirichletEnergy (primeWeight n) (primeKernel n)
          (dirichletCoordinate n c) := by
  intro c
  rw [← weightedDistance_eq_primePhysicalDistance hn c]
  exact half_kappa_anchorMass_mul_weightedDistance_le_dirichletEnergy
    (primeWeight n) (primeMetricWeight n) (primeKernel n) anchor
    (dirichletCoordinate n c) (anchorMean n anchor c)
    canonicalSlowKappa canonicalSlowKappa_pos.le
    (fun p ↦ (primeWeight_pos hn p).le)
    (fun p ↦ (primeMetricWeight_pos hn p).le)
    (fun p q ↦ covarianceKernel_nonpos (tPrime_mem_unit hn p)
      (tPrime_mem_unit hn q))
    (anchor_edge_domination hn canonicalSlowKappa_gap anchor hinterior)
    (anchor_centered anchor c hmass.ne')

/-- The fixed Dickman gap gives the exact compensated prime-reference lower
without an `n`-dependent existential witness. -/
theorem canonicalSlowKappa_primeReference_compensated_lower
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Band]
    (B : BridgeData Head Band)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    {rowError : ℝ}
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hvariance : B.partition.variance ≤ B.partition.centerEnergy) :
    ∀ q : B.RawBandGauge,
      (canonicalSlowKappa / 4) *
            anchorMass (primeWeight B.sampleData.n) anchor *
            B.partition.variance -
          rowError * B.partition.compensatedL2Sq q ≤
        primeReferenceQuadratic B.sampleData.n
          (compensatedPrimeCoefficient B.partition q) := by
  intro q
  let c : BandPrime B.sampleData.n B.sampleData.W → ℝ :=
    compensatedPrimeCoefficient B.partition q
  let mu : ℝ := anchorMean B.sampleData.n anchor c
  have hdistance : B.partition.variance / 2 ≤
      primePhysicalDistance B.sampleData.n c mu :=
    half_variance_le_primePhysicalDistance_compensated B.partition
      B.n_gt_one q mu hvariance
  have hcoef : 0 ≤ (canonicalSlowKappa / 2) *
      anchorMass (primeWeight B.sampleData.n) anchor :=
    mul_nonneg (div_nonneg canonicalSlowKappa_pos.le (by norm_num)) hmass.le
  have hscaled := mul_le_mul_of_nonneg_left hdistance hcoef
  have henergyLower :
      (canonicalSlowKappa / 4) *
            anchorMass (primeWeight B.sampleData.n) anchor *
            B.partition.variance ≤
        dirichletEnergy (primeWeight B.sampleData.n)
          (primeKernel B.sampleData.n) (dirichletCoordinate B.sampleData.n c) := by
    calc
      (canonicalSlowKappa / 4) *
            anchorMass (primeWeight B.sampleData.n) anchor *
            B.partition.variance =
          ((canonicalSlowKappa / 2) *
            anchorMass (primeWeight B.sampleData.n) anchor) *
              (B.partition.variance / 2) := by ring
      _ ≤ ((canonicalSlowKappa / 2) *
            anchorMass (primeWeight B.sampleData.n) anchor) *
              primePhysicalDistance B.sampleData.n c mu := hscaled
      _ ≤ dirichletEnergy (primeWeight B.sampleData.n)
            (primeKernel B.sampleData.n)
            (dirichletCoordinate B.sampleData.n c) :=
        canonicalSlowKappa_primeDirichlet_anchor_lower B.n_gt_one
          anchor hinterior hmass c
  have hresAbs := abs_primeRowResidualContribution_le
    B.partition B.n_gt_one q hrow
  have hresLower :
      -(rowError * B.partition.compensatedL2Sq q) ≤
        ∑ p, primeWeight B.sampleData.n p *
          rowResidual (primeWeight B.sampleData.n)
              (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p *
            (dirichletCoordinate B.sampleData.n c p) ^ 2 :=
    neg_le_of_abs_le (by simpa only [c] using hresAbs)
  rw [primeReferenceQuadratic_eq_dirichlet_add_residual B.n_gt_one c]
  linarith

end Erdos390.Full.PaperCanonicalSlowKappa

namespace Erdos390.Full.PaperBridgeFit.BridgeData

open ArithmeticModel ArithmeticBandGeometry
open ConditionedPoissonLimit OmittedTiltPairChamber
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open PaperSquarefreeSlowQuadraticLower PaperPrimePowerChamberError
open PaperWeightedInverseExport FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference PrimePowerCovariance
open PaperCanonicalSlowKappa

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Exact actual squarefree lower with the globally fixed
`canonicalSlowKappa`. -/
theorem actualSquarefree_compensated_lower_canonicalKappa_of_profiles
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    {rowError : ℝ}
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hvariance : B.partition.variance ≤ B.partition.centerEnergy)
    {Eprofile CKernel : ℝ} (hEprofile : 0 ≤ Eprofile)
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
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |covarianceKernel (tPrime B.sampleData.n p)
          (tPrime B.sampleData.n p)| ≤ CKernel) :
    (canonicalSlowKappa / 4) *
          anchorMass (primeWeight B.sampleData.n) anchor *
          B.partition.variance -
        rowError * B.partition.compensatedL2Sq q -
        ((4 * pairCovarianceScale Eprofile) *
            B.partition.compensatedL1 q ^ 2 +
          (2 * Eprofile) * B.partition.compensatedL2Sq q +
          ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
            CKernel) *
            weightedL2SqSecond reciprocalWeight
              (compensatedPrimeCoefficient B.partition q)) ≤
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) := by
  let c : BandPrime B.sampleData.n B.sampleData.W → ℝ :=
    compensatedPrimeCoefficient B.partition q
  have hentry := B.actual_squarefree_reference_entry_bound_of_profiles
    xi hEprofile hpair hsingle hKernel
  have herror := abs_subtypeSquarefreeQuadratic_sub_primeReference_le
    (B.actualValuationLaw xi) c hentry
  have herror' :
      |subtypeSquarefreeQuadratic (B.actualValuationLaw xi) c -
          primeReferenceQuadratic B.sampleData.n c| ≤
        (4 * pairCovarianceScale Eprofile) *
            B.partition.compensatedL1 q ^ 2 +
          (2 * Eprofile) * B.partition.compensatedL2Sq q +
          ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
            CKernel) * weightedL2SqSecond reciprocalWeight c := by
    simpa only [c, weightedL1_compensated_eq,
      weightedL2Sq_compensated_eq] using herror
  have hlower := neg_le_of_abs_le herror'
  rw [B.subtypeSquarefreeQuadratic_actual_eq_covariance xi q] at hlower
  have href := canonicalSlowKappa_primeReference_compensated_lower
    B anchor hinterior hmass hrow hvariance q
  linarith

/-- Relative `w²` form of the preceding fixed-`kappa` lower. -/
theorem actualSquarefree_relative_lower_canonicalKappa_of_profiles
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w rowError Eprofile CKernel anchorFloor : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w)
    (hrowError : 0 ≤ rowError) (hEprofile : 0 ≤ Eprofile)
    (hCKernel : 0 ≤ CKernel) (hW : 0 < B.sampleData.W)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hvarLower : w ^ 2 / 16 ≤ B.partition.variance)
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
      |covarianceKernel (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n r.1)| ≤ CKernel) :
    PaperBridgeFit.BridgeData.actualSquarefreeLowerConstant
        canonicalSlowKappa anchorFloor rowError Eprofile CKernel C K
          (1 / (B.sampleData.W : ℝ)) * w ^ 2 ≤
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
    simpa only [CL1, PaperBridgeFit.BridgeData.slowL1Constant] using
      hthree.2.1
  have hL2 : B.partition.compensatedL2Sq q ≤ CL2 * w ^ 2 := by
    simpa only [CL2, PaperBridgeFit.BridgeData.slowL2Constant] using
      hthree.2.2
  have hCL1 : 0 ≤ CL1 := by
    dsimp only [CL1, PaperBridgeFit.BridgeData.slowL1Constant]
    positivity
  have hCL2 : 0 ≤ CL2 := by
    dsimp only [CL2, PaperBridgeFit.BridgeData.slowL2Constant]
    positivity
  have hL1nonneg : 0 ≤ B.partition.compensatedL1 q := by
    unfold ArithmeticBandGeometry.Partition.compensatedL1
    exact Finset.sum_nonneg fun p hp ↦
      mul_nonneg (by positivity) (abs_nonneg _)
  have hL1Sq : B.partition.compensatedL1 q ^ 2 ≤ CL1 ^ 2 * w ^ 2 := by
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
      anchorFloor * (w ^ 2 / 16) ≤
        anchorMass (primeWeight B.sampleData.n) anchor *
          B.partition.variance :=
    mul_le_mul hAnchorMass hvarLower (by positivity) hmass.le
  have hmain := mul_le_mul_of_nonneg_left hmassvar hk4
  have hmain' :
      (canonicalSlowKappa * anchorFloor / 64) * w ^ 2 ≤
        (canonicalSlowKappa / 4) *
          anchorMass (primeWeight B.sampleData.n) anchor *
            B.partition.variance := by
    calc
      (canonicalSlowKappa * anchorFloor / 64) * w ^ 2 =
          (canonicalSlowKappa / 4) * (anchorFloor * (w ^ 2 / 16)) := by
        ring
      _ ≤ (canonicalSlowKappa / 4) *
          (anchorMass (primeWeight B.sampleData.n) anchor *
            B.partition.variance) := hmain
      _ = _ := by ring
  have heOff : 0 ≤ eOff := by
    dsimp only [eOff]
    exact mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hEprofile)
  have heDiag : 0 ≤ eDiag := by dsimp only [eDiag]; positivity
  have heSecond : 0 ≤ eSecond := by
    dsimp only [eSecond, PaperBridgeFit.BridgeData.signedSecondConstant]
    positivity
  have hrowLoss := mul_le_mul_of_nonneg_left hL2 hrowError
  have hoffLoss := mul_le_mul_of_nonneg_left hL1Sq heOff
  have hdiagLoss := mul_le_mul_of_nonneg_left hL2 heDiag
  have hsecondLoss := mul_le_mul_of_nonneg_left hSecond heSecond
  have htarget :
      actualSquarefreeLowerConstant canonicalSlowKappa anchorFloor
          rowError Eprofile CKernel C K invW * w ^ 2 ≤
        (canonicalSlowKappa / 4) *
              anchorMass (primeWeight B.sampleData.n) anchor *
              B.partition.variance -
          rowError * B.partition.compensatedL2Sq q -
          (eOff * B.partition.compensatedL1 q ^ 2 +
            eDiag * B.partition.compensatedL2Sq q +
            eSecond * weightedL2SqSecond reciprocalWeight
              (compensatedPrimeCoefficient B.partition q)) := by
    change (canonicalSlowKappa * anchorFloor / 64 - rowError * CL2 -
        eOff * CL1 ^ 2 - eDiag * CL2 - eSecond * invW * CL2) * w ^ 2 ≤ _
    nlinarith [hmain', hrowLoss, hoffLoss, hdiagLoss, hsecondLoss]
  simpa only [invW] using htarget.trans hlowerExact

end Erdos390.Full.PaperBridgeFit.BridgeData

end
