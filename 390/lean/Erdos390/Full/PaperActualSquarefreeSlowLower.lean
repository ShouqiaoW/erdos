import Erdos390.Full.PaperSquarefreeSlowQuadraticLower
import Erdos390.Full.PaperActualSquarefreeReference
import Erdos390.Full.PaperActualPrimePowerRelative

/-!
# Actual squarefree slow lower from signed local profiles

The local one- and two-divisor profiles are first assembled through the
literal sigma mixture, so between-cell covariance is retained.  The resulting
signed entry estimate is then combined with the finite prime Dirichlet lower
from `PaperSquarefreeSlowQuadraticLower`.  Thus the genuine squarefree
variance lower is a conclusion, not an analytic hypothesis.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperBridgeFit

open ArithmeticModel ArithmeticBandGeometry
open FiniteProbability OmittedTiltPairChamber
open PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open FixedFiniteMixturePrimePower
open PaperPrimePowerChamberError
open PaperSquarefreeSlowQuadraticLower
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference
open PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

def slowL1Constant (C K : ℝ) : ℝ := 7 + C * K

def slowL2Constant (C K : ℝ) : ℝ := 2 * (4 + C ^ 2 * K)

def signedSecondConstant (Eprofile CKernel : ℝ) : ℝ :=
  (1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 + CKernel

def actualSquarefreeLowerConstant
    (kappa anchorFloor rowError Eprofile CKernel C K invW : ℝ) : ℝ :=
  kappa * anchorFloor / 64 -
    rowError * slowL2Constant C K -
    (4 * pairCovarianceScale Eprofile) * slowL1Constant C K ^ 2 -
    (2 * Eprofile) * slowL2Constant C K -
    signedSecondConstant Eprofile CKernel * invW * slowL2Constant C K

def actualSquarefreeUpperConstant
    (Eprofile CF CKernel C K invW : ℝ) : ℝ :=
  (CKernel + 4 * pairCovarianceScale Eprofile) * slowL1Constant C K ^ 2 +
    (CF + 2 * Eprofile) * slowL2Constant C K +
    signedSecondConstant Eprofile CKernel * invW * slowL2Constant C K

/-- Local signed profiles imply the literal actual-law entry comparison.
The proof passes through the exact sigma mixture, so it includes all
between-component covariance terms. -/
theorem actual_squarefree_reference_entry_bound_of_profiles
    [Nonempty Head]
    (xi : B.ParamSpace)
    {Eprofile CKernel : ℝ} (hEprofile : 0 ≤ Eprofile)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p q 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p q 1 1)| ≤
        Eprofile * pairWeight p q 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel) :
    ∀ p r : BandPrime B.sampleData.n B.sampleData.W,
      |(B.actualValuationLaw xi).covII p.1 r.1 -
          squarefreeReferenceEntry B.sampleData.n p.1 r.1| ≤
        (4 * pairCovarianceScale Eprofile) *
            reciprocalWeight p * reciprocalWeight r +
          if p = r then
            (2 * Eprofile) * reciprocalWeight p +
              ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                CKernel) * reciprocalWeight p ^ 2
          else 0 := by
  let weight := tiltedSigmaWeight B.baselineCellProbability
    B.guardedCellProbability (B.scaledBridgeScore xi)
  have hraw :=
    sigmaMixture_squarefree_reference_entry_bound_of_squarefree_profiles
      hEprofile weight (B.actualComponentValuationLaw xi)
      B.n_gt_one hpair hsingle hKernel
  have hlaw := B.sigmaMixture_actualComponentValuationLaw_eq_actualValuationLaw xi
  dsimp only at hlaw
  rw [hlaw] at hraw
  intro p r
  have hpR : (p.1 : ℝ) ≠ 0 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).ne_zero
  have hrR : (r.1 : ℝ) ≠ 0 := by
    exact_mod_cast (prime_of_mem_primeBand r.2).ne_zero
  unfold reciprocalWeight
  convert hraw p r using 1
  split_ifs <;> field_simp [hpR, hrR]

/-- The subtype-indexed squarefree quadratic is exactly the covariance of
the paper's literal post-band squarefree score. -/
theorem subtypeSquarefreeQuadratic_actual_eq_covariance
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) :
    subtypeSquarefreeQuadratic (B.actualValuationLaw xi)
        (compensatedPrimeCoefficient B.partition q) =
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) := by
  let cNat : ℕ → ℝ := B.actualCompensatedNatCoefficient q
  have hquad := (B.actualQuadratics_eq_covariances xi q).2
  change PaperPrimePowerRelativeQuadratic.squarefreeQuadratic
      (B.actualValuationLaw xi)
      (primeBand B.sampleData.n B.sampleData.W) cNat = _ at hquad
  rw [← hquad]
  unfold subtypeSquarefreeQuadratic matrixQuadratic
    PaperPrimePowerRelativeQuadratic.squarefreeQuadratic
  have houter := Finset.sum_attach
    (primeBand B.sampleData.n B.sampleData.W)
    (fun p ↦ ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
      cNat p * cNat r * (B.actualValuationLaw xi).covII p r)
  rw [← houter]
  apply Finset.sum_congr rfl
  intro p hp
  have hinner := Finset.sum_attach
    (primeBand B.sampleData.n B.sampleData.W)
    (fun r ↦ cNat p.1 * cNat r *
      (B.actualValuationLaw xi).covII p.1 r)
  rw [← hinner]
  apply Finset.sum_congr rfl
  intro r hr
  dsimp only [cNat]
  unfold compensatedPrimeCoefficient
  rw [B.actualCompensatedNatCoefficient_of_mem q p.2]
  rw [B.actualCompensatedNatCoefficient_of_mem q r.2]
  rw [B.partition_compensatedCoefficient_eq q p]
  rw [B.partition_compensatedCoefficient_eq q r]

/-- Exact actual squarefree lower.  The displayed losses are respectively
the finite row residual, off-diagonal signed-profile error, first-order
diagonal error, and second-reciprocal diagonal error. -/
theorem exists_actualSquarefree_compensated_lower_of_profiles
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Set.Icc epsilon (1 - epsilon))
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
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel) :
    ∃ kappa : ℝ, 0 < kappa ∧
      (kappa / 4) * anchorMass (primeWeight B.sampleData.n) anchor *
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
  obtain ⟨kappa, hkappa, href⟩ :=
    exists_primeReference_compensated_lower B.partition B.n_gt_one
      hepsilon hhalf anchor hinterior hmass hrow hvariance
  refine ⟨kappa, hkappa, ?_⟩
  let c : BandPrime B.sampleData.n B.sampleData.W → ℝ :=
    compensatedPrimeCoefficient B.partition q
  have hentry := B.actual_squarefree_reference_entry_bound_of_profiles
    xi hEprofile hpair hsingle hKernel
  have herror :=
    abs_subtypeSquarefreeQuadratic_sub_primeReference_le
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
  have href' := href q
  linarith

/-- Matching actual squarefree upper bound from the same signed profiles.
No positivity shortcut is used: the reference form and the signed transfer
error are bounded separately. -/
theorem actualSquarefree_compensated_upper_of_profiles
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {Eprofile CF CKernel : ℝ} (hEprofile : 0 ≤ Eprofile)
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
          (tPrime B.sampleData.n p.1) (tPrime B.sampleData.n r.1)| ≤ CKernel) :
    (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) ≤
      CKernel * B.partition.compensatedL1 q ^ 2 +
        CF * B.partition.compensatedL2Sq q +
        (4 * pairCovarianceScale Eprofile) *
            B.partition.compensatedL1 q ^ 2 +
        (2 * Eprofile) * B.partition.compensatedL2Sq q +
        ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
          CKernel) * weightedL2SqSecond reciprocalWeight
            (compensatedPrimeCoefficient B.partition q) := by
  let c : BandPrime B.sampleData.n B.sampleData.W → ℝ :=
    compensatedPrimeCoefficient B.partition q
  have hentry := B.actual_squarefree_reference_entry_bound_of_profiles
    xi hEprofile hpair hsingle (fun p hp ↦ hKernel ⟨p, hp⟩ ⟨p, hp⟩)
  have herror :=
    abs_subtypeSquarefreeQuadratic_sub_primeReference_le
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
  have htransfer := le_of_abs_le herror'
  have href := abs_primeReferenceQuadratic_le c hF hKernel
  have hrefUpper :
      primeReferenceQuadratic B.sampleData.n c ≤
        CKernel * B.partition.compensatedL1 q ^ 2 +
          CF * B.partition.compensatedL2Sq q := by
    have hleabs : primeReferenceQuadratic B.sampleData.n c ≤
        |primeReferenceQuadratic B.sampleData.n c| := le_abs_self _
    have href' :
        |primeReferenceQuadratic B.sampleData.n c| ≤
          CKernel * B.partition.compensatedL1 q ^ 2 +
            CF * B.partition.compensatedL2Sq q := by
      simpa only [c, weightedL1_compensated_eq,
        weightedL2Sq_compensated_eq] using href
    exact hleabs.trans href'
  rw [B.subtypeSquarefreeQuadratic_actual_eq_covariance xi q] at htransfer
  dsimp only [c] at htransfer hrefUpper ⊢
  linarith

set_option maxHeartbeats 2000000 in
/-- Relative `w²` squarefree bounds with every constant displayed.  The
moving-low diagonal is paid at the sharp `1/W` scale, and the positive main
term uses the literal arithmetic variance lower `w²/16`. -/
theorem exists_actualSquarefree_compensated_bounds_of_profiles
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w rowError Eprofile CF CKernel anchorFloor : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w)
    (hrowError : 0 ≤ rowError) (hEprofile : 0 ≤ Eprofile)
    (hCF : 0 ≤ CF) (hCKernel : 0 ≤ CKernel)
    (hW : 0 < B.sampleData.W)
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
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Set.Icc epsilon (1 - epsilon))
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
    (hF : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n p.1)| ≤ CF)
    (hKernel : ∀ p r : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p.1) (tPrime B.sampleData.n r.1)| ≤ CKernel) :
    ∃ kappa : ℝ, 0 < kappa ∧
      actualSquarefreeLowerConstant kappa anchorFloor rowError Eprofile
          CKernel C K (1 / (B.sampleData.W : ℝ)) * w ^ 2 ≤
        (B.tiltedLaw xi).covariance
          (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) ∧
      (B.tiltedLaw xi).covariance
          (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) ≤
        actualSquarefreeUpperConstant Eprofile CF CKernel C K
          (1 / (B.sampleData.W : ℝ)) * w ^ 2 := by
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
  have hCL1 : 0 ≤ CL1 := by dsimp only [CL1, slowL1Constant]; positivity
  have hCL2 : 0 ≤ CL2 := by dsimp only [CL2, slowL2Constant]; positivity
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
  obtain ⟨kappa, hkappa, hlowerExact⟩ :=
    B.exists_actualSquarefree_compensated_lower_of_profiles xi q
      hepsilon hhalf anchor hinterior hmass hrow hvariance
      hEprofile hpair hsingle (fun p hp ↦ hKernel ⟨p, hp⟩ ⟨p, hp⟩)
  have hupperExact := B.actualSquarefree_compensated_upper_of_profiles
    xi q hEprofile hpair hsingle hF hKernel
  refine ⟨kappa, hkappa, ?_, ?_⟩
  · have hk4 : 0 ≤ kappa / 4 := div_nonneg hkappa.le (by norm_num)
    have hmassvar :
        anchorFloor * (w ^ 2 / 16) ≤
          anchorMass (primeWeight B.sampleData.n) anchor *
            B.partition.variance :=
      mul_le_mul hAnchorMass hvarLower (by positivity) hmass.le
    have hmain :
        (kappa / 4) * (anchorFloor * (w ^ 2 / 16)) ≤
          (kappa / 4) *
            (anchorMass (primeWeight B.sampleData.n) anchor *
              B.partition.variance) :=
      mul_le_mul_of_nonneg_left hmassvar hk4
    have hmain' :
        (kappa * anchorFloor / 64) * w ^ 2 ≤
          (kappa / 4) * anchorMass (primeWeight B.sampleData.n) anchor *
            B.partition.variance := by
      calc
        (kappa * anchorFloor / 64) * w ^ 2 =
            (kappa / 4) * (anchorFloor * (w ^ 2 / 16)) := by ring
        _ ≤ (kappa / 4) *
            (anchorMass (primeWeight B.sampleData.n) anchor *
              B.partition.variance) := hmain
        _ = (kappa / 4) * anchorMass (primeWeight B.sampleData.n) anchor *
            B.partition.variance := by ring
    have heOff : 0 ≤ eOff := by
      dsimp only [eOff]
      exact mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hEprofile)
    have heDiag : 0 ≤ eDiag := by dsimp only [eDiag]; positivity
    have heSecond : 0 ≤ eSecond := by
      dsimp only [eSecond, signedSecondConstant]
      positivity
    have hrowLoss := mul_le_mul_of_nonneg_left hL2 hrowError
    have hoffLoss := mul_le_mul_of_nonneg_left hL1Sq heOff
    have hdiagLoss := mul_le_mul_of_nonneg_left hL2 heDiag
    have hsecondLoss := mul_le_mul_of_nonneg_left hSecond heSecond
    have htarget :
        actualSquarefreeLowerConstant kappa anchorFloor rowError Eprofile
            CKernel C K invW * w ^ 2 ≤
          (kappa / 4) * anchorMass (primeWeight B.sampleData.n) anchor *
              B.partition.variance -
            rowError * B.partition.compensatedL2Sq q -
            (eOff * B.partition.compensatedL1 q ^ 2 +
              eDiag * B.partition.compensatedL2Sq q +
              eSecond * weightedL2SqSecond reciprocalWeight
                (compensatedPrimeCoefficient B.partition q)) := by
      change (kappa * anchorFloor / 64 - rowError * CL2 -
          eOff * CL1 ^ 2 - eDiag * CL2 - eSecond * invW * CL2) * w ^ 2 ≤ _
      nlinarith [hmain', hrowLoss, hoffLoss, hdiagLoss, hsecondLoss]
    simpa only [invW] using htarget.trans hlowerExact
  · have hCKoff : 0 ≤ CKernel + eOff := by
      dsimp only [eOff]
      exact add_nonneg hCKernel
        (mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hEprofile))
    have hCFdiag : 0 ≤ CF + eDiag := by
      dsimp only [eDiag]
      positivity
    have heSecond : 0 ≤ eSecond := by
      dsimp only [eSecond, signedSecondConstant]
      positivity
    have hfirst := mul_le_mul_of_nonneg_left hL1Sq hCKoff
    have hdiag := mul_le_mul_of_nonneg_left hL2 hCFdiag
    have hsecond := mul_le_mul_of_nonneg_left hSecond heSecond
    have htarget :
        CKernel * B.partition.compensatedL1 q ^ 2 +
            CF * B.partition.compensatedL2Sq q +
            eOff * B.partition.compensatedL1 q ^ 2 +
            eDiag * B.partition.compensatedL2Sq q +
            eSecond * weightedL2SqSecond reciprocalWeight
              (compensatedPrimeCoefficient B.partition q) ≤
          actualSquarefreeUpperConstant Eprofile CF CKernel C K invW *
            w ^ 2 := by
      change ((CKernel + eOff) * CL1 ^ 2 + (CF + eDiag) * CL2 +
        eSecond * invW * CL2) * w ^ 2 ≥ _
      nlinarith [hfirst, hdiag, hsecond]
    simpa only [invW] using hupperExact.trans htarget

end BridgeData

end Erdos390.Full.PaperBridgeFit
