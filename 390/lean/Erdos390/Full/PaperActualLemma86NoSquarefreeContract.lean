import Erdos390.Full.PaperActualSquarefreeSlowLower
import Erdos390.Full.PaperTwoStageSlowVarianceFromLemma86

/-!
# Lemma 8.6 without a squarefree-variance contract

This is the end-to-end finite assembly of the slow variance.  Unlike the
earlier connector, it does not assume lower or upper bounds for the
squarefree score.  Those bounds are derived here from:

* a literal interior prime anchor block;
* the sharp relative discrete row residual;
* the local signed one- and two-divisor profiles;
* the explicit coefficient moment ledgers;
* Lemma 7.5's full-versus-squarefree row transfer; and
* the finite nuisance covariance gap and reciprocal marked rows.

The conclusion displays all three losses after the positive anchored
Dirichlet term: signed squarefree transfer, prime powers, and nuisance Schur
regression.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperBridgeFit

open ArithmeticModel ArithmeticBandGeometry
open FiniteProbability OmittedTiltPairChamber
open PrimePowerCovariance PaperPrimePowerLemma75
open PaperPrimePowerChamberError
open PaperSquarefreeSlowQuadraticLower
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

def actualLemma86SlowConstant
    (kappa anchorFloor rowError Eprofile CKernel C K invW
      Cpow epsilonPow Cmarked gamma : ℝ) : ℝ :=
  actualSquarefreeLowerConstant kappa anchorFloor rowError Eprofile
      CKernel C K invW -
    ((1 + C) * (7 + C * K)) * (Cpow * invW + epsilonPow) -
    (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
      (Cmarked * (7 + C * K))) ^ 2 / gamma

set_option maxHeartbeats 2000000 in
/-- Exact paper-facing Lemma 8.6 slow lower with no squarefree lower/upper
hypothesis. -/
theorem exists_actualTwoStageCompensatedVariance_lower_without_squarefree_contract
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {C K rowError Eprofile CF CKernel anchorFloor
      Cpow epsilonPow Cmarked : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hrowError : 0 ≤ rowError) (hEprofile : 0 ≤ Eprofile)
    (hCF : 0 ≤ CF) (hCKernel : 0 ≤ CKernel)
    (hCpow : 0 ≤ Cpow) (hepsilonPow : 0 ≤ epsilonPow)
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
      tPrime B.sampleData.n p.1 ∈ Set.Icc epsilonMesh (1 - epsilonMesh))
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
          (tPrime B.sampleData.n p.1) (tPrime B.sampleData.n r.1)| ≤ CKernel)
    (h75 : PrimePowerTransferBounds (B.actualValuationLaw xi)
      B.sampleData.n B.sampleData.W Cpow epsilonPow)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ))) :
    ∃ kappa : ℝ, 0 < kappa ∧
      actualLemma86SlowConstant B kappa anchorFloor rowError Eprofile
          CKernel C K (1 / (B.sampleData.W : ℝ)) Cpow epsilonPow
          Cmarked gamma * B.w ^ 2 ≤
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
      hmass hAnchorMass hrow hpair hsingle hF hKernel
  let lower := actualSquarefreeLowerConstant kappa anchorFloor rowError
    Eprofile CKernel C K (1 / (B.sampleData.W : ℝ))
  let upper := actualSquarefreeUpperConstant Eprofile CF CKernel C K
    (1 / (B.sampleData.W : ℝ))
  let gammaSlow := actualLemma86SlowConstant B kappa anchorFloor rowError
    Eprofile CKernel C K (1 / (B.sampleData.W : ℝ)) Cpow epsilonPow
    Cmarked gamma
  have hslow := B.actualTwoStageCompensatedVariance_lower_of_squarefree_and_marked
    xi hgamma hgap e hC hK hCpow hepsilonPow hCmarked
    (by simpa only [q] using hsharp) hbandT hdevSup hdevL1 hdevL2 h75
    (by simpa only [q, lower] using hsfLower)
    (by simpa only [q, upper] using hsfUpper) hmarked
    (gammaSlow := gammaSlow) (lower := lower) (upper := upper) (by
      dsimp only [gammaSlow, actualLemma86SlowConstant, lower]
      exact le_rfl)
  exact ⟨kappa, hkappa, by simpa only [gammaSlow] using hslow⟩

end BridgeData

end Erdos390.Full.PaperBridgeFit
