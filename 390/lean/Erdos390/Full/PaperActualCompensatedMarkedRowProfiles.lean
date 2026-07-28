import Erdos390.Full.PaperActualSquarefreeMarkedRow
import Erdos390.Full.PaperActualLemma86Assembly
import Erdos390.Full.PaperActualPrimePowerRowTransfer

/-!
# The compensated slow marked row from literal analytic inputs

This removes two legacy contracts from the marked-row side of Lemma 8.6:
the squarefree marked row is derived from the signed divisor profiles, and
the prime-power correction is supplied by the literal weighted `VV-II` row.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance
open PaperPrimePowerRelativeQuadratic PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The explicit signed-profile constant in the squarefree marked row. -/
def actualSquarefreeMarkedConstant
    (C K Eprofile CF CKernel invW : ℝ) : ℝ :=
  (CKernel * (7 + C * K) + CF * (1 + C)) +
    (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
        (7 + C * K) +
      (2 * Eprofile) * (1 + C) +
      ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
          CKernel) * (1 + C) * invW

/-- Full compensated marked row, derived from the local signed profiles,
the literal weighted prime-power row, and reciprocal nuisance rows. -/
theorem actualCompensatedScore_markedRow_bound_of_profiles_and_weightedRow
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w R Eprofile CF CKernel Cmarked : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w)
    (hEprofile : 0 ≤ Eprofile) (hCF : 0 ≤ CF)
    (hCKernel : 0 ≤ CKernel) (hCmarked : 0 ≤ Cmarked)
    (hW : 0 < B.sampleData.W)
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
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (OmittedTiltPairChamber.pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (OmittedTiltPairChamber.pairPower p r 1 1)| ≤
        Eprofile * PaperPrimePowerChamberError.pairWeight p r 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
          Eprofile * PaperPrimePowerChamberError.singleWeight p 1)
    (hF : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n r.1)| ≤ CF)
    (hKernel : ∀ r s : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n r.1)
          (tPrime B.sampleData.n s.1)| ≤ CKernel)
    (hrow : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      (r.1 : ℝ) *
        ∑ s : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV r.1 s.1 -
            (B.actualValuationLaw xi).covII r.1 s.1| ≤ R)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (r : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation r.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (r.1 : ℝ)))
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ valuation p (B.sampleData.value m))
      (B.actualCompensatedScore xi hgamma hgap q)| ≤
      actualSquarefreeMarkedConstant C K Eprofile CF CKernel
          (1 / (B.sampleData.W : ℝ)) * w * (1 / (p : ℝ)) +
        (1 + C) * w * R * (1 / (p : ℝ)) +
        (((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              (Cmarked * (7 + C * K))) / gamma) *
          (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked)) * w * (1 / (p : ℝ)) := by
  have hsquarefree := B.actualSquarefreeMarkedRow_le_of_profiles
    xi q hC hw hEprofile hCF hCKernel hW hsharp hbandT hdevSup hdevL1
      hdevL2 hpair hsingle hF hKernel hp
  have hsquarefree' :
      |(B.tiltedLaw xi).covariance
          (fun m ↦ divInd p (B.sampleData.value m))
          (B.postBandSquarefreeScore q)| ≤
        actualSquarefreeMarkedConstant C K Eprofile CF CKernel
            (1 / (B.sampleData.W : ℝ)) * w * (1 / (p : ℝ)) := by
    simpa only [actualSquarefreeMarkedConstant, add_assoc] using hsquarefree
  have hpower := B.actual_primePower_relative_markedRow_bound_of_row
    xi q hC hw hsharp hbandT hdevSup hdevL1 hdevL2 hrow hp
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
          Cmarked * (1 / (p : ℝ)) := fun c ↦ hmarked c ⟨p, hp⟩
  have hmarkedZ : ‖B.nuisanceCovarianceVector xi
      (fun m ↦ valuation p (B.sampleData.value m))‖ ≤
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        Cmarked) * (1 / (p : ℝ)) := by
    have hraw := B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
      xi (fun m ↦ valuation p (B.sampleData.value m))
      (mul_nonneg hCmarked (by positivity)) hmarkedCoord
    simpa only [mul_assoc] using hraw
  have hnuisance := B.actualNuisanceCoefficient_markedRow_bound
    xi hgamma hgap q (fun m ↦ valuation p (B.sampleData.value m))
    (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg hCmarked (by positivity))) hw hcovZ hmarkedZ
  let fitted := (B.tiltedLaw xi).covariance
    (fun m ↦ valuation p (B.sampleData.value m))
    (B.actualCompensatedScore xi hgamma hgap q)
  let full := (B.tiltedLaw xi).covariance
    (fun m ↦ valuation p (B.sampleData.value m))
    (B.postBandPrimeScore q)
  let squarefree := (B.tiltedLaw xi).covariance
    (fun m ↦ divInd p (B.sampleData.value m))
    (B.postBandSquarefreeScore q)
  let nuisance := (B.tiltedLaw xi).covariance
    (fun m ↦ valuation p (B.sampleData.value m))
    (fun m ↦ inner ℝ
      (B.actualNuisanceCoefficient xi hgamma hgap q)
      (B.nuisanceStatistic m))
  have hdecomp : fitted = full - nuisance := by
    exact B.actualCompensatedScore_markedRow_decomposition
      xi hgamma hgap q p
  have hfull : |full| ≤ |full - squarefree| + |squarefree| := by
    calc
      |full| = |(full - squarefree) + squarefree| := by ring_nf
      _ ≤ |full - squarefree| + |squarefree| := abs_add_le _ _
  calc
    |fitted| = |full - nuisance| := by rw [hdecomp]
    _ ≤ |full| + |nuisance| := abs_sub _ _
    _ ≤ (|full - squarefree| + |squarefree|) + |nuisance| :=
      add_le_add hfull le_rfl
    _ ≤ ((1 + C) * w * R * (1 / (p : ℝ)) +
          actualSquarefreeMarkedConstant C K Eprofile CF CKernel
            (1 / (B.sampleData.W : ℝ)) * w * (1 / (p : ℝ))) +
        (((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              (Cmarked * (7 + C * K))) / gamma) *
          (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked)) * w * (1 / (p : ℝ)) :=
      add_le_add (add_le_add hpower hsquarefree') hnuisance
    _ = _ := by ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
