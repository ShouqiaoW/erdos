import Erdos390.Full.PaperActualCompensatedMarkedRowProfiles

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance
open PaperPrimePowerRelativeQuadratic PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- Expanded statement audit: this wrapper independently restates every
hypothesis and the complete compensated-slow marked-row conclusion. -/
theorem audit_actualCompensatedScore_markedRow
    (B : BridgeData Head Band) [Nonempty Head]
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
  exact B.actualCompensatedScore_markedRow_bound_of_profiles_and_weightedRow
    xi q hC hK hw hEprofile hCF hCKernel hCmarked hW hsharp hbandT
      hdevSup hdevL1 hdevL2 hgamma hgap hpair hsingle hF hKernel hrow
      hmarked hp

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
