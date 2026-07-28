import Erdos390.Full.PaperActualFastMarkedRowProfiles

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- Expanded statement audit: this wrapper independently restates every
hypothesis and the complete conclusion of the ordinary-fast component row. -/
theorem audit_nuisanceResidual_bandRegression_markedRow
    (B : BridgeData Head Band) [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge)
    {H K Eprofile CF Cprod R Cmarked : ℝ}
    (hH0 : 0 ≤ H) (hCmarked : 0 ≤ Cmarked)
    (hEprofile : 0 ≤ Eprofile) (hCprod : 0 ≤ Cprod)
    (hW : 0 < B.sampleData.W)
    (hH : (∑ j : Band, B.harmonicMass j) ≤ H)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
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
    (hKernelProduct : ∀ r s : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n r.1)
          (tPrime B.sampleData.n s.1)| ≤
        Cprod * tPrime B.sampleData.n r.1 * tPrime B.sampleData.n s.1)
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
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))| ≤
      ((Cprod * K + CF) +
          ((4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
              H + 2 * Eprofile +
            ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
              Cprod) * (1 / (B.sampleData.W : ℝ))) + R +
          (((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
                (Cmarked * H)) / gamma) *
            (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              Cmarked))) * ‖q‖ * (1 / (p : ℝ)) := by
  exact B.nuisanceResidual_bandRegression_markedRow_le_of_profiles
    xi hgamma hgap q hH0 hCmarked hEprofile hCprod hW hH hbandT
      hpair hsingle hF hKernelProduct hrow hmarked hp

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
