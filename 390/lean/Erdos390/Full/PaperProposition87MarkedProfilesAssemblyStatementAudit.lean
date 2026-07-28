import Erdos390.Full.PaperProposition87MarkedProfilesAssembly

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- Expanded independent wrapper for the full finite marked-row splice.
Every analytic, inverse, covariance-gap, and target hypothesis is restated. -/
theorem audit_vectorField_markedRow_from_literal_profiles
    (B : BridgeData Head Band) [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (Delta : Band → ℝ)
    {gammaFull gammaNuisance : ℝ}
    (hgammaFull : 0 < gammaFull)
    (hFull : B.vectorFamily.HasCovarianceGap gammaFull xi)
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q =
      B.actualBandSchurLinearMap xi hgammaNuisance hGamma q)
    {Vlower Tslow CinvOrd Tband Creg : ℝ}
    (hVlower : 0 < Vlower) (hTslow : 0 ≤ Tslow)
    (hCinvOrd : 0 ≤ CinvOrd) (hCreg : 0 ≤ Creg)
    (hvariance : Vlower ≤
      B.actualTwoStageCompensatedVariance xi hgammaNuisance hGamma e)
    (htarget : |B.compensatedNormalizedTarget
      xi hgammaNuisance hGamma e Delta| ≤ Tslow)
    (hinvOrd : ∀ v, ‖e.symm v‖ ≤ CinvOrd * ‖v‖)
    (htargetBand : ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband)
    {H K Eprofile CF Cprod CKernel R Cmarked : ℝ}
    (hH0 : 0 ≤ H) (hK : 0 ≤ K) (hEprofile : 0 ≤ Eprofile)
    (hCF : 0 ≤ CF) (hCprod : 0 ≤ Cprod)
    (hCKernel : 0 ≤ CKernel) (hR : 0 ≤ R)
    (hCmarked : 0 ≤ Cmarked)
    (hW : 0 < B.sampleData.W)
    (hH : (∑ j : Band, B.harmonicMass j) ≤ H)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.actualBandRegression xi hgammaNuisance hGamma e) ≤ Creg * B.w)
    (hdevSup : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation r| ≤ B.w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * B.w)
    (hdevL2 : B.partition.variance ≤ 4 * B.w ^ 2)
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
    |B.vectorFamily.scalarFamily.covariance
        (B.markedValuation p)
        (fun m ↦ B.vectorFamily.scalarFamily.score m
          (B.vectorFamily.vectorField (B.targetVector Delta) xi)) xi| ≤
      (fastProfilesMarkedConstant
          (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ))
          H K Eprofile CF Cprod R Cmarked gammaNuisance
          (1 / (B.sampleData.W : ℝ)) * (CinvOrd * Tband) +
        (Tslow / Vlower) *
          (slowProfilesMarkedConstant
            (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ))
            Creg K R Eprofile CF CKernel Cmarked gammaNuisance
            (1 / (B.sampleData.W : ℝ)) * B.w)) *
        (1 / (p : ℝ)) := by
  exact B.vectorField_markedRow_le_of_profiles_and_weightedRow
    xi Delta hgammaFull hFull hgammaNuisance hGamma e he hVlower
      hTslow hCinvOrd hCreg hvariance htarget hinvOrd htargetBand hH0 hK
      hEprofile hCF hCprod hCKernel hR hCmarked hW hH hbandT hsharp
      hdevSup hdevL1 hdevL2 hpair hsingle hF hKernelProduct hKernel hrow
      hmarked hp

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
