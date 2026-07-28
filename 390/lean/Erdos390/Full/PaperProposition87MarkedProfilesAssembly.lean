import Erdos390.Full.PaperActualFastMarkedRowProfiles
import Erdos390.Full.PaperActualCompensatedMarkedRowProfiles
import Erdos390.Full.PaperProposition87MarkedTwoStage

/-!
# Proposition 8.7 marked row from literal profile inputs

This file composes the two independently proved component rows with the
exact two-stage Schur solve.  In particular, neither component marked row
nor the marked row of the ODE vector field is assumed.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Constant in the ordinary-fast marked row before applying the ordinary
inverse to the projected target. -/
def fastProfilesMarkedConstant
    (dimension H K Eprofile CF Cprod R Cmarked gamma invW : ℝ) : ℝ :=
  (Cprod * K + CF) +
    ((4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) * H +
      2 * Eprofile +
      ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 + Cprod) *
        invW) + R +
    ((dimension * (Cmarked * H)) / gamma) * (dimension * Cmarked)

/-- Constant in the compensated-slow marked row after factoring out
`w / p`. -/
def slowProfilesMarkedConstant
    (dimension C K R Eprofile CF CKernel Cmarked gamma invW : ℝ) : ℝ :=
  actualSquarefreeMarkedConstant C K Eprofile CF CKernel invW +
    (1 + C) * R +
    ((dimension * (Cmarked * (7 + C * K))) / gamma) *
      (dimension * Cmarked)

/-- Literal finite marked-row conclusion for the Proposition 8.7 vector
field.  The only inputs are the analytic profile/kernel/prime-power rows,
the two inverse/target estimates, and the exact covariance gaps. -/
theorem vectorField_markedRow_le_of_profiles_and_weightedRow
    [Nonempty Head] [Nonempty Band]
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
    (hCinvOrd : 0 ≤ CinvOrd)
    (hCreg : 0 ≤ Creg)
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
  let dimension : ℝ :=
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let CfastBase : ℝ := fastProfilesMarkedConstant dimension H K Eprofile
    CF Cprod R Cmarked gammaNuisance (1 / (B.sampleData.W : ℝ))
  let Cslow : ℝ := slowProfilesMarkedConstant dimension Creg K R
    Eprofile CF CKernel Cmarked gammaNuisance
      (1 / (B.sampleData.W : ℝ))
  let qFast := e.symm (B.projectedNormalizedTargetBand Delta)
  let qSlow := B.actualBandRegression xi hgammaNuisance hGamma e
  have hpairScale :=
    PaperPrimePowerChamberError.pairCovarianceScale_nonneg hEprofile
  have hCfastBase : 0 ≤ CfastBase := by
    dsimp only [CfastBase, fastProfilesMarkedConstant, dimension]
    positivity
  have hqFast : ‖qFast‖ ≤ CinvOrd * Tband := by
    calc
      ‖qFast‖ ≤ CinvOrd * ‖B.projectedNormalizedTargetBand Delta‖ :=
        hinvOrd _
      _ ≤ CinvOrd * Tband :=
        mul_le_mul_of_nonneg_left htargetBand hCinvOrd
  have hfastRaw :=
    B.nuisanceResidual_bandRegression_markedRow_le_of_profiles
      xi hgammaNuisance hGamma qFast hH0 hCmarked hEprofile hCprod
        hW hH hbandT hpair hsingle hF hKernelProduct hrow hmarked hp
  have hfast :
      |(B.tiltedLaw xi).covariance (B.markedValuation p)
        (B.nuisanceResidualScore xi hgammaNuisance hGamma
          (B.bandRegressionScore qFast))| ≤
        (CfastBase * (CinvOrd * Tband)) * (1 / (p : ℝ)) := by
    have hscale : CfastBase * ‖qFast‖ * (1 / (p : ℝ)) ≤
        CfastBase * (CinvOrd * Tband) * (1 / (p : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hqFast hCfastBase) (by positivity)
    have hraw :
        |(B.tiltedLaw xi).covariance
          (fun m ↦ valuation p (B.sampleData.value m))
          (B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore qFast))| ≤
          CfastBase * ‖qFast‖ * (1 / (p : ℝ)) := by
      simpa only [CfastBase, dimension, fastProfilesMarkedConstant] using
        hfastRaw
    simpa only [markedValuation] using hraw.trans hscale
  have hslowRaw :=
    B.actualCompensatedScore_markedRow_bound_of_profiles_and_weightedRow
      xi qSlow hCreg hK B.w_pos.le hEprofile hCF hCKernel hCmarked
        hW hsharp hbandT hdevSup hdevL1 hdevL2 hgammaNuisance hGamma
        hpair hsingle hF hKernel hrow hmarked hp
  have hslow :
      |(B.tiltedLaw xi).covariance (B.markedValuation p)
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e)| ≤
        (Cslow * (1 / (p : ℝ))) * B.w := by
    have hraw :
        |(B.tiltedLaw xi).covariance
          (fun m ↦ valuation p (B.sampleData.value m))
          (B.actualCompensatedScore xi hgammaNuisance hGamma qSlow)| ≤
          (Cslow * (1 / (p : ℝ))) * B.w := by
      calc
        _ ≤ actualSquarefreeMarkedConstant Creg K Eprofile CF CKernel
              (1 / (B.sampleData.W : ℝ)) * B.w * (1 / (p : ℝ)) +
            (1 + Creg) * B.w * R * (1 / (p : ℝ)) +
            (((dimension * (Cmarked * (7 + Creg * K))) /
                gammaNuisance) * (dimension * Cmarked)) * B.w *
                  (1 / (p : ℝ)) := by
          simpa only [qSlow, dimension] using hslowRaw
        _ = (Cslow * (1 / (p : ℝ))) * B.w := by
          simp only [Cslow, slowProfilesMarkedConstant]
          ring
    simpa only [markedValuation, actualTwoStageCompensatedScore, qSlow]
      using hraw
  have hassembled := B.vectorField_markedRow_le_of_twoStage_rows
    xi Delta hgammaFull hFull hgammaNuisance hGamma e he p hVlower
      hTslow hvariance htarget hfast hslow
  simpa only [qFast, CfastBase, Cslow, dimension] using hassembled

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
