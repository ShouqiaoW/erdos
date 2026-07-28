import Erdos390.Full.PaperProposition87MarkedProfilesAssembly

/-!
# Uniform Proposition 8.7 marked rows on a preselected effective ball

This is the exact quantifier wrapper used by the ODE theorem.  It turns the
literal analytic inputs, uniform on a previously selected ball, into the
single marked-row estimate expected by the integration argument.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The fixed coefficient multiplying `1/p` after both stages of the exact
Schur solve have been assembled. -/
def vectorFieldProfilesMarkedConstant
    (H K Eprofile CF Cprod CKernel R Cmarked gammaNuisance
      CinvOrd Tband Tslow Vlower Creg : ℝ) : ℝ :=
  fastProfilesMarkedConstant
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ))
      H K Eprofile CF Cprod R Cmarked gammaNuisance
      (1 / (B.sampleData.W : ℝ)) * (CinvOrd * Tband) +
    (Tslow / Vlower) *
      (slowProfilesMarkedConstant
        (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ))
        Creg K R Eprofile CF CKernel Cmarked gammaNuisance
        (1 / (B.sampleData.W : ℝ)) * B.w)

theorem vectorFieldProfilesMarkedConstant_nonneg
    {H K Eprofile CF Cprod CKernel R Cmarked gammaNuisance
      CinvOrd Tband Tslow Vlower Creg : ℝ}
    (hH : 0 ≤ H) (hK : 0 ≤ K) (hEprofile : 0 ≤ Eprofile)
    (hCF : 0 ≤ CF) (hCprod : 0 ≤ Cprod)
    (hCKernel : 0 ≤ CKernel) (hR : 0 ≤ R)
    (hCmarked : 0 ≤ Cmarked) (hgamma : 0 < gammaNuisance)
    (hCinvOrd : 0 ≤ CinvOrd) (hTband : 0 ≤ Tband)
    (hTslow : 0 ≤ Tslow) (hVlower : 0 < Vlower)
    (hCreg : 0 ≤ Creg) (hW : 0 < B.sampleData.W) :
    0 ≤ B.vectorFieldProfilesMarkedConstant H K Eprofile CF Cprod
      CKernel R Cmarked gammaNuisance CinvOrd Tband Tslow Vlower Creg := by
  have hpairScale :=
    PaperPrimePowerChamberError.pairCovarianceScale_nonneg hEprofile
  have hrho := DickmanBasic.rho_U_pos
  let dimension : ℝ :=
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  have hdimension : 0 ≤ dimension := by
    dsimp only [dimension]
    positivity
  have hfast : 0 ≤ fastProfilesMarkedConstant dimension H K Eprofile
      CF Cprod R Cmarked gammaNuisance
        (1 / (B.sampleData.W : ℝ)) := by
    unfold fastProfilesMarkedConstant
    positivity
  have hsquarefree : 0 ≤ actualSquarefreeMarkedConstant Creg K Eprofile
      CF CKernel (1 / (B.sampleData.W : ℝ)) := by
    unfold actualSquarefreeMarkedConstant
    positivity
  have hslow : 0 ≤ slowProfilesMarkedConstant dimension Creg K R
      Eprofile CF CKernel Cmarked gammaNuisance
        (1 / (B.sampleData.W : ℝ)) := by
    unfold slowProfilesMarkedConstant
    positivity
  unfold vectorFieldProfilesMarkedConstant
  change 0 ≤
    fastProfilesMarkedConstant dimension H K Eprofile CF Cprod R Cmarked
        gammaNuisance (1 / (B.sampleData.W : ℝ)) *
          (CinvOrd * Tband) +
      (Tslow / Vlower) *
        (slowProfilesMarkedConstant dimension Creg K R Eprofile CF CKernel
          Cmarked gammaNuisance (1 / (B.sampleData.W : ℝ)) * B.w)
  exact add_nonneg
    (mul_nonneg hfast (mul_nonneg hCinvOrd hTband))
    (mul_nonneg (div_nonneg hTslow hVlower.le)
      (mul_nonneg hslow B.w_pos.le))

/-- Uniform marked row on the exact preselected ODE ball.  The monitored
set is explicitly required to lie in the moving prime band; fixed head
primes are handled by their exact head coordinates instead. -/
theorem uniform_vectorField_markedRow_on_effectiveBall_of_profiles
    [Nonempty Head] [Nonempty Band]
    (Delta : Band → ℝ) (a : NNReal)
    {gammaFull gammaNuisance Vlower Tslow CinvOrd Tband Creg : ℝ}
    (hgammaFull : 0 < gammaFull)
    (hgammaNuisance : 0 < gammaNuisance)
    (hVlower : 0 < Vlower) (hTslow : 0 ≤ Tslow)
    (hCinvOrd : 0 ≤ CinvOrd) (hCreg : 0 ≤ Creg)
    (hFull : ∀ z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ),
      B.vectorFamily.HasCovarianceGap gammaFull (B.effectiveParamEquiv z))
    (hGamma : ∀ z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ), ∀ v,
      gammaNuisance * ‖v‖ ^ 2 ≤ inner ℝ v
        (B.nuisanceCovarianceOperator (B.effectiveParamEquiv z) v))
    (e : ∀ (z : B.EffectiveParamSpace),
      z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
        B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ (z : B.EffectiveParamSpace)
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
      e z hz q = B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
        hgammaNuisance
        (by
          intro v
          exact hGamma z hz v) q)
    (hvariance : ∀ (z : B.EffectiveParamSpace)
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      Vlower ≤ B.actualTwoStageCompensatedVariance
        (B.effectiveParamEquiv z) hgammaNuisance
        (by intro v; exact hGamma z hz v) (e z hz))
    (htarget : ∀ (z : B.EffectiveParamSpace)
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      |B.compensatedNormalizedTarget (B.effectiveParamEquiv z)
        hgammaNuisance (by intro v; exact hGamma z hz v)
        (e z hz) Delta| ≤ Tslow)
    (hinvOrd : ∀ (z : B.EffectiveParamSpace)
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
      ‖(e z hz).symm v‖ ≤ CinvOrd * ‖v‖)
    (htargetBand : ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband)
    {H K Eprofile CF Cprod CKernel R Cmarked : ℝ}
    (hH0 : 0 ≤ H) (hK : 0 ≤ K) (hEprofile : 0 ≤ Eprofile)
    (hCF : 0 ≤ CF) (hCprod : 0 ≤ Cprod)
    (hCKernel : 0 ≤ CKernel) (hR : 0 ≤ R)
    (hCmarked : 0 ≤ Cmarked) (hW : 0 < B.sampleData.W)
    (hH : (∑ j : Band, B.harmonicMass j) ≤ H)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hsharp : ∀ (z : B.EffectiveParamSpace)
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegression (B.effectiveParamEquiv z)
          hgammaNuisance (by intro v; exact hGamma z hz v) (e z hz)) ≤
        Creg * B.w)
    (hdevSup : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation r| ≤ B.w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * B.w)
    (hdevL2 : B.partition.variance ≤ 4 * B.w ^ 2)
    (hpair : ∀ (z : B.EffectiveParamSpace)
      (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw (B.effectiveParamEquiv z) c).probability.expect
          (fun omega ↦ divInd (OmittedTiltPairChamber.pairPower p r 1 1)
            ((B.actualComponentValuationLaw
              (B.effectiveParamEquiv z) c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (OmittedTiltPairChamber.pairPower p r 1 1)| ≤
        Eprofile * PaperPrimePowerChamberError.pairWeight p r 1 1)
    (hsingle : ∀ (z : B.EffectiveParamSpace)
      (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw (B.effectiveParamEquiv z) c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw
              (B.effectiveParamEquiv z) c).value omega)) -
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
    (hrow : ∀ (z : B.EffectiveParamSpace)
      (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
      (r : BandPrime B.sampleData.n B.sampleData.W),
      (r.1 : ℝ) *
        ∑ s : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw (B.effectiveParamEquiv z)).covVV r.1 s.1 -
            (B.actualValuationLaw (B.effectiveParamEquiv z)).covII r.1 s.1| ≤ R)
    (hmarked : ∀ (z : B.EffectiveParamSpace)
      (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
      (c : NuisanceCoord B.HeadIndex)
      (r : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation r.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (r.1 : ℝ)))
    (monitoredPrimes : Finset ℕ)
    (hmonitored : ∀ p ∈ monitoredPrimes,
      p ∈ primeBand B.sampleData.n B.sampleData.W) :
    ∀ p ∈ monitoredPrimes,
      ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
        |B.vectorFamily.scalarFamily.covariance
            (B.markedValuation p)
            (fun m ↦ B.vectorFamily.scalarFamily.score m
              (B.vectorFamily.vectorField (B.targetVector Delta)
                (B.effectiveParamEquiv z)))
            (B.effectiveParamEquiv z)| ≤
          B.vectorFieldProfilesMarkedConstant H K Eprofile CF Cprod CKernel
            R Cmarked gammaNuisance CinvOrd Tband Tslow Vlower Creg /
              (p : ℝ) := by
  intro p hp z hz
  let hGapZ : ∀ v, gammaNuisance * ‖v‖ ^ 2 ≤
      inner ℝ v
        (B.nuisanceCovarianceOperator (B.effectiveParamEquiv z) v) :=
    fun v ↦ hGamma z hz v
  have hfinite := B.vectorField_markedRow_le_of_profiles_and_weightedRow
    (B.effectiveParamEquiv z) Delta hgammaFull (hFull z hz)
      hgammaNuisance hGapZ (e z hz)
      (by intro q; simpa only [hGapZ] using he z hz q)
      hVlower hTslow hCinvOrd hCreg
      (by simpa only [hGapZ] using hvariance z hz)
      (by simpa only [hGapZ] using htarget z hz)
      (hinvOrd z hz) htargetBand hH0 hK hEprofile hCF hCprod hCKernel
      hR hCmarked hW hH hbandT
      (by simpa only [hGapZ] using hsharp z hz)
      hdevSup hdevL1 hdevL2 (hpair z hz) (hsingle z hz) hF
      hKernelProduct hKernel (hrow z hz) (hmarked z hz) (hmonitored p hp)
  simpa only [vectorFieldProfilesMarkedConstant, div_eq_mul_inv, one_mul]
    using hfinite

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
