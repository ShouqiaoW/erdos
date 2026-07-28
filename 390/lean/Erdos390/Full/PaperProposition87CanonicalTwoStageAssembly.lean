import Erdos390.Full.PaperCanonicalNuisanceEffectiveBall
import Erdos390.Full.PaperExactSchurFastSlowCoercivity
import Erdos390.Full.PaperExactTwoStageOrdinaryFast
import Erdos390.Full.PaperProposition87Assembly
import Erdos390.Full.PaperHeadPrimeMarkedExact

/-!
# Proposition 8.7 with canonical nuisance gap and exact two-stage solve

This is the finite terminal assembly after removing the abstract nuisance
gap, main Schur gap, and the three solution-component hypotheses from the
older exact-Schur interface.  The remaining quantitative inputs are the
literal uniform analytic estimates: the ordinary raw-sup inverse used for
the fast target, the sharp weighted inverse used for slow regression,
compensated slow variance, the slow-column and target/nuisance rows, and
the marked row.  The two inverse estimates concern the same Schur
equivalence; they are deliberately kept separate because the moving low
cell prevents one from deriving the ordinary estimate from the sharp one.
Both first-stage regression and nuisance-coefficient bounds are derived.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PaperGuardCensus
open PaperWeightedInverseExport
open MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Fully specialized finite assembly.  The explicit speed comparisons are
algebraic choices of the preselected ODE radius; they are not analytic
conclusions about the unknown path. -/
theorem exists_physicallyCenteredFixedPartitionFit_of_canonicalTwoStageOutputs
    [Nonempty Head] [Nonempty Band]
    {Fixed : Type*} [Fintype Fixed]
    (I : PhysicalIntervals) {U : ℝ}
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhiIntervals : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (T : BarycentricTarget B.sampleData)
    (hbaseline : B.baseline = T.baseline)
    (hW : 1 < B.sampleData.W)
    (hcompat : B.HasPrimeLogCompatibility)
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W)
    (Delta : Band → ℝ)
    (a speed : NNReal)
    {Cinv CinvOrd gammaSlow CrightRow Tband TslowCoord Ccomp
      CfastNuisance CslowNuisance : ℝ}
    (hCinv : 0 < Cinv) (hCinvOrd : 0 ≤ CinvOrd)
    (hgammaSlow : 0 < gammaSlow)
    (hCrightRow : 0 ≤ CrightRow) (hTband : 0 ≤ Tband)
    (hTslowCoord : 0 ≤ TslowCoord) (hCcomp : 0 ≤ Ccomp)
    (e : ∀ (z : B.EffectiveParamSpace),
      z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
        B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
      e z hz q =
        B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
          (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
          (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
            hlowerOne hupperU hlo hhiIntervals T hbaseline
            hW z hz) q)
    (hinv : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) ((e z hz).symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (hinvOrd : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
      ‖(e z hz).symm v‖ ≤ CinvOrd * ‖v‖)
    (hslowVariance : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      gammaSlow * B.w ^ 2 ≤
        B.actualTwoStageCompensatedVariance (B.effectiveParamEquiv z)
          (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
          (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
            hlowerOne hupperU hlo hhiIntervals T hbaseline
            hW z hz) (e z hz))
    (hregRightRow : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) j,
      |B.normalizedBandCovarianceRow (B.effectiveParamEquiv z)
        (B.nuisanceResidualScore (B.effectiveParamEquiv z)
          (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
          (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
            hlowerOne hupperU hlo hhiIntervals T hbaseline
            hW z hz) B.slowScore) j| ≤
        (CrightRow * B.w) * B.bandCenter j)
    (htargetBand : ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband)
    (htargetSlowCoord :
      |B.mainPart (B.normalizedTarget Delta) MainCoord.slow| ≤
        TslowCoord)
    (hcomp : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
        (p : BandPrime B.sampleData.n B.sampleData.W),
      |B.actualCompensatedCoefficient
        (B.actualBandRegression (B.effectiveParamEquiv z)
          (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
          (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
            hlowerOne hupperU hlo hhiIntervals T hbaseline
            hW z hz) (e z hz)) p| ≤ Ccomp)
    (hfastNuisanceRow : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      ‖B.nuisanceCovarianceVector (B.effectiveParamEquiv z)
        (B.bandRegressionScore
          ((e z hz).symm (B.projectedNormalizedTargetBand Delta)))‖ ≤
        B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T *
          CfastNuisance)
    (hslowNuisanceRow : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      ‖B.nuisanceCovarianceVector (B.effectiveParamEquiv z)
        (B.postBandPrimeScore
          (B.actualBandRegression (B.effectiveParamEquiv z)
            (B.canonicalEffectiveNuisanceGamma_pos I U
              (3 * (a : ℝ)) T)
            (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
              hlowerOne hupperU hlo hhiIntervals T hbaseline
              hW z hz) (e z hz)))‖ ≤
        B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T *
          CslowNuisance)
    (hspeedPrime : CinvOrd * Tband +
      (B.twoStageCompensatedTargetBoundOrdinaryFast
          (Cinv * (2 * CrightRow)) Tband TslowCoord /
          (gammaSlow * B.w ^ 2)) * Ccomp ≤ (speed : ℝ))
    (hspeedNuisance : CfastNuisance +
      (B.twoStageCompensatedTargetBoundOrdinaryFast
          (Cinv * (2 * CrightRow)) Tband TslowCoord /
          (gammaSlow * B.w ^ 2)) * CslowNuisance ≤ (speed : ℝ))
    (hspeedSlow : B.w *
      (B.twoStageCompensatedTargetBoundOrdinaryFast
          (Cinv * (2 * CrightRow)) Tband TslowCoord /
          (gammaSlow * B.w ^ 2)) ≤ (speed : ℝ))
    (hmargin : speed ≤ a)
    (monitoredPrimes : Finset ℕ)
    (Crow : ℝ) (hCrow : 0 ≤ Crow)
    (hmarkedRow : ∀ p ∈ monitoredPrimes,
      ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
        |B.vectorFamily.scalarFamily.covariance
            (B.markedValuation p)
            (fun m => B.vectorFamily.scalarFamily.score m
              (B.vectorFamily.vectorField (B.targetVector Delta)
                (B.effectiveParamEquiv z)))
            (B.effectiveParamEquiv z)| ≤ Crow / (p : ℝ))
    (markedTarget : ℕ → ℝ)
    (N Cinitial Cmass : ℝ)
    (hprimePos : ∀ p ∈ monitoredPrimes, 0 < p)
    (hqMass : B.q ≤ Cmass * N)
    (hinitialMarked : ∀ p ∈ monitoredPrimes,
      |markedTarget p - B.paperMoment (B.markedValuation p) 0| ≤
        Cinitial * N / ((p : ℝ) * B.L))
    (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ)
    (quota : ℤ)
    (hquota : (quota : ℝ) = (∑ f, fixedWeight f) + B.q)
    {C Cfixed Cactive : ℝ}
    (hC : 1 ≤ C)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hfrozenFeasible : ∀ x,
      frozenAmbientWeight fixedValue fixedWeight x ∈ Set.Icc (0 : ℝ) 1)
    (hfrozenLedger : ∀ m : B.sampleData.Sample,
      frozenAmbientWeight fixedValue fixedWeight
        (B.sampleData.value m) ≤ Cfixed / B.L)
    (hactiveLedger : ∀ m : B.sampleData.Sample,
      B.baseline.baseWeight m ≤ Cactive / B.L)
    (hlarge : Cfixed +
      Real.exp (2 *
        ((PaperStatisticNorm.valuationLogCoefficient C B.sampleData.W +
          B.nuisanceStatisticCoefficient C) * (3 * (a : ℝ)))) *
            Cactive ≤ B.L) :
    ∃ path : ℝ → B.ParamSpace,
      path 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        B.effectiveParamEquiv.symm (path t) ∈
          closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        B.paperEffectiveSize (path t) ≤ 3 * (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path
          (B.vectorFamily.vectorField (B.targetVector Delta) (path t))
          (Icc (0 : ℝ) 1) t) ∧
      (∀ j : Band,
        B.paperMoment (B.bandScore j) (path 1) =
          B.paperMoment (B.bandScore j) 0 + Delta j) ∧
      B.paperMoment B.physicalScore (path 1) =
        B.paperMoment B.physicalScore 0 ∧
      B.paperMoment B.ordinaryLogScore (path 1) =
        B.paperMoment B.ordinaryLogScore 0 ∧
      (∀ h : B.HeadIndex,
        B.paperMoment (B.headIndicator h.1) (path 1) =
          B.paperMoment (B.headIndicator h.1) 0) ∧
      (∀ p : ℕ, p.Prime → p ≤ B.sampleData.W →
        B.paperMoment (B.markedValuation p) (path 1) =
          B.paperMoment (B.markedValuation p) 0) ∧
      B.paperMoment B.primeLogScore (path 1) =
        B.paperMoment B.primeLogScore 0 ∧
      (∀ p ∈ monitoredPrimes,
        |markedTarget p - B.paperMoment (B.markedValuation p) (path 1)| ≤
          (Cinitial + Cmass * Crow) * N / ((p : ℝ) * B.L)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℕ,
        B.ambientCombinedWeight
            (frozenAmbientWeight fixedValue fixedWeight) (path t) x ∈
          Set.Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ f : Fixed,
        B.combinedWeight fixedWeight (path t) (Sum.inl f) =
          B.combinedWeight fixedWeight 0 (Sum.inl f)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        (∑ m : B.sampleData.Sample,
          B.activeCoordinateWeight (path t) m) = B.q) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        (∑ x : Fixed ⊕ B.sampleData.Sample,
          B.combinedWeight fixedWeight (path t) x) = (quota : ℝ)) := by
  let gammaNuisance :=
    B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
  let Creg := Cinv * (2 * CrightRow)
  let gammaFast :=
    rawDLowerWeight B.harmonicMass B.bandCenter ^ 2 /
      (sharpWeightTotal B.harmonicMass B.bandCenter * Cinv)
  let gammaMain := min gammaFast gammaSlow /
    (1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2))
  have hgammaNuisance : 0 < gammaNuisance := by
    exact B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
  have hgammaFast : 0 < gammaFast := by
    dsimp only [gammaFast]
    exact div_pos
      (sq_pos_of_pos (rawDLowerWeight_pos B.harmonicMass B.bandCenter
        B.harmonicMass_pos
        (B.partition.center_ne_zero B.n_gt_one)))
      (mul_pos B.sharpBandWeightTotal_pos hCinv)
  have hcoordDen : 0 <
      1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2) := by
    have hg := B.gaugeCenterSquareSum_nonneg
    positivity
  have hgammaMain : 0 < gammaMain := by
    exact div_pos (lt_min hgammaFast hgammaSlow) hcoordDen
  have hGamma : ∀ z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ), ∀ v,
      gammaNuisance * ‖v‖ ^ 2 ≤
        inner ℝ v (B.nuisanceCovarianceOperator
          (B.effectiveParamEquiv z) v) := by
    intro z hz v
    exact B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
      hlowerOne hupperU hlo hhiIntervals T hbaseline hW z hz v
  have he' : ∀ z (hz : z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
      e z hz q = B.actualBandSchurLinearMap
        (B.effectiveParamEquiv z) hgammaNuisance (hGamma z hz) q := by
    intro z hz q
    simpa only [gammaNuisance] using he z hz q
  have hfast : ∀ z (hz : z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
      gammaFast *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
        (B.tiltedLaw (B.effectiveParamEquiv z)).covariance
          (B.nuisanceResidualScore (B.effectiveParamEquiv z)
            hgammaNuisance (hGamma z hz) (B.bandRegressionScore q))
          (B.nuisanceResidualScore (B.effectiveParamEquiv z)
            hgammaNuisance (hGamma z hz) (B.bandRegressionScore q)) := by
    intro z hz q
    simpa only [gammaFast] using
      B.actualBandSchur_quadratic_lower_of_inverse_arithmetic
        (B.effectiveParamEquiv z) hgammaNuisance (hGamma z hz)
        (e z hz) (he' z hz) hCinv (hinv z hz) q
  have hslow' : ∀ z (hz : z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      gammaSlow * B.w ^ 2 ≤
        (B.tiltedLaw (B.effectiveParamEquiv z)).covariance
          (B.actualTwoStageCompensatedScore (B.effectiveParamEquiv z)
            hgammaNuisance (hGamma z hz) (e z hz))
          (B.actualTwoStageCompensatedScore (B.effectiveParamEquiv z)
            hgammaNuisance (hGamma z hz) (e z hz)) := by
    intro z hz
    simpa only [actualTwoStageCompensatedVariance, gammaNuisance] using
      hslowVariance z hz
  have hCreg : 0 ≤ Creg := by
    dsimp only [Creg]
    exact mul_nonneg hCinv.le (mul_nonneg (by norm_num) hCrightRow)
  have hreg' : ∀ z (hz : z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one)
          (B.actualBandRegression (B.effectiveParamEquiv z)
            hgammaNuisance (hGamma z hz) (e z hz)) ≤ Creg * B.w := by
    intro z hz
    have hright := B.actualBandRegressionTarget_sharpNorm_le_of_row
      (B.effectiveParamEquiv z) hgammaNuisance (hGamma z hz)
      hCrightRow B.w_pos.le (by
        intro j
        simpa only [gammaNuisance] using hregRightRow z hz j)
    have hraw := B.actualBandRegression_sharpNorm_le
      (B.effectiveParamEquiv z) hgammaNuisance (hGamma z hz)
      (e z hz) hCinv.le (hinv z hz) hright
    simpa only [Creg] using hraw
  have hSchur : ∀ z (hz : z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) u,
      gammaMain * ‖u‖ ^ 2 ≤
        inner ℝ
          (B.schurResidual
            (B.exactNuisanceRegression (B.effectiveParamEquiv z)
              hgammaNuisance (hGamma z hz)) u)
          (B.covarianceOperator (B.effectiveParamEquiv z)
            (B.schurResidual
              (B.exactNuisanceRegression (B.effectiveParamEquiv z)
                hgammaNuisance (hGamma z hz)) u)) := by
    intro z hz u
    simpa only [gammaMain] using
      B.exactSchurGap_of_fastSlow_of_regressionBound
        (B.effectiveParamEquiv z) hgammaNuisance (hGamma z hz)
        (e z hz) (he' z hz) hgammaFast hgammaSlow hCreg
        (hfast z hz) (hslow' z hz) (hreg' z hz) u
  have hVlower : 0 < gammaSlow * B.w ^ 2 :=
    mul_pos hgammaSlow (sq_pos_of_pos B.w_pos)
  have hTslow : 0 ≤
      B.twoStageCompensatedTargetBoundOrdinaryFast
        Creg Tband TslowCoord := by
    unfold twoStageCompensatedTargetBoundOrdinaryFast
    have hmoment : 0 ≤ ∑ j : Band,
        B.harmonicMass j * B.bandCenter j := by
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (B.harmonicMass_pos j).le
        (B.bandCenter_pos j).le
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg hmoment
          (mul_nonneg hCreg B.w_pos.le)) hTband)
      (mul_nonneg B.w_pos.le hTslowCoord)
  have hcomponents : ∀ z (hz : z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) u,
      B.exactSchurCovarianceOperator (B.effectiveParamEquiv z)
          hgammaNuisance (hGamma z hz) u =
          B.mainPart (B.normalizedTarget Delta) →
      ‖fun p : BandPrime B.sampleData.n B.sampleData.W =>
          (B.rawGaugeOfMain u).1 (B.partition.band p) +
            (u MainCoord.slow / B.w) * B.primeDeviation p‖ ≤
          CinvOrd * Tband +
            (B.twoStageCompensatedTargetBoundOrdinaryFast
              Creg Tband TslowCoord /
              (gammaSlow * B.w ^ 2)) * Ccomp ∧
        ‖B.exactNuisanceRegression (B.effectiveParamEquiv z)
          hgammaNuisance (hGamma z hz) u‖ ≤
          CfastNuisance +
            (B.twoStageCompensatedTargetBoundOrdinaryFast
              Creg Tband TslowCoord /
              (gammaSlow * B.w ^ 2)) * CslowNuisance ∧
        |u MainCoord.slow| ≤
          B.w * (B.twoStageCompensatedTargetBoundOrdinaryFast
            Creg Tband TslowCoord / (gammaSlow * B.w ^ 2)) := by
    intro z hz u hu
    apply B.exactSchur_solution_component_bounds_of_ordinaryFast_twoStageTargets
      (B.effectiveParamEquiv z) hgammaNuisance (hGamma z hz)
      (e z hz) (he' z hz) Delta hCinvOrd hTband hVlower
      hTslow hCcomp (hinvOrd z hz) htargetBand
    · simpa only [actualTwoStageCompensatedVariance, gammaNuisance] using
        hslowVariance z hz
    · simpa only [gammaNuisance] using
        B.abs_compensatedNormalizedTarget_le_of_regression_ordinaryTarget
          (B.effectiveParamEquiv z) hgammaNuisance (hGamma z hz)
          (e z hz) Delta hCreg (hreg' z hz) htargetBand
          htargetSlowCoord
    · intro p
      simpa only [gammaNuisance] using hcomp z hz p
    · exact B.targetFastNuisanceCoefficient_norm_le_of_covarianceVector
        (B.effectiveParamEquiv z) hgammaNuisance (hGamma z hz)
        (e z hz) Delta (by
          simpa only [gammaNuisance] using hfastNuisanceRow z hz)
    · exact B.actualTwoStageNuisanceCoefficient_norm_le_of_covarianceVector
        (B.effectiveParamEquiv z) hgammaNuisance (hGamma z hz)
        (e z hz) (by
          simpa only [gammaNuisance] using hslowNuisanceRow z hz)
    · exact hu
  have hprime : ∀ z (hz : z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) u,
      B.exactSchurCovarianceOperator (B.effectiveParamEquiv z)
          hgammaNuisance (hGamma z hz) u =
          B.mainPart (B.normalizedTarget Delta) →
      ‖fun p : BandPrime B.sampleData.n B.sampleData.W =>
          (B.rawGaugeOfMain u).1 (B.partition.band p) +
            (u MainCoord.slow / B.w) * B.primeDeviation p‖ ≤
        (speed : ℝ) := by
    intro z hz u hu
    exact (hcomponents z hz u hu).1.trans hspeedPrime
  have hnuisance : ∀ z (hz : z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) u,
      B.exactSchurCovarianceOperator (B.effectiveParamEquiv z)
          hgammaNuisance (hGamma z hz) u =
          B.mainPart (B.normalizedTarget Delta) →
      ‖B.exactNuisanceRegression (B.effectiveParamEquiv z)
        hgammaNuisance (hGamma z hz) u‖ ≤ (speed : ℝ) := by
    intro z hz u hu
    exact (hcomponents z hz u hu).2.1.trans hspeedNuisance
  have hstoredSlow : ∀ z (hz : z ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) u,
      B.exactSchurCovarianceOperator (B.effectiveParamEquiv z)
          hgammaNuisance (hGamma z hz) u =
          B.mainPart (B.normalizedTarget Delta) →
      |u MainCoord.slow| ≤ (speed : ℝ) := by
    intro z hz u hu
    exact (hcomponents z hz u hu).2.2.trans hspeedSlow
  obtain ⟨path, hpathZero, hball, hsize, hderiv, hbands, hphysical,
      hordinaryLog, hheads, hlog, hmarked, hfeasible, hfixed, hmass,
      hquotaPath⟩ :=
    B.exists_physicallyCenteredFixedPartitionFit_of_exactSchurOutputs
    hcompat Delta a speed gammaMain gammaNuisance hgammaMain
    hgammaNuisance hGamma hSchur hprime hnuisance hstoredSlow hmargin
    monitoredPrimes Crow hCrow hmarkedRow markedTarget N Cinitial Cmass
    hprimePos hqMass hinitialMarked fixedValue fixedWeight quota hquota
    hC hW hhi hsep hfrozenFeasible hfrozenLedger hactiveLedger hlarge
  have hheadPrimes : ∀ p : ℕ, p.Prime → p ≤ B.sampleData.W →
      B.paperMoment (B.markedValuation p) (path 1) =
        B.paperMoment (B.markedValuation p) 0 := by
    intro p hp hpW
    exact B.headPrimeMarkedMoment_eq_of_headIndicatorMoments
      hhead 0 (path 1) hheads hp hpW
  exact ⟨path, hpathZero, hball, hsize, hderiv, hbands, hphysical,
    hordinaryLog, hheads, hheadPrimes, hlog, hmarked, hfeasible, hfixed,
    hmass, hquotaPath⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
