import Erdos390.Full.PaperProposition87CanonicalTargetPackage
import Erdos390.Full.PaperCanonicalMarkedNuisanceRows
import Erdos390.Full.PaperCanonicalNuisanceUniformFloor
import Erdos390.Full.PaperProposition87MarkedRowRate

/-!
# Canonical nuisance reserves for Proposition 8.7

The fast and slow nuisance rows in the finite two-stage assembly are not
independent analytic inputs.  Both follow from the same reciprocal marked
prime row.  This file performs the paper's non-circular choice: first fix
the effective box and hence a positive nuisance-gap floor; only afterwards
increase `n` until the marked row fits the two reserved halves.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus PaperWeightedInverseExport

namespace BridgeData

set_option maxHeartbeats 2000000 in
/-- Eventual canonical realization of the two nuisance reserves consumed by
the exact Proposition 8.7 assembly.  The only score input is the already
proved compensated `L¹` estimate; no nuisance covariance-row hypothesis is
exposed. -/
theorem eventually_canonical_twoStage_nuisance_halfReserves
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    (Phead : Head → HeadPattern.Pattern)
    (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank)
    (W : ℕ) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ p ∈ (Phead h).primes, p ≤ W)
    (a : NNReal) (marginFloor : ℝ) (hmargin : 0 < marginFloor)
    {Band : Type*} [Fintype Band] [DecidableEq Band] [Nonempty Band]
    {CinvOrd Tband CL1 gammaSlow A : ℝ}
    (hCinvOrd : 0 ≤ CinvOrd) (hTband : 0 ≤ Tband)
    (hCL1 : 0 ≤ CL1) (hgammaSlow : 0 < gammaSlow) (hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band),
        B.sampleData.n = n → B.sampleData.W = W →
        ∀ (hBWlarge : 1 < B.sampleData.W),
        ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : ∀ c : Cell Head,
            (rawCell Phead I B.sampleData.n c \
              (ledger B.sampleData.n).guards).Nonempty),
          (hcanonical : B.sampleData = canonicalSampleData
            (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
              hsep hremaining) →
          ∀ (T : BarycentricTarget B.sampleData),
            marginFloor ≤ T.cellMassMargin →
            ∀ (hbaseline : B.baseline = T.baseline),
            ∀ (z : B.EffectiveParamSpace)
              (hz : z ∈ closedBall
                (0 : B.EffectiveParamSpace) (a : ℝ)),
              ∀ (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
                (Delta : Band → ℝ),
                (∀ v, ‖e.symm v‖ ≤ CinvOrd * ‖v‖) →
                ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband →
                (let xi := B.effectiveParamEquiv z
                 let gammaN :=
                   B.canonicalEffectiveNuisanceGamma
                     I U (3 * (a : ℝ)) T
                 let hgammaN : 0 < gammaN :=
                   B.canonicalEffectiveNuisanceGamma_pos
                     I U (3 * (a : ℝ)) T
                 let hgap : ∀ v, gammaN * ‖v‖ ^ 2 ≤
                     inner ℝ v (B.nuisanceCovarianceOperator xi v) := by
                   intro v
                   simpa only [xi, gammaN] using
                     B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                       hlowerOne hupperU
                       (by intro sigma; rw [hcanonical]; rfl)
                       (by intro sigma; rw [hcanonical]; rfl)
                       T hbaseline hBWlarge z hz v
                 B.partition.compensatedL1
                     (B.actualBandRegression xi hgammaN hgap e) ≤
                   CL1 * B.w) →
                (let xi := B.effectiveParamEquiv z
                 let gammaN :=
                   B.canonicalEffectiveNuisanceGamma
                     I U (3 * (a : ℝ)) T
                 let hgammaN : 0 < gammaN :=
                   B.canonicalEffectiveNuisanceGamma_pos
                     I U (3 * (a : ℝ)) T
                 let hgap : ∀ v, gammaN * ‖v‖ ^ 2 ≤
                     inner ℝ v (B.nuisanceCovarianceOperator xi v) := by
                   intro v
                   simpa only [xi, gammaN] using
                     B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                       hlowerOne hupperU
                       (by intro sigma; rw [hcanonical]; rfl)
                       (by intro sigma; rw [hcanonical]; rfl)
                       T hbaseline hBWlarge z hz v
                 ‖B.nuisanceCovarianceVector xi
                     (B.bandRegressionScore
                       (e.symm (B.projectedNormalizedTargetBand Delta)))‖ ≤
                     gammaN * (1 / 2) ∧
                   ‖B.nuisanceCovarianceVector xi
                     (B.postBandPrimeScore
                       (B.actualBandRegression xi hgammaN hgap e))‖ ≤
                     gammaN *
                       (gammaSlow * B.w / (2 * (1 + A)))) := by
  obtain ⟨epsilon, hepsilon0, hepsilonRate, Nmarked, hmarked⟩ :=
    _root_.Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall
      Phead I U hU hlowerOne hupperU Cprom Cbank ledger
        W hW hHeadLe a
  let gammaFloor : ℝ :=
    canonicalEffectiveNuisanceGammaFloor
      Head I U (3 * (a : ℝ)) W marginFloor
  have hgammaFloor : 0 < gammaFloor := by
    dsimp only [gammaFloor]
    exact canonicalEffectiveNuisanceGammaFloor_pos I hmargin
  have hreserves := eventually_twoStageMarkedRowReserves
    (Head := Head) (Band := Band) W epsilon hepsilon0 hepsilonRate
      hCinvOrd hTband hCL1 hgammaFloor hgammaSlow hA
  filter_upwards [hreserves, eventually_ge_atTop Nmarked] with
      n hreservesN hnMarked
  intro B hBn hBW hBWlarge hsep hremaining hcanonical T hTmargin
    hbaseline z hz e Delta hinvOrd htargetBand hL1
  subst n
  subst W
  let xi : B.ParamSpace := B.effectiveParamEquiv z
  let gammaN : ℝ :=
    B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
  have hgammaN : 0 < gammaN := by
    dsimp only [gammaN]
    exact B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
  have hgap : ∀ v, gammaN * ‖v‖ ^ 2 ≤
      inner ℝ v (B.nuisanceCovarianceOperator xi v) := by
    intro v
    simpa only [xi, gammaN] using
      B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
        hlowerOne hupperU
        (by intro sigma; rw [hcanonical]; rfl)
        (by intro sigma; rw [hcanonical]; rfl)
        T hbaseline hBWlarge z hz v
  have hfloorLe : gammaFloor ≤ gammaN := by
    dsimp only [gammaFloor, gammaN]
    exact B.canonicalEffectiveNuisanceGammaFloor_le
      I hU (by positivity) hmargin T hTmargin
  obtain ⟨hfastFloor, hslowFloor⟩ := hreservesN B rfl rfl
  have hfastReserve :
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          ((epsilon B.sampleData.n *
              (∑ j : Band, B.harmonicMass j)) *
            (CinvOrd * Tband)) ≤ gammaN / 2 := by
    exact hfastFloor.trans (div_le_div_of_nonneg_right
      hfloorLe (by norm_num))
  have hslowReserve :
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (epsilon B.sampleData.n * CL1) ≤
        gammaN * gammaSlow / (2 * (1 + A)) := by
    have hmul : gammaFloor * gammaSlow ≤ gammaN * gammaSlow :=
      mul_le_mul_of_nonneg_right hfloorLe hgammaSlow.le
    exact hslowFloor.trans
      (div_le_div_of_nonneg_right hmul (by positivity))
  have hmarkedAt : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m c)
          (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        epsilon B.sampleData.n * (1 / (p.1 : ℝ)) := by
    intro c p
    simpa only [xi] using
      hmarked B z hz hnMarked rfl hsep hremaining hcanonical c p
  have hresult := B.twoStage_nuisanceCovarianceRows_le_halfReserves
    xi hgammaN hgap e (hepsilon0 B.sampleData.n) hCinvOrd
      hinvOrd Delta htargetBand hmarkedAt hL1 hfastReserve hslowReserve
  simpa only [xi, gammaN] using hresult

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
