import Erdos390.Full.PaperProposition87CanonicalStatement
import Erdos390.Full.PaperCanonicalLemma86RelativePrimePowerEventually
import Erdos390.Full.PaperCanonicalLemma86RemainingOutputsEventually
import Erdos390.Full.PaperCanonicalMomentRatioEventually
import Erdos390.Full.PaperCanonicalBandFirstMomentEventually
import Erdos390.Full.PaperProposition87CanonicalTargetPackage
import Erdos390.Full.PaperProposition87CanonicalNuisanceReservesEventually
import Erdos390.Full.PaperProposition87CanonicalSpeedPackage
import Erdos390.Full.PaperProposition87CanonicalFullGap
import Erdos390.Full.PaperProposition87CanonicalMarkedProfilesEventually
import Erdos390.Full.PaperProposition87AllPrimeMarkedSplit
import Erdos390.Full.PaperProposition87CanonicalFeasibilitySlackEventually
import Erdos390.Full.FixedFiniteMixtureFullUniform

/-!
# Closed canonical form of paper Proposition 8.7

This theorem composes the exact Lemmas 8.4 and 8.6 terminals with the
canonical target, nuisance-reserve, full-gap, marked-row, speed, and
feasibility packages.  Its public statement is
`CanonicalProposition87Statement`; in particular no analytic estimate is a
call-site premise.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PaperGuardCensus
open PaperWeightedInverseExport MovingLowGaugeTransfer
open RegularMeshPrimeCutoffs PaperPermittedRegularMesh

namespace BridgeData

set_option maxHeartbeats 4000000 in
/-- Assumption-free paper-order canonical Proposition 8.7. -/
theorem canonical_proposition87
    (cMesh : ℝ)
    (I : PhysicalIntervals) (U : ℝ)
    (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank) :
    CanonicalProposition87Statement cMesh I U Cprom Cbank ledger := by
  unfold CanonicalProposition87Statement
  intro hcMesh hU hlowerOne hupperU
  obtain ⟨relTol, hrelTol, Csharp, hCsharp, Cordinary, hCordinary,
      Crow, hCrow, Creg, hCreg, hCregEq,
      _Crel, _hCrel, Wrel, hRel⟩ :=
    exists_paperFineMesh_cutoff_eventually_canonical_lemma86_relativePrimePower
      cMesh hcMesh
  obtain ⟨varTol, hvarTol, gammaSlow, hgammaSlow,
      _Cvar, _hCvar, Wvar, hVar⟩ :=
    exists_paperFineMesh_cutoff_eventually_canonical_lemma86_variance_of_base
      cMesh Creg hcMesh hCreg
  obtain ⟨Rproj, hRproj, ratioTol, hratioTol, Wratio, hRatio⟩ :=
    exists_paperFineMesh_cutoff_eventually_canonical_momentRatio
  obtain ⟨Wmarked, hMarkedRoot⟩ :=
    exists_cutoff_eventually_canonical_movingPrime_markedRow_of_schurSplice
      I U hU hlowerOne hupperU Cprom Cbank ledger
  let meshTol : ℝ := min relTol (min varTol ratioTol)
  let W₀ : ℕ := max 2 (max Wrel (max Wvar (max Wratio Wmarked)))
  have hmeshTol : 0 < meshTol := by
    dsimp only [meshTol]
    exact lt_min hrelTol (lt_min hvarTol hratioTol)
  refine ⟨meshTol, hmeshTol, W₀, ?_⟩
  intro W hW Head _instHeadFintype _instHeadDecidable _instHeadNonempty
    Phead hPhead Ctarget Cinitial Cmass Cfixed Cactive marginFloor
    hCtarget hCinitial hCmass hCfixed hCactive hmarginFloor
  have hWone : 1 < W := by
    dsimp only [W₀] at hW
    omega
  have hWrel : Wrel ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWvar : Wvar ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWratio : Wratio ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWmarked : Wmarked ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hHeadLe : ∀ h, ∀ p ∈ (Phead h).primes, p ≤ W := by
    intro h p hp
    exact (hPhead h p).mp hp |>.2
  let K : ℝ := 2 * Real.log 4
  let Tband : ℝ := (1 + Rproj) * Ctarget
  let Ccoef : ℝ := 1 + Creg
  let CL1 : ℝ := 7 + Creg * K
  let A : ℝ := K * Creg * Tband + Ctarget
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hTband : 0 ≤ Tband := by
    dsimp only [Tband]
    positivity
  have hCcoef : 0 ≤ Ccoef := by dsimp only [Ccoef]; positivity
  have hCL1 : 0 ≤ CL1 := by dsimp only [CL1]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  obtain ⟨speed, a, hspeedOne, hspeedLeA, _haeq, hSpeed⟩ :=
    exists_speed_radius_with_canonicalTwoStage_bounds_uniformTypes
      (CinvOrd := Cordinary) (Tband := Tband) (Creg := Creg)
      (Tslow := Ctarget) (K := K) (gammaSlow := gammaSlow)
      (Ccoef := Ccoef) hTband hCreg hCtarget hK hgammaSlow hCcoef
  have ha : 0 < (a : ℝ) := by
    have hsa : (speed : ℝ) ≤ (a : ℝ) := by
      exact_mod_cast hspeedLeA
    linarith
  obtain ⟨CrowMarked, hCrowMarked, hMarkedMesh⟩ :=
    hMarkedRoot W hWmarked hCordinary.le hTband hA hgammaSlow hCreg
      Phead hHeadLe a marginFloor hmarginFloor
  let Cpost : ℝ := Cinitial + Cmass * CrowMarked
  have hCpost : 0 ≤ Cpost := by
    dsimp only [Cpost]
    positivity
  refine ⟨a, ha, Cpost, hCpost, ?_⟩
  intro delta eta M hdelta hPermitted hfine
  have hfineRel : delta + eta ≤ relTol :=
    hfine.trans (min_le_left relTol (min varTol ratioTol))
  have hfineVar : delta + eta ≤ varTol :=
    hfine.trans ((min_le_right relTol (min varTol ratioTol)).trans
      (min_le_left varTol ratioTol))
  have hfineRatio : delta + eta ≤ ratioTol :=
    hfine.trans ((min_le_right relTol (min varTol ratioTol)).trans
      (min_le_right varTol ratioTol))
  obtain ⟨epsilonRel, _hepsilonRel0, _hepsilonRel,
      _hepsilonRelRate, hRelN⟩ :=
    hRel W hWrel M hdelta hPermitted hfineRel Head Phead hPhead
      I U hU hlowerOne hupperU Cprom Cbank ledger
      a marginFloor hmarginFloor
  have hVarN := hVar W hWvar M hdelta hPermitted hfineVar
    Phead hPhead I U hU hlowerOne hupperU Cprom Cbank ledger
      a marginFloor hmarginFloor
  have hRatioN := hRatio W hWratio M hdelta hfineRatio
    (Head := Head)
  have hMomentN := eventually_bandFirstMoment_le_two_log_four
    (Head := Head) (Band := Fin (M.cellCount + 1)) W
  have hNuisanceN := eventually_canonical_twoStage_nuisance_halfReserves
    (Band := Fin (M.cellCount + 1)) Phead I U hU hlowerOne hupperU
      Cprom Cbank ledger W hWone hHeadLe a marginFloor hmarginFloor
      (CinvOrd := Cordinary) (Tband := Tband) (CL1 := CL1)
      (gammaSlow := gammaSlow) (A := A)
      hCordinary.le hTband hCL1 hgammaSlow hA
  have hMarkedN := hMarkedMesh hdelta M
  have hSlackN := eventually_canonical_exponential_slack_le_L
    (Head := Head) (Band := Fin (M.cellCount + 1))
      U hU W a Cfixed Cactive hCactive
  filter_upwards [hRelN, hVarN, hRatioN, hMomentN, hNuisanceN,
    hMarkedN, hSlackN] with n hRelAt hVarAt hRatioAt hMomentAt
      hNuisanceAt hMarkedAt hSlackAt
  intro B hBn hBW hsep hremaining hcanonical hpartition hscale
    T hTmargin hbaseline Delta henv monitoredPrimes hprime hleY
    markedTarget N _hN hqMass hinitialMarked Fixed _instFixedFintype
    fixedValue fixedWeight quota hquota hheadSeparated
    hfrozenFeasible hfrozenLedger hactiveLedger
  have hBWlarge : 1 < B.sampleData.W := by
    rw [hBW]
    exact hWone
  have hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W := by
    intro h p
    rw [hcanonical, hBW]
    exact hPhead h p
  have hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hhiIntervals : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hhiU : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound U B.sampleData.n := by
    intro sigma
    rw [hhiIntervals]
    exact FixedFiniteMixtureFullUniform.physicalBound_mono
      (hupperU sigma) B.sampleData.n
  have hcompat : B.HasPrimeLogCompatibility :=
    B.hasPrimeLogCompatibility_of_exactHeadPrimes hhead
  have hratio : (∑ j : Fin (M.cellCount + 1),
      B.harmonicMass j * B.bandCenter j) ≤
      Rproj * sharpWeightTotal B.harmonicMass B.bandCenter :=
    hRatioAt B hBn hBW hpartition
  have hmoment : (∑ j : Fin (M.cellCount + 1),
      B.harmonicMass j * B.bandCenter j) ≤ K := by
    simpa only [K] using hMomentAt B hBn hBW
  obtain ⟨hdev, hgeomL1, hVlower, hVupper, hVcenter,
      e, he, hinv, hinvOrd, hBaseZ⟩ :=
    hRelAt B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
      hscale T hTmargin hbaseline
  have hslowRow : ∀ z (hz : z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ)) j,
      |B.normalizedBandCovarianceRow (B.effectiveParamEquiv z)
        (B.nuisanceResidualScore (B.effectiveParamEquiv z)
          (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
          (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
            hlowerOne hupperU hlo hhiIntervals T hbaseline
              hBWlarge z hz) B.slowScore) j| ≤
        (Crow * B.w) * B.bandCenter j := by
    intro z hz j
    exact (hBaseZ z hz).1 j
  have hreg : ∀ z (hz : z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ)),
      paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegression (B.effectiveParamEquiv z)
          (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
          (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
            hlowerOne hupperU hlo hhiIntervals T hbaseline
              hBWlarge z hz) (e z hz)) ≤ Creg * B.w := by
    intro z hz
    exact (hBaseZ z hz).2.2.1
  have hcoeff : ∀ z (hz : z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ))
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |B.actualCompensatedCoefficient
        (B.actualBandRegression (B.effectiveParamEquiv z)
          (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
          (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
            hlowerOne hupperU hlo hhiIntervals T hbaseline
              hBWlarge z hz) (e z hz)) p| ≤ Ccoef * B.w := by
    intro z hz p
    simpa only [Ccoef] using (hBaseZ z hz).2.2.2.1 p
  have hcoeffL1 : ∀ z (hz : z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ)),
      B.partition.compensatedL1
        (B.actualBandRegression (B.effectiveParamEquiv z)
          (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
          (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
            hlowerOne hupperU hlo hhiIntervals T hbaseline
              hBWlarge z hz) (e z hz)) ≤ CL1 * B.w := by
    intro z hz
    simpa only [CL1, K] using (hBaseZ z hz).2.2.2.2.1
  have hvariance : ∀ z (hz : z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ)),
      gammaSlow * B.w ^ 2 ≤
        B.actualTwoStageCompensatedVariance (B.effectiveParamEquiv z)
          (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
          (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
            hlowerOne hupperU hlo hhiIntervals T hbaseline
              hBWlarge z hz) (e z hz) := by
    intro z hz
    exact (hVarAt B hBn hBW hBWlarge hsep hremaining hcanonical
      hpartition hscale T hTmargin hbaseline z hz (e z hz)
      (hreg z hz) hdev hgeomL1 hVlower hVupper hVcenter).1
  have hzero : (0 : B.EffectiveParamSpace) ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ) := by
    simpa only [mem_closedBall, dist_self] using (show (0 : ℝ) ≤ a by
      positivity)
  have htargetPackage : ∀ z (hz : z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ)),
      ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband ∧
      |B.mainPart (B.normalizedTarget Delta) MainCoord.slow| ≤ Ctarget ∧
      |B.compensatedNormalizedTarget (B.effectiveParamEquiv z)
        (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
        (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
          hlowerOne hupperU hlo hhiIntervals T hbaseline
            hBWlarge z hz) (e z hz) Delta| ≤
          B.twoStageCompensatedTargetBoundOrdinaryFast
            Creg Tband Ctarget ∧
      B.twoStageCompensatedTargetBoundOrdinaryFast
          Creg Tband Ctarget ≤ B.w * A := by
    intro z hz
    simpa only [Tband, A, K] using
      B.canonicalTwoStageTargetPackage_of_envelopes
        (B.effectiveParamEquiv z)
        (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
        (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
          hlowerOne hupperU hlo hhiIntervals T hbaseline
            hBWlarge z hz) (e z hz) Delta hCtarget hRproj.le hCreg
          henv hratio hmoment (hreg z hz)
  have htargetBand := (htargetPackage 0 hzero).1
  have htargetSlow := (htargetPackage 0 hzero).2.1
  have htargetComp : ∀ z (hz : z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ)),
      |B.compensatedNormalizedTarget (B.effectiveParamEquiv z)
        (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
        (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
          hlowerOne hupperU hlo hhiIntervals T hbaseline
            hBWlarge z hz) (e z hz) Delta| ≤ B.w * A := by
    intro z hz
    exact (htargetPackage z hz).2.2.1.trans
      (htargetPackage z hz).2.2.2
  have hNuisanceRows : ∀ z (hz : z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ)),
      ‖B.nuisanceCovarianceVector (B.effectiveParamEquiv z)
        (B.bandRegressionScore
          ((e z hz).symm (B.projectedNormalizedTargetBand Delta)))‖ ≤
          B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T *
            (1 / 2) ∧
      ‖B.nuisanceCovarianceVector (B.effectiveParamEquiv z)
        (B.postBandPrimeScore
          (B.actualBandRegression (B.effectiveParamEquiv z)
            (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
            (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
              hlowerOne hupperU hlo hhiIntervals T hbaseline
                hBWlarge z hz) (e z hz)))‖ ≤
          B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T *
            (gammaSlow * B.w / (2 * (1 + A))) := by
    intro z hz
    exact hNuisanceAt B hBn hBW hBWlarge hsep hremaining hcanonical
      T hTmargin hbaseline z hz (e z hz) Delta (hinvOrd z hz)
        htargetBand (hcoeffL1 z hz)
  let gammaN : ℝ :=
    B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
  let gammaFull : ℝ :=
    B.canonicalTwoStageFullGap Csharp gammaSlow Creg gammaN
  have hGamma : ∀ z (hz : z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ)) v,
      gammaN * ‖v‖ ^ 2 ≤ inner ℝ v
        (B.nuisanceCovarianceOperator (B.effectiveParamEquiv z) v) := by
    intro z hz v
    simpa only [gammaN] using
      B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
        hlowerOne hupperU hlo hhiIntervals T hbaseline
          hBWlarge z hz v
  have hFullAt : ∀ z (hz : z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ)),
      0 < gammaFull ∧ B.vectorFamily.HasCovarianceGap gammaFull
        (B.effectiveParamEquiv z) := by
    intro z hz
    simpa only [gammaN, gammaFull] using
      B.hasCovarianceGap_of_sameMap_sharpInverse_and_slow
        (B.effectiveParamEquiv z)
        (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
        (by intro v; simpa only [gammaN] using hGamma z hz v)
        (e z hz) (he z hz) hCsharp hgammaSlow hCreg
          (hinv z hz) (hvariance z hz) (hreg z hz)
  have hgammaFull : 0 < gammaFull := (hFullAt 0 hzero).1
  have hFull : ∀ z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ),
      B.vectorFamily.HasCovarianceGap gammaFull
        (B.effectiveParamEquiv z) := by
    intro z hz
    exact (hFullAt z hz).2
  let movingPrimes := monitoredPrimes.filter
    (fun p ↦ p ∈ primeBand B.sampleData.n B.sampleData.W)
  have hMovingFiltered := hMarkedAt B hBn hBW hBWlarge hsep hremaining
    hcanonical hpartition hscale Delta T hTmargin hbaseline
      hgammaFull hFull e he hvariance htargetComp hinvOrd htargetBand hreg
      movingPrimes (by
        intro p hp
        exact (Finset.mem_filter.mp hp).2)
  have hMoving : ∀ p ∈ monitoredPrimes,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
      |B.vectorFamily.scalarFamily.covariance
        (B.markedValuation p)
        (fun m ↦ B.vectorFamily.scalarFamily.score m
          (B.vectorFamily.vectorField (B.targetVector Delta)
            (B.effectiveParamEquiv z)))
        (B.effectiveParamEquiv z)| ≤ CrowMarked / (p : ℝ) := by
    intro p hp hband z hz
    exact hMovingFiltered p (Finset.mem_filter.mpr ⟨hp, hband⟩) z hz
  have hMarkedAll := B.uniform_allPrime_markedRow_of_exactHead_and_moving
    hhead Delta a hgammaFull hFull hCrowMarked monitoredPrimes
      hprime hleY hMoving
  obtain ⟨hspeedPrime, hspeedNuisance, hspeedSlow⟩ := hSpeed B hmoment
  have hlarge := hSlackAt B hBn hBW
  have hfit :=
    B.exists_physicallyCenteredFixedPartitionFit_of_canonicalTwoStageOutputs
      I hU hlowerOne hupperU hlo hhiIntervals T hbaseline hBWlarge
      hcompat hhead Delta a speed hCsharp hCordinary.le hgammaSlow
      hCrow hTband hCtarget
      (mul_nonneg hCcoef B.w_pos.le)
      e he hinv hinvOrd hvariance hslowRow htargetBand htargetSlow
      hcoeff (fun z hz ↦ (hNuisanceRows z hz).1)
      (fun z hz ↦ (hNuisanceRows z hz).2)
      (by simpa only [hCregEq] using hspeedPrime)
      (by simpa only [A, hCregEq] using hspeedNuisance)
      (by simpa only [hCregEq] using hspeedSlow) hspeedLeA
      monitoredPrimes CrowMarked hCrowMarked hMarkedAll markedTarget
      N Cinitial Cmass
      (by
        intro p hp
        exact_mod_cast (hprime p hp).pos)
      hqMass hinitialMarked fixedValue fixedWeight quota hquota
      hU hhiU hheadSeparated hfrozenFeasible hfrozenLedger
      hactiveLedger hlarge
  simpa only [HasPhysicallyCenteredFixedPartitionFit, Cpost] using hfit

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
