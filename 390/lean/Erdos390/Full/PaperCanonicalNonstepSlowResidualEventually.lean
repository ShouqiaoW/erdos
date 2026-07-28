import Erdos390.Full.PaperCanonicalNonstepSlowRightColumnEventually
import Erdos390.Full.PaperNonstepSlowNuisanceCorrection
import Erdos390.Full.PaperCanonicalMarkedNuisanceRows
import Erdos390.Full.PaperCanonicalNuisanceUniformFloor
import Erdos390.Full.PaperSelectedMeshSchurRateEventually
import Erdos390.Full.CanonicalEndpointCenterEnvelopeEventually
import Erdos390.Full.PaperCanonicalActualMomentBoundsEventually

/-!
# Canonical Schur-projected non-step slow row

The literal full-valuation slow row is projected off the finite nuisance
space.  The marked-prime rate is squared before paying the moving-low
`1/alpha_0` loss, and all nuisance dimension and coercivity constants are
fixed only after `W` and the head/physical data are fixed.  The structural
cutoff remains before `delta`, `eta`, the mesh, and the effective box.
-/

open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus RegularMeshPrimeCutoffs
open PaperWeightedInverseExport

namespace BridgeData

set_option maxHeartbeats 2500000

/-- Fully discharged paper-scale slow right row after nuisance Schur
projection.  This is the row hypothesis consumed by the canonical
coefficient package for Lemma 8.6. -/
theorem exists_global_cutoff_eventually_canonical_nonstepSlowResidualRow_le :
    ∃ CF Cprod : ℝ, 0 ≤ CF ∧ 0 ≤ Cprod ∧
      ∃ W₀ : ℕ, ∃ hW₀two : 2 ≤ W₀,
        ∀ W : ℕ, (hW : W₀ ≤ W) →
      ∀ {delta eta : ℝ} (hdelta : 0 < delta)
        (M : RegularRelativeMesh.Mesh delta eta),
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
        (Phead : Head → HeadPattern.Pattern),
        (∀ h : Head, ∀ p : ℕ,
          p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
      ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U),
        (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma) →
        (hupperU : ∀ sigma, I.upper sigma ≤ U) →
      ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank)
        (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
        ∀ᶠ n : ℕ in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
            (hBn : B.sampleData.n = n) → (hBW : B.sampleData.W = W) →
            ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
                physicalBound (I.lower .plus) B.sampleData.n)
              (hremaining : ∀ c : Cell Head,
                (rawCell Phead I B.sampleData.n c \
                  (ledger B.sampleData.n).guards).Nonempty),
              (hcanonical : B.sampleData = canonicalSampleData
                (W := B.sampleData.W) Phead I
                  (ledger B.sampleData.n) hsep hremaining) →
            (∃ (hWne : B.sampleData.W ≠ 0)
              (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            (hscale : B.w = delta + eta) →
            ∀ (T : BarycentricTarget B.sampleData),
              (hTmargin : marginFloor ≤ T.cellMassMargin) →
              (hbaseline : B.baseline = T.baseline) →
              ∀ (z : B.EffectiveParamSpace),
                (hz : z ∈ closedBall
                  (0 : B.EffectiveParamSpace) (a : ℝ)) →
                ∀ i : Fin (M.cellCount + 1),
                  |B.normalizedBandCovarianceRow
                      (B.effectiveParamEquiv z)
                      (B.nuisanceResidualScore
                        (B.effectiveParamEquiv z)
                        (B.canonicalEffectiveNuisanceGamma_pos
                          I U (3 * (a : ℝ)) T)
                        (B.canonicalEffectiveNuisanceGap_on_closedBall
                          I a hU
                          hlowerOne hupperU
                          (by
                            intro sigma
                            rw [hcanonical]
                            rfl)
                          (by
                            intro sigma
                            rw [hcanonical]
                            rfl)
                          T hbaseline
                          (by rw [hBW]; omega) z hz)
                        B.slowScore) i| ≤
                    ((2 + CF + 7 * Cprod) * B.w) *
                      B.bandCenter i := by
  obtain ⟨CF, Cprod, hCF, hCprod, Wraw, hRawMain⟩ :=
    exists_global_cutoff_eventually_canonical_nonstepSlowRightColumn_le
  let W₀ : ℕ := max 2 (max Wraw
    (max canonicalActualMomentCutoff canonicalCenterEnvelopeCutoff))
  refine ⟨CF, Cprod, hCF, hCprod, W₀, ?_, ?_⟩
  · dsimp only [W₀]
    omega
  intro W hW delta eta hdelta M Head _instFintype _instDecidable
    _instNonempty Phead hhead I U hU hlowerOne hupperU
    Cprom Cbank ledger a marginFloor hmarginFloor
  have hWraw : Wraw ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWmoment : canonicalActualMomentCutoff ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWcenter : canonicalCenterEnvelopeCutoff ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWone : 1 < W := by
    omega
  have hHeadLe : ∀ h, ∀ p ∈ (Phead h).primes, p ≤ W := by
    intro h p hp
    exact (hhead h p).mp hp |>.2
  let Acoef : ℝ := 3 * (a : ℝ)
  have hAcoef : 0 ≤ Acoef := by dsimp only [Acoef]; positivity
  have hRaw := hRawMain W hWraw hdelta M Phead hhead I U
    hlowerOne hupperU Cprom Cbank ledger Acoef Acoef hAcoef hAcoef
  obtain ⟨markedError, hmarked0, hmarkedRate, Nmarked, hmarked⟩ :=
    _root_.Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall
      Phead I U hU hlowerOne hupperU Cprom Cbank ledger
        W hWone hHeadLe a
  let Calpha : ℝ := canonicalCenterEnvelopeConstant delta
  have hCalpha : 0 < Calpha := by
    simpa only [Calpha] using canonicalCenterEnvelopeConstant_pos hdelta
  let centerScale : ℝ := 1 / Calpha
  have hcenterScale : 0 < centerScale := one_div_pos.mpr hCalpha
  let gammaFloor : ℝ := canonicalEffectiveNuisanceGammaFloor
    Head I U (3 * (a : ℝ)) W marginFloor
  have hgammaFloor : 0 < gammaFloor := by
    dsimp only [gammaFloor]
    exact canonicalEffectiveNuisanceGammaFloor_pos I hmarginFloor
  let droot : ℝ := nuisanceDimensionCeiling Head
  have hdroot : 0 ≤ droot := by
    dsimp only [droot, nuisanceDimensionCeiling]
    positivity
  have hmarkedT : Tendsto markedError atTop (nhds 0) :=
    tendsto_zero_of_nonneg_mul_logL_zero
      markedError hmarked0 hmarkedRate
  let rateMajorant : ℕ → ℝ :=
    selectedMeshSchurRateMajorant
      markedError droot 7 gammaFloor centerScale
  have hrateT : Tendsto rateMajorant atTop (nhds 0) := by
    simpa only [rateMajorant] using
      tendsto_selectedMeshSchurRateMajorant_zero
        markedError hmarkedT hmarkedRate hgammaFloor hcenterScale
  have hrateSmall : ∀ᶠ n : ℕ in atTop, rateMajorant n < 1 :=
    hrateT.eventually (eventually_lt_nhds (by norm_num))
  have hMoment :=
    Mesh.canonicalActualFirstMomentCutoff_eventually M hdelta W hWmoment
  have hCenterLower :=
    Mesh.canonicalCenterEnvelopeCutoff_eventually_lower
      M hdelta W hWcenter
  have hLogL : ∀ᶠ n : ℕ in atTop,
      0 < Real.log (Scale.L n) := by
    have hLTop : Tendsto Scale.L atTop atTop := by
      simpa only [Scale.L] using
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact (Real.tendsto_log_atTop.comp hLTop).eventually
      (eventually_gt_atTop 0)
  filter_upwards [hRaw, hrateSmall, hMoment, hCenterLower, hLogL,
    eventually_ge_atTop Nmarked] with n hRawN hrateSmallN hMomentN
      hCenterLowerN hLogLN hnMarked
  intro B hBn hBW hsep hremaining hcanonical hpartition hscale
    T hTmargin hbaseline z hz i
  subst n
  subst W
  obtain ⟨_hWneMoment, _hnMoment, hMomentAll⟩ := hMomentN
  obtain ⟨hWne, S, hpartitionUser⟩ := hpartition
  let Pcanonical := Mesh.canonicalPartition M hdelta B.n_gt_one hWne S
  have hpartitionCanonical : B.partition = Pcanonical := by
    exact hpartitionUser.trans (by rfl)
  obtain ⟨_hdevSupRaw, hdevL1Raw⟩ := hMomentAll S
  have hactualScale : delta + M.ratio ≤ B.w := by
    rw [hscale]
    linarith [M.ratio_le_eta]
  have hw : 0 < B.w :=
    (add_pos hdelta M.ratio_pos).trans_le hactualScale
  have hdevL1 : B.primeDeviationL1 ≤ 7 * B.w := by
    change B.partition.totalL1 ≤ 7 * B.w
    rw [hpartitionCanonical]
    exact hdevL1Raw.trans
      (mul_le_mul_of_nonneg_left hactualScale (by norm_num))
  have hLo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hHi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  let xi : B.ParamSpace := B.effectiveParamEquiv z
  have hznorm : ‖z‖ ≤ (a : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using hz
  have hsize : B.paperEffectiveSize xi ≤ Acoef := by
    dsimp only [xi, Acoef]
    exact (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
      (mul_le_mul_of_nonneg_left hznorm (by norm_num))
  have heffective := B.effective_bounds_of_paperEffectiveSize xi hsize
  have heta : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ Acoef := heffective.1
  have hnuisance : ‖B.nuisanceParameter xi‖ ≤ Acoef := heffective.2
  have hphys : |xi MomentCoord.physical| ≤ Acoef := by
    calc
      |xi MomentCoord.physical| =
          ‖B.nuisanceParameter xi NuisanceCoord.physical‖ := by
        simp only [B.nuisanceParameter_physical, Real.norm_eq_abs]
      _ ≤ ‖B.nuisanceParameter xi‖ :=
        PiLp.norm_apply_le (B.nuisanceParameter xi)
          NuisanceCoord.physical
      _ ≤ Acoef := hnuisance
  have hraw := hRawN B rfl rfl hsep hremaining hcanonical
    ⟨hWne, S, hpartitionUser⟩ hscale xi heta hphys i
  have hmarkedRows : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          markedError B.sampleData.n * (1 / (p.1 : ℝ)) := by
    intro c p
    simpa only [xi] using
      hmarked B z hz hnMarked rfl hsep hremaining hcanonical c p
  let gamma := B.canonicalEffectiveNuisanceGamma
    I U (3 * (a : ℝ)) T
  have hgamma : 0 < gamma := by
    dsimp only [gamma]
    exact B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
  have hgap : ∀ v, gamma * ‖v‖ ^ 2 ≤
      inner ℝ v (B.nuisanceCovarianceOperator xi v) := by
    intro v
    simpa only [gamma, xi] using
      B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
        hlowerOne hupperU hLo hHi T hbaseline
          (by simpa only using hWone) z hz v
  have hgammaFloorLe : gammaFloor ≤ gamma := by
    dsimp only [gammaFloor, gamma]
    exact B.canonicalEffectiveNuisanceGammaFloor_le I hU
      (by positivity : 0 ≤ 3 * (a : ℝ)) hmarginFloor T hTmargin
  let amin : ℝ := centerScale / Real.log (Scale.L B.sampleData.n)
  have hamin : 0 < amin := div_pos hcenterScale hLogLN
  have hcenterAmin : ∀ j : Fin (M.cellCount + 1),
      amin ≤ B.bandCenter j := by
    intro j
    change centerScale / Real.log (Scale.L B.sampleData.n) ≤
      B.partition.center j
    rw [hpartitionUser]
    simpa only [centerScale, Calpha] using
      hCenterLowerN B.n_gt_one hWne S j
  have hdimension : Real.sqrt
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤ droot := by
    dsimp only [droot]
    exact B.sqrt_nuisanceCoord_card_le_ceiling
  have hrateMajorized :
      B.nonstepSlowNuisanceRate (markedError B.sampleData.n)
          gamma 7 amin ≤ rateMajorant B.sampleData.n := by
    have heps0 : 0 ≤ markedError B.sampleData.n :=
      hmarked0 B.sampleData.n
    dsimp only [nonstepSlowNuisanceRate, rateMajorant,
      selectedMeshSchurRateMajorant, amin]
    gcongr
  have hrateOne :
      B.nonstepSlowNuisanceRate (markedError B.sampleData.n)
          gamma 7 amin ≤ 1 :=
    hrateMajorized.trans hrateSmallN.le
  have hcorrection :=
    B.abs_normalizedBandCovarianceRow_slow_nuisanceCorrection_le_rate
      xi hgamma hgap (hmarked0 B.sampleData.n) (by norm_num : (0 : ℝ) ≤ 7)
      hw.le hamin hmarkedRows hdevL1 hcenterAmin i
  have hcorrectionOne :
      |B.normalizedBandCovarianceRow xi
          (fun m ↦ inner ℝ
            (B.nuisanceCoefficientOfScore xi hgamma hgap B.slowScore)
            (B.nuisanceStatistic m)) i| ≤
        B.w * B.bandCenter i := by
    exact hcorrection.trans (by
      calc
        B.nonstepSlowNuisanceRate (markedError B.sampleData.n)
              gamma 7 amin * B.w * B.bandCenter i =
            B.nonstepSlowNuisanceRate (markedError B.sampleData.n)
              gamma 7 amin * (B.w * B.bandCenter i) := by ring
        _ ≤ 1 * (B.w * B.bandCenter i) :=
          mul_le_mul_of_nonneg_right hrateOne
            (mul_nonneg hw.le (B.bandCenter_pos i).le)
        _ = B.w * B.bandCenter i := by ring)
  change |B.normalizedBandCovarianceRow xi
      (B.nuisanceResidualScore xi hgamma hgap B.slowScore) i| ≤ _
  unfold nuisanceResidualScore
  rw [B.normalizedBandCovarianceRow_sub]
  calc
    |B.normalizedBandCovarianceRow xi B.slowScore i -
        B.normalizedBandCovarianceRow xi
          (fun m ↦ inner ℝ
            (B.nuisanceCoefficientOfScore xi hgamma hgap B.slowScore)
            (B.nuisanceStatistic m)) i| ≤
      |B.normalizedBandCovarianceRow xi B.slowScore i| +
        |B.normalizedBandCovarianceRow xi
          (fun m ↦ inner ℝ
            (B.nuisanceCoefficientOfScore xi hgamma hgap B.slowScore)
            (B.nuisanceStatistic m)) i| := abs_sub _ _
    _ ≤ (1 + CF + 7 * Cprod) *
          B.w * B.bandCenter i + B.w * B.bandCenter i :=
      add_le_add hraw hcorrectionOne
    _ = ((2 + CF + 7 * Cprod) * B.w) *
          B.bandCenter i := by ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
