import Erdos390.Full.PaperProposition87MarkedProfilesMajorant
import Erdos390.Full.PaperCanonicalActualMomentBoundsEventually
import Erdos390.Full.PaperCanonicalActualPrimePowerWeightedRowEventually
import Erdos390.Full.PaperCanonicalMarkedNuisanceRows
import Erdos390.Full.PaperActualSquarefreeReference
import Erdos390.Full.PaperProposition87MarkedRowRate
import Erdos390.Full.PaperCanonicalLemma86Eventually

/-!
# Canonical eventual moving-prime row for Proposition 8.7

All signed-profile, prime-power, nuisance, kernel, harmonic-mass, and regular
mesh inputs are selected here.  The only remaining call-site assumptions are
the exact same-map Schur solve and its ordinary/slow quantitative outputs.
Fixed head primes are intentionally outside this theorem.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PrimeSums PaperWeightedInverseExport
open RegularMeshPrimeCutoffs

namespace BridgeData

/-! The cutoff is independent of the regular mesh.  Keeping it as a named
object makes the paper quantifier order visible in the exported statement:
`W` is fixed before the head data, the mesh, and the ODE ball. -/
noncomputable def canonicalMovingPrimeMarkedRowCutoff : ℕ :=
  max 2 RegularMeshPrimeCutoffs.canonicalActualMomentCutoff

set_option maxHeartbeats 3000000 in
/-- Canonical eventual `C/p` row on the preselected effective ball.  The
universal cutoff is chosen before the head type and head patterns; after a
permitted `W` is fixed, those patterns and then the ODE ball are quantified.
The final ambient threshold may depend on all of that already selected
finite data. -/
theorem exists_cutoff_eventually_canonical_movingPrime_markedRow_of_schurSplice
    (I : PhysicalIntervals) (U : ℝ)
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {CinvOrd Tband targetScale gammaSlow Creg : ℝ},
      0 ≤ CinvOrd → 0 ≤ Tband → 0 ≤ targetScale →
      0 < gammaSlow → 0 ≤ Creg →
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
        (Phead : Head → HeadPattern.Pattern),
      (∀ h, ∀ p ∈ (Phead h).primes, p ≤ W) →
      ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
      ∃ Crow : ℝ, 0 ≤ Crow ∧
      ∀ {delta eta : ℝ} (hdelta : 0 < delta)
        (M : RegularRelativeMesh.Mesh delta eta),
      ∀ᶠ n : ℕ in atTop,
        ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
          (hBn : B.sampleData.n = n) →
          (hBW : B.sampleData.W = W) →
          (hBWlarge : 1 < B.sampleData.W) →
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
            (hcanonical : B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Phead I (ledger B.sampleData.n) hsep hremaining) →
            (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
                B.n_gt_one hWne S) →
            (hscale : B.w = delta + eta) →
            ∀ (Delta : Fin (M.cellCount + 1) → ℝ),
            ∀ (T : BarycentricTarget B.sampleData),
              (hTmargin : marginFloor ≤ T.cellMassMargin) →
              (hbaseline : B.baseline = T.baseline) →
              ∀ {gammaFull : ℝ}, 0 < gammaFull →
              (hFull : ∀ z ∈ closedBall
                (0 : B.EffectiveParamSpace) (a : ℝ),
                B.vectorFamily.HasCovarianceGap gammaFull
                  (B.effectiveParamEquiv z)) →
              ∀ (e : ∀ (z : B.EffectiveParamSpace),
                z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
                  B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge),
              (he : ∀ (z : B.EffectiveParamSpace)
                  (hz : z ∈ closedBall
                    (0 : B.EffectiveParamSpace) (a : ℝ)) q,
                e z hz q = B.actualBandSchurLinearMap
                  (B.effectiveParamEquiv z)
                  (B.canonicalEffectiveNuisanceGamma_pos
                    I U (3 * (a : ℝ)) T)
                  (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                    hlowerOne hupperU
                    (by intro sigma; rw [hcanonical]; rfl)
                    (by intro sigma; rw [hcanonical]; rfl)
                    T hbaseline hBWlarge z hz) q) →
              (hvariance : ∀ (z : B.EffectiveParamSpace)
                  (hz : z ∈ closedBall
                    (0 : B.EffectiveParamSpace) (a : ℝ)),
                gammaSlow * B.w ^ 2 ≤ B.actualTwoStageCompensatedVariance
                  (B.effectiveParamEquiv z)
                  (B.canonicalEffectiveNuisanceGamma_pos
                    I U (3 * (a : ℝ)) T)
                  (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                    hlowerOne hupperU
                    (by intro sigma; rw [hcanonical]; rfl)
                    (by intro sigma; rw [hcanonical]; rfl)
                    T hbaseline hBWlarge z hz) (e z hz)) →
              (htarget : ∀ (z : B.EffectiveParamSpace)
                  (hz : z ∈ closedBall
                    (0 : B.EffectiveParamSpace) (a : ℝ)),
                |B.compensatedNormalizedTarget (B.effectiveParamEquiv z)
                  (B.canonicalEffectiveNuisanceGamma_pos
                    I U (3 * (a : ℝ)) T)
                  (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                    hlowerOne hupperU
                    (by intro sigma; rw [hcanonical]; rfl)
                  (by intro sigma; rw [hcanonical]; rfl)
                    T hbaseline hBWlarge z hz) (e z hz) Delta| ≤
                    B.w * targetScale) →
              (hinvOrd : ∀ (z : B.EffectiveParamSpace)
                  (hz : z ∈ closedBall
                    (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                ‖(e z hz).symm v‖ ≤ CinvOrd * ‖v‖) →
              (htargetBand :
                ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband) →
              (hsharp : ∀ (z : B.EffectiveParamSpace)
                  (hz : z ∈ closedBall
                    (0 : B.EffectiveParamSpace) (a : ℝ)),
                paperSharpNorm B.harmonicMass B.bandCenter
                  (B.partition.center_ne_zero B.n_gt_one)
                  (B.actualBandRegression (B.effectiveParamEquiv z)
                    (B.canonicalEffectiveNuisanceGamma_pos
                      I U (3 * (a : ℝ)) T)
                    (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                      hlowerOne hupperU
                      (by intro sigma; rw [hcanonical]; rfl)
                      (by intro sigma; rw [hcanonical]; rfl)
                      T hbaseline hBWlarge z hz) (e z hz)) ≤ Creg * B.w) →
              ∀ (monitoredPrimes : Finset ℕ),
                (∀ p ∈ monitoredPrimes,
                  p ∈ primeBand B.sampleData.n B.sampleData.W) →
                ∀ p ∈ monitoredPrimes,
                  ∀ z ∈ closedBall
                    (0 : B.EffectiveParamSpace) (a : ℝ),
                  |B.vectorFamily.scalarFamily.covariance
                    (B.markedValuation p)
                    (fun m ↦ B.vectorFamily.scalarFamily.score m
                      (B.vectorFamily.vectorField
                        (B.targetVector Delta)
                        (B.effectiveParamEquiv z)))
                    (B.effectiveParamEquiv z)| ≤ Crow / (p : ℝ) := by
  obtain ⟨Cprod, hCprod, hProduct⟩ := DickmanBasic.kernel_product_bound
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  have hCpow : 0 < Cpow := by
    simpa only [Cpow] using
      FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant_pos
  let W₀ := canonicalMovingPrimeMarkedRowCutoff
  refine ⟨W₀, ?_⟩
  intro W hWcut CinvOrd Tband targetScale gammaSlow Creg hCinvOrd
    hTband hTargetScale hgammaSlow hCreg
    Head instFintype instDecidable instNonempty Phead
    hHeadLe a marginFloor hmarginFloor
  have hWone : 1 < W := by
    have : 2 ≤ W := (le_max_left 2
      RegularMeshPrimeCutoffs.canonicalActualMomentCutoff).trans hWcut
    omega
  have hWgeom : RegularMeshPrimeCutoffs.canonicalActualMomentCutoff ≤ W :=
    (le_max_right 2
      RegularMeshPrimeCutoffs.canonicalActualMomentCutoff).trans hWcut
  let CF : ℝ := 1 / DickmanBasic.rho DickmanBasic.U
  have hCF : 0 ≤ CF := by
    dsimp only [CF]
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  let K : ℝ := 2 * Real.log 4
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let Rmax : ℝ := Cpow * (1 / (W : ℝ)) + 2
  have hRmax : 0 ≤ Rmax := by
    dsimp only [Rmax]
    positivity
  let gammaFloor : ℝ := canonicalEffectiveNuisanceGammaFloor
    Head I U (3 * (a : ℝ)) W marginFloor
  have hgammaFloor : 0 < gammaFloor := by
    dsimp only [gammaFloor]
    exact canonicalEffectiveNuisanceGammaFloor_pos I hmarginFloor
  let Crow : ℝ :=
    vectorFieldProfilesMarkedScaledHeadMajorant Head K CF Cprod Cprod
      Rmax gammaFloor CinvOrd Tband targetScale gammaSlow Creg
  have hCrow : 0 ≤ Crow := by
    dsimp only [Crow, vectorFieldProfilesMarkedScaledHeadMajorant]
    have hA : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U :=
      one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
    positivity
  refine ⟨Crow, hCrow, ?_⟩
  intro delta eta hdelta M
  obtain ⟨_hCpowTerminal, hpowerTerminal⟩ :=
    boxIndependent_canonicalRaw_actualWeightedRow
      Phead I U hlowerOne hupperU Cprom Cbank ledger
  let Acoef : ℝ := 3 * (a : ℝ)
  let Aphys : ℝ := 3 * (a : ℝ)
  have hAcoef : 0 ≤ Acoef := by dsimp only [Acoef]; positivity
  have hAphys : 0 ≤ Aphys := by dsimp only [Aphys]; positivity
  obtain ⟨profileError, hprofile0, hprofileT, hprofileRate,
      Nprofile, hprofile⟩ :=
    exists_boxIndependent_actual_component_signed_profiles
      Phead I U hlowerOne hupperU Cprom Cbank ledger
        W hWone hHeadLe Acoef Aphys hAcoef hAphys
  obtain ⟨epsilon75, hepsilon750, hepsilon75T, _hepsilon75Rate,
      hcombinedRateRaw, Npower, hpower⟩ :=
    hpowerTerminal W hWone hHeadLe Acoef hAcoef Aphys hAphys
  obtain ⟨markedError, hmarked0, hmarkedRate, Nmarked, hmarked⟩ :=
    _root_.Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall
      Phead I U hU hlowerOne hupperU Cprom Cbank ledger
        W hWone hHeadLe a
  let combined : ℕ → ℝ := fun n ↦
    canonicalCombinedPowerCorrection
      Phead I U Cprom Cbank W Acoef Aphys n
  have hcombinedRate : Tendsto
      (fun n : ℕ ↦ combined n * Real.log (Scale.L n))
        atTop (nhds 0) := by
    simpa only [combined, canonicalCombinedPowerCorrection] using
      hcombinedRateRaw
  have hUstrict : 1 < U :=
    (hlowerOne .minus).trans_lt
      ((I.lower_lt_upper .minus).trans_le (hupperU .minus))
  have hcombinedNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ combined n := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    exact canonicalCombinedPowerCorrection_nonneg
      Phead I hUstrict.le hAphys hWone hn
  have hcombinedT : Tendsto combined atTop (nhds 0) :=
    tendsto_zero_of_eventually_nonneg_mul_logL_zero
      combined hcombinedNonneg hcombinedRate
  have hprofileOne : ∀ᶠ n : ℕ in atTop, profileError n ≤ 1 :=
    hprofileT.eventually (eventually_le_nhds (by norm_num))
  have hprofileProduct : ∀ᶠ n : ℕ in atTop,
      12 * (profileError n * Real.log (Scale.L n)) ≤ 1 := by
    have ht : Tendsto
        (fun n : ℕ ↦ 12 *
          (profileError n * Real.log (Scale.L n))) atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hprofileRate
    exact ht.eventually (eventually_le_nhds (by norm_num))
  have hmarkedT : Tendsto markedError atTop (nhds 0) :=
    tendsto_zero_of_nonneg_mul_logL_zero markedError hmarked0 hmarkedRate
  have hmarkedOne : ∀ᶠ n : ℕ in atTop, markedError n ≤ 1 :=
    hmarkedT.eventually (eventually_le_nhds (by norm_num))
  have hmarkedProduct : ∀ᶠ n : ℕ in atTop,
      12 * (markedError n * Real.log (Scale.L n)) ≤ 1 := by
    have ht : Tendsto
        (fun n : ℕ ↦ 12 *
          (markedError n * Real.log (Scale.L n))) atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hmarkedRate
    exact ht.eventually (eventually_le_nhds (by norm_num))
  have hepsilonOne : ∀ᶠ n : ℕ in atTop, epsilon75 n ≤ 1 :=
    hepsilon75T.eventually (eventually_le_nhds (by norm_num))
  have hcombinedOne : ∀ᶠ n : ℕ in atTop, combined n ≤ 1 :=
    hcombinedT.eventually (eventually_le_nhds (by norm_num))
  have hlogL0 : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (Scale.L n) := by
    have htop : Tendsto (fun n : ℕ ↦ Real.log (Scale.L n))
        atTop atTop :=
      Real.tendsto_log_atTop.comp (by
        simpa only [Scale.L] using
          Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact htop.eventually (eventually_ge_atTop 0)
  have hgeomN :=
    RegularMeshPrimeCutoffs.Mesh.canonicalActualUpperMomentCutoff_eventually
      M hdelta W hWgeom
  have hmassN := eventually_sum_harmonicMass_le_twelve_logL
    (Head := Head) (Band := Fin (M.cellCount + 1)) W
  have hbandTN := eventually_bandTReciprocalSum_le W
  filter_upwards [hprofileOne, hprofileProduct, hmarkedOne,
    hmarkedProduct, hepsilonOne, hcombinedOne, hcombinedNonneg, hlogL0,
    hgeomN, hmassN, hbandTN, eventually_ge_atTop Nprofile,
    eventually_ge_atTop Npower, eventually_ge_atTop Nmarked] with
      n hprofileOneN hprofileProductN hmarkedOneN hmarkedProductN
      hepsilonOneN hcombinedOneN hcombinedNonnegN hlogL0N hgeomAt
      hmassAt hbandTAt hnProfile hnPower hnMarked
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition hscale
    Delta T hTmargin hbaseline gammaFull hgammaFull hFull e he hvariance
    htarget hinvOrd htargetBand hsharp monitoredPrimes hmonitored
  subst n
  subst W
  obtain ⟨hWneGeom, hnGeom, hgeomAll⟩ := hgeomAt
  obtain ⟨hWneUser, S, hpartitionUser⟩ := hpartition
  have hpartitionCanonical : B.partition =
      RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
        hnGeom hWneGeom S := by
    exact hpartitionUser.trans (by rfl)
  obtain ⟨hdevSupRaw, hdevL1Raw, hdevL2Raw⟩ := hgeomAll S
  have hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ B.w := by
    intro p
    rw [hpartitionCanonical]
    calc
      |(RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta hnGeom
          hWneGeom S).deviation p| ≤ delta + M.ratio := hdevSupRaw p
      _ ≤ delta + eta := add_le_add_right M.ratio_le_eta delta
      _ = B.w := hscale.symm
  have hdevL1 : B.partition.totalL1 ≤ 7 * B.w := by
    rw [hpartitionCanonical]
    calc
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta hnGeom
          hWneGeom S).totalL1 ≤ 7 * (delta + M.ratio) := hdevL1Raw
      _ ≤ 7 * (delta + eta) := by
        gcongr
        exact M.ratio_le_eta
      _ = 7 * B.w := by rw [hscale]
  have hdevL2 : B.partition.variance ≤ 4 * B.w ^ 2 := by
    rw [hpartitionCanonical]
    have hactualNonneg : 0 ≤ delta + M.ratio := by
      linarith [M.ratio_pos]
    have hpaperNonneg : 0 ≤ delta + eta :=
      hactualNonneg.trans (add_le_add_right M.ratio_le_eta delta)
    calc
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta hnGeom
          hWneGeom S).variance ≤ 4 * (delta + M.ratio) ^ 2 := hdevL2Raw
      _ ≤ 4 * (delta + eta) ^ 2 := by
        gcongr
        exact M.ratio_le_eta
      _ = 4 * B.w ^ 2 := by rw [hscale]
  have hPattern : B.sampleData.pattern = Phead := by
    rw [hcanonical]
    rfl
  have hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hGuards : B.sampleData.guards =
      (ledger B.sampleData.n).guards := by
    rw [hcanonical]
    rfl
  have heta : ∀ (z : B.EffectiveParamSpace)
      (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |B.effectivePrimeCoefficient (B.effectiveParamEquiv z) p| ≤ Acoef := by
    intro z hz p
    have hznorm : ‖z‖ ≤ (a : ℝ) := by
      simpa only [mem_closedBall, dist_zero_right] using hz
    have hsize : B.paperEffectiveSize (B.effectiveParamEquiv z) ≤ Acoef := by
      dsimp only [Acoef]
      exact (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
        (mul_le_mul_of_nonneg_left hznorm (by norm_num))
    exact (B.effective_bounds_of_paperEffectiveSize
      (B.effectiveParamEquiv z) hsize).1 p
  have hphys : ∀ (z : B.EffectiveParamSpace)
      (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      |B.effectiveParamEquiv z MomentCoord.physical| ≤ Aphys := by
    intro z hz
    have hznorm : ‖z‖ ≤ (a : ℝ) := by
      simpa only [mem_closedBall, dist_zero_right] using hz
    have hsize : B.paperEffectiveSize (B.effectiveParamEquiv z) ≤ Acoef := by
      dsimp only [Acoef]
      exact (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
        (mul_le_mul_of_nonneg_left hznorm (by norm_num))
    have hnuisance := (B.effective_bounds_of_paperEffectiveSize
      (B.effectiveParamEquiv z) hsize).2
    calc
      |B.effectiveParamEquiv z MomentCoord.physical| =
          ‖B.nuisanceParameter (B.effectiveParamEquiv z)
            NuisanceCoord.physical‖ := by
        simp only [B.nuisanceParameter_physical, Real.norm_eq_abs]
      _ ≤ ‖B.nuisanceParameter (B.effectiveParamEquiv z)‖ :=
        PiLp.norm_apply_le _ _
      _ ≤ Aphys := by simpa only [Acoef, Aphys] using hnuisance
  have hprofiles : ∀ (z : B.EffectiveParamSpace),
      z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
      (∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
        ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
        |(B.actualComponentValuationLaw (B.effectiveParamEquiv z) c).probability.expect
            (fun omega ↦ divInd (OmittedTiltPairChamber.pairPower p r 1 1)
              ((B.actualComponentValuationLaw
                (B.effectiveParamEquiv z) c).value omega)) -
          PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
            (OmittedTiltPairChamber.pairPower p r 1 1)| ≤
          profileError B.sampleData.n *
            PaperPrimePowerChamberError.pairWeight p r 1 1) ∧
      (∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
        |(B.actualComponentValuationLaw (B.effectiveParamEquiv z) c).probability.expect
            (fun omega ↦ divInd p
              ((B.actualComponentValuationLaw
                (B.effectiveParamEquiv z) c).value omega)) -
          PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
            profileError B.sampleData.n *
              PaperPrimePowerChamberError.singleWeight p 1) := by
    intro z hz
    exact hprofile B (B.effectiveParamEquiv z) hnProfile hPattern hlo hhi
      hGuards (heta z hz) (hphys z hz) rfl
  let R : ℝ := Cpow * (1 / (B.sampleData.W : ℝ)) +
    epsilon75 B.sampleData.n + combined B.sampleData.n
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    exact add_nonneg
      (add_nonneg (mul_nonneg hCpow.le (by positivity))
        (hepsilon750 B.sampleData.n)) hcombinedNonnegN
  have hRRmax : R ≤ Rmax := by
    dsimp only [R, Rmax]
    linarith
  have hactualRow : ∀ (z : B.EffectiveParamSpace)
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
      (p : BandPrime B.sampleData.n B.sampleData.W),
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw (B.effectiveParamEquiv z)).covVV p.1 r.1 -
            (B.actualValuationLaw (B.effectiveParamEquiv z)).covII p.1 r.1| ≤ R := by
    intro z hz p
    have hraw := hpower B (B.effectiveParamEquiv z) hnPower rfl
      hsep hremaining hcanonical (heta z hz) (hphys z hz) p
    simpa only [R, combined, canonicalCombinedPowerCorrection] using hraw
  have hmarkedRows : ∀ (z : B.EffectiveParamSpace)
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
      (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          markedError B.sampleData.n * (1 / (p.1 : ℝ)) := by
    intro z hz c p
    exact hmarked B z hz hnMarked rfl hsep hremaining hcanonical c p
  have hF : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n p.1)| ≤ CF := by
    intro p
    have ht0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
      B.n_gt_one p.2
    have ht1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
      B.n_gt_one p.2
    have harg : DickmanBasic.U - tPrime B.sampleData.n p.1 ∈
        Set.Icc (1 : ℝ) 5 := by
      constructor <;> norm_num [DickmanBasic.U] <;> linarith
    have hone : (1 : ℝ) ∈ Set.Icc (1 : ℝ) 5 := by norm_num
    have hrho : DickmanBasic.rho
        (DickmanBasic.U - tPrime B.sampleData.n p.1) ≤ 1 := by
      simpa only [DickmanBasic.rho_one] using
        DickmanBasic.antitoneOn_rho_one_five hone harg (by
          norm_num [DickmanBasic.U]
          linarith)
    rw [abs_of_pos (DickmanBasic.F_pos ⟨ht0, ht1.trans (by norm_num)⟩)]
    unfold DickmanBasic.F
    exact (div_le_div_iff_of_pos_right DickmanBasic.rho_U_pos).2 hrho
  have hKernelProduct : ∀ p r :
      BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p.1) (tPrime B.sampleData.n r.1)| ≤
        Cprod * tPrime B.sampleData.n p.1 *
          tPrime B.sampleData.n r.1 := by
    intro p r
    exact hProduct _ ⟨
      PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand B.n_gt_one p.2,
      PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand B.n_gt_one p.2⟩ _ ⟨
      PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand B.n_gt_one r.2,
      PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand B.n_gt_one r.2⟩
  have hKernel : ∀ p r : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p.1) (tPrime B.sampleData.n r.1)| ≤
        Cprod := by
    intro p r
    have hp0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
      B.n_gt_one p.2
    have hp1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
      B.n_gt_one p.2
    have hr0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
      B.n_gt_one r.2
    have hr1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
      B.n_gt_one r.2
    have hprod : tPrime B.sampleData.n p.1 *
        tPrime B.sampleData.n r.1 ≤ 1 := by
      calc
        tPrime B.sampleData.n p.1 * tPrime B.sampleData.n r.1 ≤
            1 * tPrime B.sampleData.n r.1 :=
          mul_le_mul_of_nonneg_right hp1 hr0
        _ ≤ 1 := by simpa using hr1
    calc
      _ ≤ Cprod * tPrime B.sampleData.n p.1 *
          tPrime B.sampleData.n r.1 := hKernelProduct p r
      _ = Cprod * (tPrime B.sampleData.n p.1 *
          tPrime B.sampleData.n r.1) := by ring
      _ ≤ Cprod * 1 := mul_le_mul_of_nonneg_left hprod hCprod.le
      _ = Cprod := by ring
  let H : ℝ := 12 * Real.log (Scale.L B.sampleData.n)
  have hH0 : 0 ≤ H := mul_nonneg (by norm_num) hlogL0N
  have hH : (∑ j : Fin (M.cellCount + 1), B.harmonicMass j) ≤ H := by
    simpa only [H] using hmassAt B rfl rfl
  have hEH : profileError B.sampleData.n * H ≤ 1 := by
    dsimp only [H]
    nlinarith
  have hMH : markedError B.sampleData.n * H ≤ 1 := by
    dsimp only [H]
    nlinarith
  have hbandT : bandTReciprocalSum B.sampleData.n B.sampleData.W ≤ K := by
    simpa only [K] using hbandTAt
  let gamma := B.canonicalEffectiveNuisanceGamma
    I U (3 * (a : ℝ)) T
  have hgamma : 0 < gamma := by
    dsimp only [gamma]
    exact B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
  have hGamma : ∀ z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ), ∀ v,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ v
        (B.nuisanceCovarianceOperator (B.effectiveParamEquiv z) v) := by
    intro z hz v
    simpa only [gamma] using
      B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
        hlowerOne hupperU hlo hhi T hbaseline hBWlarge z hz v
  have hgammaCompare : gammaFloor ≤ gamma := by
    dsimp only [gammaFloor, gamma]
    exact B.canonicalEffectiveNuisanceGammaFloor_le I hU
      (by positivity : 0 ≤ 3 * (a : ℝ)) hmarginFloor T hTmargin
  have huniform := B.uniform_vectorField_markedRow_on_effectiveBall_of_profiles
    Delta a hgammaFull hgamma
      (mul_pos hgammaSlow (sq_pos_of_pos B.w_pos))
      (mul_nonneg B.w_pos.le hTargetScale) hCinvOrd hCreg
      hFull hGamma e
      (by intro z hz q; simpa only [gamma] using he z hz q)
      (by intro z hz; simpa only [gamma] using hvariance z hz)
      (by intro z hz; simpa only [gamma] using htarget z hz)
      hinvOrd htargetBand hH0 hK (hprofile0 B.sampleData.n) hCF
      hCprod.le hCprod.le hR0 (hmarked0 B.sampleData.n) (by omega)
      hH hbandT
      (by intro z hz; simpa only [gamma] using hsharp z hz)
      hdevSup hdevL1 hdevL2
      (fun z hz ↦ (hprofiles z hz).1)
      (fun z hz ↦ (hprofiles z hz).2)
      hF hKernelProduct hKernel hactualRow hmarkedRows
      monitoredPrimes hmonitored
  have hconstant := B.vectorFieldProfilesMarkedConstant_le_scaledMajorant
    hH0 hK (hprofile0 B.sampleData.n) hprofileOneN hEH hCF hCprod.le
      hCprod.le hR0 hRRmax (hmarked0 B.sampleData.n) hmarkedOneN hMH
      hgammaFloor hgamma hgammaCompare hCinvOrd hTband hTargetScale
      hgammaSlow hCreg hBWlarge
  have hheadMajorant :=
    B.vectorFieldProfilesMarkedScaledMajorant_le_headMajorant
      (K := K) (CF := CF) (Cprod := Cprod) (CKernel := Cprod)
      (Rmax := Rmax)
      hK hgammaFloor hCinvOrd hTband hTargetScale hgammaSlow hCreg
  have hconstantHead :
      B.vectorFieldProfilesMarkedConstant H K
          (profileError B.sampleData.n) CF Cprod Cprod R
          (markedError B.sampleData.n) gamma CinvOrd Tband
            (B.w * targetScale) (gammaSlow * B.w ^ 2) Creg ≤ Crow :=
    hconstant.trans (by simpa only [Crow] using hheadMajorant)
  intro p hp z hz
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (prime_of_mem_primeBand (hmonitored p hp)).pos
  calc
    _ ≤ B.vectorFieldProfilesMarkedConstant H K
          (profileError B.sampleData.n) CF Cprod Cprod R
          (markedError B.sampleData.n) gamma CinvOrd Tband
            (B.w * targetScale) (gammaSlow * B.w ^ 2) Creg /
        (p : ℝ) := huniform p hp z hz
    _ ≤ Crow / (p : ℝ) :=
      div_le_div_of_nonneg_right
        hconstantHead hpR.le

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
