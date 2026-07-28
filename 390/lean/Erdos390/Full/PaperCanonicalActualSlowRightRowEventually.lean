import Erdos390.Full.PaperActualSlowRightRowFiniteAssembly
import Erdos390.Full.PaperActualSquarefreeReference
import Erdos390.Full.PaperActualFullProjectedInverseEventually
import Erdos390.Full.PaperBridgeCanonicalPowerCorrectionTriangle
import Erdos390.Full.PaperCanonicalActualMomentBoundsEventually
import Erdos390.Full.CanonicalEndpointCenterEnvelopeEventually
import Erdos390.Full.PaperCanonicalPrimeRowResidualEventually
import Erdos390.Full.PaperCanonicalMarkedNuisanceRows
import Erdos390.Full.PaperCanonicalNuisanceUniformFloor
import Erdos390.Full.PaperSelectedMeshSchurRateEventually
import Erdos390.Full.PoissonDickmanKernelBounds

/-!
# Canonical eventual slow right row

This module discharges the literal slow-column estimate used in paper
Lemma 8.6.  The cutoff is selected from universal Dickman constants and the
fixed mesh before the head type and its patterns are introduced.  After the
cutoff, all head-dependent quantities occur only in the final ambient
threshold.

The moving low cell is retained throughout: every finite error is bounded
by the actual arithmetic centre of the output band.  In particular, no
additive `o(1)` estimate is substituted for the required sharp relative
bound.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus PrimeSums PaperWeightedInverseExport
open RegularMeshPrimeCutoffs
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open ConditionedPoissonLimit DickmanBasic
open SquarefreeSharpBandTransfer PrimePowerSharpBandTransfer
open PaperActualSlowRightRowFinite

namespace BridgeData

/-- The literal slow right column is uniformly `O(w alpha_i)` on the
canonical arithmetic partition.  The structural cutoff is chosen before
`Head` and `Phead`; the latter affect only the eventual `n` threshold.

The hypothesis `hhead` is the exact head-prime condition needed for the
finite logarithmic null relation.  Its forward implication supplies the
strictly weaker support condition used by all marked-cell estimates, so no
incompatible bound on the product modulus occurs. -/
theorem exists_cutoff_eventually_canonical_actualSlowRightRow
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ Crow : ℝ, 0 < Crow ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        ∀ (M : RegularRelativeMesh.Mesh delta delta),
        ∀ {Head : Type*} [Fintype Head] [DecidableEq Head]
          [Nonempty Head],
        ∀ (Phead : Head → HeadPattern.Pattern),
        (∀ h : Head, ∀ p : ℕ,
          p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
        ∀ (I : PhysicalIntervals) (U : ℝ),
        ∀ (hU : 1 ≤ U)
          (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
          (hupperU : ∀ sigma, I.upper sigma ≤ U),
        ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank)
          (a : NNReal) (marginFloor : ℝ),
        0 < marginFloor →
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
              (hcanonical : B.sampleData = canonicalSampleData
                  (W := B.sampleData.W) Phead I
                    (ledger B.sampleData.n) hsep hremaining) →
              (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                  (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
                B.partition = Mesh.canonicalPartition M hdelta
                  B.n_gt_one hWne S) →
              (hscale : B.w = delta + M.ratio) →
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
                            I a hU hlowerOne hupperU
                            (by
                              intro sigma
                              rw [hcanonical]
                              rfl)
                            (by
                              intro sigma
                              rw [hcanonical]
                              rfl)
                            T hbaseline hBWlarge z hz)
                          B.slowScore) i| ≤
                      (Crow * B.w) * B.bandCenter i := by
  obtain ⟨CF, hCF, hFLipschitz⟩ := exists_F_lipschitz_unit
  obtain ⟨Cprod, hCprod, hProduct⟩ := kernel_product_bound
  obtain ⟨CKernel, hCKernel, hKernelBound⟩ :=
    PoissonDickmanKernelBounds.exists_covarianceKernel_abs_le_second
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  have hCpow : 0 < Cpow := by
    simpa only [Cpow] using
      FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant_pos
  let K : ℝ := 2 * Real.log 4
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let Crow : ℝ := 6 + 2 * CF + 7 * Cprod
  have hCrow : 0 < Crow := by
    dsimp only [Crow]
    positivity
  let Wmoment : ℕ := RegularMeshPrimeCutoffs.canonicalActualMomentCutoff
  let Wcenter : ℕ := RegularMeshPrimeCutoffs.canonicalCenterEnvelopeCutoff
  let Calpha : ℝ :=
    RegularMeshPrimeCutoffs.canonicalCenterEnvelopeConstant delta
  have hCalpha : 0 < Calpha := by
    simpa only [Calpha] using
      RegularMeshPrimeCutoffs.canonicalCenterEnvelopeConstant_pos hdelta
  let centerScale : ℝ := 1 / Calpha
  have hcenterScale : 0 < centerScale := by
    exact one_div_pos.mpr hCalpha
  obtain ⟨Wrow, hrowEvent⟩ :=
    PaperCanonicalPrimeRowResidualEventually.exists_cutoff_eventually_primeRowResidual_le
      hdelta
  have hInvNat : Tendsto (fun W : ℕ ↦ 1 / (W : ℝ))
      atTop (nhds 0) := by
    have hinv : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    have h := hinv.comp tendsto_natCast_atTop_atTop
    simpa only [one_div] using h
  let squareTailConstant : ℝ :=
    (1 / rho DickmanBasic.U) ^ 2 + CKernel
  have hSquareTail : Tendsto (fun W : ℕ ↦
      squareTailConstant * (1 / (W : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hInvNat
  obtain ⟨Wsquare, hWsquare⟩ := eventually_atTop.1
    (hSquareTail.eventually (eventually_lt_nhds hdelta))
  let fullTailConstant : ℝ := 3 * Cpow * (K + 1)
  have hFullTail : Tendsto (fun W : ℕ ↦
      fullTailConstant * (1 / (W : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hInvNat
  obtain ⟨Wfull, hWfull⟩ := eventually_atTop.1
    (hFullTail.eventually (eventually_lt_nhds hdelta))
  let W₀ := max 2
    (max Wmoment (max Wcenter (max Wrow (max Wsquare Wfull))))
  refine ⟨Crow, hCrow, W₀, ?_⟩
  intro W hWcut M Head _instHead _instHeadDec _instHeadNonempty
    Phead hhead I U hU hlowerOne hupperU Cprom Cbank ledger
    a marginFloor hmarginFloor
  let w₀ : ℝ := delta + M.ratio
  have hw₀ : 0 < w₀ := by
    dsimp only [w₀]
    exact add_pos hdelta M.ratio_pos
  have hdeltaW₀ : delta ≤ w₀ := by
    dsimp only [w₀]
    linarith [M.ratio_pos]
  have hWone : 1 < W := by
    dsimp only [W₀] at hWcut
    omega
  have hWmoment : Wmoment ≤ W := by
    dsimp only [W₀] at hWcut
    omega
  have hWcenter : Wcenter ≤ W := by
    dsimp only [W₀] at hWcut
    omega
  have hWrow : Wrow ≤ W := by
    dsimp only [W₀] at hWcut
    omega
  have hWsquareCut : Wsquare ≤ W := by
    dsimp only [W₀] at hWcut
    omega
  have hWfullCut : Wfull ≤ W := by
    dsimp only [W₀] at hWcut
    omega
  have hSquareTailSmall :
      squareTailConstant * (1 / (W : ℝ)) < delta :=
    hWsquare W hWsquareCut
  have hFullTailSmall :
      fullTailConstant * (1 / (W : ℝ)) < delta :=
    hWfull W hWfullCut
  have hHeadLe : ∀ h, ∀ p ∈ (Phead h).primes, p ≤ W := by
    intro h p hp
    exact (hhead h p).mp hp |>.2
  let Acoef : ℝ := 3 * (a : ℝ)
  let Aphys : ℝ := 3 * (a : ℝ)
  have hAcoef : 0 ≤ Acoef := by dsimp only [Acoef]; positivity
  have hAphys : 0 ≤ Aphys := by dsimp only [Aphys]; positivity
  obtain ⟨profileError, hprofile0, hprofileT, hprofileRate,
      Nprofile, hprofile⟩ :=
    exists_boxIndependent_actual_component_signed_profiles
      Phead I U hlowerOne hupperU Cprom Cbank ledger
        W hWone hHeadLe Acoef Aphys hAcoef hAphys
  obtain ⟨_hCpowFull, hfullTerminal⟩ :=
    boxIndependent_canonicalRaw_fullSharp
      Phead I U hlowerOne hupperU Cprom Cbank ledger
  obtain ⟨epsilon75, hepsilon750, hepsilon75T, hepsilon75Rate,
      hcombinedRateRaw, Nfull, hfullRaw⟩ :=
    hfullTerminal W hWone hHeadLe Acoef hAcoef Aphys hAphys
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
  have hSquareRemainderT := tendsto_squarefreeSharpProfileRemainder
    profileError Calpha K CKernel W hprofileT hprofileRate
  have hSquareSmall : ∀ᶠ n : ℕ in atTop,
      squarefreeSharpProfileRemainder
        profileError Calpha K CKernel W n < 2 * w₀ :=
    hSquareRemainderT.eventually (eventually_lt_nhds (by
      simpa only [squareTailConstant] using hSquareTailSmall.trans
        (hdeltaW₀.trans_lt (by linarith [hw₀] : w₀ < 2 * w₀))))
  have hFullRemainderT := tendsto_canonicalFullSharpRemainder
    epsilon75 combined Cpow Calpha K W
      hepsilon75T hepsilon75Rate hcombinedRate
  have hFullSmall : ∀ᶠ n : ℕ in atTop,
      canonicalFullSharpRemainder
        epsilon75 combined Cpow Calpha K W n < 2 * w₀ :=
    hFullRemainderT.eventually (eventually_lt_nhds (by
      simpa only [fullTailConstant] using hFullTailSmall.trans
        (hdeltaW₀.trans_lt (by linarith [hw₀] : w₀ < 2 * w₀))))
  have hmarkedT : Tendsto markedError atTop (nhds 0) :=
    tendsto_zero_of_nonneg_mul_logL_zero markedError hmarked0 hmarkedRate
  let gammaFloor : ℝ := canonicalEffectiveNuisanceGammaFloor
    Head I U (3 * (a : ℝ)) W marginFloor
  have hgammaFloor : 0 < gammaFloor := by
    dsimp only [gammaFloor]
    exact canonicalEffectiveNuisanceGammaFloor_pos I hmarginFloor
  let droot : ℝ := nuisanceDimensionCeiling Head
  have hdroot : 0 ≤ droot := by
    dsimp only [droot, nuisanceDimensionCeiling]
    positivity
  let schurMajorant : ℕ → ℝ :=
    selectedMeshSchurRateMajorant markedError droot K
      gammaFloor centerScale
  have hschurT : Tendsto schurMajorant atTop (nhds 0) := by
    simpa only [schurMajorant] using
      tendsto_selectedMeshSchurRateMajorant_zero
        markedError hmarkedT hmarkedRate hgammaFloor hcenterScale
  have hSchurSmall : ∀ᶠ n : ℕ in atTop,
      schurMajorant n < w₀ :=
    hschurT.eventually (eventually_lt_nhds hw₀)
  have hMoment :=
    RegularMeshPrimeCutoffs.Mesh.canonicalActualMomentCutoff_eventually
      M hdelta W (by simpa only [Wmoment] using hWmoment)
  have hCenterInv :=
    RegularMeshPrimeCutoffs.Mesh.canonicalCenterEnvelopeCutoff_eventually_inverse
      M hdelta W (by simpa only [Wcenter] using hWcenter)
  have hCenterLower :=
    RegularMeshPrimeCutoffs.Mesh.canonicalCenterEnvelopeCutoff_eventually_lower
      M hdelta W (by simpa only [Wcenter] using hWcenter)
  have hRow := hrowEvent W hWrow
  have hBandT := eventually_bandTReciprocalSum_le W
  have hLogL : ∀ᶠ n : ℕ in atTop,
      0 < Real.log (Scale.L n) := by
    have hLTop : Tendsto Scale.L atTop atTop := by
      simpa only [Scale.L] using
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact (Real.tendsto_log_atTop.comp hLTop).eventually
      (eventually_gt_atTop 0)
  filter_upwards [hMoment, hCenterInv, hCenterLower, hRow, hBandT,
    hSquareSmall, hFullSmall, hSchurSmall, hLogL,
    eventually_ge_atTop Nprofile, eventually_ge_atTop Nfull,
    eventually_ge_atTop Nmarked] with
      n hMomentN hCenterInvN hCenterLowerN hRowN hBandTN
      hSquareN hFullN hSchurN hLogLN hnProfile hnFull hnMarked
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition hscale
    T hTmargin hbaseline z hz i
  subst n
  subst W
  obtain ⟨_hWneMoment, _hnMoment, hMomentAll⟩ := hMomentN
  obtain ⟨hWne, S, hpartitionUser⟩ := hpartition
  let Pcanonical := Mesh.canonicalPartition M hdelta B.n_gt_one hWne S
  let Ecanonical := Mesh.canonicalCertificate M hdelta B.n_gt_one hWne S
  have hpartitionCanonical : B.partition = Pcanonical := by
    exact hpartitionUser.trans (by rfl)
  obtain ⟨hdevSupRaw, hdevL1Raw, _hvarLower, _hvarUpper,
      _hrelL1, _hrelInv, _hrelVar⟩ := hMomentAll S
  have hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation p| ≤ w₀ := by
    intro p
    change |B.partition.deviation p| ≤ w₀
    rw [hpartitionCanonical]
    simpa only [Pcanonical, w₀] using hdevSupRaw p
  have hdevL1 : B.primeDeviationL1 ≤ 7 * w₀ := by
    change B.partition.totalL1 ≤ 7 * w₀
    rw [hpartitionCanonical]
    simpa only [Pcanonical, w₀] using hdevL1Raw
  have hCenterInvCanonical : ∀ j : Fin (M.cellCount + 1),
      1 / Pcanonical.center j ≤
        Calpha * Real.log (Scale.L B.sampleData.n) := by
    intro j
    simpa only [Pcanonical, Calpha] using
      hCenterInvN B.n_gt_one hWne S j
  have hCenterInvActual : ∀ j : Fin (M.cellCount + 1),
      1 / B.partition.center j ≤
        Calpha * Real.log (Scale.L B.sampleData.n) := by
    intro j
    rw [hpartitionUser]
    simpa only [Calpha] using hCenterInvN B.n_gt_one hWne S j
  have hCenterLowerActual : ∀ j : Fin (M.cellCount + 1),
      centerScale / Real.log (Scale.L B.sampleData.n) ≤
        B.partition.center j := by
    intro j
    rw [hpartitionUser]
    simpa only [centerScale, Calpha] using
      hCenterLowerN B.n_gt_one hWne S j
  have hPattern : B.sampleData.pattern = Phead := by
    rw [hcanonical]
    rfl
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
  have hGuards : B.sampleData.guards =
      (ledger B.sampleData.n).guards := by
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
  have hphys : |xi MomentCoord.physical| ≤ Aphys := by
    calc
      |xi MomentCoord.physical| =
          ‖B.nuisanceParameter xi NuisanceCoord.physical‖ := by
        simp only [B.nuisanceParameter_physical, Real.norm_eq_abs]
      _ ≤ ‖B.nuisanceParameter xi‖ :=
        PiLp.norm_apply_le (B.nuisanceParameter xi)
          NuisanceCoord.physical
      _ ≤ Aphys := by simpa only [Acoef, Aphys] using hnuisance
  obtain ⟨hpair, hsingle⟩ := hprofile B xi hnProfile
    hPattern hLo hHi hGuards heta hphys rfl
  have hKernelDiagonal : ∀ p ∈
      primeBand B.sampleData.n B.sampleData.W,
      |covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤
        CKernel := by
    intro p hp
    have ht0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
      B.n_gt_one hp
    have ht1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
      B.n_gt_one hp
    calc
      |covarianceKernel (tPrime B.sampleData.n p)
          (tPrime B.sampleData.n p)| ≤
          CKernel * tPrime B.sampleData.n p :=
        hKernelBound _ ⟨ht0, ht1⟩ _ ⟨ht0, ht1⟩
      _ ≤ CKernel := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left ht1 hCKernel
  have hSquare : ∀ j : Fin (M.cellCount + 1),
      |squarefreeSharpRow (B.actualValuationLaw xi) B.partition
          (fun _ ↦ (1 : ℝ)) j -
        referenceSharpRow B.partition (fun _ ↦ (1 : ℝ)) j| ≤
          2 * w₀ := by
    intro j
    have hsquareArithmetic :=
      B.abs_actual_squarefreeSharpRow_sub_equalPartitionArithmetic_le
        xi hpartitionCanonical Ecanonical
        (hprofile0 B.sampleData.n) hBWlarge hpair hsingle
        hKernelDiagonal hBandTN hCenterInvCanonical
        (fun _ ↦ (1 : ℝ)) (fun _ ↦ by simp) j
    have href :=
      SquarefreeReferenceOperatorIdentification.referenceSharpRow_eq_arithmeticSharpOperator
      Ecanonical (fun _ ↦ (1 : ℝ)) j
        (Pcanonical.center_ne_zero B.n_gt_one j)
    rw [← href] at hsquareArithmetic
    have hsquareReference :
        |squarefreeSharpRow (B.actualValuationLaw xi) B.partition
            (fun _ ↦ (1 : ℝ)) j -
          referenceSharpRow Pcanonical (fun _ ↦ (1 : ℝ)) j| ≤
            squarefreeSharpProfileRemainder
              (fun _n ↦ profileError B.sampleData.n)
                Calpha K CKernel B.sampleData.W B.sampleData.n :=
      hsquareArithmetic
    have hrem : squarefreeSharpProfileRemainder
        (fun _n ↦ profileError B.sampleData.n)
          Calpha K CKernel B.sampleData.W B.sampleData.n =
        squarefreeSharpProfileRemainder
          profileError Calpha K CKernel B.sampleData.W B.sampleData.n := by
      rfl
    rw [hrem] at hsquareReference
    rw [← hpartitionCanonical] at hsquareReference
    exact hsquareReference.trans hSquareN.le
  have hUstrict : 1 < U :=
    (hlowerOne .minus).trans_lt
      ((I.lower_lt_upper .minus).trans_le (hupperU .minus))
  have hcombined0 : 0 ≤ combined B.sampleData.n := by
    dsimp only [combined]
    exact canonicalCombinedPowerCorrection_nonneg
      Phead I hUstrict.le hAphys hBWlarge B.n_gt_one
  have hrawFull := hfullRaw B xi hnFull rfl hsep hremaining
    hcanonical heta hphys
  have hFull : ∀ j : Fin (M.cellCount + 1),
      |fullSharpRow (B.actualValuationLaw xi) B.partition
          (fun _ ↦ (1 : ℝ)) j -
        squarefreeSharpRow (B.actualValuationLaw xi) B.partition
          (fun _ ↦ (1 : ℝ)) j| ≤ 2 * w₀ := by
    intro j
    have hraw := hrawFull (fun _ ↦ (1 : ℝ)) (fun _ ↦ by simp) j
    have hbounded := B.fullSharpRow_le_canonicalFullSharpRemainder
      xi epsilon75 combined hCpow.le (hepsilon750 B.sampleData.n)
        hcombined0 (by omega) hBandTN hCenterInvActual
        (fun _ ↦ (1 : ℝ)) j
        (by simpa only [combined, canonicalCombinedPowerCorrection] using hraw)
    exact hbounded.trans hFullN.le
  have hrowResidual : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n)
          (primeKernel B.sampleData.n) p| ≤
        w₀ * tPrime B.sampleData.n p.1 := by
    intro p
    exact (hRowN p).trans
      (mul_le_mul_of_nonneg_right hdeltaW₀
        (B.bandPrime_tPrime_pos p).le)
  have hFdiff : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |F (tPrime B.sampleData.n p.1) -
          F (B.bandCenter (B.partition.band p))| ≤
        CF * |B.primeDeviation p| := by
    intro p
    have ht : tPrime B.sampleData.n p.1 ∈ Icc (0 : ℝ) 1 :=
      ⟨(B.bandPrime_tPrime_pos p).le,
        PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
          B.n_gt_one p.2⟩
    have hc := B.partition.center_mem_zero_one B.n_gt_one
      (B.partition.band p)
    have h := hFLipschitz _ ht _ hc
    simpa only [primeDeviation, bandCenter, abs_sub_comm] using h
  have hKernelProduct : ∀
      p q : BandPrime B.sampleData.n B.sampleData.W,
      |covarianceKernel (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n q.1)| ≤
        Cprod * tPrime B.sampleData.n p.1 *
          tPrime B.sampleData.n q.1 := by
    intro p q
    have hp : tPrime B.sampleData.n p.1 ∈ Icc (0 : ℝ) 1 :=
      ⟨(B.bandPrime_tPrime_pos p).le,
        PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
          B.n_gt_one p.2⟩
    have hq : tPrime B.sampleData.n q.1 ∈ Icc (0 : ℝ) 1 :=
      ⟨(B.bandPrime_tPrime_pos q).le,
        PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
          B.n_gt_one q.2⟩
    simpa only [covarianceKernel] using
      hProduct _ hp _ hq
  have hmarkedRows : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          markedError B.sampleData.n * (1 / (p.1 : ℝ)) := by
    intro c p
    exact hmarked B z hz hnMarked rfl hsep hremaining hcanonical c p
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
        hlowerOne hupperU hLo hHi T hbaseline hBWlarge z hz v
  have hgammaFloorLe : gammaFloor ≤ gamma := by
    dsimp only [gammaFloor, gamma]
    exact B.canonicalEffectiveNuisanceGammaFloor_le I hU
      (by positivity : 0 ≤ 3 * (a : ℝ)) hmarginFloor T hTmargin
  have hdimension : Real.sqrt
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤ droot := by
    dsimp only [droot]
    exact B.sqrt_nuisanceCoord_card_le_ceiling
  have hmomentExact :
      (∑ j : Fin (M.cellCount + 1),
        B.harmonicMass j * B.bandCenter j) =
          bandTReciprocalSum B.sampleData.n B.sampleData.W :=
    B.sum_harmonicMass_mul_bandCenter_eq_bandTReciprocalSum
  have hmoment :
      (∑ j : Fin (M.cellCount + 1),
        B.harmonicMass j * B.bandCenter j) ≤ K := by
    rw [hmomentExact]
    exact hBandTN
  let amin : ℝ := centerScale / Real.log (Scale.L B.sampleData.n)
  have hamin : 0 < amin := by
    dsimp only [amin]
    exact div_pos hcenterScale hLogLN
  have hcenterAmin : ∀ j : Fin (M.cellCount + 1),
      amin ≤ B.bandCenter j := by
    intro j
    simpa only [amin, bandCenter] using hCenterLowerActual j
  have hrateMajorized :
      B.nuisanceMarkedSchurRate (markedError B.sampleData.n) gamma amin ≤
        schurMajorant B.sampleData.n := by
    have hraw := B.nuisanceMarkedSchurRate_le_selectedMeshSchurRateMajorant
      (epsilon := markedError B.sampleData.n)
      (droot := droot) (momentBound := K)
      (gammaFloor := gammaFloor) (gamma := gamma)
      (centerScale := centerScale) (n := B.sampleData.n)
      (hmarked0 B.sampleData.n) hdroot hK hgammaFloor hgammaFloorLe
      hcenterScale hLogLN hdimension hmoment
    simpa only [amin, schurMajorant] using hraw
  have hrateSmall :
      B.nuisanceMarkedSchurRate (markedError B.sampleData.n) gamma amin ≤
        w₀ := hrateMajorized.trans hSchurN.le
  let nuisanceRaw : ℝ :=
    ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (markedError B.sampleData.n *
          (∑ j : Fin (M.cellCount + 1),
            B.harmonicMass j * B.bandCenter j))) / gamma) *
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        markedError B.sampleData.n)
  have hnuisanceAmin : nuisanceRaw ≤ w₀ * amin := by
    have hdiv := (div_le_iff₀ hamin).mp hrateSmall
    simpa only [nuisanceMarkedSchurRate, nuisanceRaw] using hdiv
  have hnuisance : nuisanceRaw ≤ w₀ * B.bandCenter i :=
    hnuisanceAmin.trans
      (mul_le_mul_of_nonneg_left (hcenterAmin i) hw₀.le)
  have hheadActual : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W := by
    intro h p
    rw [hPattern]
    exact hhead h p
  have hfinite := B.abs_actualSlowRightRow_le_of_profiles
    xi hgamma hgap hheadActual (hmarked0 B.sampleData.n) hmarkedRows
    hw₀.le hCF.le hCprod.le hrowResidual hFdiff hKernelProduct
    hdevSup hdevL1 hFull hSquare i
  have hassembled :
      |B.normalizedBandCovarianceRow xi
          (B.nuisanceResidualScore xi hgamma hgap B.slowScore) i| ≤
        (Crow * w₀) * B.bandCenter i := by
    have hraw :
        |B.normalizedBandCovarianceRow xi
            (B.nuisanceResidualScore xi hgamma hgap B.slowScore) i| ≤
          (2 * w₀ + 2 * w₀ +
              (w₀ + (2 * CF + 7 * Cprod) * w₀)) *
              B.bandCenter i + nuisanceRaw := by
      simpa only [nuisanceRaw] using hfinite
    calc
      |B.normalizedBandCovarianceRow xi
          (B.nuisanceResidualScore xi hgamma hgap B.slowScore) i| ≤
          (2 * w₀ + 2 * w₀ +
              (w₀ + (2 * CF + 7 * Cprod) * w₀)) *
              B.bandCenter i + nuisanceRaw := hraw
      _ ≤ (2 * w₀ + 2 * w₀ +
              (w₀ + (2 * CF + 7 * Cprod) * w₀)) *
              B.bandCenter i + w₀ * B.bandCenter i :=
        by
          simpa only [add_comm] using
            add_le_add_left hnuisance
              ((2 * w₀ + 2 * w₀ +
                (w₀ + (2 * CF + 7 * Cprod) * w₀)) *
                B.bandCenter i)
      _ = (Crow * w₀) * B.bandCenter i := by
        dsimp only [Crow]
        ring
  simpa only [xi, gamma, hscale] using hassembled

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
