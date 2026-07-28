import Erdos390.Full.PaperCanonicalLemma86RelativePrimePowerEventually
import Erdos390.Full.PaperActualCompensatedMarkedRowProfiles
import Erdos390.Full.PaperCanonicalActualPrimePowerWeightedRowEventually
import Erdos390.Full.PaperCanonicalMarkedNuisanceRows
import Erdos390.Full.PaperCanonicalNuisanceUniformFloor
import Erdos390.Full.PoissonDickmanKernelBounds

/-!
# Canonical compensated marked rows for paper Lemma 8.6

This file enriches the single exact Schur witness supplied by
`exists_paperFineMesh_cutoff_eventually_canonical_lemma86_relativePrimePower`.
All signed-profile, full-prime-power, and nuisance marked-row inputs are
discharged before the public conclusion.  After the prime cutoff `W` is
fixed, the final row constant is chosen before the mesh, head data, and
effective box; only the vanishing errors and the ambient threshold retain
dependence on those later data.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PrimeSums PaperWeightedInverseExport
open OmittedTiltPairChamber PaperPrimePowerChamberError
open RegularMeshPrimeCutoffs PaperPermittedRegularMesh

namespace BridgeData

/-- Product-log decay plus eventual nonnegativity implies ordinary decay. -/
private theorem tendsto_zero_of_eventually_nonneg_mul_logL_zero_marked
    (epsilon : ℕ → ℝ)
    (hepsilonNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ epsilon n)
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0)) :
    Tendsto epsilon atTop (nhds 0) := by
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne : ∀ᶠ n : ℕ in atTop,
      1 ≤ Real.log (Scale.L n) :=
    (Real.tendsto_log_atTop.comp hLTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hupper : ∀ᶠ n : ℕ in atTop,
      epsilon n ≤ epsilon n * Real.log (Scale.L n) := by
    filter_upwards [hepsilonNonneg, hlogOne] with n he hn
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn he
  exact squeeze_zero' hepsilonNonneg hupper hepsilonRate

/-- A deterministic head-majorant for the coefficient in the literal finite
compensated marked-row estimate. -/
def canonicalLemma86MarkedCoefficientMajorant
    (Head : Type*) [Fintype Head]
    (Creg K Eprofile CF CKernel invW R markedError gammaFloor : ℝ) : ℝ :=
  actualSquarefreeMarkedConstant Creg K Eprofile CF CKernel invW +
    (1 + Creg) * R +
    (((nuisanceDimensionCeiling Head *
          (markedError * slowL1Constant Creg K)) / gammaFloor) *
      (nuisanceDimensionCeiling Head * markedError))

/-- The limit of the preceding majorant when all ambient errors vanish. -/
def canonicalLemma86MarkedCoefficientLimit
    (Cpow Creg K CF CKernel invW : ℝ) : ℝ :=
  actualSquarefreeMarkedConstant Creg K 0 CF CKernel invW +
    (1 + Creg) * (Cpow * invW)

set_option maxHeartbeats 3000000 in
/--
Assumption-free canonical marked-row terminal.  It retains the complete
single-witness output of the relative prime-power terminal and appends the
literal compensated valuation row for every moving band prime.
-/
theorem exists_paperFineMesh_cutoff_eventually_canonical_lemma86_compensatedMarkedRow
    (cMesh : ℝ) (hcMesh : 0 < cMesh) :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Csharp : ℝ, 0 < Csharp ∧
      ∃ Cordinary : ℝ, 0 < Cordinary ∧
      ∃ Crow : ℝ, 0 ≤ Crow ∧
      ∃ Creg : ℝ, 0 ≤ Creg ∧
        Creg = Csharp * (2 * Crow) ∧
      ∃ Crel : ℝ, 0 < Crel ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∃ CmarkedFinal : ℝ, 0 ≤ CmarkedFinal ∧
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta)
        (hPermitted : IsPermitted (cMesh := cMesh) M),
        delta + eta ≤ meshTol →
        ∀ (Head : Type*) [Fintype Head] [DecidableEq Head] [Nonempty Head],
        ∀ (Phead : Head → HeadPattern.Pattern),
          (∀ h : Head, ∀ p : ℕ,
            p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
        ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
          (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
          (hupperU : ∀ sigma, I.upper sigma ≤ U),
        ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
        ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
        ∃ epsilonRel : ℕ → ℝ,
          (∀ᶠ n : ℕ in atTop, 0 ≤ epsilonRel n) ∧
          Tendsto epsilonRel atTop (nhds 0) ∧
          Tendsto
            (fun n : ℕ ↦ epsilonRel n * Real.log (Scale.L n))
              atTop (nhds 0) ∧
          ∀ᶠ n : ℕ in atTop,
            ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
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
                (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                    (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
                  B.partition =
                    RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                      M hdelta B.n_gt_one hWne S) →
                (hscale : B.w = delta + eta) →
                ∀ (T : BarycentricTarget B.sampleData)
                  (hTmargin : marginFloor ≤ T.cellMassMargin)
                  (hbaseline : B.baseline = T.baseline),
                  (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                      |B.partition.deviation p| ≤ B.w) ∧
                  B.partition.totalL1 ≤ 7 * B.w ∧
                  B.w ^ 2 ≤
                    (456 / cMesh ^ 2) * B.partition.variance ∧
                  B.partition.variance ≤ 4 * B.w ^ 2 ∧
                  B.partition.variance ≤ B.partition.centerEnergy ∧
                  ∃ e : ∀ (z : B.EffectiveParamSpace),
                      z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ) →
                        B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
                    (∀ (z : B.EffectiveParamSpace)
                        (hz : z ∈ closedBall
                          (0 : B.EffectiveParamSpace) (a : ℝ)) q,
                      e z hz q =
                        B.actualBandSchurLinearMap
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz) q) ∧
                    (∀ (z : B.EffectiveParamSpace)
                        (hz : z ∈ closedBall
                          (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                      paperSharpNorm B.harmonicMass B.bandCenter
                          (B.partition.center_ne_zero B.n_gt_one)
                          ((e z hz).symm v) ≤
                        Csharp *
                          paperSharpNorm B.harmonicMass B.bandCenter
                            (B.partition.center_ne_zero B.n_gt_one) v) ∧
                    (∀ (z : B.EffectiveParamSpace)
                        (hz : z ∈ closedBall
                          (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                      ‖(e z hz).symm v‖ ≤ Cordinary * ‖v‖) ∧
                    ∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ)),
                      (∀ j,
                        |B.normalizedBandCovarianceRow
                            (B.effectiveParamEquiv z)
                            (B.nuisanceResidualScore
                              (B.effectiveParamEquiv z)
                              (B.canonicalEffectiveNuisanceGamma_pos
                                I U (3 * (a : ℝ)) T)
                              (B.canonicalEffectiveNuisanceGap_on_closedBall
                                I a hU hlowerOne hupperU
                                (by intro sigma; rw [hcanonical]; rfl)
                                (by intro sigma; rw [hcanonical]; rfl)
                                T hbaseline hBWlarge z hz)
                              B.slowScore) j| ≤
                          (Crow * B.w) * B.bandCenter j) ∧
                      B.actualBandSchurLinearMap
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz)
                          (B.actualBandRegression
                            (B.effectiveParamEquiv z)
                            (B.canonicalEffectiveNuisanceGamma_pos
                              I U (3 * (a : ℝ)) T)
                            (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                              hU hlowerOne hupperU
                              (by intro sigma; rw [hcanonical]; rfl)
                              (by intro sigma; rw [hcanonical]; rfl)
                              T hbaseline hBWlarge z hz)
                            (e z hz)) =
                        B.actualBandRegressionTarget
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz) ∧
                      paperSharpNorm B.harmonicMass B.bandCenter
                          (B.partition.center_ne_zero B.n_gt_one)
                          (B.actualBandRegression
                            (B.effectiveParamEquiv z)
                            (B.canonicalEffectiveNuisanceGamma_pos
                              I U (3 * (a : ℝ)) T)
                            (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                              hU hlowerOne hupperU
                              (by intro sigma; rw [hcanonical]; rfl)
                              (by intro sigma; rw [hcanonical]; rfl)
                              T hbaseline hBWlarge z hz)
                            (e z hz)) ≤ Creg * B.w ∧
                      (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                        |B.actualCompensatedCoefficient
                          (B.actualBandRegression
                            (B.effectiveParamEquiv z)
                            (B.canonicalEffectiveNuisanceGamma_pos
                              I U (3 * (a : ℝ)) T)
                            (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                              hU hlowerOne hupperU
                              (by intro sigma; rw [hcanonical]; rfl)
                              (by intro sigma; rw [hcanonical]; rfl)
                              T hbaseline hBWlarge z hz)
                            (e z hz)) p| ≤ (1 + Creg) * B.w) ∧
                      B.partition.compensatedL1
                          (B.actualBandRegression
                            (B.effectiveParamEquiv z)
                            (B.canonicalEffectiveNuisanceGamma_pos
                              I U (3 * (a : ℝ)) T)
                            (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                              hU hlowerOne hupperU
                              (by intro sigma; rw [hcanonical]; rfl)
                              (by intro sigma; rw [hcanonical]; rfl)
                              T hbaseline hBWlarge z hz)
                            (e z hz)) ≤
                        (7 + Creg * (2 * Real.log 4)) * B.w ∧
                      B.partition.compensatedL2Sq
                          (B.actualBandRegression
                            (B.effectiveParamEquiv z)
                            (B.canonicalEffectiveNuisanceGamma_pos
                              I U (3 * (a : ℝ)) T)
                            (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                              hU hlowerOne hupperU
                              (by intro sigma; rw [hcanonical]; rfl)
                              (by intro sigma; rw [hcanonical]; rfl)
                              T hbaseline hBWlarge z hz)
                            (e z hz)) ≤
                        2 * (4 + Creg ^ 2 * (2 * Real.log 4)) * B.w ^ 2 ∧
                      |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
                          (B.postBandPrimeScore
                            (B.actualBandRegression
                              (B.effectiveParamEquiv z)
                              (B.canonicalEffectiveNuisanceGamma_pos
                                I U (3 * (a : ℝ)) T)
                              (B.canonicalEffectiveNuisanceGap_on_closedBall
                                I a hU hlowerOne hupperU
                                (by intro sigma; rw [hcanonical]; rfl)
                                (by intro sigma; rw [hcanonical]; rfl)
                                T hbaseline hBWlarge z hz)
                              (e z hz)))
                          (B.postBandPrimeScore
                            (B.actualBandRegression
                              (B.effectiveParamEquiv z)
                              (B.canonicalEffectiveNuisanceGamma_pos
                                I U (3 * (a : ℝ)) T)
                              (B.canonicalEffectiveNuisanceGap_on_closedBall
                                I a hU hlowerOne hupperU
                                (by intro sigma; rw [hcanonical]; rfl)
                                (by intro sigma; rw [hcanonical]; rfl)
                                T hbaseline hBWlarge z hz)
                              (e z hz))) -
                        (B.tiltedLaw (B.effectiveParamEquiv z)).covariance
                          (B.postBandSquarefreeScore
                            (B.actualBandRegression
                              (B.effectiveParamEquiv z)
                              (B.canonicalEffectiveNuisanceGamma_pos
                                I U (3 * (a : ℝ)) T)
                              (B.canonicalEffectiveNuisanceGap_on_closedBall
                                I a hU hlowerOne hupperU
                                (by intro sigma; rw [hcanonical]; rfl)
                                (by intro sigma; rw [hcanonical]; rfl)
                                T hbaseline hBWlarge z hz)
                              (e z hz)))
                          (B.postBandSquarefreeScore
                            (B.actualBandRegression
                              (B.effectiveParamEquiv z)
                              (B.canonicalEffectiveNuisanceGamma_pos
                                I U (3 * (a : ℝ)) T)
                              (B.canonicalEffectiveNuisanceGap_on_closedBall
                                I a hU hlowerOne hupperU
                                (by intro sigma; rw [hcanonical]; rfl)
                                (by intro sigma; rw [hcanonical]; rfl)
                                T hbaseline hBWlarge z hz)
                              (e z hz)))| ≤
                        (Crel * (1 / (B.sampleData.W : ℝ)) +
                          epsilonRel B.sampleData.n) * B.w ^ 2 ∧
                      ∀ p : BandPrime B.sampleData.n B.sampleData.W,
                        |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
                          (fun m ↦ valuation p.1 (B.sampleData.value m))
                          (B.actualCompensatedScore
                            (B.effectiveParamEquiv z)
                            (B.canonicalEffectiveNuisanceGamma_pos
                              I U (3 * (a : ℝ)) T)
                            (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                              hU hlowerOne hupperU
                              (by intro sigma; rw [hcanonical]; rfl)
                              (by intro sigma; rw [hcanonical]; rfl)
                              T hbaseline hBWlarge z hz)
                            (B.actualBandRegression
                              (B.effectiveParamEquiv z)
                              (B.canonicalEffectiveNuisanceGamma_pos
                                I U (3 * (a : ℝ)) T)
                              (B.canonicalEffectiveNuisanceGap_on_closedBall
                                I a hU hlowerOne hupperU
                                (by intro sigma; rw [hcanonical]; rfl)
                                (by intro sigma; rw [hcanonical]; rfl)
                                T hbaseline hBWlarge z hz)
                              (e z hz)))| ≤
                          CmarkedFinal * B.w * (1 / (p.1 : ℝ)) := by
  obtain ⟨meshTol, hmeshTol, Csharp, hCsharp, Cordinary, hCordinary,
      Crow, hCrow, Creg, hCreg, hCregEq, Crel, hCrel, Wrelative,
      hRelative⟩ :=
    exists_paperFineMesh_cutoff_eventually_canonical_lemma86_relativePrimePower
      cMesh hcMesh
  obtain ⟨CKernel, hCKernel, hKernelBound⟩ :=
    PoissonDickmanKernelBounds.exists_covarianceKernel_abs_le_second
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  let K : ℝ := 2 * Real.log 4
  let CF : ℝ := 1 / DickmanBasic.rho DickmanBasic.U
  let W₀ : ℕ := max Wrelative 2
  have hCpow : 0 < Cpow := by
    simpa only [Cpow] using
      FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant_pos
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hCF : 0 ≤ CF := by
    dsimp only [CF]
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  refine ⟨meshTol, hmeshTol, Csharp, hCsharp, Cordinary, hCordinary,
    Crow, hCrow, Creg, hCreg, hCregEq, Crel, hCrel, W₀, ?_⟩
  intro W hW
  have hWrelative : Wrelative ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWone : 1 < W := by
    dsimp only [W₀] at hW
    omega
  let invW : ℝ := 1 / (W : ℝ)
  let markedLimit : ℝ :=
    canonicalLemma86MarkedCoefficientLimit Cpow Creg K CF CKernel invW
  let CmarkedFinal : ℝ := 1 + |markedLimit|
  have hCmarkedFinal : 0 ≤ CmarkedFinal := by
    dsimp only [CmarkedFinal]
    positivity
  refine ⟨CmarkedFinal, hCmarkedFinal, ?_⟩
  intro delta eta M hdelta hPermitted hfine
    Head _instFintype _instDecidable _instNonempty Phead hPhead
    I U hU hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  have hHeadLe : ∀ h, ∀ p ∈ (Phead h).primes, p ≤ W := by
    intro h p hp
    exact (hPhead h p).mp hp |>.2
  have hRelativeN := hRelative W hWrelative M hdelta hPermitted hfine
    Head Phead hPhead I U hU hlowerOne hupperU Cprom Cbank ledger
      a marginFloor hmargin
  obtain ⟨epsilonRel, hepsilonRelNonneg, hepsilonRelT,
      hepsilonRelRate, hRelativeEvent⟩ := hRelativeN
  let Acoef : ℝ := 3 * (a : ℝ)
  let Aphys : ℝ := 3 * (a : ℝ)
  have hAcoef : 0 ≤ Acoef := by dsimp only [Acoef]; positivity
  have hAphys : 0 ≤ Aphys := by dsimp only [Aphys]; positivity
  obtain ⟨profileError, hprofile0, hprofileT, _hprofileRate,
      Nprofile, hprofile⟩ :=
    exists_boxIndependent_actual_component_signed_profiles
      Phead I U hlowerOne hupperU Cprom Cbank ledger
        W hWone hHeadLe Acoef Aphys hAcoef hAphys
  obtain ⟨_hCpowTerminal, hPowerFamily⟩ :=
    boxIndependent_canonicalRaw_actualWeightedRow
      Phead I U hlowerOne hupperU Cprom Cbank ledger
  obtain ⟨epsilon75, hepsilon750, hepsilon75T, _hepsilon75Rate,
      hcombinedRateRaw, Npower, hpower⟩ :=
    hPowerFamily W hWone hHeadLe Acoef hAcoef Aphys hAphys
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
    tendsto_zero_of_eventually_nonneg_mul_logL_zero_marked
      combined hcombinedNonneg hcombinedRate
  have hmarkedT : Tendsto markedError atTop (nhds 0) :=
    tendsto_zero_of_nonneg_mul_logL_zero markedError hmarked0 hmarkedRate
  let R : ℕ → ℝ := fun n ↦
    Cpow * invW + epsilon75 n + combined n
  have hRT : Tendsto R atTop (nhds (Cpow * invW)) := by
    simpa only [R, add_zero] using
      (tendsto_const_nhds.add hepsilon75T).add hcombinedT
  let gammaFloor : ℝ := canonicalEffectiveNuisanceGammaFloor
    Head I U (3 * (a : ℝ)) W marginFloor
  have hgammaFloor : 0 < gammaFloor := by
    dsimp only [gammaFloor]
    exact canonicalEffectiveNuisanceGammaFloor_pos I hmargin
  let markedCoefficient : ℕ → ℝ := fun n ↦
    canonicalLemma86MarkedCoefficientMajorant Head Creg K
      (profileError n) CF CKernel invW (R n) (markedError n) gammaFloor
  have hsquarefreeMarkedT : Tendsto
      (fun n : ℕ ↦ actualSquarefreeMarkedConstant Creg K
        (profileError n) CF CKernel invW)
      atTop
      (nhds (actualSquarefreeMarkedConstant Creg K 0 CF CKernel invW)) := by
    have hcont : Continuous
        (fun x : ℝ ↦ actualSquarefreeMarkedConstant
          Creg K x CF CKernel invW) := by
      unfold actualSquarefreeMarkedConstant pairCovarianceScale
      fun_prop
    exact hcont.continuousAt.tendsto.comp hprofileT
  have hpowerMarkedT : Tendsto
      (fun n : ℕ ↦ (1 + Creg) * R n)
      atTop (nhds ((1 + Creg) * (Cpow * invW))) :=
    tendsto_const_nhds.mul hRT
  have hnuisanceMarkedT : Tendsto
      (fun n : ℕ ↦
        (((nuisanceDimensionCeiling Head *
              (markedError n * slowL1Constant Creg K)) / gammaFloor) *
          (nuisanceDimensionCeiling Head * markedError n)))
      atTop (nhds 0) := by
    have hcont : Continuous (fun x : ℝ ↦
        (((nuisanceDimensionCeiling Head *
              (x * slowL1Constant Creg K)) / gammaFloor) *
          (nuisanceDimensionCeiling Head * x))) := by
      fun_prop
    simpa only [mul_zero, zero_mul, zero_div] using
      hcont.continuousAt.tendsto.comp hmarkedT
  have hmarkedCoefficientT : Tendsto markedCoefficient atTop
      (nhds markedLimit) := by
    have hsum :=
      (hsquarefreeMarkedT.add hpowerMarkedT).add hnuisanceMarkedT
    simpa only [markedCoefficient, markedLimit,
      canonicalLemma86MarkedCoefficientMajorant,
      canonicalLemma86MarkedCoefficientLimit, add_zero] using hsum
  have hlimitLt : markedLimit < CmarkedFinal := by
    dsimp only [CmarkedFinal]
    linarith [le_abs_self markedLimit]
  have hmarkedCoefficientBound : ∀ᶠ n : ℕ in atTop,
      markedCoefficient n < CmarkedFinal :=
    hmarkedCoefficientT.eventually (eventually_lt_nhds hlimitLt)
  have hBandT := eventually_bandTReciprocalSum_le W
  refine ⟨epsilonRel, hepsilonRelNonneg, hepsilonRelT,
    hepsilonRelRate, ?_⟩
  filter_upwards [hRelativeEvent, hcombinedNonneg,
    hmarkedCoefficientBound, hBandT, eventually_ge_atTop Nprofile,
    eventually_ge_atTop Npower, eventually_ge_atTop Nmarked] with
      n hRelativeAt hcombinedAt hmarkedCoefficientAt hBandTAt
      hnProfile hnPower hnMarked
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition hscale
    T hTmargin hbaseline
  obtain ⟨hdev, hdevL1, hvarLower, hdevL2, hcenter,
      e, he, hinv, hinvOrd, hRelativeZ⟩ :=
    hRelativeAt B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
      hscale T hTmargin hbaseline
  refine ⟨hdev, hdevL1, hvarLower, hdevL2, hcenter,
    e, he, hinv, hinvOrd, ?_⟩
  intro z hz
  obtain ⟨hslow, hnormal, hqSharp, hcoeffSup, hcoeffL1,
      hcoeffL2, hrelativePower⟩ := hRelativeZ z hz
  refine ⟨hslow, hnormal, hqSharp, hcoeffSup, hcoeffL1,
    hcoeffL2, hrelativePower, ?_⟩
  intro p
  let xi : B.ParamSpace := B.effectiveParamEquiv z
  have hznorm : ‖z‖ ≤ (a : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using hz
  have hsize : B.paperEffectiveSize xi ≤ Acoef := by
    dsimp only [xi, Acoef]
    exact (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
      (mul_le_mul_of_nonneg_left hznorm (by norm_num))
  have heffective := B.effective_bounds_of_paperEffectiveSize xi hsize
  have heta : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi r| ≤ Acoef := heffective.1
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
  have hnProfileB : Nprofile ≤ B.sampleData.n := by
    simpa only [hBn] using hnProfile
  have hnPowerB : Npower ≤ B.sampleData.n := by
    simpa only [hBn] using hnPower
  have hnMarkedB : Nmarked ≤ B.sampleData.n := by
    simpa only [hBn] using hnMarked
  have hcombinedB : 0 ≤ combined B.sampleData.n := by
    simpa only [hBn] using hcombinedAt
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
  obtain ⟨hpair, hsingle⟩ := hprofile B xi hnProfileB
    hPattern hlo hhi hGuards heta hphys hBW
  have hrowRaw := hpower B xi hnPowerB hBW hsep hremaining hcanonical
    heta hphys
  have hRnonneg : 0 ≤ R B.sampleData.n := by
    dsimp only [R]
    exact add_nonneg
      (add_nonneg (mul_nonneg hCpow.le (by positivity))
        (hepsilon750 B.sampleData.n)) hcombinedB
  have hrow : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      (r.1 : ℝ) *
        ∑ s : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV r.1 s.1 -
            (B.actualValuationLaw xi).covII r.1 s.1| ≤
        R B.sampleData.n := by
    intro r
    simpa only [R, invW, combined,
      canonicalCombinedPowerCorrection, hBW] using hrowRaw r
  have hmarkedRows : ∀ (c : NuisanceCoord B.HeadIndex)
      (r : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation r.1 (B.sampleData.value m))| ≤
          markedError B.sampleData.n * (1 / (r.1 : ℝ)) := by
    intro c r
    simpa only [xi] using
      hmarked B z hz hnMarkedB hBW hsep hremaining hcanonical c r
  have hF : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n r.1)| ≤ CF := by
    intro r
    have ht0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
      B.n_gt_one r.2
    have ht1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
      B.n_gt_one r.2
    have harg : DickmanBasic.U - tPrime B.sampleData.n r.1 ∈
        Set.Icc (1 : ℝ) 5 := by
      constructor <;> norm_num [DickmanBasic.U] <;> linarith
    have hone : (1 : ℝ) ∈ Set.Icc (1 : ℝ) 5 := by norm_num
    have hrho : DickmanBasic.rho
        (DickmanBasic.U - tPrime B.sampleData.n r.1) ≤ 1 := by
      simpa only [DickmanBasic.rho_one] using
        DickmanBasic.antitoneOn_rho_one_five hone harg (by
          norm_num [DickmanBasic.U]
          linarith)
    rw [abs_of_pos (DickmanBasic.F_pos ⟨ht0, ht1.trans (by norm_num)⟩)]
    unfold DickmanBasic.F
    exact (div_le_div_iff_of_pos_right DickmanBasic.rho_U_pos).2 hrho
  have hKernel : ∀ r s : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n r.1)
          (tPrime B.sampleData.n s.1)| ≤ CKernel := by
    intro r s
    have hr0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
      B.n_gt_one r.2
    have hr1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
      B.n_gt_one r.2
    have hs0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
      B.n_gt_one s.2
    have hs1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
      B.n_gt_one s.2
    calc
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n r.1)
          (tPrime B.sampleData.n s.1)| ≤
          CKernel * tPrime B.sampleData.n s.1 :=
        hKernelBound _ ⟨hr0, hr1⟩ _ ⟨hs0, hs1⟩
      _ ≤ CKernel := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hs1 hCKernel
  have hbandTB : bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K := by
    simpa only [hBn, hBW, K] using hBandTAt
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
        hlowerOne hupperU hlo hhi T hbaseline hBWlarge z hz v
  let q := B.actualBandRegression xi hgamma hgap (e z hz)
  have hq : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ Creg * B.w := by
    simpa only [q, xi, gamma, hgap] using hqSharp
  have hgammaFloorLe : gammaFloor ≤ gamma := by
    dsimp only [gammaFloor, gamma]
    simpa only [hBW] using
      B.canonicalEffectiveNuisanceGammaFloor_le I hU
        (by positivity : 0 ≤ 3 * (a : ℝ)) hmargin T hTmargin
  have hdim : Real.sqrt
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤
        nuisanceDimensionCeiling Head :=
    B.sqrt_nuisanceCoord_card_le_ceiling
  have hCL1 : 0 ≤ slowL1Constant Creg K := by
    unfold slowL1Constant
    positivity
  have hdim0 : 0 ≤ nuisanceDimensionCeiling Head := by
    unfold nuisanceDimensionCeiling
    positivity
  have hmarkedB : 0 ≤ markedError B.sampleData.n :=
    hmarked0 B.sampleData.n
  let sqrtDim : ℝ :=
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  have hsqrtDim0 : 0 ≤ sqrtDim := by
    dsimp only [sqrtDim]
    positivity
  have hA : sqrtDim *
      (markedError B.sampleData.n * slowL1Constant Creg K) ≤
      nuisanceDimensionCeiling Head *
        (markedError B.sampleData.n * slowL1Constant Creg K) := by
    exact mul_le_mul_of_nonneg_right hdim
      (mul_nonneg hmarkedB hCL1)
  have hB : sqrtDim * markedError B.sampleData.n ≤
      nuisanceDimensionCeiling Head * markedError B.sampleData.n := by
    exact mul_le_mul_of_nonneg_right hdim hmarkedB
  have hAprime0 : 0 ≤ nuisanceDimensionCeiling Head *
      (markedError B.sampleData.n * slowL1Constant Creg K) :=
    mul_nonneg hdim0 (mul_nonneg hmarkedB hCL1)
  have hAdiv :
      (sqrtDim *
          (markedError B.sampleData.n * slowL1Constant Creg K)) / gamma ≤
        (nuisanceDimensionCeiling Head *
          (markedError B.sampleData.n * slowL1Constant Creg K)) /
            gammaFloor := by
    calc
      _ ≤ (nuisanceDimensionCeiling Head *
            (markedError B.sampleData.n * slowL1Constant Creg K)) /
          gamma :=
        div_le_div_of_nonneg_right hA hgamma.le
      _ ≤ (nuisanceDimensionCeiling Head *
            (markedError B.sampleData.n * slowL1Constant Creg K)) /
          gammaFloor :=
        div_le_div_of_nonneg_left hAprime0 hgammaFloor hgammaFloorLe
  have hB0 : 0 ≤ sqrtDim * markedError B.sampleData.n :=
    mul_nonneg hsqrtDim0 hmarkedB
  have hAprimeDiv0 : 0 ≤
      (nuisanceDimensionCeiling Head *
        (markedError B.sampleData.n * slowL1Constant Creg K)) /
          gammaFloor :=
    div_nonneg hAprime0 hgammaFloor.le
  have hnuisanceCoefficient :
      ((sqrtDim *
          (markedError B.sampleData.n * slowL1Constant Creg K)) / gamma) *
          (sqrtDim * markedError B.sampleData.n) ≤
        ((nuisanceDimensionCeiling Head *
          (markedError B.sampleData.n * slowL1Constant Creg K)) /
            gammaFloor) *
          (nuisanceDimensionCeiling Head * markedError B.sampleData.n) := by
    calc
      _ ≤ ((nuisanceDimensionCeiling Head *
            (markedError B.sampleData.n * slowL1Constant Creg K)) /
              gammaFloor) *
          (sqrtDim * markedError B.sampleData.n) :=
        mul_le_mul_of_nonneg_right hAdiv hB0
      _ ≤ ((nuisanceDimensionCeiling Head *
            (markedError B.sampleData.n * slowL1Constant Creg K)) /
              gammaFloor) *
          (nuisanceDimensionCeiling Head * markedError B.sampleData.n) :=
        mul_le_mul_of_nonneg_left hB hAprimeDiv0
  let actualCoefficient : ℝ :=
    actualSquarefreeMarkedConstant Creg K (profileError B.sampleData.n)
        CF CKernel (1 / (B.sampleData.W : ℝ)) +
      (1 + Creg) * R B.sampleData.n +
      ((sqrtDim *
          (markedError B.sampleData.n * slowL1Constant Creg K)) / gamma) *
        (sqrtDim * markedError B.sampleData.n)
  have hactualCoefficientMajorant : actualCoefficient ≤
      markedCoefficient B.sampleData.n := by
    dsimp only [actualCoefficient, markedCoefficient,
      canonicalLemma86MarkedCoefficientMajorant]
    rw [show (1 / (B.sampleData.W : ℝ)) = invW by
      dsimp only [invW]; rw [hBW]]
    linarith
  have hmarkedCoefficientB : markedCoefficient B.sampleData.n <
      CmarkedFinal := by
    simpa only [hBn] using hmarkedCoefficientAt
  have hactualCoefficientFinal : actualCoefficient ≤ CmarkedFinal :=
    hactualCoefficientMajorant.trans hmarkedCoefficientB.le
  have hfinite :=
    B.actualCompensatedScore_markedRow_bound_of_profiles_and_weightedRow
      xi q hCreg hK B.w_pos.le (hprofile0 B.sampleData.n) hCF hCKernel
      (hmarked0 B.sampleData.n) hBWlarge.le hq hbandTB hdev hdevL1
      hdevL2 hgamma hgap hpair hsingle hF hKernel hrow hmarkedRows p.2
  have hinvp0 : 0 ≤ (1 / (p.1 : ℝ)) := by positivity
  have hscaleNonneg : 0 ≤ B.w * (1 / (p.1 : ℝ)) :=
    mul_nonneg B.w_pos.le hinvp0
  have hcoefficientScaled :
      actualCoefficient * (B.w * (1 / (p.1 : ℝ))) ≤
        CmarkedFinal * (B.w * (1 / (p.1 : ℝ))) :=
    mul_le_mul_of_nonneg_right hactualCoefficientFinal hscaleNonneg
  have hfinite' :
      |(B.tiltedLaw xi).covariance
        (fun m ↦ valuation p.1 (B.sampleData.value m))
        (B.actualCompensatedScore xi hgamma hgap q)| ≤
          actualCoefficient * (B.w * (1 / (p.1 : ℝ))) := by
    calc
      _ ≤ actualSquarefreeMarkedConstant Creg K
              (profileError B.sampleData.n) CF CKernel
              (1 / (B.sampleData.W : ℝ)) * B.w *
              (1 / (p.1 : ℝ)) +
            (1 + Creg) * B.w * R B.sampleData.n *
              (1 / (p.1 : ℝ)) +
            (((sqrtDim *
                (markedError B.sampleData.n * slowL1Constant Creg K)) /
                gamma) *
              (sqrtDim * markedError B.sampleData.n)) * B.w *
                (1 / (p.1 : ℝ)) := by
          simpa only [sqrtDim, slowL1Constant] using hfinite
      _ = actualCoefficient * (B.w * (1 / (p.1 : ℝ))) := by
        dsimp only [actualCoefficient]
        ring
  have hfinal :
      |(B.tiltedLaw xi).covariance
        (fun m ↦ valuation p.1 (B.sampleData.value m))
        (B.actualCompensatedScore xi hgamma hgap q)| ≤
          CmarkedFinal * B.w * (1 / (p.1 : ℝ)) := by
    calc
      _ ≤ actualCoefficient * (B.w * (1 / (p.1 : ℝ))) := hfinite'
      _ ≤ CmarkedFinal * (B.w * (1 / (p.1 : ℝ))) := hcoefficientScaled
      _ = CmarkedFinal * B.w * (1 / (p.1 : ℝ)) := by ring
  simpa only [xi, gamma, hgap, q] using hfinal

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
