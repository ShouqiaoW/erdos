import Erdos390.Full.PaperCanonicalLemma86GeometryCoefficientsEventually
import Erdos390.Full.PaperCanonicalLemma86RelativePrimePowerEventually
import Erdos390.Full.PaperActualLemma86PaperScale
import Erdos390.Full.PaperActualCompensatedMarkedRowProfiles
import Erdos390.Full.PaperCanonicalActualMomentBoundsEventually
import Erdos390.Full.PaperCanonicalActualPrimePowerWeightedRowEventually
import Erdos390.Full.PaperCanonicalMarkedNuisanceRows
import Erdos390.Full.PaperCanonicalNuisanceUniformFloor
import Erdos390.Full.PoissonDickmanKernelBounds
import Erdos390.Full.PaperActualSquarefreeReference
import Erdos390.Full.PaperCanonicalPrimeRowResidualEventually
import Erdos390.Full.PaperCanonicalLemma86AnchorEventually
import Erdos390.Full.PaperLemma86CommonConstants
import Erdos390.Full.PaperCanonicalLemma86CompensatedMarkedRowEventually

/-!
# Closed remaining outputs of paper Lemma 8.6

This file closes the three quantitative conclusions not contained in the
geometric/coefficient umbrella: two-sided paper-scale slow variance, the
relative prime-power quadratic error, and every compensated marked prime
row.  Its public theorem has no analytic hypotheses, anchor data, contracts,
or abstract comparison assumptions.  The two mesh parameters remain
independent and all constants used to choose the prime cutoff precede the
cutoff and the effective tilt box.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PrimeSums PaperWeightedInverseExport
open OmittedTiltPairChamber PaperPrimePowerChamberError
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open RegularMeshPrimeCutoffs PaperPermittedRegularMesh
open PaperCanonicalSlowKappa

namespace BridgeData

/-- Convert the permitted-mesh variance comparison to the literal relative
factor used by the finite paper-scale variance theorem. -/
private theorem paper_varianceFactor_mul_le
    {c w variance : ℝ} (hc : 0 < c)
    (h : w ^ 2 ≤ (456 / c ^ 2) * variance) :
    (c ^ 2 / 456) * w ^ 2 ≤ variance := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hfactor : 0 ≤ c ^ 2 / (456 : ℝ) := by positivity
  calc
    (c ^ 2 / 456) * w ^ 2 ≤
        (c ^ 2 / 456) * ((456 / c ^ 2) * variance) :=
      mul_le_mul_of_nonneg_left h hfactor
    _ = variance := by field_simp [hc2.ne']

/-- Eventual nonnegativity is enough to recover ordinary convergence from
the product-log rate supplied by the canonical power-correction APIs. -/
private theorem tendsto_zero_of_eventually_nonneg_mul_logL_zero_remaining
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

/-- A fixed upper-variance constant obtained by replacing every vanishing
profile by `1`, the reciprocal cutoff by `1`, and the weighted power row by
the fixed majorant `Rmax`. -/
def paperScaleLemma86SlowUpperUniformConstant
    (CF CKernel C K Rmax : ℝ) : ℝ :=
  paperScaleLemma86SlowUpperConstantOfRow 1 CF CKernel C K 1 Rmax

/-- Exact monotonicity calculation behind the uniform upper constant. -/
private theorem paperScaleLemma86SlowUpperConstantOfRow_le_uniform
    {Eprofile CF CKernel C K invW R Rmax : ℝ}
    (hE : 0 ≤ Eprofile) (hEone : Eprofile ≤ 1)
    (hCKernel : 0 ≤ CKernel)
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hInvW : 0 ≤ invW) (hInvWone : invW ≤ 1)
    (hRRmax : R ≤ Rmax) :
    paperScaleLemma86SlowUpperConstantOfRow
        Eprofile CF CKernel C K invW R ≤
      paperScaleLemma86SlowUpperUniformConstant CF CKernel C K Rmax := by
  let A : ℝ := 1 / DickmanBasic.rho DickmanBasic.U
  let CL1 : ℝ := slowL1Constant C K
  let CL2 : ℝ := slowL2Constant C K
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  have hCL1 : 0 ≤ CL1 := by dsimp only [CL1, slowL1Constant]; positivity
  have hCL2 : 0 ≤ CL2 := by dsimp only [CL2, slowL2Constant]; positivity
  have hE2 : Eprofile ^ 2 ≤ Eprofile := by
    nlinarith [mul_nonneg hE (sub_nonneg.mpr hEone)]
  have hpair : pairCovarianceScale Eprofile ≤
      pairCovarianceScale 1 := by
    dsimp only [pairCovarianceScale]
    have hcoef : 0 ≤ 1 + 2 * A := by positivity
    dsimp only [A] at hcoef ⊢
    nlinarith
  have hsigned : signedSecondConstant Eprofile CKernel ≤
      signedSecondConstant 1 CKernel := by
    dsimp only [signedSecondConstant]
    have hbase : A + 2 * Eprofile ≤ A + 2 := by linarith
    have hsquare := (sq_le_sq₀ (by positivity) (by positivity)).2 hbase
    dsimp only [A] at hsquare ⊢
    linarith
  have hsigned0 : 0 ≤ signedSecondConstant 1 CKernel := by
    dsimp only [signedSecondConstant]
    positivity
  have hsignedInv : signedSecondConstant Eprofile CKernel * invW ≤
      signedSecondConstant 1 CKernel * 1 := by
    calc
      _ ≤ signedSecondConstant 1 CKernel * invW :=
        mul_le_mul_of_nonneg_right hsigned hInvW
      _ ≤ signedSecondConstant 1 CKernel * 1 :=
        mul_le_mul_of_nonneg_left hInvWone hsigned0
  have hpairTerm : (4 * pairCovarianceScale Eprofile) * CL1 ^ 2 ≤
      (4 * pairCovarianceScale 1) * CL1 ^ 2 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpair (by norm_num)) (sq_nonneg CL1)
  have hdiagTerm : (2 * Eprofile) * CL2 ≤ (2 * 1) * CL2 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hEone (by norm_num)) hCL2
  have hsecondTerm :
      signedSecondConstant Eprofile CKernel * invW * CL2 ≤
        signedSecondConstant 1 CKernel * 1 * CL2 := by
    exact mul_le_mul_of_nonneg_right hsignedInv hCL2
  have hprimeFactor : 0 ≤ (1 + C) * (7 + C * K) := by positivity
  have hprimeTerm : ((1 + C) * (7 + C * K)) * R ≤
      ((1 + C) * (7 + C * K)) * Rmax :=
    mul_le_mul_of_nonneg_left hRRmax hprimeFactor
  dsimp only [paperScaleLemma86SlowUpperUniformConstant,
    paperScaleLemma86SlowUpperConstantOfRow,
    paperScaleSquarefreeSlowUpperConstant, CL1, CL2]
  dsimp only [CL1, CL2] at hpairTerm hdiagTerm hsecondTerm
  linarith

/- The main assumption-free eventual theorem is assembled below from the
geometry/coefficient terminal and the literal finite variance and marked-row
estimates. -/

set_option maxHeartbeats 4000000 in
/-- Canonical two-sided slow variance once the exact same-witness base
outputs have been supplied.  Every analytic ingredient is discharged inside
the theorem; its remaining hypotheses are precisely literal outputs of the
strengthened relative-power terminal on the same `e`. -/
theorem exists_paperFineMesh_cutoff_eventually_canonical_lemma86_variance_of_base
    (cMesh Creg : ℝ) (hcMesh : 0 < cMesh) (hCreg : 0 ≤ Creg) :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ gammaSlow : ℝ, 0 < gammaSlow ∧
      ∃ Cvar : ℝ, 0 < Cvar ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta)
        (_hPermitted : IsPermitted (cMesh := cMesh) M),
        delta + eta ≤ meshTol →
        ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
          (Phead : Head → HeadPattern.Pattern),
          (∀ h : Head, ∀ p : ℕ,
            p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
        ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
          (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
          (hupperU : ∀ sigma, I.upper sigma ≤ U),
        ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank)
          (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
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
                B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                  M hdelta B.n_gt_one hWne S) →
              (hscale : B.w = delta + eta) →
              ∀ (T : BarycentricTarget B.sampleData)
                (hTmargin : marginFloor ≤ T.cellMassMargin)
                (hbaseline : B.baseline = T.baseline)
                (z : B.EffectiveParamSpace)
                (hz : z ∈ closedBall
                  (0 : B.EffectiveParamSpace) (a : ℝ))
                (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge),
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
                        T hbaseline hBWlarge z hz) e) ≤ Creg * B.w →
                (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                  |B.partition.deviation p| ≤ B.w) →
                B.partition.totalL1 ≤ 7 * B.w →
                B.w ^ 2 ≤
                  (456 / cMesh ^ 2) * B.partition.variance →
                B.partition.variance ≤ 4 * B.w ^ 2 →
                B.partition.variance ≤ B.partition.centerEnergy →
                gammaSlow * B.w ^ 2 ≤
                    B.actualTwoStageCompensatedVariance
                      (B.effectiveParamEquiv z)
                      (B.canonicalEffectiveNuisanceGamma_pos
                        I U (3 * (a : ℝ)) T)
                      (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                        hU hlowerOne hupperU
                        (by intro sigma; rw [hcanonical]; rfl)
                        (by intro sigma; rw [hcanonical]; rfl)
                        T hbaseline hBWlarge z hz) e ∧
                  B.actualTwoStageCompensatedVariance
                      (B.effectiveParamEquiv z)
                      (B.canonicalEffectiveNuisanceGamma_pos
                        I U (3 * (a : ℝ)) T)
                      (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                        hU hlowerOne hupperU
                        (by intro sigma; rw [hcanonical]; rfl)
                        (by intro sigma; rw [hcanonical]; rfl)
                        T hbaseline hBWlarge z hz) e ≤
                    Cvar * B.w ^ 2 := by
  obtain ⟨CKernel, hCKernel, hKernelBound⟩ :=
    PoissonDickmanKernelBounds.exists_covarianceKernel_abs_le_second
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  let K : ℝ := paperLemma86BandTConstant
  let CL1 : ℝ := slowL1Constant Creg K
  let CL2 : ℝ := slowL2Constant Creg K
  let varianceFactor : ℝ := paperLemma86VarianceFactor cMesh
  let anchorFloor : ℝ := (1 : ℝ) / 8
  let main : ℝ :=
    (canonicalSlowKappa / 4) * anchorFloor * varianceFactor
  let rowTarget : ℝ := main / (16 * CL2)
  let primeFactor : ℝ := (1 + Creg) * CL1
  let gammaSlow : ℝ := main / 2
  let CF : ℝ := 1 / DickmanBasic.rho DickmanBasic.U
  let Rmax : ℝ := Cpow + 2
  let Cvar : ℝ :=
    paperScaleLemma86SlowUpperUniformConstant CF CKernel Creg K Rmax
  have hCpow : 0 < Cpow := by
    simpa only [Cpow] using
      FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant_pos
  have hK : 0 ≤ K := by
    simpa only [K] using paperLemma86BandTConstant_nonneg
  have hCL1 : 0 < CL1 := by
    dsimp only [CL1, slowL1Constant]
    positivity
  have hCL2 : 0 < CL2 := by
    dsimp only [CL2, slowL2Constant]
    positivity
  have hvarianceFactor : 0 < varianceFactor := by
    simpa only [varianceFactor] using paperLemma86VarianceFactor_pos hcMesh
  have hanchorFloor : 0 < anchorFloor := by
    dsimp only [anchorFloor]
    norm_num
  have hmain : 0 < main := by
    dsimp only [main]
    exact mul_pos
      (mul_pos (div_pos canonicalSlowKappa_pos (by norm_num)) hanchorFloor)
      hvarianceFactor
  have hrowTarget : 0 < rowTarget := by
    dsimp only [rowTarget]
    positivity
  have hprimeFactor : 0 ≤ primeFactor := by
    dsimp only [primeFactor]
    positivity
  have hgammaSlow : 0 < gammaSlow := by
    dsimp only [gammaSlow]
    positivity
  have hCF : 0 < CF := by
    dsimp only [CF]
    exact one_div_pos.mpr DickmanBasic.rho_U_pos
  have hRmax : 0 < Rmax := by
    dsimp only [Rmax]
    positivity
  have hCvar : 0 < Cvar := by
    dsimp only [Cvar, paperScaleLemma86SlowUpperUniformConstant,
      paperScaleLemma86SlowUpperConstantOfRow,
      paperScaleSquarefreeSlowUpperConstant, CF, K, Rmax,
      slowL1Constant, slowL2Constant, signedSecondConstant,
      pairCovarianceScale]
    positivity
  obtain ⟨Wrow, hrowEvent⟩ :=
    _root_.Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.exists_cutoff_eventually_primeRowResidual_le
      hrowTarget
  have hInvNat : Tendsto (fun W : ℕ ↦ 1 / (W : ℝ))
      atTop (nhds 0) := by
    have hcast : Tendsto (fun W : ℕ ↦ (W : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hcast
  let tailConstant : ℝ :=
    signedSecondConstant 0 CKernel * CL2 + primeFactor * Cpow
  have htailT : Tendsto
      (fun W : ℕ ↦ tailConstant * (1 / (W : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hInvNat
  obtain ⟨Wtail, hWtail⟩ := eventually_atTop.1
    (htailT.eventually (eventually_lt_nhds
      (show 0 < main / 16 by positivity)))
  let meshTol : ℝ := (1 : ℝ) / 16
  let W₀ : ℕ := max 2 (max
    RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff
      (max Wrow Wtail))
  have hmeshTol : 0 < meshTol := by dsimp only [meshTol]; norm_num
  refine ⟨meshTol, hmeshTol, gammaSlow, hgammaSlow,
    Cvar, hCvar, W₀, ?_⟩
  intro W hW delta eta M hdelta hPermitted hfine
    Head _instHF _instHD _instHN Phead hPhead
    I U hU hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  have hWone : 1 < W := by
    dsimp only [W₀] at hW
    omega
  have hWanchor :
      RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWrow : Wrow ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWtail' : Wtail ≤ W := by
    dsimp only [W₀] at hW
    omega
  have htailSmall : tailConstant * (1 / (W : ℝ)) < main / 16 :=
    hWtail W hWtail'
  have hHeadLe : ∀ h, ∀ p ∈ (Phead h).primes, p ≤ W := by
    intro h p hp
    exact (hPhead h p).mp hp |>.2
  have hAnchorN :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPaperInteriorAnchorCutoff_eventually
      W hWanchor M hdelta (by simpa only [meshTol] using hfine)
  obtain ⟨_hCpowTerminal, hpowerTerminal⟩ :=
    boxIndependent_canonicalRaw_actualWeightedRow
      Phead I U hlowerOne hupperU Cprom Cbank ledger
  let Acoef : ℝ := 3 * (a : ℝ)
  let Aphys : ℝ := 3 * (a : ℝ)
  have hAcoef : 0 ≤ Acoef := by dsimp only [Acoef]; positivity
  have hAphys : 0 ≤ Aphys := by dsimp only [Aphys]; positivity
  obtain ⟨profileError, hprofile0, hprofileT, _hprofileRate,
      Nprofile, hprofile⟩ :=
    exists_boxIndependent_actual_component_signed_profiles
      Phead I U hlowerOne hupperU Cprom Cbank ledger W hWone hHeadLe
        Acoef Aphys hAcoef hAphys
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
  have hcombinedNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ combined n := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    exact canonicalCombinedPowerCorrection_nonneg
      Phead I hU hAphys hWone hn
  have hcombinedT : Tendsto combined atTop (nhds 0) :=
    tendsto_zero_of_eventually_nonneg_mul_logL_zero_remaining
      combined hcombinedNonneg hcombinedRate
  have hmarkedT : Tendsto markedError atTop (nhds 0) :=
    tendsto_zero_of_nonneg_mul_logL_zero
      markedError hmarked0 hmarkedRate
  let R : ℕ → ℝ := fun n ↦
    Cpow * (1 / (W : ℝ)) + epsilon75 n + combined n
  have hRT : Tendsto R atTop
      (nhds (Cpow * (1 / (W : ℝ)))) := by
    simpa only [R, add_zero] using
      (tendsto_const_nhds.add hepsilon75T).add hcombinedT
  have hpairT : Tendsto
      (fun n : ℕ ↦ pairCovarianceScale (profileError n))
      atTop (nhds 0) := by
    unfold pairCovarianceScale
    have hcoefT : Tendsto
        (fun _n : ℕ ↦
          (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U) : ℝ))
        atTop (nhds
          (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U) : ℝ)) :=
      tendsto_const_nhds
    simpa only [zero_mul, zero_pow (by norm_num : 2 ≠ 0), add_zero] using
      (hprofileT.mul hcoefT).add (hprofileT.pow 2)
  have hsignedT : Tendsto
      (fun n : ℕ ↦ signedSecondConstant (profileError n) CKernel)
      atTop (nhds (signedSecondConstant 0 CKernel)) := by
    have hcont : Continuous
        (fun x : ℝ ↦ signedSecondConstant x CKernel) := by
      unfold signedSecondConstant
      fun_prop
    exact hcont.continuousAt.tendsto.comp hprofileT
  let gammaFloor : ℝ := canonicalEffectiveNuisanceGammaFloor
    Head I U (3 * (a : ℝ)) W marginFloor
  have hgammaFloor : 0 < gammaFloor := by
    dsimp only [gammaFloor]
    exact canonicalEffectiveNuisanceGammaFloor_pos I hmargin
  let nuisanceLoss : ℕ → ℝ := fun n ↦
    (nuisanceDimensionCeiling Head * (markedError n * CL1)) ^ 2 /
      gammaFloor
  have hnuisanceT : Tendsto nuisanceLoss atTop (nhds 0) := by
    have hinner : Tendsto
        (fun n : ℕ ↦ nuisanceDimensionCeiling Head *
          (markedError n * CL1)) atTop (nhds 0) := by
      simpa only [mul_zero, zero_mul] using
        (tendsto_const_nhds.mul
          (hmarkedT.mul (tendsto_const_nhds : Tendsto
            (fun _n : ℕ ↦ CL1) atTop (nhds CL1))))
    have hdiv := (hinner.pow 2).div
      (tendsto_const_nhds : Tendsto
        (fun _n : ℕ ↦ gammaFloor) atTop (nhds gammaFloor))
      hgammaFloor.ne'
    simpa only [nuisanceLoss, zero_pow (by norm_num : 2 ≠ 0),
      zero_div] using hdiv
  let loss : ℕ → ℝ := fun n ↦
    rowTarget * CL2 +
      (4 * pairCovarianceScale (profileError n)) * CL1 ^ 2 +
      (2 * profileError n) * CL2 +
      signedSecondConstant (profileError n) CKernel *
        (1 / (W : ℝ)) * CL2 +
      primeFactor * R n + nuisanceLoss n
  let limitLoss : ℝ :=
    rowTarget * CL2 +
      signedSecondConstant 0 CKernel * (1 / (W : ℝ)) * CL2 +
      primeFactor * (Cpow * (1 / (W : ℝ)))
  have hlossT : Tendsto loss atTop (nhds limitLoss) := by
    have hrowConst : Tendsto (fun _n : ℕ ↦ rowTarget * CL2)
        atTop (nhds (rowTarget * CL2)) := tendsto_const_nhds
    have hoff : Tendsto
        (fun n : ℕ ↦
          (4 * pairCovarianceScale (profileError n)) * CL1 ^ 2)
        atTop (nhds 0) := by
      simpa only [mul_zero, zero_mul] using
        (tendsto_const_nhds.mul hpairT).mul tendsto_const_nhds
    have hdiag : Tendsto
        (fun n : ℕ ↦ (2 * profileError n) * CL2)
        atTop (nhds 0) := by
      simpa only [mul_zero, zero_mul] using
        (tendsto_const_nhds.mul hprofileT).mul tendsto_const_nhds
    have hsecond : Tendsto
        (fun n : ℕ ↦ signedSecondConstant (profileError n) CKernel *
          (1 / (W : ℝ)) * CL2)
        atTop (nhds (signedSecondConstant 0 CKernel *
          (1 / (W : ℝ)) * CL2)) :=
      (hsignedT.mul tendsto_const_nhds).mul tendsto_const_nhds
    have hprime : Tendsto (fun n : ℕ ↦ primeFactor * R n)
        atTop (nhds (primeFactor * (Cpow * (1 / (W : ℝ))))) :=
      tendsto_const_nhds.mul hRT
    simpa only [loss, limitLoss, add_zero] using
      ((((hrowConst.add hoff).add hdiag).add hsecond).add hprime).add
        hnuisanceT
  have hrowLoss : rowTarget * CL2 = main / 16 := by
    dsimp only [rowTarget]
    field_simp [hCL2.ne']
  have htailIdentity :
      signedSecondConstant 0 CKernel * (1 / (W : ℝ)) * CL2 +
          primeFactor * (Cpow * (1 / (W : ℝ))) =
        tailConstant * (1 / (W : ℝ)) := by
    dsimp only [tailConstant]
    ring
  have hlimitSmall : limitLoss < main / 8 := by
    dsimp only [limitLoss]
    rw [hrowLoss]
    calc
      main / 16 +
            signedSecondConstant 0 CKernel * (1 / (W : ℝ)) * CL2 +
            primeFactor * (Cpow * (1 / (W : ℝ))) =
          main / 16 + tailConstant * (1 / (W : ℝ)) := by
            rw [add_assoc, htailIdentity]
      _ < main / 8 := by linarith
  have hlossSmall : ∀ᶠ n : ℕ in atTop, loss n < main / 2 :=
    hlossT.eventually (eventually_lt_nhds (by linarith))
  have hprofileOne : ∀ᶠ n : ℕ in atTop, profileError n ≤ 1 :=
    hprofileT.eventually (eventually_le_nhds (by norm_num))
  have hepsilonOne : ∀ᶠ n : ℕ in atTop, epsilon75 n ≤ 1 :=
    hepsilon75T.eventually (eventually_le_nhds (by norm_num))
  have hcombinedOne : ∀ᶠ n : ℕ in atTop, combined n ≤ 1 :=
    hcombinedT.eventually (eventually_le_nhds (by norm_num))
  have hRowN := hrowEvent W hWrow
  have hbandTN := eventually_bandTReciprocalSum_le W
  filter_upwards [hAnchorN, hlossSmall, hprofileOne, hepsilonOne,
    hcombinedOne, hRowN, hbandTN, eventually_ge_atTop Nprofile,
    eventually_ge_atTop Npower, eventually_ge_atTop Nmarked,
    hcombinedNonneg] with
      n hAnchorAt hlossN hprofileOneN hepsilonOneN hcombinedOneN
      hRowAt hbandTAt hnProfile hnPower hnMarked hcombinedN
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition hscale
    T hTmargin hbaseline z hz e hsharp hdevSup hdevL1 hvarLower
    hdevL2 hvariance
  subst n
  subst W
  obtain ⟨hWneAnchor, hnAnchor, hAnchorAll⟩ := hAnchorAt
  obtain ⟨hWneUser, S, hpartitionUser⟩ := hpartition
  let Pcanonical := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hnAnchor hWneAnchor S
  let anchor := RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorSet
    M Pcanonical M.interiorAnchors
  have hpartitionCanonical : B.partition = Pcanonical := by
    exact hpartitionUser.trans (by dsimp only [Pcanonical])
  obtain ⟨hinteriorRaw, hAnchorMassRaw⟩ := hAnchorAll S
  have hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈
        Set.Icc ((1 : ℝ) / 8) (1 - (1 : ℝ) / 8) := by
    simpa only [anchor, Pcanonical] using hinteriorRaw
  have hAnchorMass : anchorFloor ≤
      anchorMass (primeWeight B.sampleData.n) anchor := by
    simpa only [anchorFloor, anchor, Pcanonical] using hAnchorMassRaw
  have hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor :=
    hanchorFloor.trans_le hAnchorMass
  have hrowResidual : ∀ p : PrimeIndex B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowTarget * tPrime B.sampleData.n p.1 := hRowAt
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
    hPattern hlo hhi hGuards heta hphys rfl
  have hactualRowRaw := hpower B xi hnPower rfl hsep hremaining
    hcanonical heta hphys
  have hactualRow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 r.1 -
            (B.actualValuationLaw xi).covII p.1 r.1| ≤
        R B.sampleData.n := by
    intro p
    simpa only [R, combined, canonicalCombinedPowerCorrection] using
      hactualRowRaw p
  have hmarkedRows : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          markedError B.sampleData.n * (1 / (p.1 : ℝ)) := by
    intro c p
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
  have hKernel : ∀ p r : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p.1) (tPrime B.sampleData.n r.1)| ≤
        CKernel := by
    intro p r
    have hp0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
      B.n_gt_one p.2
    have hp1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
      B.n_gt_one p.2
    have hr0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
      B.n_gt_one r.2
    have hr1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
      B.n_gt_one r.2
    calc
      _ ≤ CKernel * tPrime B.sampleData.n r.1 :=
        hKernelBound _ ⟨hp0, hp1⟩ _ ⟨hr0, hr1⟩
      _ ≤ CKernel := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hr1 hCKernel
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
  have hRnonneg : 0 ≤ R B.sampleData.n := by
    dsimp only [R]
    exact add_nonneg
      (add_nonneg (mul_nonneg hCpow.le (by positivity))
        (hepsilon750 B.sampleData.n)) hcombinedN
  have hgammaFloorLe : gammaFloor ≤ gamma := by
    dsimp only [gammaFloor, gamma]
    exact B.canonicalEffectiveNuisanceGammaFloor_le I hU
      (by positivity : 0 ≤ 3 * (a : ℝ)) hmargin T hTmargin
  have hdim : Real.sqrt
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤
        nuisanceDimensionCeiling Head :=
    B.sqrt_nuisanceCoord_card_le_ceiling
  have hnuisanceActual :
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (markedError B.sampleData.n * CL1)) ^ 2 / gamma ≤
        nuisanceLoss B.sampleData.n := by
    have hmul := mul_le_mul_of_nonneg_right hdim
      (mul_nonneg (hmarked0 B.sampleData.n) hCL1.le)
    have hsq := (sq_le_sq₀
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (hmarked0 B.sampleData.n) hCL1.le))
      (mul_nonneg (by unfold nuisanceDimensionCeiling; positivity)
        (mul_nonneg (hmarked0 B.sampleData.n) hCL1.le))).2 hmul
    calc
      _ ≤ (nuisanceDimensionCeiling Head *
            (markedError B.sampleData.n * CL1)) ^ 2 / gamma :=
        div_le_div_of_nonneg_right hsq hgamma.le
      _ ≤ (nuisanceDimensionCeiling Head *
            (markedError B.sampleData.n * CL1)) ^ 2 / gammaFloor :=
        div_le_div_of_nonneg_left (sq_nonneg _) hgammaFloor
          hgammaFloorLe
      _ = nuisanceLoss B.sampleData.n := by rfl
  have hconstant : gammaSlow ≤
      B.paperScaleLemma86SlowConstantOfRow varianceFactor anchorFloor
        rowTarget (profileError B.sampleData.n) CKernel Creg K
        (1 / (B.sampleData.W : ℝ)) (R B.sampleData.n)
        (markedError B.sampleData.n) gamma := by
    have hloss := hlossN.le
    dsimp only [nuisanceLoss, CL1, slowL1Constant] at hnuisanceActual
    dsimp only [loss, nuisanceLoss, gammaSlow, main,
      paperScaleLemma86SlowConstantOfRow,
      paperScaleSquarefreeSlowConstant, slowL1Constant,
      slowL2Constant, signedSecondConstant, CL1, CL2, primeFactor]
      at hloss ⊢
    nlinarith [hnuisanceActual]
  have hbandTB : bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K := by
    simpa only [K, paperLemma86BandTConstant] using hbandTAt
  have hvarFactor : varianceFactor * B.w ^ 2 ≤
      B.partition.variance := by
    simpa only [varianceFactor, paperLemma86VarianceFactor] using
      paper_varianceFactor_mul_le hcMesh hvarLower
  have hfinite :=
    B.actualTwoStageCompensatedVariance_bounds_paperScale_of_weightedRow
      xi hgamma hgap e hCreg hK hRnonneg hvarianceFactor.le
      hrowTarget.le (hprofile0 B.sampleData.n) hCF.le hCKernel
      (hmarked0 B.sampleData.n) hBWlarge.le hsharp hbandTB
      hdevSup hdevL1 hvarFactor hdevL2 hvariance anchor hinterior
      hmass hAnchorMass hrowResidual hpair hsingle hF hKernel
      hactualRow hmarkedRows
  have hlower :=
    (mul_le_mul_of_nonneg_right hconstant (sq_nonneg B.w)).trans hfinite.1
  have hInvWone : 1 / (B.sampleData.W : ℝ) ≤ 1 :=
    PaperPrimePowerRow.reciprocalCutoff_le_one hBWlarge
  have hRupper : R B.sampleData.n ≤ Rmax := by
    have hmainW := mul_le_mul_of_nonneg_left hInvWone hCpow.le
    dsimp only [R, Rmax]
    linarith
  have hupperConstant :=
    paperScaleLemma86SlowUpperConstantOfRow_le_uniform (CF := CF)
      (hprofile0 B.sampleData.n) hprofileOneN hCKernel hCreg hK
      (by positivity) hInvWone hRupper
  have hupper := hfinite.2.trans
    (mul_le_mul_of_nonneg_right hupperConstant (sq_nonneg B.w))
  exact ⟨by simpa only [xi, gamma, hgap] using hlower,
    by simpa only [Cvar, xi, gamma, hgap] using hupper⟩

/-!
The final paper interface below deliberately repeats the quantitative
clauses instead of returning an opaque package.  Thus its type itself checks
that the geometry, inverse, regression, prime-power, variance, and marked-row
conclusions all use one and the same finite Schur equivalence `e z hz`.
-/
set_option maxHeartbeats 4000000 in
/-- Complete assumption-free canonical terminal for paper Lemma 8.6. -/
theorem exists_paperFineMesh_cutoff_eventually_canonical_lemma86
    (cMesh : ℝ) (hcMesh : 0 < cMesh) :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Csharp : ℝ, 0 < Csharp ∧
      ∃ Cordinary : ℝ, 0 < Cordinary ∧
      ∃ Crow : ℝ, 0 ≤ Crow ∧
      ∃ Creg : ℝ, 0 ≤ Creg ∧
        Creg = Csharp * (2 * Crow) ∧
      ∃ Ccmp : ℝ, 0 < Ccmp ∧
      ∃ Crel : ℝ, 0 < Crel ∧
      ∃ gammaSlow : ℝ, 0 < gammaSlow ∧
      ∃ Cvar : ℝ, 0 < Cvar ∧
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
                  paperLemma86VarianceFactor cMesh * B.w ^ 2 ≤
                    B.partition.variance ∧
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
                            (e z hz)) p| ≤ Ccmp * B.w) ∧
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
                            (e z hz)) ≤ Ccmp * B.w ∧
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
                            (e z hz)) ≤ Ccmp * B.w ^ 2 ∧
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
                      gammaSlow * B.w ^ 2 ≤
                        B.actualTwoStageCompensatedVariance
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz) (e z hz) ∧
                      B.actualTwoStageCompensatedVariance
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz) (e z hz) ≤
                        Cvar * B.w ^ 2 ∧
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
  obtain ⟨markedTol, hmarkedTol, Csharp, hCsharp, Cordinary,
      hCordinary, Crow, hCrow, Creg, hCreg, hCregEq, Crel, hCrel,
      Wmarked, hMarked⟩ :=
    exists_paperFineMesh_cutoff_eventually_canonical_lemma86_compensatedMarkedRow
      cMesh hcMesh
  obtain ⟨Ccmp, hCcmp, hCommon⟩ :=
    exists_paperLemma86CompensatedConstant Creg hCreg
  obtain ⟨varianceTol, hvarianceTol, gammaSlow, hgammaSlow, Cvar,
      hCvar, Wvariance, hVariance⟩ :=
    exists_paperFineMesh_cutoff_eventually_canonical_lemma86_variance_of_base
      cMesh Creg hcMesh hCreg
  let meshTol : ℝ := min markedTol varianceTol
  let W₀ : ℕ := max Wmarked Wvariance
  have hmeshTol : 0 < meshTol := by
    dsimp only [meshTol]
    exact lt_min hmarkedTol hvarianceTol
  refine ⟨meshTol, hmeshTol, Csharp, hCsharp, Cordinary, hCordinary,
    Crow, hCrow, Creg, hCreg, hCregEq, Ccmp, hCcmp, Crel, hCrel,
    gammaSlow, hgammaSlow, Cvar, hCvar, W₀, ?_⟩
  intro W hW
  have hWmarked : Wmarked ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWvariance : Wvariance ≤ W := by
    dsimp only [W₀] at hW
    omega
  obtain ⟨CmarkedFinal, hCmarkedFinal, hMarkedW⟩ :=
    hMarked W hWmarked
  refine ⟨CmarkedFinal, hCmarkedFinal, ?_⟩
  intro delta eta M hdelta hPermitted hfine
    Head _instHF _instHD _instHN Phead hPhead I U hU hlowerOne hupperU
    Cprom Cbank ledger a marginFloor hmargin
  have hfineMarked : delta + eta ≤ markedTol :=
    hfine.trans (min_le_left _ _)
  have hfineVariance : delta + eta ≤ varianceTol :=
    hfine.trans (min_le_right _ _)
  obtain ⟨epsilonRel, hepsilonRel0, hepsilonRelT, hepsilonRelRate,
      hMarkedN⟩ :=
    hMarkedW M hdelta hPermitted hfineMarked Head Phead hPhead
      I U hU hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  have hVarianceN := hVariance W hWvariance M hdelta hPermitted
    hfineVariance Phead hPhead I U hU hlowerOne hupperU Cprom Cbank
      ledger a marginFloor hmargin
  refine ⟨epsilonRel, hepsilonRel0, hepsilonRelT, hepsilonRelRate, ?_⟩
  filter_upwards [hMarkedN, hVarianceN] with n hMarkedAt hVarianceAt
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition hscale
    T hTmargin hbaseline
  obtain ⟨hdev, hgL1, hVlowerRaw, hVupper, hVcenter, e, he,
      hinvSharp, hinvOrdinary, hTilt⟩ :=
    hMarkedAt B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
      hscale T hTmargin hbaseline
  have hGeometry := lemma86_geometry_bounds_with_positive_varianceFactor
    hcMesh hgL1 hVlowerRaw hVupper
  refine ⟨hdev, hGeometry.1, hGeometry.2.1, hGeometry.2.2,
    hVcenter, e, he, hinvSharp, hinvOrdinary, ?_⟩
  intro z hz
  obtain ⟨hslow, hnormal, hqSharp, hsupRaw, hL1Raw, hL2Raw,
      hrelative, hmarked⟩ := hTilt z hz
  let gamma := B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
  have hgamma : 0 < gamma := by
    dsimp only [gamma]
    exact B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
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
  have hgap : ∀ v, gamma * ‖v‖ ^ 2 ≤
      inner ℝ v (B.nuisanceCovarianceOperator
        (B.effectiveParamEquiv z) v) := by
    intro v
    simpa only [gamma] using
      B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
        hlowerOne hupperU hlo hhi T hbaseline hBWlarge z hz v
  have hL1ForCommon : B.partition.compensatedL1
      (B.actualBandRegression (B.effectiveParamEquiv z) hgamma hgap
        (e z hz)) ≤
        slowL1Constant Creg paperLemma86BandTConstant * B.w := by
    simpa only [gamma, hgap, paperLemma86BandTConstant,
      slowL1Constant] using hL1Raw
  have hL2ForCommon : B.partition.compensatedL2Sq
      (B.actualBandRegression (B.effectiveParamEquiv z) hgamma hgap
        (e z hz)) ≤
        slowL2Constant Creg paperLemma86BandTConstant * B.w ^ 2 := by
    simpa only [gamma, hgap, paperLemma86BandTConstant,
      slowL2Constant] using hL2Raw
  have hsupForCommon : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.actualCompensatedCoefficient
        (B.actualBandRegression (B.effectiveParamEquiv z) hgamma hgap
          (e z hz)) p| ≤ (1 + Creg) * B.w := by
    simpa only [gamma, hgap] using hsupRaw
  obtain ⟨hsup, hL1, hL2⟩ :=
    hCommon B (B.effectiveParamEquiv z) hgamma hgap (e z hz)
      hsupForCommon hL1ForCommon hL2ForCommon
  have hvariance := hVarianceAt B hBn hBW hBWlarge hsep hremaining
    hcanonical hpartition hscale T hTmargin hbaseline z hz (e z hz)
      hqSharp hdev hgL1 hVlowerRaw hVupper hVcenter
  refine ⟨hslow, hnormal, hqSharp, ?_, ?_, ?_, hrelative,
    hvariance.1, hvariance.2, hmarked⟩
  · simpa only [gamma, hgap] using hsup
  · simpa only [gamma, hgap] using hL1
  · simpa only [gamma, hgap] using hL2

end BridgeData

end


end Erdos390.Full.PaperBridgeFit
