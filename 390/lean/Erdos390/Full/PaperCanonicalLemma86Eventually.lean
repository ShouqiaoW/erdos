import Erdos390.Full.PaperActualLemma86WeightedRow
import Erdos390.Full.PaperCanonicalActualMomentBoundsEventually
import Erdos390.Full.PaperCanonicalActualPrimePowerWeightedRowEventually
import Erdos390.Full.PaperCanonicalMarkedNuisanceRows
import Erdos390.Full.PaperCanonicalNuisanceUniformFloor
import Erdos390.Full.PaperSelectedMeshSchurRateEventually
import Erdos390.Full.PoissonDickmanKernelBounds

/-!
# Canonical eventual Lemma 8.6 up to the Lemma 8.4 splice

All inputs specific to the slow-variance proof are discharged here:

* actual prime moments and the moving-low relative normalization;
* a positive interior anchor block and the relative row residual;
* full signed component profiles;
* the actual weighted prime-power row through the raw reference law; and
* the finite nuisance marked rows and their uniform positive gap.

The only two displayed call-site estimates are the sharp inverse supplied by
Lemma 8.4 and the normalized slow right column.  They are left as explicit
arguments rather than hidden in a structure.  The cutoff `W` is selected
before the effective ball; all ball dependence enters only the eventual
ambient threshold.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PrimeSums PaperWeightedInverseExport
open OmittedTiltPairChamber PaperPrimePowerChamberError
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open RegularMeshPrimeCutoffs
open PaperCanonicalSlowKappa

namespace BridgeData

/-- A product-log rate together with eventual nonnegativity implies ordinary
convergence to zero.  This version is convenient for explicit arithmetic
remainders which are only meaningful after the ambient threshold. -/
theorem tendsto_zero_of_eventually_nonneg_mul_logL_zero
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

set_option maxHeartbeats 3000000 in
/-- Uniform canonical slow variance, with the exact Lemma 8.4 inverse and
slow-right-row splice left visible.

The dependency order is part of the statement: `Cinv` and `Crow` precede
the prime cutoff; the effective ball `a` is quantified only after `W` has
been fixed; the final `n` threshold may depend on that already selected
ball. -/
theorem exists_cutoff_eventually_canonicalLemma86_slow_of_schurSplice
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ (1 : ℝ) / 32)
    (Cinv Crow : ℝ) (hCinv : 0 < Cinv) (hCrow : 0 ≤ Crow) :
    ∃ gammaSlow : ℝ, 0 < gammaSlow ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        ∀ (M : RegularRelativeMesh.Mesh delta delta),
        ∀ (anchors : Finset (Fin M.cellCount)), anchors.Nonempty →
        (∀ k ∈ anchors, (1 / 8 : ℝ) < M.lower k) →
        (∀ k ∈ anchors, M.upper k ≤ 1 - (1 / 8 : ℝ)) →
        ((1 / 8 : ℝ) ≤ (∑ k ∈ anchors, M.width k) / 2) →
        ∀ {Head : Type*} [Fintype Head] [DecidableEq Head]
          [Nonempty Head],
        ∀ (Phead : Head → HeadPattern.Pattern)
          (I : PhysicalIntervals) (U : ℝ),
        (hU : 1 ≤ U) →
        (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma) →
        (hupperU : ∀ sigma, I.upper sigma ≤ U) →
        ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
        (∀ h, ∀ p ∈ (Phead h).primes, p ≤ W) →
        ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
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
                B.partition = Mesh.canonicalPartition M hdelta
                  B.n_gt_one hWne S) →
              (hscale : B.w = delta + M.ratio) →
              ∀ (T : BarycentricTarget B.sampleData),
                (hTmargin : marginFloor ≤ T.cellMassMargin) →
                (hbaseline : B.baseline = T.baseline) →
                ∀ (z : B.EffectiveParamSpace),
                  (hz : z ∈ closedBall
                    (0 : B.EffectiveParamSpace) (a : ℝ)) →
                  ∀ (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge),
                    (hinv : ∀ v,
                      paperSharpNorm B.harmonicMass B.bandCenter
                          (B.partition.center_ne_zero B.n_gt_one)
                          (e.symm v) ≤
                        Cinv *
                          paperSharpNorm B.harmonicMass B.bandCenter
                            (B.partition.center_ne_zero B.n_gt_one) v) →
                    (hrightRow : ∀ j,
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
                            B.slowScore) j| ≤
                        (Crow * B.w) * B.bandCenter j) →
                    gammaSlow * B.w ^ 2 ≤
                      B.actualTwoStageCompensatedVariance
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
                        e := by
  obtain ⟨CKernel, hCKernel, hKernelBound⟩ :=
    PoissonDickmanKernelBounds.exists_covarianceKernel_abs_le_second
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  have hCpow : 0 < Cpow := by
    simpa only [Cpow] using
      FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant_pos
  let K : ℝ := 2 * Real.log 4
  let Creg : ℝ := Cinv * (2 * Crow)
  let CL1 : ℝ := slowL1Constant Creg K
  let CL2 : ℝ := slowL2Constant Creg K
  let main : ℝ := canonicalSlowKappa * (1 / 8 : ℝ) / 64
  let rowTarget : ℝ := main / (16 * CL2)
  let primeFactor : ℝ := (1 + Creg) * CL1
  let gammaSlow : ℝ := main / 2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hCreg : 0 ≤ Creg := by
    dsimp only [Creg]
    exact mul_nonneg hCinv.le (mul_nonneg (by norm_num) hCrow)
  have hCL1 : 0 < CL1 := by
    dsimp only [CL1, slowL1Constant]
    positivity
  have hCL2 : 0 < CL2 := by
    dsimp only [CL2, slowL2Constant]
    positivity
  have hmain : 0 < main := by
    dsimp only [main]
    exact div_pos
      (mul_pos canonicalSlowKappa_pos (by norm_num)) (by norm_num)
  have hrowTarget : 0 < rowTarget := by
    dsimp only [rowTarget]
    exact div_pos hmain (mul_pos (by norm_num) hCL2)
  have hprimeFactor : 0 ≤ primeFactor := by
    dsimp only [primeFactor]
    positivity
  have hgammaSlow : 0 < gammaSlow := by
    dsimp only [gammaSlow]
    positivity
  obtain ⟨Wrow, hrowEvent⟩ :=
    _root_.Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.exists_cutoff_eventually_primeRowResidual_le
      hrowTarget
  let Wgeom : ℕ := max
    RegularMeshPrimeCutoffs.canonicalActualMomentCutoff
      (max RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff Wrow)
  have hInvNat : Tendsto (fun W : ℕ ↦ 1 / (W : ℝ))
      atTop (nhds 0) := by
    have hcast : Tendsto (fun W : ℕ ↦ (W : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun W : ℕ ↦ ((W : ℝ))⁻¹)
        atTop (nhds 0) := tendsto_inv_atTop_zero.comp hcast
    simpa only [one_div] using hinv
  let tailConstant : ℝ :=
    signedSecondConstant 0 CKernel * CL2 + primeFactor * Cpow
  have htailT : Tendsto
      (fun W : ℕ ↦ tailConstant * (1 / (W : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hInvNat
  obtain ⟨Wtail, hWtail⟩ := eventually_atTop.1
    (htailT.eventually (eventually_lt_nhds (show 0 < main / 16 by
      positivity)))
  let W₀ := max 2 (max Wgeom Wtail)
  refine ⟨gammaSlow, hgammaSlow, W₀, ?_⟩
  intro W hWcut M anchors hAnchors hIdealLower hIdealUpper hIdealMass
    Head _instHead _instHeadDec _instHeadNonempty
    Phead I U hU hlowerOne hupperU Cprom Cbank ledger hHeadLe
    a marginFloor hmarginFloor
  have hWone : 1 < W := by
    have : 2 ≤ W := (le_max_left 2 _).trans hWcut
    omega
  have hWgeom : Wgeom ≤ W :=
    ((le_max_left Wgeom Wtail).trans (le_max_right 2 _)).trans hWcut
  have hWmoment : RegularMeshPrimeCutoffs.canonicalActualMomentCutoff ≤ W :=
    (le_max_left _ _).trans hWgeom
  have hWanchor : RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff ≤ W :=
    ((le_max_left _ _).trans (le_max_right
      RegularMeshPrimeCutoffs.canonicalActualMomentCutoff _)).trans hWgeom
  have hWrow : Wrow ≤ W :=
    ((le_max_right _ Wrow).trans (le_max_right
      RegularMeshPrimeCutoffs.canonicalActualMomentCutoff _)).trans hWgeom
  have hWtail' : Wtail ≤ W :=
    ((le_max_right Wgeom Wtail).trans (le_max_right 2 _)).trans hWcut
  have htailSmall : tailConstant * (1 / (W : ℝ)) < main / 16 :=
    hWtail W hWtail'
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
      Phead I U hlowerOne hupperU Cprom Cbank ledger
      W hWone hHeadLe
        Acoef Aphys hAcoef hAphys
  obtain ⟨epsilon75, hepsilon750, hepsilon75T, _hepsilon75Rate,
      hcombinedRateRaw, Npower, hpower⟩ :=
    hpowerTerminal W hWone hHeadLe
      Acoef hAcoef Aphys hAphys
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
        (fun _n : ℕ ↦ (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U) : ℝ))
        atTop
        (nhds (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U) : ℝ)) :=
      tendsto_const_nhds
    have hlinear := hprofileT.mul hcoefT
    have hsquare := hprofileT.pow 2
    simpa only [zero_mul, zero_pow (by norm_num : 2 ≠ 0), add_zero] using
      hlinear.add hsquare
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
    exact canonicalEffectiveNuisanceGammaFloor_pos I hmarginFloor
  let nuisanceLoss : ℕ → ℝ := fun n ↦
    (nuisanceDimensionCeiling Head * (markedError n * CL1)) ^ 2 /
      gammaFloor
  have hnuisanceT : Tendsto nuisanceLoss atTop (nhds 0) := by
    have hinner : Tendsto
        (fun n : ℕ ↦ nuisanceDimensionCeiling Head *
          (markedError n * CL1)) atTop (nhds 0) := by
      have hdimT : Tendsto
          (fun _n : ℕ ↦ nuisanceDimensionCeiling Head)
          atTop (nhds (nuisanceDimensionCeiling Head)) :=
        tendsto_const_nhds
      have hCL1T : Tendsto (fun _n : ℕ ↦ CL1)
          atTop (nhds CL1) := tendsto_const_nhds
      simpa only [mul_zero, zero_mul] using
        hdimT.mul (hmarkedT.mul hCL1T)
    have hsq := hinner.pow 2
    have hconst : Tendsto (fun _n : ℕ ↦ gammaFloor)
        atTop (nhds gammaFloor) := tendsto_const_nhds
    have hdiv := hsq.div hconst hgammaFloor.ne'
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
        (fun n : ℕ ↦ (4 * pairCovarianceScale (profileError n)) * CL1 ^ 2)
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
    calc
      rowTarget * CL2 +
            signedSecondConstant 0 CKernel * (1 / (W : ℝ)) * CL2 +
          primeFactor * (Cpow * (1 / (W : ℝ))) =
          main / 16 +
            (signedSecondConstant 0 CKernel * (1 / (W : ℝ)) * CL2 +
              primeFactor * (Cpow * (1 / (W : ℝ)))) := by
            rw [hrowLoss]
            ring
      _ = main / 16 + tailConstant * (1 / (W : ℝ)) := by
        rw [htailIdentity]
      _ < main / 8 := by linarith
  have hlossSmall : ∀ᶠ n : ℕ in atTop, loss n < main / 2 :=
    hlossT.eventually (eventually_lt_nhds (by linarith))
  have hMomentN :=
    RegularMeshPrimeCutoffs.Mesh.canonicalActualMomentCutoff_eventually
      M hdelta W hWmoment
  have hAnchorN :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff_eventually
      M hdelta W hWanchor (epsilon := (1 / 8 : ℝ))
        anchors hAnchors hIdealLower hIdealUpper hIdealMass
  have hRowN := hrowEvent W hWrow
  have hbandTN := eventually_bandTReciprocalSum_le W
  filter_upwards [hlossSmall, hMomentN, hAnchorN, hRowN, hbandTN,
    eventually_ge_atTop Nprofile, eventually_ge_atTop Npower,
    eventually_ge_atTop Nmarked, hcombinedNonneg] with
      n hlossN hMomentAt hAnchorAt hRowAt hbandT
      hnProfile hnPower hnMarked hcombinedN
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition hscale
    T hTmargin hbaseline z hz e hinv hrightRow
  subst n
  subst W
  obtain ⟨hWneMoment, hnMoment, hMomentAll⟩ := hMomentAt
  obtain ⟨hWneAnchor, hnAnchor, hAnchorAll⟩ := hAnchorAt
  obtain ⟨hWneUser, S, hpartitionUser⟩ := hpartition
  let Pcanonical := Mesh.canonicalPartition M hdelta hnMoment hWneMoment S
  let anchor := Mesh.canonicalPrimeAnchorSet M Pcanonical anchors
  have hpartitionCanonical : B.partition = Pcanonical := by
    exact hpartitionUser.trans (by
      dsimp only [Pcanonical])
  obtain ⟨hdevSupRaw, hdevL1Raw, hvarLowerRaw, hdevL2Raw,
      _hrelL1, _hrelInv, _hrelVar⟩ := hMomentAll S
  obtain ⟨hinteriorRaw, hAnchorMassRaw⟩ := hAnchorAll S
  have hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈
        Set.Icc ((1 : ℝ) / 8) (1 - (1 : ℝ) / 8) := by
    simpa only [anchor, Pcanonical,
      Subsingleton.elim hnAnchor hnMoment,
      Subsingleton.elim hWneAnchor hWneMoment] using hinteriorRaw
  have hAnchorMass : (1 : ℝ) / 8 ≤
      anchorMass (primeWeight B.sampleData.n) anchor := by
    simpa only [anchor, Pcanonical,
      Subsingleton.elim hnAnchor hnMoment,
      Subsingleton.elim hWneAnchor hWneMoment] using hAnchorMassRaw
  have hvarianceRaw : Pcanonical.variance ≤ Pcanonical.centerEnergy :=
    RegularMeshPrimeCutoffs.Mesh.variance_le_centerEnergy_of_canonical_anchor
      M hdelta hdeltaSmall hnMoment hWneMoment S anchors
        hinterior hAnchorMass hdevL2Raw
  have hrowResidual : ∀ p : PrimeIndex B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n)
          (primeKernel B.sampleData.n) p| ≤
        rowTarget * tPrime B.sampleData.n p.1 := hRowAt
  have hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ B.w := by
    intro p
    rw [hpartitionCanonical, hscale]
    exact hdevSupRaw p
  have hdevL1 : B.partition.totalL1 ≤ 7 * B.w := by
    rw [hpartitionCanonical, hscale]
    exact hdevL1Raw
  have hvarLower : B.w ^ 2 / 16 ≤ B.partition.variance := by
    rw [hpartitionCanonical, hscale]
    exact hvarLowerRaw
  have hdevL2 : B.partition.variance ≤ 4 * B.w ^ 2 := by
    rw [hpartitionCanonical, hscale]
    exact hdevL2Raw
  have hvariance : B.partition.variance ≤ B.partition.centerEnergy := by
    rw [hpartitionCanonical]
    exact hvarianceRaw
  have hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor :=
    (by norm_num : (0 : ℝ) < 1 / 8).trans_le hAnchorMass
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
            (B.actualValuationLaw xi).covII p.1 r.1| ≤ R B.sampleData.n := by
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
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p.1) (tPrime B.sampleData.n r.1)| ≤
          CKernel * tPrime B.sampleData.n r.1 :=
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
        hlowerOne hupperU hlo hhi T hbaseline (by omega) z hz v
  have hright : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.actualBandRegressionTarget xi hgamma hgap) ≤
        (2 * Crow) * B.w := by
    exact B.actualBandRegressionTarget_sharpNorm_le_of_row
      xi hgamma hgap hCrow B.w_pos.le hrightRow
  have hsharpRaw := B.actualBandRegression_sharpNorm_le
    xi hgamma hgap e hCinv.le hinv hright
  have hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.actualBandRegression xi hgamma hgap e) ≤ Creg * B.w := by
    simpa only [Creg] using hsharpRaw
  have hRnonneg : 0 ≤ R B.sampleData.n := by
    dsimp only [R]
    exact add_nonneg
      (add_nonneg (mul_nonneg hCpow.le (by positivity))
        (hepsilon750 B.sampleData.n)) hcombinedN
  have hgammaFloorLe : gammaFloor ≤ gamma := by
    dsimp only [gammaFloor, gamma]
    exact B.canonicalEffectiveNuisanceGammaFloor_le I hU
      (by positivity : 0 ≤ 3 * (a : ℝ)) hmarginFloor T hTmargin
  have hdim : Real.sqrt
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤
        nuisanceDimensionCeiling Head :=
    B.sqrt_nuisanceCoord_card_le_ceiling
  have hnuisanceActual :
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (markedError B.sampleData.n * CL1)) ^ 2 / gamma ≤
        nuisanceLoss B.sampleData.n := by
    have hmarkedNonneg := hmarked0 B.sampleData.n
    have hCL1nonneg := hCL1.le
    have hmul := mul_le_mul_of_nonneg_right hdim
      (mul_nonneg hmarkedNonneg hCL1nonneg)
    have hsq := (sq_le_sq₀
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg hmarkedNonneg hCL1nonneg))
      (mul_nonneg (by
        unfold nuisanceDimensionCeiling
        positivity) (mul_nonneg hmarkedNonneg hCL1nonneg))).2 hmul
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
      B.actualLemma86SlowConstantOfRow canonicalSlowKappa (1 / 8)
        rowTarget (profileError B.sampleData.n) CKernel Creg K
        (R B.sampleData.n) (markedError B.sampleData.n) gamma := by
    have hloss := hlossN.le
    dsimp only [nuisanceLoss, CL1, slowL1Constant] at hnuisanceActual
    dsimp only [loss, nuisanceLoss, gammaSlow, main,
      actualLemma86SlowConstantOfRow,
      actualSquarefreeLowerConstant, slowL1Constant,
      slowL2Constant, signedSecondConstant, CL1, CL2, primeFactor]
      at hloss ⊢
    nlinarith [hnuisanceActual]
  have hbandTB : bandTReciprocalSum B.sampleData.n B.sampleData.W ≤ K := by
    simpa only [K] using hbandT
  have hfinite :=
    B.actualTwoStageCompensatedVariance_lower_canonicalKappa_of_weightedRow
      xi hgamma hgap e hCreg hK hRnonneg hrowTarget.le
      (hprofile0 B.sampleData.n) hCKernel (hmarked0 B.sampleData.n)
      hBWlarge.le hsharp hbandTB hdevSup hdevL1 hvarLower hdevL2
      hvariance anchor hinterior hmass hAnchorMass hrowResidual
      hpair hsingle hKernel hactualRow hmarkedRows
  exact (mul_le_mul_of_nonneg_right hconstant (sq_nonneg B.w)).trans hfinite

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
