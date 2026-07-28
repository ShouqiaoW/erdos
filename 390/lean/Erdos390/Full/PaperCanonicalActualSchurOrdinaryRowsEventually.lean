import Erdos390.Full.PaperCanonicalActualSchurOrdinaryEndpointEventually
import Erdos390.Full.PaperActualFullOrdinaryRowTransfer
import Erdos390.Full.PaperActualSchurOrdinaryRow
import Erdos390.Full.PaperCanonicalActualPrimePowerWeightedRowEventually
import Erdos390.Full.PaperCanonicalMarkedNuisanceRows
import Erdos390.Full.PaperCanonicalNuisanceUniformFloor
import Erdos390.Full.PaperActualSquarefreeReference
import Erdos390.Full.PaperProposition87MarkedRowRate

/-!
# Fully discharged ordinary perturbation rows for Lemma 8.4

This file packages the three analytic perturbations used by the endpoint
ordinary inverse: squarefree-to-reference, full-to-squarefree, and the
nuisance Schur correction.  The fixed `1/W` tails are made small before the
head data and the effective tilt ball are selected.  Every dependence on the
later ball is confined to an eventual error in the ambient parameter `n`.

The only local premise retained by the last row is the exact first-moment to
centre-energy ratio.  That geometric premise is supplied, without analytic
assumptions, by the separate canonical moment-ratio terminal when the final
Lemma 8.4 wrapper is assembled.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PrimeSums PaperWeightedInverseExport
open RegularMeshPrimeCutoffs
open SquarefreeCovarianceReference
open PaperPrimePowerChamberError
open PrimeSquarefreeDirichletGeometry

namespace BridgeData

/-- A fixed ordinary row budget small enough for the two-stage endpoint
perturbation. -/
def canonicalOrdinaryRowTolerance (Cref Rproj : ℝ) : ℝ :=
  1 / (8 * Cref * (1 + Rproj))

/-- A fixed ordinary Schur-row budget small enough for the second Neumann
step. -/
def canonicalOrdinarySchurTolerance (Cref : ℝ) : ℝ :=
  1 / (8 * Cref)

theorem canonicalOrdinaryRowTolerance_pos
    {Cref Rproj : ℝ} (hCref : 0 < Cref) (hRproj : 0 ≤ Rproj) :
    0 < canonicalOrdinaryRowTolerance Cref Rproj := by
  unfold canonicalOrdinaryRowTolerance
  positivity

theorem canonicalOrdinarySchurTolerance_pos
    {Cref : ℝ} (hCref : 0 < Cref) :
    0 < canonicalOrdinarySchurTolerance Cref := by
  unfold canonicalOrdinarySchurTolerance
  positivity

theorem canonicalOrdinaryRows_small
    {Cref Rproj : ℝ} (hCref : 0 < Cref) (hRproj : 0 ≤ Rproj) :
    Cref * ((1 + Rproj) *
      (canonicalOrdinaryRowTolerance Cref Rproj +
        canonicalOrdinaryRowTolerance Cref Rproj)) ≤ 1 / 2 := by
  have hden : 0 < 8 * Cref * (1 + Rproj) := by positivity
  unfold canonicalOrdinaryRowTolerance
  field_simp [hCref.ne', (by linarith : (1 + Rproj) ≠ 0)]
  linarith

theorem canonicalOrdinarySchur_small
    {Cref : ℝ} (hCref : 0 < Cref) :
    (2 * Cref) * canonicalOrdinarySchurTolerance Cref ≤ 1 / 2 := by
  unfold canonicalOrdinarySchurTolerance
  field_simp [hCref.ne']
  linarith

/-- A product-log rate and eventual nonnegativity imply ordinary
convergence. -/
private theorem tendsto_zero_of_eventually_nonneg_mul_logL_zero
    (epsilon : ℕ → ℝ)
    (hepsilon : ∀ᶠ n : ℕ in atTop, 0 ≤ epsilon n)
    (hrate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0)) :
    Tendsto epsilon atTop (nhds 0) := by
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (Scale.L n) :=
    (Real.tendsto_log_atTop.comp hLTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hupper : ∀ᶠ n : ℕ in atTop,
      epsilon n ≤ epsilon n * Real.log (Scale.L n) := by
    filter_upwards [hepsilon, hlogOne] with n hn hlog
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog hn
  exact squeeze_zero' hepsilon hupper hrate

/-- The literal ordinary nuisance rate is bounded by a scalar majorant once
the total harmonic mass and the nuisance gap have uniform bounds. -/
theorem nuisanceMarkedOrdinarySchurRate_le_majorant
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {Cmarked gamma gammaFloor R H : ℝ}
    (hCmarked : 0 ≤ Cmarked) (hgammaFloor : 0 < gammaFloor)
    (hgammaFloorLe : gammaFloor ≤ gamma)
    (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hmass : (∑ j : Band, B.harmonicMass j) ≤ H) :
    B.nuisanceMarkedOrdinarySchurRate Cmarked gamma R ≤
      (1 + R) *
        (((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              (Cmarked * H)) / gammaFloor) *
          (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked)) := by
  have hgamma : 0 < gamma := hgammaFloor.trans_le hgammaFloorLe
  have hdroot : 0 ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) :=
    Real.sqrt_nonneg _
  have hmass0 : 0 ≤ ∑ j : Band, B.harmonicMass j :=
    Finset.sum_nonneg fun j hj ↦ (B.harmonicMass_pos j).le
  unfold nuisanceMarkedOrdinarySchurRate
  dsimp only
  have hsource :
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * ∑ j : Band, B.harmonicMass j) ≤
        Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * H) := by
    gcongr
  have hnum0 : 0 ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked * H) := by positivity
  have hdiv :
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * ∑ j : Band, B.harmonicMass j)) / gamma ≤
        (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * H)) / gammaFloor := by
    exact (div_le_div₀ hnum0 hsource hgammaFloor hgammaFloorLe : _)
  gcongr

set_option maxHeartbeats 3000000 in
/--
All three ordinary perturbation rows, with every analytic error discharged.

`Cref` and `Rproj` are fixed before `W`.  The cutoff is then fixed before the
head patterns and the effective ball.  The conclusion is uniform over that
whole ball and over every canonical bridge at the displayed `n,W`.
-/
theorem exists_cutoff_eventually_canonical_ordinary_perturbation_rows
    (Cref Rproj : ℝ) (hCref : 0 < Cref) (hRproj : 0 ≤ Rproj) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head],
      ∀ (Phead : Head → HeadPattern.Pattern),
        (∀ h : Head, ∀ p ∈ (Phead h).primes, p ≤ W) →
      ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
        (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
        (hupperU : ∀ sigma, I.upper sigma ≤ U),
      ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
      ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
      ∀ {Band : Type*} [Fintype Band] [DecidableEq Band] [Nonempty Band],
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
            ∀ (T : BarycentricTarget B.sampleData)
              (_hTmargin : marginFloor ≤ T.cellMassMargin)
              (hbaseline : B.baseline = T.baseline),
              ((∑ j : Band, B.harmonicMass j * B.bandCenter j) ≤
                Rproj * MovingLowGaugeTransfer.sharpWeightTotal
                  B.harmonicMass B.bandCenter) →
              ( (∀ (z : B.EffectiveParamSpace)
                    (_hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ))
                    (q : B.RawBandGauge) (i : Band),
                  |SquarefreeSharpBandTransfer.squarefreeBandRow
                      (B.actualValuationLaw (B.effectiveParamEquiv z))
                        B.partition q.1 i -
                    SquarefreeSharpBandTransfer.referenceBandRow
                      B.partition q.1 i| ≤
                    ‖q‖ * canonicalOrdinaryRowTolerance Cref Rproj) ∧
                (∀ (z : B.EffectiveParamSpace)
                    (_hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ))
                    (q : B.RawBandGauge) (i : Band),
                  |PrimePowerSharpBandTransfer.fullBandRow
                      (B.actualValuationLaw (B.effectiveParamEquiv z))
                        B.partition q.1 i -
                    SquarefreeSharpBandTransfer.squarefreeBandRow
                      (B.actualValuationLaw (B.effectiveParamEquiv z))
                        B.partition q.1 i| ≤
                    ‖q‖ * canonicalOrdinaryRowTolerance Cref Rproj) ∧
                ∀ (z : B.EffectiveParamSpace)
                    (hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ))
                    (q : B.RawBandGauge),
                  ‖B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                        (B.canonicalEffectiveNuisanceGamma_pos
                          I U (3 * (a : ℝ)) T)
                        (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                          hU hlowerOne hupperU (by
                            intro sigma; rw [hcanonical]; rfl) (by
                            intro sigma; rw [hcanonical]; rfl)
                          T hbaseline hBWlarge z hz) q -
                      B.actualBandFullLinearMap
                        (B.effectiveParamEquiv z) q‖ ≤
                    canonicalOrdinarySchurTolerance Cref * ‖q‖ ) := by
  obtain ⟨CKernel, hCKernel, hKernelBound⟩ :=
    PoissonDickmanKernelBounds.exists_covarianceKernel_abs_le_second
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  have hCpow : 0 < Cpow := by
    simpa only [Cpow] using
      FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant_pos
  let rowTol : ℝ := canonicalOrdinaryRowTolerance Cref Rproj
  let schurTol : ℝ := canonicalOrdinarySchurTolerance Cref
  have hrowTol : 0 < rowTol := by
    dsimp only [rowTol]
    exact canonicalOrdinaryRowTolerance_pos hCref hRproj
  have hschurTol : 0 < schurTol := by
    dsimp only [schurTol]
    exact canonicalOrdinarySchurTolerance_pos hCref
  have hInvNat : Tendsto (fun W : ℕ ↦ 1 / (W : ℝ))
      atTop (nhds 0) := by
    have hreal : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    have h := hreal.comp tendsto_natCast_atTop_atTop
    simpa only [one_div] using h
  let squareTailConstant : ℝ :=
    (1 / DickmanBasic.rho DickmanBasic.U) ^ 2 + CKernel
  have hSquareTail : Tendsto (fun W : ℕ ↦
      squareTailConstant * (1 / (W : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hInvNat : Tendsto
        (fun W : ℕ ↦ squareTailConstant * (1 / (W : ℝ)))
          atTop (nhds (squareTailConstant * 0)))
  have hFullTail : Tendsto (fun W : ℕ ↦
      Cpow * (1 / (W : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hInvNat : Tendsto
        (fun W : ℕ ↦ Cpow * (1 / (W : ℝ)))
          atTop (nhds (Cpow * 0)))
  obtain ⟨Wsquare, hWsquare⟩ := eventually_atTop.1
    (hSquareTail.eventually
      (eventually_lt_nhds (half_pos hrowTol)))
  obtain ⟨Wfull, hWfull⟩ := eventually_atTop.1
    (hFullTail.eventually
      (eventually_lt_nhds (half_pos hrowTol)))
  let W₀ : ℕ := max 2 (max Wsquare Wfull)
  refine ⟨W₀, ?_⟩
  intro W hWcut Head _instHead _instHeadDec _instHeadNonempty
    Phead hHeadLe I U hU hlowerOne hupperU Cprom Cbank ledger
    a marginFloor hmarginFloor Band _instBand _instBandDec _instBandNonempty
  have hWtwo : 2 ≤ W := (le_max_left 2 _).trans hWcut
  have hWone : 1 < W := by omega
  have hWsquare' : Wsquare ≤ W := by
    exact (le_max_left Wsquare Wfull).trans
      ((le_max_right 2 _).trans hWcut)
  have hWfull' : Wfull ≤ W := by
    exact (le_max_right Wsquare Wfull).trans
      ((le_max_right 2 _).trans hWcut)
  have hSquareTailLt :
      squareTailConstant * (1 / (W : ℝ)) < rowTol / 2 :=
    hWsquare W hWsquare'
  have hFullTailLt : Cpow * (1 / (W : ℝ)) < rowTol / 2 :=
    hWfull W hWfull'
  let Acoef : ℝ := 3 * (a : ℝ)
  let Aphys : ℝ := 3 * (a : ℝ)
  have hAcoef : 0 ≤ Acoef := by dsimp only [Acoef]; positivity
  have hAphys : 0 ≤ Aphys := by dsimp only [Aphys]; positivity
  obtain ⟨profileError, hprofile0, hprofileT, hprofileRate,
      Nprofile, hprofile⟩ :=
    exists_boxIndependent_actual_component_signed_profiles
      Phead I U hlowerOne hupperU Cprom Cbank ledger W hWone hHeadLe
        Acoef Aphys hAcoef hAphys
  obtain ⟨_hCpowTerminal, hpowerTerminal⟩ :=
    boxIndependent_canonicalRaw_actualWeightedRow
      Phead I U hlowerOne hupperU Cprom Cbank ledger
  obtain ⟨epsilon75, hepsilon750, hepsilon75T, _hepsilon75Rate,
      hcombinedRateRaw, Npower, hpower⟩ :=
    hpowerTerminal W hWone hHeadLe Acoef hAcoef Aphys hAphys
  obtain ⟨markedError, hmarked0, hmarkedRate, Nmarked, hmarked⟩ :=
    _root_.Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall
      Phead I U hU hlowerOne hupperU Cprom Cbank ledger W hWone
        hHeadLe a
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
  have hSquareRemainderT := tendsto_squarefreeSharpProfileRemainder
    profileError 1 12 CKernel W hprofileT hprofileRate
  have hSquareSmall : ∀ᶠ n : ℕ in atTop,
      squarefreeSharpProfileRemainder
        profileError 1 12 CKernel W n < rowTol :=
    hSquareRemainderT.eventually (eventually_lt_nhds (by
      simpa only [squareTailConstant] using
        (hSquareTailLt.trans (half_lt_self hrowTol))))
  let Rpow : ℕ → ℝ := fun n ↦
    Cpow * (1 / (W : ℝ)) + epsilon75 n + combined n
  have hRpowT : Tendsto Rpow atTop
      (nhds (Cpow * (1 / (W : ℝ)))) := by
    simpa only [Rpow, add_zero] using
      (tendsto_const_nhds.add hepsilon75T).add hcombinedT
  have hFullSmall : ∀ᶠ n : ℕ in atTop, Rpow n < rowTol :=
    hRpowT.eventually (eventually_lt_nhds (by
      exact hFullTailLt.trans (half_lt_self hrowTol)))
  have hmarkedT : Tendsto markedError atTop (nhds 0) :=
    tendsto_zero_of_eventually_nonneg_mul_logL_zero markedError
      (Filter.Eventually.of_forall hmarked0) hmarkedRate
  let gammaFloor : ℝ := canonicalEffectiveNuisanceGammaFloor
    Head I U (3 * (a : ℝ)) W marginFloor
  have hgammaFloor : 0 < gammaFloor := by
    dsimp only [gammaFloor]
    exact canonicalEffectiveNuisanceGammaFloor_pos I hmarginFloor
  let droot : ℝ := nuisanceDimensionCeiling Head
  have hdroot : 0 ≤ droot := by
    dsimp only [droot, nuisanceDimensionCeiling]
    positivity
  let H : ℕ → ℝ := fun n ↦ 12 * Real.log (Scale.L n)
  have hmarkedSquareLog : Tendsto
      (fun n : ℕ ↦ markedError n *
        (markedError n * Real.log (Scale.L n))) atTop (nhds 0) := by
    simpa only [mul_zero] using hmarkedT.mul hmarkedRate
  let nuisanceMajorant : ℕ → ℝ := fun n ↦
    (1 + Rproj) *
      (((droot * (markedError n * H n)) / gammaFloor) *
        (droot * markedError n))
  have hnuisanceT : Tendsto nuisanceMajorant atTop (nhds 0) := by
    have hcore : Tendsto (fun n : ℕ ↦
        markedError n * (markedError n * H n)) atTop (nhds 0) := by
      have hconst : Tendsto (fun _n : ℕ ↦ (12 : ℝ))
          atTop (nhds 12) := tendsto_const_nhds
      have hscaled : Tendsto (fun n : ℕ ↦
          (12 : ℝ) *
            (markedError n * (markedError n * Real.log (Scale.L n))))
          atTop (nhds 0) := by
        simpa only [mul_zero] using hconst.mul hmarkedSquareLog
      apply hscaled.congr'
      filter_upwards with n
      dsimp only [H]
      ring
    have hconst : Tendsto (fun _n : ℕ ↦
        (1 + Rproj) * (droot ^ 2 / gammaFloor))
        atTop (nhds ((1 + Rproj) * (droot ^ 2 / gammaFloor))) :=
      tendsto_const_nhds
    have hscaled : Tendsto (fun n : ℕ ↦
        ((1 + Rproj) * (droot ^ 2 / gammaFloor)) *
          (markedError n * (markedError n * H n)))
        atTop (nhds 0) := by
      simpa only [mul_zero] using hconst.mul hcore
    apply hscaled.congr'
    filter_upwards with n
    dsimp only [nuisanceMajorant]
    field_simp [hgammaFloor.ne']
  have hNuisanceSmall : ∀ᶠ n : ℕ in atTop,
      nuisanceMajorant n < schurTol :=
    hnuisanceT.eventually (eventually_lt_nhds hschurTol)
  have hmassN := eventually_sum_harmonicMass_le_twelve_logL
    (Head := Head) (Band := Band) W
  filter_upwards [hSquareSmall, hFullSmall, hNuisanceSmall, hmassN,
      eventually_ge_atTop Nprofile, eventually_ge_atTop Npower,
      eventually_ge_atTop Nmarked] with
      n hSquareN hFullN hNuisanceN hmassAt hnProfile hnPower hnMarked
  intro B hBn hBW hBWlarge hsep hremaining hcanonical
    T hTmargin hbaseline hRatio
  subst n
  subst W
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
  have hmass : (∑ j : Band, B.harmonicMass j) ≤
      H B.sampleData.n := by
    simpa only [H] using hmassAt B rfl rfl
  have hH0 : 0 ≤ H B.sampleData.n :=
    (Finset.sum_nonneg fun j hj ↦ (B.harmonicMass_pos j).le).trans hmass
  have hKernel : ∀ p ∈
      primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤
        CKernel := by
    intro p hp
    let p' : PrimeIndex B.sampleData.n B.sampleData.W := ⟨p, hp⟩
    have ht := tPrime_mem_unit B.n_gt_one p'
    calc
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤
          CKernel * tPrime B.sampleData.n p :=
        hKernelBound _ ht _ ht
      _ ≤ CKernel := mul_le_of_le_one_right hCKernel ht.2
  have hEffectiveBounds : ∀ (z : B.EffectiveParamSpace),
      z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
      (∀ p : BandPrime B.sampleData.n B.sampleData.W,
        |B.effectivePrimeCoefficient (B.effectiveParamEquiv z) p| ≤ Acoef) ∧
      |B.effectiveParamEquiv z MomentCoord.physical| ≤ Aphys := by
    intro z hz
    have hznorm : ‖z‖ ≤ (a : ℝ) := by
      simpa only [mem_closedBall, dist_zero_right] using hz
    have hsize : B.paperEffectiveSize (B.effectiveParamEquiv z) ≤ Acoef := by
      dsimp only [Acoef]
      exact (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
        (mul_le_mul_of_nonneg_left hznorm (by norm_num))
    have heffective :=
      B.effective_bounds_of_paperEffectiveSize (B.effectiveParamEquiv z) hsize
    refine ⟨heffective.1, ?_⟩
    calc
      |B.effectiveParamEquiv z MomentCoord.physical| =
          ‖B.nuisanceParameter (B.effectiveParamEquiv z)
            NuisanceCoord.physical‖ := by
        simp only [B.nuisanceParameter_physical, Real.norm_eq_abs]
      _ ≤ ‖B.nuisanceParameter (B.effectiveParamEquiv z)‖ :=
        PiLp.norm_apply_le _ _
      _ ≤ Aphys := by simpa only [Aphys, Acoef] using heffective.2
  have hSquareRows : ∀ (z : B.EffectiveParamSpace)
      (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
      (q : B.RawBandGauge) (i : Band),
      |SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw (B.effectiveParamEquiv z))
            B.partition q.1 i -
        SquarefreeSharpBandTransfer.referenceBandRow
          B.partition q.1 i| ≤ ‖q‖ * rowTol := by
    intro z hz q i
    obtain ⟨heta, hphys⟩ := hEffectiveBounds z hz
    obtain ⟨hpair, hsingle⟩ := hprofile B (B.effectiveParamEquiv z)
      hnProfile hPattern hLo hHi hGuards heta hphys rfl
    let weight := tiltedSigmaWeight B.baselineCellProbability
      B.guardedCellProbability
        (B.scaledBridgeScore (B.effectiveParamEquiv z))
    have hentryMix :=
      sigmaMixture_squarefree_reference_entry_bound_of_squarefree_profiles
        (hprofile0 B.sampleData.n) weight
        (B.actualComponentValuationLaw (B.effectiveParamEquiv z))
        B.n_gt_one hpair hsingle hKernel
    have hlaw :=
      B.sigmaMixture_actualComponentValuationLaw_eq_actualValuationLaw
        (B.effectiveParamEquiv z)
    dsimp only at hentryMix hlaw
    rw [hlaw] at hentryMix
    let E : ℝ := profileError B.sampleData.n
    let eOff : ℝ := 4 * pairCovarianceScale E
    let eDiag : ℝ := 2 * E
    let cDiag : ℝ :=
      (1 / DickmanBasic.rho DickmanBasic.U + 2 * E) ^ 2 + CKernel
    have hE : 0 ≤ E := by simpa only [E] using hprofile0 B.sampleData.n
    have heOff : 0 ≤ eOff := by
      dsimp only [eOff]
      exact mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hE)
    have hcDiag : 0 ≤ cDiag := by
      dsimp only [cDiag]
      positivity
    have hentry : ∀ p r,
        p ∈ primeBand B.sampleData.n B.sampleData.W →
        r ∈ primeBand B.sampleData.n B.sampleData.W →
        |(B.actualValuationLaw (B.effectiveParamEquiv z)).covII p r -
            squarefreeReferenceEntry B.sampleData.n p r| ≤
          eOff * (1 / (p : ℝ)) * (1 / (r : ℝ)) +
            if p = r then
              eDiag * (1 / (p : ℝ)) +
                cDiag * (1 / (p : ℝ)) ^ 2
            else 0 := by
      intro p r hp hr
      let p' : BandPrime B.sampleData.n B.sampleData.W := ⟨p, hp⟩
      let r' : BandPrime B.sampleData.n B.sampleData.W := ⟨r, hr⟩
      have hraw := hentryMix p' r'
      simpa only [p', r', E, eOff, eDiag, cDiag, div_eq_mul_inv,
        one_div, Subtype.mk.injEq, mul_inv_rev, inv_pow, mul_assoc,
        mul_left_comm, mul_comm, one_mul, mul_one] using hraw
    have hrow := B.squarefreeBandRow_sub_referenceBandRow_le_ordinary
      (B.effectiveParamEquiv z) q heOff hcDiag
      (by exact_mod_cast (show 0 < B.sampleData.W by omega))
      hmass hentry i
    have hremainder :
        eOff * H B.sampleData.n + eDiag +
            cDiag * (1 / (B.sampleData.W : ℝ)) =
          squarefreeSharpProfileRemainder
            profileError 1 12 CKernel B.sampleData.W B.sampleData.n := by
      dsimp only [eOff, eDiag, cDiag, E, H,
        squarefreeSharpProfileRemainder]
      ring
    calc
      _ ≤ ‖q‖ * (eOff * H B.sampleData.n + eDiag +
          cDiag * (1 / (B.sampleData.W : ℝ))) := hrow
      _ = ‖q‖ * squarefreeSharpProfileRemainder
          profileError 1 12 CKernel B.sampleData.W B.sampleData.n := by
        rw [hremainder]
      _ ≤ ‖q‖ * rowTol :=
        mul_le_mul_of_nonneg_left hSquareN.le (norm_nonneg q)
  have hFullRows : ∀ (z : B.EffectiveParamSpace)
      (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
      (q : B.RawBandGauge) (i : Band),
      |PrimePowerSharpBandTransfer.fullBandRow
          (B.actualValuationLaw (B.effectiveParamEquiv z))
            B.partition q.1 i -
        SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw (B.effectiveParamEquiv z))
            B.partition q.1 i| ≤ ‖q‖ * rowTol := by
    intro z hz q i
    obtain ⟨heta, hphys⟩ := hEffectiveBounds z hz
    have hweighted : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
        (p.1 : ℝ) *
          ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            |(B.actualValuationLaw (B.effectiveParamEquiv z)).covVV p.1 r.1 -
              (B.actualValuationLaw (B.effectiveParamEquiv z)).covII p.1 r.1| ≤
          Rpow B.sampleData.n := by
      intro p
      have hraw := hpower B (B.effectiveParamEquiv z) hnPower rfl
        hsep hremaining hcanonical heta hphys p
      simpa only [Rpow, Cpow, combined,
        canonicalCombinedPowerCorrection] using hraw
    have hrow := B.fullBandRow_sub_squarefreeBandRow_le_ordinary
      (B.effectiveParamEquiv z) q hweighted i
    exact hrow.trans
      (mul_le_mul_of_nonneg_left hFullN.le (norm_nonneg q))
  refine ⟨by simpa only [rowTol] using hSquareRows,
    by simpa only [rowTol] using hFullRows, ?_⟩
  intro z hz q
  let xi : B.ParamSpace := B.effectiveParamEquiv z
  let gamma : ℝ :=
    B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
  have hgamma : 0 < gamma := by
    dsimp only [gamma]
    exact B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
  have hgap : ∀ v, gamma * ‖v‖ ^ 2 ≤
      inner ℝ v (B.nuisanceCovarianceOperator xi v) := by
    intro v
    dsimp only [gamma, xi]
    exact B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
      hlowerOne hupperU hLo hHi T hbaseline hBWlarge z hz v
  have hgammaFloorLe : gammaFloor ≤ gamma := by
    dsimp only [gammaFloor, gamma]
    exact B.canonicalEffectiveNuisanceGammaFloor_le I hU
      (by positivity : 0 ≤ 3 * (a : ℝ)) hmarginFloor T hTmargin
  have hmarkedRows : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          markedError B.sampleData.n * (1 / (p.1 : ℝ)) := by
    intro c p
    dsimp only [xi]
    exact hmarked B z hz hnMarked rfl hsep hremaining hcanonical c p
  have hrow := B.actualBandSchur_sub_full_norm_le_of_marked_ordinary
    xi hgamma hgap (hmarked0 B.sampleData.n) hRproj hRatio hmarkedRows q
  have hrateExact := B.nuisanceMarkedOrdinarySchurRate_le_majorant
    (hmarked0 B.sampleData.n) hgammaFloor hgammaFloorLe hRproj hH0 hmass
  have hdrootCompare :
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤
        droot := by
    simpa only [droot] using B.sqrt_nuisanceCoord_card_le_ceiling
  have hmajorant :
      B.nuisanceMarkedOrdinarySchurRate
          (markedError B.sampleData.n) gamma Rproj ≤
        nuisanceMajorant B.sampleData.n := by
    refine hrateExact.trans ?_
    dsimp only [nuisanceMajorant]
    have hmarkedN0 := hmarked0 B.sampleData.n
    have hleft0 : 0 ≤ 1 + Rproj := by linarith
    gcongr
  calc
    ‖B.actualBandSchurLinearMap xi hgamma hgap q -
        B.actualBandFullLinearMap xi q‖ ≤
      B.nuisanceMarkedOrdinarySchurRate
          (markedError B.sampleData.n) gamma Rproj * ‖q‖ := hrow
    _ ≤ nuisanceMajorant B.sampleData.n * ‖q‖ :=
      mul_le_mul_of_nonneg_right hmajorant (norm_nonneg q)
    _ ≤ schurTol * ‖q‖ :=
      mul_le_mul_of_nonneg_right hNuisanceN.le (norm_nonneg q)
    _ = canonicalOrdinarySchurTolerance Cref * ‖q‖ := by
      rw [show schurTol = canonicalOrdinarySchurTolerance Cref by rfl]

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
