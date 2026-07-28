import Erdos390.Full.PaperCanonicalLemma86GeometryCoefficientsEventually
import Erdos390.Full.PaperCanonicalActualPrimePowerWeightedRowEventually
import Erdos390.Full.PaperActualPrimePowerRowTransfer

/-!
# Canonical relative prime-power clause of paper Lemma 8.6

The paper needs the replacement of full prime valuations by squarefree prime
indicators at the relative `w^2` scale.  This file performs that replacement
for the literal regression produced by the exact finite nuisance-Schur map.

The nonvanishing constant is selected before `W`, the permitted mesh, and the
effective tilt box.  All later dependence is confined to a named remainder
whose product with `log (log n)` tends to zero (and which therefore itself
tends to zero).  No `PrimePowerTransferBounds`, weighted-row estimate,
coefficient bound, convergence assertion, or abstract inverse is exposed at
the public call site.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PaperWeightedInverseExport PrimeSums
open RegularMeshPrimeCutoffs PaperPermittedRegularMesh

namespace BridgeData

/-- An eventually nonnegative error whose product with `log (log n)` tends
to zero tends to zero. -/
private theorem tendsto_zero_of_eventually_nonneg_mul_logL_zero_relative
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

set_option maxHeartbeats 2500000 in
/--
Assumption-free, paper-order, relative prime-power estimate for the same
`q^reg` which is obtained from the exact finite nuisance-Schur equivalence.

The output includes the same-map identity and both inverse bounds so a later
umbrella theorem can reuse this exact `e`; it never needs to identify two
separately chosen equivalences after the fact.
-/
theorem exists_paperFineMesh_cutoff_eventually_canonical_lemma86_relativePrimePower
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
                          epsilonRel B.sampleData.n) * B.w ^ 2 := by
  obtain ⟨baseTol, hbaseTol, Csharp, hCsharp, Cordinary, hCordinary,
      Crow, hCrow, Wbase, hBase⟩ :=
    exists_paperFineMesh_cutoff_eventually_canonical_lemma86_geometry_coefficients
      cMesh hcMesh
  let Creg : ℝ := Csharp * (2 * Crow)
  let K : ℝ := 2 * Real.log 4
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  let relativeFactor : ℝ := (1 + Creg) * (7 + Creg * K)
  let Crel : ℝ := relativeFactor * Cpow
  let W₀ : ℕ := max Wbase 2
  have hCreg : 0 ≤ Creg := by
    dsimp only [Creg]
    positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hCpow : 0 < Cpow := by
    simpa only [Cpow] using
      FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant_pos
  have hrelativeFactor : 0 < relativeFactor := by
    dsimp only [relativeFactor]
    positivity
  have hCrel : 0 < Crel := by
    dsimp only [Crel]
    positivity
  refine ⟨baseTol, hbaseTol, Csharp, hCsharp, Cordinary, hCordinary,
    Crow, hCrow, Creg, hCreg, rfl, Crel, hCrel, W₀, ?_⟩
  intro W hW delta eta M hdelta hPermitted hfine
    Head _instFintype _instDecidable _instNonempty Phead hPhead
    I U hU hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  have hWbase : Wbase ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWone : 1 < W := by
    dsimp only [W₀] at hW
    omega
  have hHeadLe : ∀ h, ∀ p ∈ (Phead h).primes, p ≤ W := by
    intro h p hp
    exact (hPhead h p).mp hp |>.2
  let Acoef : ℝ := 3 * (a : ℝ)
  let Aphys : ℝ := 3 * (a : ℝ)
  have hAcoef : 0 ≤ Acoef := by dsimp only [Acoef]; positivity
  have hAphys : 0 ≤ Aphys := by dsimp only [Aphys]; positivity
  obtain ⟨_hCpowTerminal, hPowerFamily⟩ :=
    boxIndependent_canonicalRaw_actualWeightedRow
      Phead I U hlowerOne hupperU Cprom Cbank ledger
  obtain ⟨epsilon75, hepsilon750, _hepsilon75T, hepsilon75Rate,
      hcombinedRateRaw, Npower, hpower⟩ :=
    hPowerFamily W hWone hHeadLe Acoef hAcoef Aphys hAphys
  let combined : ℕ → ℝ := fun n ↦
    canonicalCombinedPowerCorrection
      Phead I U Cprom Cbank W Acoef Aphys n
  let epsilonRel : ℕ → ℝ := fun n ↦
    relativeFactor * (epsilon75 n + combined n)
  have hcombinedRate : Tendsto
      (fun n : ℕ ↦ combined n * Real.log (Scale.L n))
        atTop (nhds 0) := by
    simpa only [combined, canonicalCombinedPowerCorrection] using
      hcombinedRateRaw
  have hcombinedNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ combined n := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    exact canonicalCombinedPowerCorrection_nonneg
      Phead I hU hAphys hWone hn
  have hepsilonRelNonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ epsilonRel n := by
    filter_upwards [hcombinedNonneg] with n hcombinedN
    dsimp only [epsilonRel]
    exact mul_nonneg hrelativeFactor.le
      (add_nonneg (hepsilon750 n) hcombinedN)
  have hepsilonRelRate : Tendsto
      (fun n : ℕ ↦ epsilonRel n * Real.log (Scale.L n))
        atTop (nhds 0) := by
    have hsum := hepsilon75Rate.add hcombinedRate
    have hconst : Tendsto (fun _n : ℕ ↦ relativeFactor)
        atTop (nhds relativeFactor) := tendsto_const_nhds
    have hscaled := hconst.mul hsum
    simpa only [epsilonRel, add_mul, mul_add, mul_assoc,
      zero_mul, mul_zero, add_zero] using hscaled
  have hepsilonRel : Tendsto epsilonRel atTop (nhds 0) :=
    tendsto_zero_of_eventually_nonneg_mul_logL_zero_relative
      epsilonRel hepsilonRelNonneg hepsilonRelRate
  have hBaseN := hBase W hWbase M hdelta hPermitted hfine
    Head Phead hPhead I U hU hlowerOne hupperU
      Cprom Cbank ledger a marginFloor hmargin
  have hBandT := eventually_bandTReciprocalSum_le W
  refine ⟨epsilonRel, hepsilonRelNonneg, hepsilonRel,
    hepsilonRelRate, ?_⟩
  filter_upwards [hBaseN, hBandT, hcombinedNonneg,
    eventually_ge_atTop Npower] with
      n hBaseAt hBandTAt hcombinedNonnegAt hnPower
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
    hscale T hTmargin hbaseline
  subst n
  subst W
  obtain ⟨hdev, hdevL1, hvarLower, hdevL2, hcenter,
      e, he, hinv, hinvOrd, hBaseZ⟩ :=
    hBaseAt B rfl rfl hBWlarge hsep hremaining hcanonical hpartition
      hscale T hTmargin hbaseline
  have hdevW : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ B.w := by
    simpa only [hscale] using hdev
  have hdevL1W : B.partition.totalL1 ≤ 7 * B.w := by
    simpa only [hscale] using hdevL1
  have hvarLowerW : B.w ^ 2 ≤
      (456 / cMesh ^ 2) * B.partition.variance := by
    simpa only [hscale] using hvarLower
  have hdevL2W : B.partition.variance ≤ 4 * B.w ^ 2 := by
    simpa only [hscale] using hdevL2
  refine ⟨hdevW, hdevL1W, hvarLowerW, hdevL2W, hcenter,
    e, he, hinv, hinvOrd, ?_⟩
  intro z hz
  obtain ⟨hslow, hnormal, hqSharp, hcoeffSup,
      hcoeffL1, hcoeffL2⟩ := hBaseZ z hz
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
  let R : ℝ := Cpow * (1 / (B.sampleData.W : ℝ)) +
    epsilon75 B.sampleData.n + combined B.sampleData.n
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact add_nonneg
      (add_nonneg (mul_nonneg hCpow.le (by positivity))
        (hepsilon750 B.sampleData.n)) hcombinedNonnegAt
  have hrowRaw := hpower B xi hnPower rfl hsep hremaining hcanonical
    heta hphys
  have hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 r.1 -
            (B.actualValuationLaw xi).covII p.1 r.1| ≤ R := by
    intro p
    simpa only [R, combined, canonicalCombinedPowerCorrection] using
      hrowRaw p
  let hgamma : 0 < B.canonicalEffectiveNuisanceGamma
      I U (3 * (a : ℝ)) T :=
    B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
  let hgap : ∀ v,
      B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T * ‖v‖ ^ 2 ≤
        inner ℝ v (B.nuisanceCovarianceOperator xi v) :=
    B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
      hlowerOne hupperU
      (by intro sigma; rw [hcanonical]; rfl)
      (by intro sigma; rw [hcanonical]; rfl)
      T hbaseline hBWlarge z hz
  let q := B.actualBandRegression xi hgamma hgap (e z hz)
  have hq : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ Creg * B.w := by
    simpa only [q, xi, hgamma, hgap, Creg, hscale] using hqSharp
  have hrelative := B.actual_primePower_relative_variance_bound_of_row
    xi q hCreg hK B.w_pos.le hR hq hBandTAt hdevW hdevL1W hdevL2W hrow
  have hcoeffSupW : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.actualCompensatedCoefficient q p| ≤ (1 + Creg) * B.w := by
    simpa only [q, xi, hgamma, hgap, Creg, hscale] using hcoeffSup
  have hcoeffL1W : B.partition.compensatedL1 q ≤
      (7 + Creg * (2 * Real.log 4)) * B.w := by
    simpa only [q, xi, hgamma, hgap, Creg, hscale] using hcoeffL1
  have hcoeffL2W : B.partition.compensatedL2Sq q ≤
      2 * (4 + Creg ^ 2 * (2 * Real.log 4)) * B.w ^ 2 := by
    simpa only [q, xi, hgamma, hgap, Creg, hscale] using hcoeffL2
  refine ⟨by simpa only [xi, hgamma, hgap] using hslow,
    by simpa only [q, xi, hgamma, hgap] using hnormal,
    hq, hcoeffSupW, hcoeffL1W, hcoeffL2W, ?_⟩
  have hrelativeRhs : relativeFactor * R * B.w ^ 2 =
      (Crel * (1 / (B.sampleData.W : ℝ)) +
        epsilonRel B.sampleData.n) * B.w ^ 2 := by
    dsimp only [R, Crel, epsilonRel]
    ring
  rw [hrelativeRhs] at hrelative
  simpa only [q, xi, hgamma, hgap] using hrelative

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
