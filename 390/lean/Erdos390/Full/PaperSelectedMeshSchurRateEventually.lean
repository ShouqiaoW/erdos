import Erdos390.Full.PaperCanonicalBandSchurInverseFromFull
import Erdos390.Full.PaperExactSchurTwoStageQuadratic
import Erdos390.Full.PaperCanonicalNuisanceUniformFloor
import Erdos390.Full.PrimeSums

/-!
# Vanishing nuisance-Schur rate at the moving-low scale

This file isolates the rate calculation needed after the selected-mesh
full-band inverse.  A reciprocal nuisance row of size `epsilon n / p`,
with both `epsilon n -> 0` and `epsilon n * log (log n) -> 0`, survives the
moving-low loss `amin = c / log (log n)`: the resulting Schur perturbation
still tends to zero.  All dimension, moment, and nuisance-gap constants are
explicit.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

open ArithmeticBandGeometry PaperWeightedInverseExport MovingLowGaugeTransfer

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- The normalized first band moment is literally the prime sum
`sum t_p / p`; this removes a separate moment hypothesis from the eventual
Schur estimate. -/
theorem sum_harmonicMass_mul_bandCenter_eq_bandTReciprocalSum
    (B : BridgeData Head Band) :
    (∑ j : Band, B.harmonicMass j * B.bandCenter j) =
      PrimeSums.bandTReciprocalSum B.sampleData.n B.sampleData.W := by
  unfold harmonicMass bandCenter ArithmeticBandGeometry.Partition.center
    Erdos390.Lemma84.WeightedBandData.center
  have hmass : ∀ j : Band, B.partition.data.mass j ≠ 0 :=
    fun j ↦ ne_of_gt (B.partition.data.mass_pos j)
  simp_rw [mul_div_cancel₀ _ (hmass _)]
  change (∑ j : Band, ∑ p ∈ B.partition.data.fiber j,
      (1 / (p.1 : ℝ)) * ArithmeticModel.tPrime B.sampleData.n p.1) = _
  unfold Erdos390.Lemma84.WeightedBandData.fiber
  rw [Finset.sum_fiberwise Finset.univ B.partition.data.band
    (fun p : BandPrime B.sampleData.n B.sampleData.W ↦
      (1 / (p.1 : ℝ)) * ArithmeticModel.tPrime B.sampleData.n p.1)]
  unfold PrimeSums.bandTReciprocalSum
  calc
    (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        (1 / (p.1 : ℝ)) * ArithmeticModel.tPrime B.sampleData.n p.1) =
        ∑ p ∈ ArithmeticModel.primeBand B.sampleData.n B.sampleData.W,
          (1 / (p : ℝ)) * ArithmeticModel.tPrime B.sampleData.n p := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach
          (ArithmeticModel.primeBand B.sampleData.n B.sampleData.W)
          (fun p ↦ (1 / (p : ℝ)) *
            ArithmeticModel.tPrime B.sampleData.n p))
    _ = ∑ p ∈ ArithmeticModel.primeBand B.sampleData.n B.sampleData.W,
          ArithmeticModel.tPrime B.sampleData.n p / (p : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-- Explicit scalar majorant for the nuisance-Schur perturbation. -/
def selectedMeshSchurRateMajorant
    (epsilon : ℕ → ℝ) (droot momentBound gammaFloor centerScale : ℝ)
    (n : ℕ) : ℝ :=
  (((droot * (epsilon n * momentBound)) / gammaFloor) *
      (droot * epsilon n)) /
    (centerScale / Real.log (Scale.L n))

/-- A nonnegative row rate whose product with `log (log n)` tends to zero
already tends to zero.  This small lemma lets the analytic marked-row API
expose only its genuinely sharp rate. -/
theorem tendsto_zero_of_nonneg_mul_logL_zero
    (epsilon : ℕ → ℝ)
    (hepsilonNonneg : ∀ n, 0 ≤ epsilon n)
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
  have hlower : ∀ᶠ n : ℕ in atTop, 0 ≤ epsilon n :=
    Filter.Eventually.of_forall hepsilonNonneg
  have hupper : ∀ᶠ n : ℕ in atTop,
      epsilon n ≤ epsilon n * Real.log (Scale.L n) := by
    filter_upwards [hlogOne] with n hn
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hn (hepsilonNonneg n)
  exact squeeze_zero' hlower hupper hepsilonRate

/-- The moving-low loss is harmless at the sharp marked-row rate. -/
theorem tendsto_selectedMeshSchurRateMajorant_zero
    (epsilon : ℕ → ℝ) {droot momentBound gammaFloor centerScale : ℝ}
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0))
    (hgamma : 0 < gammaFloor) (hcenter : 0 < centerScale) :
    Tendsto
      (selectedMeshSchurRateMajorant epsilon droot momentBound
        gammaFloor centerScale) atTop (nhds 0) := by
  have hproduct : Tendsto (fun n : ℕ ↦
      (epsilon n * Real.log (Scale.L n)) * epsilon n)
      atTop (nhds 0) := by
    simpa only [zero_mul] using hepsilonRate.mul hepsilon
  let C : ℝ := droot ^ 2 * momentBound / (gammaFloor * centerScale)
  have hscaled : Tendsto (fun n : ℕ ↦
      C * ((epsilon n * Real.log (Scale.L n)) * epsilon n))
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hproduct
  apply hscaled.congr'
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogTop : Tendsto (fun n : ℕ ↦ Real.log (Scale.L n))
      atTop atTop := Real.tendsto_log_atTop.comp hLTop
  filter_upwards [hlogTop.eventually (eventually_gt_atTop (0 : ℝ))]
      with n hlog
  unfold selectedMeshSchurRateMajorant
  dsimp only [C]
  field_simp [hgamma.ne', hcenter.ne', hlog.ne']

/-- Reserving half of the Neumann denominator leaves the structural factor
two and removes every moving-low or mesh parameter from the retained inverse
constant. -/
theorem schurInverseConstant_le_two_mul
    {C rate : ℝ} (hC : 0 < C)
    (hhalf : C * (2 * rate) ≤ 1 / 2) :
    C / (1 - C * (2 * rate)) ≤ 2 * C := by
  have hdenHalf : 1 / 2 ≤ 1 - C * (2 * rate) := by linarith
  calc
    C / (1 - C * (2 * rate)) ≤ C / (1 / 2) :=
      div_le_div_of_nonneg_left hC.le (by norm_num) hdenHalf
    _ = 2 * C := by ring

/-- Literal comparison between the finite nuisance-Schur rate and the
preceding scalar majorant. -/
theorem nuisanceMarkedSchurRate_le_selectedMeshSchurRateMajorant
    (B : BridgeData Head Band)
    {epsilon droot momentBound gammaFloor gamma centerScale : ℝ}
    {n : ℕ}
    (hepsilon : 0 ≤ epsilon) (hdroot : 0 ≤ droot)
    (hmomentBound : 0 ≤ momentBound)
    (hgammaFloor : 0 < gammaFloor) (hgamma : gammaFloor ≤ gamma)
    (hcenterScale : 0 < centerScale)
    (hlog : 0 < Real.log (Scale.L n))
    (hdimension : Real.sqrt
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤ droot)
    (hmoment : (∑ j : Band,
      B.harmonicMass j * B.bandCenter j) ≤ momentBound) :
    B.nuisanceMarkedSchurRate epsilon gamma
        (centerScale / Real.log (Scale.L n)) ≤
      selectedMeshSchurRateMajorant (fun _ ↦ epsilon) droot
        momentBound gammaFloor centerScale n := by
  have hgammaPos : 0 < gamma := hgammaFloor.trans_le hgamma
  have hcenterPos : 0 < centerScale / Real.log (Scale.L n) :=
    div_pos hcenterScale hlog
  have hdim0 : 0 ≤ Real.sqrt
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) := Real.sqrt_nonneg _
  have hmoment0 : 0 ≤ ∑ j : Band,
      B.harmonicMass j * B.bandCenter j := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (B.harmonicMass_pos j).le (B.bandCenter_pos j).le
  unfold nuisanceMarkedSchurRate selectedMeshSchurRateMajorant
  dsimp only
  gcongr

/-- Finite ball-uniform Schur inverse together with its literal arithmetic
quadratic-form gap.  The nuisance gap is constructed from the canonical
baseline; the quadratic gap is derived from the inverse and covariance
Cauchy--Schwarz, not assumed. -/
theorem exists_uniform_actualBandSchurEquiv_and_quadratic_of_full_of_marked
    (B : BridgeData Head Band) [Nonempty Head] [Nonempty Band]
    (I : PaperGuardCensus.PhysicalIntervals) {U : ℝ}
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      ArithmeticModel.physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      ArithmeticModel.physicalBound (I.upper sigma) B.sampleData.n)
    (T : PaperGuardCensus.BarycentricTarget B.sampleData)
    (hbaseline : B.baseline = T.baseline)
    (hW : 1 < B.sampleData.W)
    (a : NNReal)
    (fullEquiv : ∀ (z : B.EffectiveParamSpace),
      z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
        SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
          SharpGaugeSpace B.partition.mass B.partition.center)
    (hfull : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
      fullEquiv z hz q =
        B.actualFullProjectedCLM (B.effectiveParamEquiv z) q)
    {Cfull Cmarked amin : ℝ}
    (hCfull : 0 < Cfull) (hCmarked : 0 ≤ Cmarked)
    (hamin : 0 < amin)
    (hcenter : ∀ i : Band, amin ≤ B.bandCenter i)
    (hinvFull : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
      ‖(fullEquiv z hz).symm v‖ ≤ Cfull * ‖v‖)
    (hsmall : Cfull *
      (2 * B.nuisanceMarkedSchurRate Cmarked
        (B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T)
        amin) < 1)
    (hmarked : ∀ (z : B.EffectiveParamSpace)
        (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
        (c : NuisanceCoord B.HeadIndex)
        (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    let gamma :=
      B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
    let Cschur := Cfull / (1 - Cfull *
      (2 * B.nuisanceMarkedSchurRate Cmarked gamma amin))
    ∃ e : ∀ (z : B.EffectiveParamSpace),
        z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
          B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
      (∀ (z : B.EffectiveParamSpace)
          (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
        e z hz q =
          B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
            (B.canonicalEffectiveNuisanceGamma_pos
              I U (3 * (a : ℝ)) T)
            (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
              hlowerOne hupperU hlo hhi T hbaseline hW z hz) q) ∧
      (∀ (z : B.EffectiveParamSpace)
          (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
        paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) ((e z hz).symm v) ≤
          Cschur * paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) v) ∧
      ∀ (z : B.EffectiveParamSpace)
          (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
          (q : B.RawBandGauge),
        (rawDLowerWeight B.harmonicMass B.bandCenter ^ 2 /
            (sharpWeightTotal B.harmonicMass B.bandCenter * Cschur)) *
            paperSharpNorm B.harmonicMass B.bandCenter
              (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
          (B.tiltedLaw (B.effectiveParamEquiv z)).covariance
            (B.nuisanceResidualScore (B.effectiveParamEquiv z)
              (B.canonicalEffectiveNuisanceGamma_pos
                I U (3 * (a : ℝ)) T)
              (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                hlowerOne hupperU hlo hhi T hbaseline hW z hz)
              (B.bandRegressionScore q))
            (B.nuisanceResidualScore (B.effectiveParamEquiv z)
              (B.canonicalEffectiveNuisanceGamma_pos
                I U (3 * (a : ℝ)) T)
              (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                hlowerOne hupperU hlo hhi T hbaseline hW z hz)
              (B.bandRegressionScore q)) := by
  let gamma :=
    B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
  let Cschur := Cfull / (1 - Cfull *
    (2 * B.nuisanceMarkedSchurRate Cmarked gamma amin))
  obtain ⟨e, he, hinv⟩ :=
    B.exists_uniform_actualBandSchurEquiv_of_full_of_marked_on_closedBall
      I hU hlowerOne hupperU hlo hhi T hbaseline hW a
      fullEquiv hfull hCfull.le hCmarked hamin hcenter hinvFull
      (by simpa only [gamma] using hsmall) hmarked
  have hden : 0 < 1 - Cfull *
      (2 * B.nuisanceMarkedSchurRate Cmarked gamma amin) :=
    sub_pos.mpr (by simpa only [gamma] using hsmall)
  have hCschur : 0 < Cschur := by
    dsimp only [Cschur]
    exact div_pos hCfull hden
  refine ⟨e, he, ?_, ?_⟩
  · intro z hz v
    simpa only [gamma, Cschur] using hinv z hz v
  · intro z hz q
    exact B.actualBandSchur_quadratic_lower_of_inverse_arithmetic
      (B.effectiveParamEquiv z)
      (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
      (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
        hlowerOne hupperU hlo hhi T hbaseline hW z hz)
      (e z hz) (he z hz) hCschur
      (by
        intro v
        simpa only [gamma, Cschur] using hinv z hz v)
      q

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
