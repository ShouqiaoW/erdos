import Erdos390.Full.PaperSelectedMeshSchurRateEventually

/-!
# Eventual nuisance--Schur closure on a selected arithmetic mesh

This file combines the exact finite Schur connector with the moving-low
rate calculation.  The statement retains only the two analytic inputs that
are genuinely specific to the selected mesh: a lower envelope for every
arithmetic band center and the sharp `epsilon n / p` marked nuisance rows.
The band first moment, nuisance dimension, and positive nuisance floor are
derived internally from the canonical arithmetic objects.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

open ArithmeticModel ArithmeticBandGeometry PaperWeightedInverseExport
  MovingLowGaugeTransfer

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- Once the actual-full inverse, sharp marked rows, moving-low center
envelope, and a fixed positive barycentric mass floor are available, the
literal arithmetic nuisance Schur complement is eventually invertible on
the whole effective ball.  Its retained inverse constant is at most
`2 * Cfull`; in particular it is independent of the moving low cell and of
the arithmetic mesh.

No continuum convergence or covariance estimate is assumed in this
connector.  Those analytic inputs enter only through `fullEquiv`, `hcenter`,
and `hmarked` in the displayed finite arithmetic statement. -/
theorem eventually_exists_uniform_actualBandSchurEquiv_and_quadratic
    [Nonempty Head] [Nonempty Band]
    (I : PaperGuardCensus.PhysicalIntervals) {U : ℝ}
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (W : ℕ) (hW : 1 < W)
    (a : NNReal)
    (marginFloor centerScale Cfull : ℝ)
    (hmarginFloor : 0 < marginFloor)
    (hcenterScale : 0 < centerScale)
    (hCfull : 0 < Cfull)
    (epsilon : ℕ → ℝ)
    (hepsilonNonneg : ∀ n, 0 ≤ epsilon n)
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0)) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band)
        (hBn : B.sampleData.n = n)
        (hBW : B.sampleData.W = W)
        (T : PaperGuardCensus.BarycentricTarget B.sampleData)
        (hTmargin : marginFloor ≤ T.cellMassMargin)
        (hbaseline : B.baseline = T.baseline)
        (hlo : ∀ sigma, B.sampleData.lo sigma =
          ArithmeticModel.physicalBound (I.lower sigma) B.sampleData.n)
        (hhi : ∀ sigma, B.sampleData.hi sigma =
          ArithmeticModel.physicalBound (I.upper sigma) B.sampleData.n),
      ∀ (fullEquiv : ∀ (z : B.EffectiveParamSpace),
          z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
            SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
              SharpGaugeSpace B.partition.mass B.partition.center),
        (∀ (z : B.EffectiveParamSpace)
            (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
          fullEquiv z hz q =
            B.actualFullProjectedCLM (B.effectiveParamEquiv z) q) →
        (∀ (z : B.EffectiveParamSpace)
            (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
          ‖(fullEquiv z hz).symm v‖ ≤ Cfull * ‖v‖) →
        (∀ i : Band,
          centerScale / Real.log (Scale.L B.sampleData.n) ≤
            B.bandCenter i) →
        (∀ (z : B.EffectiveParamSpace)
            (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
            (c : NuisanceCoord B.HeadIndex)
            (p : BandPrime B.sampleData.n B.sampleData.W),
          |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
            (fun m ↦ B.nuisanceStatistic m c)
            (fun m ↦ ArithmeticModel.valuation p.1
              (B.sampleData.value m))| ≤
            epsilon B.sampleData.n * (1 / (p.1 : ℝ))) →
      let gamma :=
        B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
      let rate := B.nuisanceMarkedSchurRate
        (epsilon B.sampleData.n) gamma
          (centerScale / Real.log (Scale.L B.sampleData.n))
      let Cschur := Cfull / (1 - Cfull * (2 * rate))
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
                hlowerOne hupperU hlo hhi T hbaseline (by omega) z hz) q) ∧
        (∀ (z : B.EffectiveParamSpace)
            (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
          paperSharpNorm B.harmonicMass B.bandCenter
              (B.partition.center_ne_zero B.n_gt_one) ((e z hz).symm v) ≤
            Cschur * paperSharpNorm B.harmonicMass B.bandCenter
              (B.partition.center_ne_zero B.n_gt_one) v) ∧
        Cschur ≤ 2 * Cfull ∧
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
                  hlowerOne hupperU hlo hhi T hbaseline (by omega) z hz)
                (B.bandRegressionScore q))
              (B.nuisanceResidualScore (B.effectiveParamEquiv z)
                (B.canonicalEffectiveNuisanceGamma_pos
                  I U (3 * (a : ℝ)) T)
                (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                  hlowerOne hupperU hlo hhi T hbaseline (by omega) z hz)
                (B.bandRegressionScore q)) := by
  let droot : ℝ := nuisanceDimensionCeiling Head
  let momentBound : ℝ := 2 * Real.log 4
  let gammaFloor : ℝ := canonicalEffectiveNuisanceGammaFloor
    Head I U (3 * (a : ℝ)) W marginFloor
  have hdroot : 0 ≤ droot := by
    dsimp only [droot, nuisanceDimensionCeiling]
    positivity
  have hmomentBound : 0 ≤ momentBound := by
    dsimp only [momentBound]
    positivity
  have hgammaFloor : 0 < gammaFloor := by
    dsimp only [gammaFloor]
    exact canonicalEffectiveNuisanceGammaFloor_pos
      (Head := Head) I hmarginFloor
  have hepsilon : Tendsto epsilon atTop (nhds 0) :=
    tendsto_zero_of_nonneg_mul_logL_zero epsilon
      hepsilonNonneg hepsilonRate
  have hmajorT : Tendsto
      (selectedMeshSchurRateMajorant epsilon droot momentBound
        gammaFloor centerScale) atTop (nhds 0) :=
    tendsto_selectedMeshSchurRateMajorant_zero epsilon
      hepsilon hepsilonRate hgammaFloor hcenterScale
  have hscaledT : Tendsto (fun n : ℕ ↦
      Cfull * (2 * selectedMeshSchurRateMajorant epsilon droot
        momentBound gammaFloor centerScale n)) atTop (nhds 0) := by
    simpa only [mul_zero] using
      tendsto_const_nhds.mul (tendsto_const_nhds.mul hmajorT)
  have hsmallEvent : ∀ᶠ n : ℕ in atTop,
      Cfull * (2 * selectedMeshSchurRateMajorant epsilon droot
        momentBound gammaFloor centerScale n) < 1 / 2 :=
    hscaledT.eventually (eventually_lt_nhds (by norm_num))
  have hbandTEvent := PrimeSums.eventually_bandTReciprocalSum_le W
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogEvent : ∀ᶠ n : ℕ in atTop,
      0 < Real.log (Scale.L n) :=
    (Real.tendsto_log_atTop.comp hLTop).eventually
      (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hsmallEvent, hbandTEvent, hlogEvent] with n hsmallMajor
      hbandT hlog
  intro B hBn hBW T hTmargin hbaseline hlo hhi fullEquiv hfull hinvFull
    hcenter hmarked
  subst n
  let gamma :=
    B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
  let rate := B.nuisanceMarkedSchurRate
    (epsilon B.sampleData.n) gamma
      (centerScale / Real.log (Scale.L B.sampleData.n))
  let Cschur := Cfull / (1 - Cfull * (2 * rate))
  have hdimension : Real.sqrt
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤ droot := by
    simpa only [droot] using B.sqrt_nuisanceCoord_card_le_ceiling
  have hmoment : (∑ j : Band,
      B.harmonicMass j * B.bandCenter j) ≤ momentBound := by
    rw [B.sum_harmonicMass_mul_bandCenter_eq_bandTReciprocalSum]
    rw [hBW]
    simpa only [momentBound] using hbandT
  have hgamma : gammaFloor ≤ gamma := by
    have h := B.canonicalEffectiveNuisanceGammaFloor_le I hU
      (by positivity : 0 ≤ 3 * (a : ℝ)) hmarginFloor T hTmargin
    rw [hBW] at h
    simpa only [gammaFloor, gamma] using h
  have hrateLe : rate ≤
      selectedMeshSchurRateMajorant epsilon droot momentBound
        gammaFloor centerScale B.sampleData.n := by
    dsimp only [rate]
    exact B.nuisanceMarkedSchurRate_le_selectedMeshSchurRateMajorant
      (hepsilonNonneg B.sampleData.n) hdroot hmomentBound hgammaFloor
      (by simpa only [gamma] using hgamma) hcenterScale hlog hdimension hmoment
  have hsmallHalf : Cfull * (2 * rate) < 1 / 2 := by
    have hmul : (2 * Cfull) * rate ≤
        (2 * Cfull) *
          selectedMeshSchurRateMajorant epsilon droot momentBound
            gammaFloor centerScale B.sampleData.n :=
      mul_le_mul_of_nonneg_left hrateLe (by positivity)
    nlinarith
  have hsmall : Cfull * (2 * rate) < 1 := by linarith
  obtain ⟨e, he, hinv, hquadratic⟩ :=
    B.exists_uniform_actualBandSchurEquiv_and_quadratic_of_full_of_marked
      I hU hlowerOne hupperU hlo hhi T hbaseline (by omega) a
      fullEquiv hfull hCfull (hepsilonNonneg B.sampleData.n)
      (div_pos hcenterScale hlog) hcenter hinvFull
      (by simpa only [gamma, rate] using hsmall) hmarked
  have hCschur : Cschur ≤ 2 * Cfull := by
    dsimp only [Cschur]
    exact schurInverseConstant_le_two_mul hCfull hsmallHalf.le
  refine ⟨e, ?_, ?_, hCschur, ?_⟩
  · simpa only [gamma, rate, Cschur] using he
  · simpa only [gamma, rate, Cschur] using hinv
  · simpa only [gamma, rate, Cschur] using hquadratic

/-- Named exact conclusion of the preceding theorem.  This is a proposition,
not an input package: its sole witness is the literal arithmetic Schur
equivalence, together with the map identity, inverse estimate, structural
constant bound, and covariance quadratic gap. -/
def ActualBandSchurCertificate
    (B : BridgeData Head Band) [Nonempty Head] [Nonempty Band]
    (I : PaperGuardCensus.PhysicalIntervals) (U : ℝ) (a : NNReal)
    (T : PaperGuardCensus.BarycentricTarget B.sampleData)
    (Cfull centerScale markedRate : ℝ)
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      ArithmeticModel.physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      ArithmeticModel.physicalBound (I.upper sigma) B.sampleData.n)
    (hbaseline : B.baseline = T.baseline)
    (hW : 1 < B.sampleData.W) : Prop :=
  let gamma :=
    B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
  let rate := B.nuisanceMarkedSchurRate markedRate gamma
    (centerScale / Real.log (Scale.L B.sampleData.n))
  let Cschur := Cfull / (1 - Cfull * (2 * rate))
  ∃ e : ∀ (z : B.EffectiveParamSpace),
      z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
        B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
    (∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
      e z hz q =
        B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
          (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
          (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
            hlowerOne hupperU hlo hhi T hbaseline hW z hz) q) ∧
    (∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) ((e z hz).symm v) ≤
        Cschur * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v) ∧
    Cschur ≤ 2 * Cfull ∧
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
            (B.bandRegressionScore q))

/-- Certificate-valued restatement of the exact terminal, convenient for
nesting it under the selected-mesh quantifiers without hiding any analytic
hypothesis in an input structure. -/
theorem eventually_actualBandSchurCertificate
    [Nonempty Head] [Nonempty Band]
    (I : PaperGuardCensus.PhysicalIntervals) {U : ℝ}
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (W : ℕ) (hW : 1 < W) (a : NNReal)
    (marginFloor centerScale Cfull : ℝ)
    (hmarginFloor : 0 < marginFloor)
    (hcenterScale : 0 < centerScale) (hCfull : 0 < Cfull)
    (epsilon : ℕ → ℝ) (hepsilonNonneg : ∀ n, 0 ≤ epsilon n)
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0)) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band)
        (_hBn : B.sampleData.n = n) (hBW : B.sampleData.W = W)
        (T : PaperGuardCensus.BarycentricTarget B.sampleData)
        (_hTmargin : marginFloor ≤ T.cellMassMargin)
        (hbaseline : B.baseline = T.baseline)
        (hlo : ∀ sigma, B.sampleData.lo sigma =
          ArithmeticModel.physicalBound (I.lower sigma) B.sampleData.n)
        (hhi : ∀ sigma, B.sampleData.hi sigma =
          ArithmeticModel.physicalBound (I.upper sigma) B.sampleData.n)
        (fullEquiv : ∀ (z : B.EffectiveParamSpace),
          z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
            SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
              SharpGaugeSpace B.partition.mass B.partition.center)
        (_hfull : ∀ (z : B.EffectiveParamSpace)
            (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
          fullEquiv z hz q =
            B.actualFullProjectedCLM (B.effectiveParamEquiv z) q)
        (_hinvFull : ∀ (z : B.EffectiveParamSpace)
            (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
          ‖(fullEquiv z hz).symm v‖ ≤ Cfull * ‖v‖)
        (_hcenter : ∀ i : Band,
          centerScale / Real.log (Scale.L B.sampleData.n) ≤ B.bandCenter i)
        (_hmarked : ∀ (z : B.EffectiveParamSpace)
            (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
            (c : NuisanceCoord B.HeadIndex)
            (p : BandPrime B.sampleData.n B.sampleData.W),
          |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
            (fun m ↦ B.nuisanceStatistic m c)
            (fun m ↦ ArithmeticModel.valuation p.1
              (B.sampleData.value m))| ≤
            epsilon B.sampleData.n * (1 / (p.1 : ℝ))),
        ActualBandSchurCertificate B I U a T Cfull centerScale
          (epsilon B.sampleData.n) hU hlowerOne hupperU hlo hhi
          hbaseline (by omega) := by
  filter_upwards [eventually_exists_uniform_actualBandSchurEquiv_and_quadratic
    (Head := Head) (Band := Band)
    I hU hlowerOne hupperU W hW a marginFloor centerScale Cfull
      hmarginFloor hcenterScale hCfull epsilon hepsilonNonneg
      hepsilonRate] with n hn
  intro B hBn hBW T hTmargin hbaseline hlo hhi fullEquiv hfull hinvFull
    hcenter hmarked
  exact hn B hBn hBW T hTmargin hbaseline hlo hhi fullEquiv hfull
    hinvFull hcenter hmarked

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
