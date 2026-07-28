import Erdos390.Full.PaperActualSchurMarkedRow
import Erdos390.Full.PaperCanonicalNuisanceEffectiveBall

/-!
# Uniform raw band-Schur inverse from a full projected inverse

This file is the exact finite connector between the moving-low-cell output
of Lemma 8.4 and the raw-gauge interface used by the two-stage solve.  A
family of literal full projected inverses and one coordinatewise reciprocal
nuisance row are converted, uniformly on the preselected effective ball,
into linear equivalences whose maps are the actual finite band Schur maps.

No continuum limit, eventual estimate, or smallness assertion is hidden:
the Neumann smallness inequality and every constant occur in the statement.
-/

open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperGuardCensus
open PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Ball-uniform attachment of the literal nuisance Schur correction to a
given family of full projected inverses. -/
theorem exists_uniform_actualBandSchurEquiv_of_full_of_marked_on_closedBall
    [Nonempty Head] [Nonempty Band]
    (I : PhysicalIntervals) {U : ℝ}
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      ArithmeticModel.physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      ArithmeticModel.physicalBound (I.upper sigma) B.sampleData.n)
    (T : BarycentricTarget B.sampleData)
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
    (hCfull : 0 ≤ Cfull) (hCmarked : 0 ≤ Cmarked)
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
      ∀ (z : B.EffectiveParamSpace)
          (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
        paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) ((e z hz).symm v) ≤
          (Cfull / (1 - Cfull *
            (2 * B.nuisanceMarkedSchurRate Cmarked
              (B.canonicalEffectiveNuisanceGamma
                I U (3 * (a : ℝ)) T) amin))) *
            paperSharpNorm B.harmonicMass B.bandCenter
              (B.partition.center_ne_zero B.n_gt_one) v := by
  let gamma :=
    B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
  have hgamma : 0 < gamma := by
    exact B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
  have hgap : ∀ z
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
      gamma * ‖v‖ ^ 2 ≤
        inner ℝ v
          (B.nuisanceCovarianceOperator (B.effectiveParamEquiv z) v) := by
    intro z hz v
    exact B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
      hlowerOne hupperU hlo hhi T hbaseline hW z hz v
  have hexists : ∀ z
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      ∃ rawEquiv : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
        (∀ b, rawEquiv b =
          B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
            hgamma (hgap z hz) b) ∧
        ∀ u,
          paperSharpNorm B.harmonicMass B.bandCenter
              (B.partition.center_ne_zero B.n_gt_one)
              (rawEquiv.symm u) ≤
            (Cfull / (1 - Cfull *
              (2 * B.nuisanceMarkedSchurRate Cmarked gamma amin))) *
              paperSharpNorm B.harmonicMass B.bandCenter
                (B.partition.center_ne_zero B.n_gt_one) u := by
    intro z hz
    exact B.exists_actualBandSchurEquiv_of_full_of_marked
      (B.effectiveParamEquiv z) (fullEquiv z hz) (hfull z hz)
      hgamma (hgap z hz) hCfull hCmarked hamin hcenter
      (hinvFull z hz) (by simpa only [gamma] using hsmall)
      (hmarked z hz)
  choose e he hinv using hexists
  refine ⟨e, ?_, ?_⟩
  · intro z hz q
    simpa only [gamma] using he z hz q
  · intro z hz v
    simpa only [gamma] using hinv z hz v

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
