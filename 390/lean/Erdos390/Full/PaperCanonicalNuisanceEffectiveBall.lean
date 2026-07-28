import Erdos390.Full.PaperCanonicalNuisanceEffectiveGap

/-!
# Canonical nuisance gap on the actual effective ODE ball

The canonical finite nuisance theorem is stated in the paper effective
size.  The ODE is run in the equivalent effective max norm.  This file
records the exact conversion, including the factor three, so later Schur
constructors need not assume a nuisance gap separately.
-/

open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel PaperGuardCensus

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The root canonical finite nuisance gap, specialized to every point of
the preselected effective ODE ball. -/
theorem canonicalEffectiveNuisanceGap_on_closedBall
    [Nonempty Head]
    (I : PhysicalIntervals) {U : ℝ} (a : NNReal)
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (T : BarycentricTarget B.sampleData)
    (hbaseline : B.baseline = T.baseline)
    (hW : 1 < B.sampleData.W)
    (z : B.EffectiveParamSpace)
    (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) :
    ∀ v : B.NuisanceSpace,
      B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T *
          ‖v‖ ^ 2 ≤
        inner ℝ v
          (B.nuisanceCovarianceOperator (B.effectiveParamEquiv z) v) := by
  have hznorm : ‖z‖ ≤ (a : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using hz
  have hsize : B.paperEffectiveSize (B.effectiveParamEquiv z) ≤
      3 * (a : ℝ) :=
    (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
      (mul_le_mul_of_nonneg_left hznorm (by norm_num))
  exact B.canonicalEffectiveNuisanceGapProof I hU hlowerOne hupperU
    hlo hhi T hbaseline hW (B.effectiveParamEquiv z) hsize

end BridgeData

end


end Erdos390.Full.PaperBridgeFit
