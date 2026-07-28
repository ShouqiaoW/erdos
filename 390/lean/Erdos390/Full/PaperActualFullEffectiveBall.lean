import Erdos390.Full.PaperSelectedMeshActualFullProjectedInverseEventually
import Erdos390.Full.PaperBridgeBaselineL1

/-!
# From pointwise paper boxes to the preselected effective ODE ball

The selected-mesh actual-full theorem is naturally stated pointwise in the
literal prime-coefficient and physical-coordinate box.  The ODE is run on a
closed ball in the equivalent effective max norm.  This file records the
exact factor-three conversion and packages the pointwise inverses into one
ball-indexed family.
-/

open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- A pointwise actual-full inverse on the literal paper box supplies a
single family on the closed effective ODE ball.  The family is allowed to
depend on the proof of ball membership, exactly as in the later Schur
constructor; no continuity of this auxiliary choice is needed. -/
theorem exists_actualFullProjectedEquiv_on_closedBall_of_box
    (B : BridgeData Head Band) [Nonempty Head]
    (a : NNReal) {Cfull : ℝ}
    (hpoint : ∀ (xi : B.ParamSpace),
      (∀ p : BandPrime B.sampleData.n B.sampleData.W,
        |B.effectivePrimeCoefficient xi p| ≤ 3 * (a : ℝ)) →
      |xi MomentCoord.physical| ≤ 3 * (a : ℝ) →
      ∃ actualEquiv :
          SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
            SharpGaugeSpace B.partition.mass B.partition.center,
        (∀ q, actualEquiv q = B.actualFullProjectedCLM xi q) ∧
        ∀ v, ‖actualEquiv.symm v‖ ≤ Cfull * ‖v‖) :
    ∃ fullEquiv : ∀ (z : B.EffectiveParamSpace),
        z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
          SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
            SharpGaugeSpace B.partition.mass B.partition.center,
      (∀ (z : B.EffectiveParamSpace)
          (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
        fullEquiv z hz q =
          B.actualFullProjectedCLM (B.effectiveParamEquiv z) q) ∧
      ∀ (z : B.EffectiveParamSpace)
          (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
        ‖(fullEquiv z hz).symm v‖ ≤ Cfull * ‖v‖ := by
  have hbox : ∀ (z : B.EffectiveParamSpace),
      z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
        B.paperEffectiveSize (B.effectiveParamEquiv z) ≤ 3 * (a : ℝ) := by
    intro z hz
    have hznorm : ‖z‖ ≤ (a : ℝ) := by
      simpa only [mem_closedBall, dist_zero_right] using hz
    exact (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
      (mul_le_mul_of_nonneg_left hznorm (by norm_num))
  have hdata : ∀ (z : B.EffectiveParamSpace)
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      ∃ actualEquiv :
          SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
            SharpGaugeSpace B.partition.mass B.partition.center,
        (∀ q, actualEquiv q =
          B.actualFullProjectedCLM (B.effectiveParamEquiv z) q) ∧
        ∀ v, ‖actualEquiv.symm v‖ ≤ Cfull * ‖v‖ := by
    intro z hz
    have hb := B.effective_bounds_of_paperEffectiveSize
      (B.effectiveParamEquiv z) (hbox z hz)
    have hphysNorm :
        ‖B.nuisanceParameter (B.effectiveParamEquiv z)‖ ≤ 3 * (a : ℝ) :=
      hb.2
    have hphys :
        |B.effectiveParamEquiv z MomentCoord.physical| ≤ 3 * (a : ℝ) := by
      calc
        |B.effectiveParamEquiv z MomentCoord.physical| =
            ‖B.nuisanceParameter (B.effectiveParamEquiv z)
                NuisanceCoord.physical‖ := by
              simp only [B.nuisanceParameter_physical, Real.norm_eq_abs]
        _ ≤ ‖B.nuisanceParameter (B.effectiveParamEquiv z)‖ := by
              exact PiLp.norm_apply_le
                (B.nuisanceParameter (B.effectiveParamEquiv z))
                NuisanceCoord.physical
        _ ≤ 3 * (a : ℝ) := hphysNorm
    exact hpoint (B.effectiveParamEquiv z) hb.1 hphys
  let fullEquiv : ∀ (z : B.EffectiveParamSpace),
      z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
        SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
          SharpGaugeSpace B.partition.mass B.partition.center :=
    fun z hz ↦ (hdata z hz).choose
  refine ⟨fullEquiv, ?_, ?_⟩
  · intro z hz q
    exact (hdata z hz).choose_spec.1 q
  · intro z hz v
    exact (hdata z hz).choose_spec.2 v

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
