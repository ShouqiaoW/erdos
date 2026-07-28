import Erdos390.Full.PaperActualPrimePowerRelative
import Erdos390.Full.PaperBridgeNuisanceTiltFallback
import Erdos390.Full.PaperGuardPowerCorrectionMixture

/-!
# The bounded medium-only bridge mixture

The reference law used after guard deletion has the same literal integer
values as the bridge sample and differs from the actual component law only by
the residual physical tilt.  This file records that law with the paper's
common endpoint and proves the exact `VV-II = JI+IJ+JJ` identities used by
the physical-transfer ledger.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The medium-only component law, widened to the common bridge endpoint. -/
def mediumComponentValuationLaw [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) :
    BoundedValuationLaw (B.sampleData.SampleAt c) B.sampleEndpoint where
  probability := B.cellMediumLaw xi c
  value := fun m ↦ (m : ℕ)
  value_pos := by
    intro m
    let sample : B.sampleData.Sample := ⟨c, m⟩
    simpa only [sample, StructuredSampleData.value] using
      B.sampleData.value_pos sample
  value_le := by
    intro m
    let sample : B.sampleData.Sample := ⟨c, m⟩
    simpa only [sample, StructuredSampleData.value] using
      B.sample_value_le_endpoint sample

@[simp] theorem mediumComponentValuationLaw_probability [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) :
    (B.mediumComponentValuationLaw xi c).probability =
      B.cellMediumLaw xi c := rfl

@[simp] theorem mediumComponentValuationLaw_value [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (m : B.sampleData.SampleAt c) :
    (B.mediumComponentValuationLaw xi c).value m = (m : ℕ) := rfl

/-- The bounded-law and raw finite-probability definitions of the
prime-power correction are definitionally the same. -/
theorem powerCorrectionCovariance_eq_covVV_sub_covII
    {Omega : Type*} [Fintype Omega] {M : ℕ}
    (law : BoundedValuationLaw Omega M) (p q : ℕ) :
    PaperGuardCensus.powerCorrectionCovariance
        law.probability law.value p q =
      law.covVV p q - law.covII p q := rfl

/-- Exact three-orientation expansion of the prime-power correction. -/
theorem powerCorrectionCovariance_eq_three_orientations
    {Omega : Type*} [Fintype Omega] {M : ℕ}
    (law : BoundedValuationLaw Omega M) (p q : ℕ) :
    PaperGuardCensus.powerCorrectionCovariance
        law.probability law.value p q =
      law.covJI p q + law.covIJ p q + law.covJJ p q := by
  rw [powerCorrectionCovariance_eq_covVV_sub_covII law p q,
    law.covVV_sub_covII]

/-- The probability under the bounded tagged medium mixture is exactly the
tagged mixture of the literal component medium laws. -/
theorem sigmaMixture_mediumComponent_probability [Nonempty Head]
    (xi : B.ParamSpace) (weight : FiniteProbability (Cell Head)) :
    (BoundedValuationLaw.sigmaMixture weight
        (B.mediumComponentValuationLaw xi)).probability =
      FiniteProbability.sigmaMixture weight (B.cellMediumLaw xi) := rfl

/-- The global value map of the tagged medium mixture is the underlying
integer in each component. -/
@[simp] theorem sigmaMixture_mediumComponent_value [Nonempty Head]
    (xi : B.ParamSpace) (weight : FiniteProbability (Cell Head))
    (x : Sigma fun c : Cell Head ↦ B.sampleData.SampleAt c) :
    (BoundedValuationLaw.sigmaMixture weight
        (B.mediumComponentValuationLaw xi)).value x = (x.2 : ℕ) := rfl

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
