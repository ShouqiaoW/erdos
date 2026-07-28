import Erdos390.Full.PaperActualFullBandIdentification

/-!
# Raw-gauge transport of the literal actual-full inverse

The eventual Lemma 8.4 theorem constructs its inverse in the centre-scaled
sharp gauge.  This exact conjugacy transports it to the paper raw gauge
before the later finite nuisance-Schur perturbation.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

theorem rawBandEquivOfSharpEquiv_eq_actualBandFullLinearMap
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace)
    (e : SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
      SharpGaugeSpace B.partition.mass B.partition.center)
    (he : ∀ q, e q = B.actualFullProjectedCLM xi q)
    (b : RawGaugeSpace B.partition.mass B.partition.center) :
    B.rawBandEquivOfSharpEquiv e b =
      B.actualBandFullLinearMap xi b := by
  let S := scaleGaugeLinearEquiv B.partition.mass B.partition.center
    (B.partition.center_ne_zero B.n_gt_one)
  change S (e (S.symm b)) = B.actualBandFullLinearMap xi b
  rw [he]
  have hscale := B.scale_actualFullProjected_eq_actualBandFull xi (S.symm b)
  calc
    S (B.actualFullProjectedCLM xi (S.symm b)) =
        B.actualBandFullLinearMap xi (S (S.symm b)) := by
      simpa only [S] using hscale
    _ = B.actualBandFullLinearMap xi b := by rw [S.apply_symm_apply]

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
