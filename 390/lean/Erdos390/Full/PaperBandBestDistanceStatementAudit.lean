import Erdos390.Full.PaperBandBestDistance

/-! Independently expanded audit of the literal weighted infimum identity. -/

namespace Erdos390.Full.PaperBandBestDistanceStatementAudit

noncomputable section

open Set
open Erdos390.Lemma84

variable {Prime Band : Type*}
variable [Fintype Prime] [Fintype Band]
variable [DecidableEq Prime] [DecidableEq Band]

example (d : WeightedBandData Prime Band) (b : Band → ℝ)
    (hA : d.centerEnergy ≠ 0) :
    (⨅ mu : ℝ, ∑ j : Band,
        d.mass j * |b j - mu * d.center j| ^ 2) =
      ∑ j : Band, d.mass j * |d.gaugePart b j| ^ 2 := by
  rw [← d.bestBandDistance_eq_iInf b,
    d.bestBandDistance_eq_bandNormSq_gaugePart b hA]
  unfold WeightedBandData.bandNormSq WeightedBandData.bandInner
  apply Finset.sum_congr rfl
  intro j _hj
  rw [sq_abs]
  ring

end

end Erdos390.Full.PaperBandBestDistanceStatementAudit
