import Erdos390.Lemma84

/-!
# Exact weighted distance to the logarithmic null direction

The paper states the quotient gap using an infimum over the scalar multiple
of the band-centre vector.  The finite Lean development uses the explicit
weighted orthogonal projection `gaugePart`.  This file proves that the two
forms are literally equal, so a paper-facing terminal can use the displayed
infimum without changing the result.
-/

namespace Erdos390.Lemma84

noncomputable section

open Set

variable {Prime Band : Type*}
variable [Fintype Prime] [Fintype Band]
variable [DecidableEq Prime] [DecidableEq Band]

namespace WeightedBandData

variable (d : WeightedBandData Prime Band)

/-- The literal weighted distance appearing in the paper. -/
def bestBandDistance (b : Band → ℝ) : ℝ :=
  ⨅ mu : ℝ, d.bandNormSq (fun j ↦ b j - mu * d.center j)

/-- The explicit gauge projection attains the literal infimum. -/
theorem bestBandDistance_eq_bandNormSq_gaugePart
    (b : Band → ℝ) (hA : d.centerEnergy ≠ 0) :
    d.bestBandDistance b = d.bandNormSq (d.gaugePart b) := by
  unfold bestBandDistance
  apply le_antisymm
  · have hBdd : BddBelow (range
        (fun mu : ℝ ↦ d.bandNormSq
          (fun j ↦ b j - mu * d.center j))) := by
      refine ⟨0, ?_⟩
      rintro x ⟨mu, rfl⟩
      exact d.bandNormSq_nonneg _
    have h := ciInf_le hBdd (d.gaugeCoefficient b)
    simpa only [gaugePart] using h
  · exact le_ciInf fun mu ↦ d.gaugePart_best_distance b mu hA

/-- Paper-display form of the same identity. -/
theorem bestBandDistance_eq_iInf
    (b : Band → ℝ) :
    d.bestBandDistance b =
      ⨅ mu : ℝ, ∑ j : Band,
        d.mass j * |b j - mu * d.center j| ^ 2 := by
  unfold bestBandDistance
  congr 1
  funext mu
  unfold bandNormSq bandInner
  apply Finset.sum_congr rfl
  intro j _hj
  rw [sq_abs]
  ring

end WeightedBandData

end


end Erdos390.Lemma84
