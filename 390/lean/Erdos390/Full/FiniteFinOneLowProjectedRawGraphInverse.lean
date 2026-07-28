import Erdos390.Full.FiniteOneLowProjectedRawGraphInverse
import Erdos390.Full.FinOneLowRelabel

/-!
# Projected ordinary inverse on `Fin (k+1)`

This is the exact indexing used by the canonical endpoint partition: zero is
the moving low cell and `i.succ` is positive cell `i`.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.FiniteFinOneLowProjectedRawGraphInverse

open FiniteGraphQuotientInverse
open FiniteOneLowProjectedRawGraphInverse
open FinOneLowRelabel

variable {k : ℕ}

theorem ordinary_projected_raw_bound_fin
    [NeZero k]
    (edge : Fin (k + 1) → Fin (k + 1) → ℝ)
    (anchor omega alpha q : Fin (k + 1) → ℝ)
    {kappa anchorMass alphaMin alphaMax incoming gaugeRatio
      lowMass lowRowMass G : ℝ}
    (hG : 0 ≤ G)
    (hbalance : ∀ i j, omega i * edge i j = omega j * edge j i)
    (hkappa : 0 < kappa)
    (hAnchorMass : ∑ j : Fin k, anchor j.succ = anchorMass)
    (hAnchorMassPos : 0 < anchorMass)
    (hPositiveDom : ∀ i j : Fin k,
      kappa * anchor j.succ ≤ edge i.succ j.succ)
    (hAlphaLow : 0 < alpha 0)
    (hAlphaPositiveLower : ∀ i : Fin k, alphaMin ≤ alpha i.succ)
    (hAlphaMin : 0 < alphaMin)
    (hAlphaPositiveUpper : ∀ i : Fin k, alpha i.succ ≤ alphaMax)
    (hAlphaPositiveNonneg : ∀ i : Fin k, 0 ≤ alpha i.succ)
    (hIncomingNonneg : ∀ i : Fin k, 0 ≤ edge i.succ 0)
    (hIncoming : ∀ i : Fin k, edge i.succ 0 ≤ incoming * alpha 0)
    (hIncomingNonnegConst : 0 ≤ incoming)
    (hOmegaPositiveNonneg : ∀ i : Fin k, 0 ≤ omega i.succ)
    (hOmegaPositive : 0 < ∑ i : Fin k, omega i.succ)
    (hOmegaLowNonneg : 0 ≤ omega 0)
    (hGaugeRatio : omega 0 ≤
      gaugeRatio * alpha 0 * (∑ i : Fin k, omega i.succ))
    (hGaugeRatioNonneg : 0 ≤ gaugeRatio)
    (hGauge : ∑ i : Fin (k + 1), omega i * q i = 0)
    (hLowEdgeNonneg : ∀ j : Fin k, 0 ≤ edge 0 j.succ)
    (hLowMassLower : lowMass ≤ ∑ j : Fin k, edge 0 j.succ)
    (hLowMassPos : 0 < lowMass)
    (hLowMassUpper : ∑ j : Fin k, edge 0 j.succ ≤ lowRowMass)
    (hLowRowMassNonneg : 0 ≤ lowRowMass)
    (hOutput : ∀ i : Fin (k + 1),
      |alpha i * meanProjection omega (graphOperator edge q) i| ≤ G)
    (hAbsorbPositive :
      2 * (1 / (kappa * anchorMass)) * incoming * alpha 0 ≤ 1 / 2)
    (hAbsorbLow :
      alpha 0 * lowRowMass *
          (4 * (1 / (kappa * anchorMass)) * incoming +
            2 * gaugeRatio) / lowMass ≤ 1 / 2) :
    ∀ i : Fin (k + 1),
      |alpha i * q i| ≤
        max
          (2 * (1 / lowMass +
            alpha 0 * lowRowMass *
              (4 * (1 / (kappa * anchorMass)) / alphaMin) / lowMass))
          (alphaMax *
            ((4 * (1 / (kappa * anchorMass)) / alphaMin) +
              (4 * (1 / (kappa * anchorMass)) * incoming +
                2 * gaugeRatio) *
                (2 * (1 / lowMass +
                  alpha 0 * lowRowMass *
                    (4 * (1 / (kappa * anchorMass)) / alphaMin) /
                      lowMass)))) * G := by
  let e : Option (Fin k) ≃ Fin (k + 1) := optionFinEquiv
  let edge' : Option (Fin k) → Option (Fin k) → ℝ :=
    fun i j ↦ edge (e i) (e j)
  let anchor' : Option (Fin k) → ℝ := fun i ↦ anchor (e i)
  let omega' : Option (Fin k) → ℝ := fun i ↦ omega (e i)
  let alpha' : Option (Fin k) → ℝ := fun i ↦ alpha (e i)
  let q' : Option (Fin k) → ℝ := fun i ↦ q (e i)
  have hbound := ordinary_projected_raw_bound edge' anchor' omega' alpha' q'
    hG (fun i j ↦ hbalance (e i) (e j)) hkappa hAnchorMass
    hAnchorMassPos hPositiveDom hAlphaLow hAlphaPositiveLower hAlphaMin
    hAlphaPositiveUpper hAlphaPositiveNonneg hIncomingNonneg hIncoming
    hIncomingNonnegConst hOmegaPositiveNonneg hOmegaPositive
    hOmegaLowNonneg hGaugeRatio hGaugeRatioNonneg
    (by simpa only [q', omega', e] using
      (sum_pull (fun i ↦ omega i * q i)).symm.trans hGauge)
    hLowEdgeNonneg hLowMassLower hLowMassPos hLowMassUpper
    hLowRowMassNonneg
    (by
      intro i
      have hgraph :
          graphOperator edge' q' i = graphOperator edge q (e i) := by
        exact graphOperator_pull edge q i
      have hproj :
          meanProjection omega' (graphOperator edge' q') i =
            meanProjection omega (graphOperator edge q) (e i) := by
        rw [show graphOperator edge' q' =
            fun a ↦ graphOperator edge q (e a) by
          funext a
          exact graphOperator_pull edge q a]
        exact meanProjection_pull omega (graphOperator edge q) i
      rw [hproj]
      exact hOutput (e i))
    hAbsorbPositive hAbsorbLow
  intro i
  let oi : Option (Fin k) := e.symm i
  have hi := hbound oi
  simpa only [alpha', q', oi, e, Equiv.apply_symm_apply] using hi

end Erdos390.Full.FiniteFinOneLowProjectedRawGraphInverse
