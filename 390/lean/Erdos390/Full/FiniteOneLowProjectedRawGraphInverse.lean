import Erdos390.Full.FiniteOneLowRawGraphInverse
import Erdos390.Full.FiniteReversibleGraph

/-!
# Projected ordinary inverse for a reversible one-low graph

The raw covariance operator is projected to its arithmetic gauge.  For the
continuum reference graph detailed balance makes that projection exactly the
identity on every graph row.  This wrapper therefore applies the proved
one-low maximum principle to the literal projected output.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.FiniteOneLowProjectedRawGraphInverse

open FiniteGraphQuotientInverse
open FiniteOneLowRawGraphInverse
open FiniteReversibleGraph

variable {Pos : Type*} [Fintype Pos] [DecidableEq Pos]

omit [DecidableEq Pos] in
theorem ordinary_projected_raw_bound
    [Nonempty Pos]
    (edge : Option Pos → Option Pos → ℝ)
    (anchor omega alpha q : Option Pos → ℝ)
    {kappa anchorMass alphaMin alphaMax incoming gaugeRatio
      lowMass lowRowMass G : ℝ}
    (hG : 0 ≤ G)
    (hbalance : ∀ i j, omega i * edge i j = omega j * edge j i)
    (hkappa : 0 < kappa)
    (hAnchorMass : ∑ j : Pos, anchor (some j) = anchorMass)
    (hAnchorMassPos : 0 < anchorMass)
    (hPositiveDom : ∀ i j : Pos,
      kappa * anchor (some j) ≤ edge (some i) (some j))
    (hAlphaLow : 0 < alpha none)
    (hAlphaPositiveLower : ∀ i : Pos, alphaMin ≤ alpha (some i))
    (hAlphaMin : 0 < alphaMin)
    (hAlphaPositiveUpper : ∀ i : Pos, alpha (some i) ≤ alphaMax)
    (hAlphaPositiveNonneg : ∀ i : Pos, 0 ≤ alpha (some i))
    (hIncomingNonneg : ∀ i : Pos, 0 ≤ edge (some i) none)
    (hIncoming : ∀ i : Pos,
      edge (some i) none ≤ incoming * alpha none)
    (hIncomingNonnegConst : 0 ≤ incoming)
    (hOmegaPositiveNonneg : ∀ i : Pos, 0 ≤ omega (some i))
    (hOmegaPositive : 0 < ∑ i : Pos, omega (some i))
    (hOmegaLowNonneg : 0 ≤ omega none)
    (hGaugeRatio : omega none ≤
      gaugeRatio * alpha none * (∑ i : Pos, omega (some i)))
    (hGaugeRatioNonneg : 0 ≤ gaugeRatio)
    (hGauge : ∑ i : Option Pos, omega i * q i = 0)
    (hLowEdgeNonneg : ∀ j : Pos, 0 ≤ edge none (some j))
    (hLowMassLower : lowMass ≤ ∑ j : Pos, edge none (some j))
    (hLowMassPos : 0 < lowMass)
    (hLowMassUpper : ∑ j : Pos, edge none (some j) ≤ lowRowMass)
    (hLowRowMassNonneg : 0 ≤ lowRowMass)
    (hOutput : ∀ i : Option Pos,
      |alpha i * meanProjection omega (graphOperator edge q) i| ≤ G)
    (hAbsorbPositive :
      2 * (1 / (kappa * anchorMass)) * incoming * alpha none ≤ 1 / 2)
    (hAbsorbLow :
      alpha none * lowRowMass *
          (4 * (1 / (kappa * anchorMass)) * incoming +
            2 * gaugeRatio) / lowMass ≤ 1 / 2) :
    ∀ i : Option Pos,
      |alpha i * q i| ≤
        max
          (2 * (1 / lowMass +
            alpha none * lowRowMass *
              (4 * (1 / (kappa * anchorMass)) / alphaMin) / lowMass))
          (alphaMax *
            ((4 * (1 / (kappa * anchorMass)) / alphaMin) +
              (4 * (1 / (kappa * anchorMass)) * incoming +
                2 * gaugeRatio) *
                (2 * (1 / lowMass +
                  alpha none * lowRowMass *
                    (4 * (1 / (kappa * anchorMass)) / alphaMin) /
                      lowMass)))) * G := by
  have hProjection := meanProjection_graphOperator_eq edge omega q hbalance
  apply ordinary_raw_bound edge anchor omega alpha q hG hkappa
    hAnchorMass hAnchorMassPos hPositiveDom hAlphaLow
    hAlphaPositiveLower hAlphaMin hAlphaPositiveUpper
    hAlphaPositiveNonneg hIncomingNonneg hIncoming
    hIncomingNonnegConst hOmegaPositiveNonneg hOmegaPositive
    hOmegaLowNonneg hGaugeRatio hGaugeRatioNonneg hGauge
    hLowEdgeNonneg hLowMassLower hLowMassPos hLowMassUpper
    hLowRowMassNonneg
  · intro i
    rw [← hProjection]
    exact hOutput i
  · exact hAbsorbPositive
  · exact hAbsorbLow

end Erdos390.Full.FiniteOneLowProjectedRawGraphInverse
