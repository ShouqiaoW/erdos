import Erdos390.WholePaper.TangentPairArithmetic

/-!
# Expanded statement audit for tangent pair arithmetic

The examples below keep the remaining quantitative boundary visible.  The
effective density, endpoint cutoff bounds, and final traffic smallness are
inputs.  The module proves the finite four-equation aggregation and the
resulting constants; it does not prove those analytic inputs.
-/

namespace Erdos390.WholePaper.TangentPairArithmeticStatementAudit

noncomputable section

example (n K h : ℕ) : tangentBroadUpper n K h ≤ 2 * n :=
  tangentBroadUpper_le_two_mul n K h

example {Request : Type*} (n : ℕ) (source target : Request → ℕ)
    (lowerCard : Request → ℕ) (baseDensity ratio : ℝ)
    (hratioPos : 0 < ratio)
    (hmaxLower : ∀ request,
      baseDensity * n ≤
        (lowerCard request : ℝ) *
          ((max (source request) (target request) : ℕ) : ℝ))
    (hratio : ∀ request,
      ((max (source request) (target request) : ℕ) : ℝ) ≤
        ratio *
          ((min (source request) (target request) : ℕ) : ℝ)) :
    ∀ request side,
      (baseDensity / ratio) * n ≤
        (lowerCard request : ℝ) *
          tangentEndpointLabel source target side request :=
  tangentEndpointLowerScale_of_maxLower
    n source target lowerCard baseDensity ratio hratioPos hmaxLower hratio

/-- This conclusion has exactly the shape of `hpairArithmetic` in the split
request terminals; the distinct-request proof is intentionally unused because
the finite estimate holds for every ordered pair. -/
example {Request : Type*} [DecidableEq Request]
    (n K h labelUpper : ℕ) (source target : Request → ℕ)
    (lowerCard : Request → ℕ) (density : ℝ)
    (hn : 0 < n) (hdensity : 0 < density)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hendpointDistinct : ∀ request, source request ≠ target request)
    (hprime : ∀ request side,
      (tangentEndpointLabel source target side request).Prime)
    (hlabelUpper : ∀ request side,
      tangentEndpointLabel source target side request ≤ labelUpper)
    (hlabelUpperLe : (labelUpper : ℝ) ≤ n)
    (hlabelUpperSq : (labelUpper : ℝ) ^ 2 ≤ n)
    (hlowerScale : ∀ request side,
      density * n ≤
        (lowerCard request : ℝ) *
          tangentEndpointLabel source target side request) :
    ∀ left right, ∀ _hne : left ≠ right,
      (tangentOrderedPairEndpointBudget (tangentBroadUpper n K h)
          source target left right : ℝ) /
          (lowerCard left * lowerCard right) ≤
        tangentDensityDisjointCoefficient density / n +
          (if tangentRequestHasLabel source target (source left) right
            then tangentDensitySharedCoefficient density * source left / n
            else 0) +
          (if tangentRequestHasLabel source target (target left) right
            then tangentDensitySharedCoefficient density * target left / n
            else 0) := by
  intro left right _hne
  exact tangentOrderedPairEndpointBudget_div_le_densityCoefficients
    n K h labelUpper source target lowerCard density hn hdensity hlowerPos
      hendpointDistinct hprime hlabelUpper hlabelUpperLe hlabelUpperSq
        hlowerScale left right

example {density totalTerm sourceTerm targetTerm : ℝ}
    (hdensity : 0 < density)
    (hsmall :
      4 * totalTerm + sourceTerm + targetTerm ≤ density ^ 2 / 24) :
    totalTerm * tangentDensityDisjointCoefficient density +
        sourceTerm * tangentDensitySharedCoefficient density +
        targetTerm * tangentDensitySharedCoefficient density ≤
      1 / 8 :=
  tangentDensityCollisionBudget_le_eighth hdensity hsmall

example {E : Type*} [DecidableEq E]
    (n : ℕ) (edges : Finset E) (source target : E → ℕ)
    {flow : E → ℝ}
    (L sigma totalTraffic : ℝ) (incidentTraffic : ℕ → ℝ)
    (supportCount : ℕ) (density : ℝ)
    (hdensity : 0 < density)
    (request : TangentSplitRequest edges L sigma flow)
    (hsmall :
      4 * (tangentSplitCensusTotalRequestUpper
            L sigma totalTraffic supportCount / n) +
        (((tangentSplitRequestSource (P := ℕ) source request : ℕ) : ℝ) *
          tangentSplitCensusLabelRequestUpper L sigma incidentTraffic
            supportCount (tangentSplitRequestSource source request) / n) +
        (((tangentSplitRequestTarget (P := ℕ) target request : ℕ) : ℝ) *
          tangentSplitCensusLabelRequestUpper L sigma incidentTraffic
            supportCount (tangentSplitRequestTarget target request) / n) ≤
          density ^ 2 / 24) :
    tangentSplitNormalizedCollisionCensusBudget
        (flow := flow) n edges source target L sigma
          totalTraffic incidentTraffic supportCount
          (tangentDensityDisjointCoefficient density)
          (tangentDensitySharedCoefficient density) request ≤ 1 / 8 :=
  tangentSplitNormalizedCollisionCensusBudget_le_eighth_of_density
    n edges source target L sigma totalTraffic incidentTraffic supportCount
      density hdensity request hsmall

/-! ## Supporting public API -/

example {density : ℝ} (hdensity : 0 ≤ density) :
    0 ≤ tangentDensityDisjointCoefficient density :=
  tangentDensityDisjointCoefficient_nonneg hdensity

example {density : ℝ} (hdensity : 0 ≤ density) :
    0 ≤ tangentDensitySharedCoefficient density :=
  tangentDensitySharedCoefficient_nonneg hdensity

example {N leftLabel rightLabel : ℕ} (hne : leftLabel ≠ rightLabel) :
    (tangentEndpointEquationBudget N leftLabel rightLabel : ℝ) ≤
      (N : ℝ) / ((leftLabel : ℝ) * rightLabel) + 1 :=
  cast_tangentEndpointEquationBudget_le_of_ne hne

example (N label : ℕ) :
    (tangentEndpointEquationBudget N label label : ℝ) ≤
      (N : ℝ) / (label : ℝ) + 1 :=
  cast_tangentEndpointEquationBudget_le_of_eq N label

example {Request : Type*} [DecidableEq Request]
    (N : ℕ) (source target : Request → ℕ)
    (lowerCard : Request → ℕ)
    (disjointCharge : ℝ) (sharedCharge : ℕ → ℝ)
    (hendpointDistinct : ∀ request, source request ≠ target request)
    (hEquation : ∀ left right,
      ∀ leftSide rightSide : TangentEndpointSide,
      (tangentEndpointEquationBudget N
          (tangentEndpointLabel source target leftSide left)
          (tangentEndpointLabel source target rightSide right) : ℝ) /
          (lowerCard left * lowerCard right) ≤
        disjointCharge / 4 +
          (if tangentEndpointLabel source target leftSide left =
              tangentEndpointLabel source target rightSide right
            then sharedCharge
              (tangentEndpointLabel source target leftSide left)
            else 0))
    (left right : Request) :
    (tangentOrderedPairEndpointBudget N source target left right : ℝ) /
        (lowerCard left * lowerCard right) ≤
      disjointCharge +
        (if tangentRequestHasLabel source target (source left) right
          then sharedCharge (source left) else 0) +
        (if tangentRequestHasLabel source target (target left) right
          then sharedCharge (target left) else 0) :=
  tangentOrderedPairEndpointBudget_div_le_charges_of_equationBounds
    N source target lowerCard disjointCharge sharedCharge
      hendpointDistinct hEquation left right

end

end Erdos390.WholePaper.TangentPairArithmeticStatementAudit
