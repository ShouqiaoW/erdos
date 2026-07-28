import Erdos390.WholePaper.TangentStarSplitRequestBridge

/-! # Expanded statement audit for the star-to-split-request bridge -/

open scoped BigOperators

namespace Erdos390.WholePaper.TangentStarSplitRequestBridgeStatementAudit

open Erdos390.Full.ArithmeticModel

noncomputable section

example {V : Type*} [DecidableEq V]
    (pivot : V) (residual : V → ℝ) (label : V → ℕ) (edge : V × V) :
    tangentStarEdgeSource label edge = label edge.1 ∧
      tangentStarEdgeTarget label edge = label edge.2 ∧
      tangentStarEdgeFlow pivot residual edge =
        tangentStarFlow pivot residual edge.1 edge.2 := by
  constructor
  · rfl
  constructor <;> rfl

example {V : Type*} [Fintype V] [DecidableEq V]
    (pivot : V) (residual : V → ℝ) (label : V → ℕ) (q : ℕ) :
    tangentStarLabelIncidentTraffic pivot residual label q =
      tangentIncidentFlowMass
        (tangentStarPositiveEdges pivot residual)
        (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
        (tangentStarEdgeFlow pivot residual) q := by
  rfl

example {V : Type*} [Fintype V] [DecidableEq V]
    (pivot : V) (residual : V → ℝ) :
    tangentStarPositiveEdges pivot residual =
      tangentPositiveFlowEdges (tangentStarFlow pivot residual) ∧
      tangentStarResidualL1 residual = ∑ v : V, |residual v| ∧
      (∀ label : ℕ, tangentStarResidualL1IncidentTraffic residual label =
        ∑ v : V, |residual v|) ∧
    tangentStarSupportCount V = 2 * Fintype.card V := by
  simp [tangentStarPositiveEdges, tangentStarResidualL1,
    tangentStarResidualL1IncidentTraffic, tangentStarSupportCount]

example {V : Type*} [Fintype V] [DecidableEq V]
    (pivot : V) (residual : V → ℝ) (label : V → ℕ) :
    (∑ edge ∈ tangentStarPositiveEdges pivot residual,
        tangentStarEdgeFlow pivot residual edge) =
        ∑ v ∈ (Finset.univ : Finset V).erase pivot, |residual v| ∧
      (∑ edge ∈ tangentStarPositiveEdges pivot residual,
          tangentStarEdgeFlow pivot residual edge) ≤
        tangentStarResidualL1 residual ∧
      (∀ q,
        tangentIncidentFlowMass
            (tangentStarPositiveEdges pivot residual)
            (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
            (tangentStarEdgeFlow pivot residual) q ≤
          tangentStarResidualL1IncidentTraffic residual q) ∧
      (tangentStarPositiveEdges pivot residual).card ≤
        tangentStarSupportCount V := by
  exact ⟨sum_tangentStarPositiveEdges_eq_sum_erase_abs pivot residual,
    sum_tangentStarPositiveEdges_le_residualL1 pivot residual,
    tangentStarIncidentFlowMass_le_residualL1 pivot residual label,
    card_tangentStarPositiveEdges_le_supportCount pivot residual⟩

example {V : Type*} [Fintype V] [DecidableEq V]
    {pivot : V} {residual : V → ℝ}
    (hsum : (∑ v : V, residual v) = 0)
    (label : V → ℕ) (L sigma : ℝ) :
    (∀ v,
      tangentFlowDivergence (tangentStarFlow pivot residual) v =
        residual v) ∧
      (∀ p,
        (∑ request : TangentSplitRequest
              (tangentStarPositiveEdges pivot residual) L sigma
                (tangentStarEdgeFlow pivot residual),
            tangentSplitRequestWeight request *
              (((tangentSplitRequestSource (tangentStarEdgeSource label)
                    request).factorization p : ℝ) -
                ((tangentSplitRequestTarget (tangentStarEdgeTarget label)
                    request).factorization p : ℝ))) =
          ∑ v : V, residual v * (label v).factorization p) := by
  exact ⟨tangentStarFlow_divergence_eq hsum,
    tangentStarSplitRequest_factorizationBoundary_eq_residual
      hsum label L sigma⟩

example
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : ℝ} {depth n M : ℕ}
    {left right : ℕ → ℕ} {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (K h Phead X0 : ℕ)
    (pivot : V) (residual : V → ℝ) (label : V → ℕ)
    (hsum : (∑ v : V, residual v) = 0)
    (hlabelInjective : Function.Injective label)
    (hlabelPrime : ∀ v, (label v).Prime)
    (incidentTraffic : ℕ → ℝ)
    (hincidentTraffic : ∀ q,
      tangentStarLabelIncidentTraffic pivot residual label q ≤
        incidentTraffic q)
    (labelUpper : ℕ) (density : ℝ)
    (hn : 0 < n) (hdensity : 0 < density)
    (hlabelUpper : ∀ v, label v ≤ labelUpper)
    (hlabelUpperLe : (labelUpper : ℝ) ≤ n)
    (hlabelUpperSq : (labelUpper : ℝ) ^ 2 ≤ n)
    {L sigma : ℝ} (hL : 0 < L) (hsigma : 0 < sigma)
    (lowerCard : TangentSplitRequest
      (tangentStarPositiveEdges pivot residual) L sigma
        (tangentStarEdgeFlow pivot residual) → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request,
      lowerCard request ≤
        (tangentSplitCleanMultiplierLists
          (tangentStarPositiveEdges pivot residual)
          (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
          L sigma (tangentStarEdgeFlow pivot residual)
          n K h Phead X0 (yNat n) R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request).card)
    (hlowerScale : ∀ request side,
      density * n ≤ (lowerCard request : ℝ) *
        tangentEndpointLabel
          (tangentSplitRequestSource (tangentStarEdgeSource label))
          (tangentSplitRequestTarget (tangentStarEdgeTarget label))
          side request)
    (hsmall : ∀ request : TangentSplitRequest
        (tangentStarPositiveEdges pivot residual) L sigma
          (tangentStarEdgeFlow pivot residual),
      4 * (tangentSplitCensusTotalRequestUpper L sigma
            (tangentStarResidualL1 residual)
            (tangentStarSupportCount V) / n) +
        (((tangentSplitRequestSource (P := ℕ)
              (tangentStarEdgeSource label) request : ℕ) : ℝ) *
          tangentSplitCensusLabelRequestUpper L sigma
            incidentTraffic
            (tangentStarSupportCount V)
            (tangentSplitRequestSource (tangentStarEdgeSource label)
              request) / n) +
        (((tangentSplitRequestTarget (P := ℕ)
              (tangentStarEdgeTarget label) request : ℕ) : ℝ) *
          tangentSplitCensusLabelRequestUpper L sigma
            incidentTraffic
            (tangentStarSupportCount V)
            (tangentSplitRequestTarget (tangentStarEdgeTarget label)
              request) / n) ≤ density ^ 2 / 24) :
    (∀ v, tangentFlowDivergence (tangentStarFlow pivot residual) v =
        residual v) ∧
      (∀ p,
        (∑ request : TangentSplitRequest
              (tangentStarPositiveEdges pivot residual) L sigma
                (tangentStarEdgeFlow pivot residual),
            tangentSplitRequestWeight request *
              (((tangentSplitRequestSource (tangentStarEdgeSource label)
                    request).factorization p : ℝ) -
                ((tangentSplitRequestTarget (tangentStarEdgeTarget label)
                    request).factorization p : ℝ))) =
          ∑ v : V, residual v * (label v).factorization p) ∧
      ∃ multiplier : TangentSplitRequest
          (tangentStarPositiveEdges pivot residual) L sigma
            (tangentStarEdgeFlow pivot residual) → ℕ,
        (∀ request,
          multiplier request ∈
            tangentSplitCleanMultiplierLists
              (tangentStarPositiveEdges pivot residual)
              (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
              L sigma (tangentStarEdgeFlow pivot residual)
              n K h Phead X0 (yNat n) R.tangentPaperDedicatedRows
              (R.tangentPaperNumericalGuardSet
                certificate fixedExceptional) request) ∧
        TangentEndpointsDistinct
          (tangentSplitRequests
            (tangentStarPositiveEdges pivot residual) L sigma
              (tangentStarEdgeFlow pivot residual))
          (tangentSplitRequestSource (tangentStarEdgeSource label))
          (tangentSplitRequestTarget (tangentStarEdgeTarget label))
          multiplier :=
  R.tangentPaperStarSplitEndpointsDistinct_of_residualL1Census
    certificate fixedExceptional K h Phead X0 pivot residual label hsum
      hlabelInjective hlabelPrime incidentTraffic hincidentTraffic
      labelUpper density hn hdensity
      hlabelUpper hlabelUpperLe hlabelUpperSq hL hsigma lowerCard
      hlowerPos hlower hlowerScale hsmall

/-! ## Supporting public API -/

#check mem_tangentStarPositiveEdges
#check tangentStarEdgeFlow_nonneg
#check tangentStarPositiveEdge_labels_ne
#check sum_tangentStarPositiveEdges_eq_traffic
#check sum_tangentStarPositiveEdges_mul_eq_full
#check tangentStarPositiveEdges_factorizationBoundary_eq_residual

end

end Erdos390.WholePaper.TangentStarSplitRequestBridgeStatementAudit
