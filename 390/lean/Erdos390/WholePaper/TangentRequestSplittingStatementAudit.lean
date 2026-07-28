import Erdos390.WholePaper.TangentRequestSplitting

/-! # Expanded literal statement audit for tangent request splitting -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example (L sigma f : ℝ) :
    tangentRequestCount L sigma f =
      max 1 (Nat.ceil (4 * L * f / sigma)) := rfl

example (L sigma f : ℝ) :
    tangentRequestPieceMass L sigma f =
      f / max 1 (Nat.ceil (4 * L * f / sigma)) := rfl

example (L sigma f : ℝ) :
    1 ≤ max 1 (Nat.ceil (4 * L * f / sigma)) := by
  simpa only [tangentRequestCount] using
    one_le_tangentRequestCount L sigma f

example {L sigma f : ℝ} (hf : 0 ≤ f) (hL : 0 < L) (hsigma : 0 < sigma) :
    4 * L * f / sigma ≤
        (max 1 (Nat.ceil (4 * L * f / sigma)) : ℕ) ∧
      f / (max 1 (Nat.ceil (4 * L * f / sigma)) : ℕ) ≤
        sigma / (4 * L) ∧
      f ≤ sigma * (max 1 (Nat.ceil (4 * L * f / sigma)) : ℕ) /
        (4 * L) ∧
      ((max 1 (Nat.ceil (4 * L * f / sigma)) : ℕ) : ℝ) ≤
        4 * L * f / sigma + 1 := by
  exact ⟨normalizedMass_le_tangentRequestCount L sigma f,
    tangentRequestPieceMass_le hf hL hsigma,
    tangentMass_le_count_mul hf hL hsigma,
    cast_tangentRequestCount_le hf hL hsigma⟩

example {L sigma f : ℝ} (hf : 0 < f) (hL : 0 < L) (hsigma : 0 < sigma) :
    ((max 1 (Nat.ceil (4 * L * f / sigma)) : ℕ) : ℝ) <
      4 * L * f / sigma + 1 := by
  simpa only [tangentRequestCount] using
    cast_tangentRequestCount_lt hf hL hsigma

example (L sigma f : ℝ) :
    (∑ _i : Fin (max 1 (Nat.ceil (4 * L * f / sigma))),
      f / (max 1 (Nat.ceil (4 * L * f / sigma)) : ℕ)) = f := by
  simpa only [tangentRequestCount, tangentRequestPieceMass] using
    sum_tangentRequestPieceMass L sigma f

example {E : Type*} {edges : Finset E} {L sigma : ℝ}
    {flow : E → ℝ} (hflow : ∀ e ∈ edges, 0 ≤ flow e)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (request : TangentSplitRequest edges L sigma flow) :
    0 ≤ flow request.1.1 /
          (max 1 (Nat.ceil (4 * L * flow request.1.1 / sigma)) : ℕ) ∧
      flow request.1.1 /
          (max 1 (Nat.ceil (4 * L * flow request.1.1 / sigma)) : ℕ) ≤
        (sigma / L) / 4 := by
  simpa only [tangentSplitRequestWeight, tangentRequestPieceMass,
    tangentRequestCount] using
      tangentSplitRequestWeight_mem_slackQuarter hflow hL hsigma request

example {E : Type*} (edges : Finset E)
    (L sigma : ℝ) (flow : E → ℝ) :
    Fintype.card
        (Σ e : ↑edges,
          Fin (max 1 (Nat.ceil (4 * L * flow e.1 / sigma)))) =
      ∑ e ∈ edges, max 1 (Nat.ceil (4 * L * flow e / sigma)) := by
  simpa only [TangentSplitRequest, tangentRequestCount,
    tangentRequestTotal] using
      card_tangentSplitRequest edges L sigma flow

example {E : Type*} (edges : Finset E)
    (L sigma : ℝ) (flow : E → ℝ) :
    (∑ request :
        (Σ e : ↑edges,
          Fin (max 1 (Nat.ceil (4 * L * flow e.1 / sigma)))),
        flow request.1.1 /
          (max 1 (Nat.ceil (4 * L * flow request.1.1 / sigma)) : ℕ)) =
      ∑ e ∈ edges, flow e := by
  simpa only [TangentSplitRequest, tangentRequestCount,
    tangentSplitRequestWeight, tangentRequestPieceMass] using
      sum_tangentSplitRequestWeight edges L sigma flow

example {E P : Type*} (edges : Finset E) (source target : E → P)
    (L sigma : ℝ) (flow : E → ℝ) (value : P → ℝ) :
    (∑ request :
        (Σ e : ↑edges,
          Fin (max 1 (Nat.ceil (4 * L * flow e.1 / sigma)))),
        (flow request.1.1 /
            (max 1 (Nat.ceil (4 * L * flow request.1.1 / sigma)) : ℕ)) *
          (value (source request.1.1) - value (target request.1.1))) =
      ∑ e ∈ edges, flow e * (value (source e) - value (target e)) := by
  simpa only [TangentSplitRequest, tangentRequestCount,
    tangentSplitRequestWeight, tangentRequestPieceMass,
    tangentSplitRequestSource, tangentSplitRequestTarget,
    tangentSplitRequestEdge] using
      sum_tangentSplitRequestWeight_mul_sub edges source target L sigma flow value

example {E : Type*} [DecidableEq E] (edges : Finset E)
    (source target : E → ℕ) (L sigma : ℝ) (flow : E → ℝ)
    (multiplier : TangentSplitRequest edges L sigma flow → ℕ)
    (x : ℕ → ℝ) (A : Finset ℕ) (p : ℕ)
    (hsourceMem : ∀ request : TangentSplitRequest edges L sigma flow,
      source request.1.1 * multiplier request ∈ A)
    (htargetMem : ∀ request : TangentSplitRequest edges L sigma flow,
      target request.1.1 * multiplier request ∈ A)
    (hsourcePos : ∀ request : TangentSplitRequest edges L sigma flow,
      source request.1.1 ≠ 0)
    (htargetPos : ∀ request : TangentSplitRequest edges L sigma flow,
      target request.1.1 ≠ 0)
    (hmultiplierPos : ∀ request : TangentSplitRequest edges L sigma flow,
      multiplier request ≠ 0) :
    ∑ a ∈ A,
        tangentUpdate Finset.univ
            (fun request ↦ source request.1.1)
            (fun request ↦ target request.1.1) multiplier
            (fun request ↦ flow request.1.1 /
              max 1 (Nat.ceil (4 * L * flow request.1.1 / sigma)))
            x a * (a.factorization p : ℝ) =
      (∑ a ∈ A, x a * (a.factorization p : ℝ)) +
        ∑ e ∈ edges, flow e *
          ((source e).factorization p - (target e).factorization p : ℝ) := by
  simpa only [tangentSplitRequests, tangentSplitRequestSource,
    tangentSplitRequestTarget, tangentSplitRequestEdge,
    tangentSplitRequestWeight, tangentRequestPieceMass,
    tangentRequestCount] using
      tangentSplitUpdate_valuation edges source target L sigma flow multiplier
        x A p
        (by simpa only [tangentSplitRequestSource,
          tangentSplitRequestEdge] using hsourceMem)
        (by simpa only [tangentSplitRequestTarget,
          tangentSplitRequestEdge] using htargetMem)
        (by simpa only [tangentSplitRequestSource,
          tangentSplitRequestEdge] using hsourcePos)
        (by simpa only [tangentSplitRequestTarget,
          tangentSplitRequestEdge] using htargetPos)
        hmultiplierPos

example {E : Type*} (edges : Finset E)
    {L sigma : ℝ} (flow : E → ℝ)
    (hflow : ∀ e ∈ edges, 0 ≤ flow e)
    (hL : 0 < L) (hsigma : 0 < sigma) :
    ((∑ e ∈ edges,
        max 1 (Nat.ceil (4 * L * flow e / sigma)) : ℕ) : ℝ) ≤
      (4 * L / sigma) * (∑ e ∈ edges, flow e) + edges.card := by
  simpa only [tangentRequestTotal, tangentRequestCount] using
    cast_tangentRequestTotal_le edges flow hflow hL hsigma

example {E P : Type*} [DecidableEq E] [DecidableEq P]
    (edges : Finset E) (source target : E → P)
    {L sigma : ℝ} (flow : E → ℝ)
    (hflow : ∀ e ∈ edges, 0 ≤ flow e)
    (hL : 0 < L) (hsigma : 0 < sigma) (p : P) :
    ((∑ e ∈ edges.filter
        (fun e ↦ source e = p ∨ target e = p),
          max 1 (Nat.ceil (4 * L * flow e / sigma)) : ℕ) : ℝ) ≤
      (4 * L / sigma) *
          (∑ e ∈ edges.filter
            (fun e ↦ source e = p ∨ target e = p), flow e) +
        (edges.filter
          (fun e ↦ source e = p ∨ target e = p)).card := by
  simpa only [tangentIncidentRequestCount, tangentRequestTotal,
    tangentRequestCount, tangentIncidentFlowMass, tangentSupportDegree,
    tangentIncidentEdges] using
      cast_tangentIncidentRequestCount_le edges source target flow
        hflow hL hsigma p

end

end Erdos390.WholePaper
