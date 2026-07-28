import Erdos390.WholePaper.TangentCollisionFreeFeasibility

/-! # Expanded statement audit for collision-free tangent feasibility -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example {ι : Type*} {requests : Finset ι}
    {source target multiplier : ι → ℕ} {weight : ι → ℝ}
    {x : ℕ → ℝ} {A : Finset ℕ} {δ : ℝ}
    (hsourceInjective : Set.InjOn
      (fun e ↦ source e * multiplier e) requests)
    (htargetInjective : Set.InjOn
      (fun e ↦ target e * multiplier e) requests)
    (hcross : ∀ e ∈ requests, ∀ f ∈ requests,
      source e * multiplier e ≠ target f * multiplier f)
    (hδ : 0 ≤ δ)
    (hweight : ∀ e ∈ requests, 0 ≤ weight e ∧ weight e ≤ δ)
    (hsourceSlack : ∀ e ∈ requests,
      δ ≤ x (source e * multiplier e) ∧
        x (source e * multiplier e) ≤ 1 - δ)
    (htargetSlack : ∀ e ∈ requests,
      δ ≤ x (target e * multiplier e) ∧
        x (target e * multiplier e) ≤ 1 - δ)
    (hglobal : ∀ a ∈ A, x a ∈ Set.Icc (0 : ℝ) 1) :
    ∀ a ∈ A,
      x a +
          ∑ e ∈ requests, weight e *
            ((if a = source e * multiplier e then (1 : ℝ) else 0) -
              (if a = target e * multiplier e then (1 : ℝ) else 0)) ∈
        Set.Icc (0 : ℝ) 1 := by
  simpa only [tangentUpdate, tangentDelta, tangentPointMass] using
    tangentUpdate_mem_unitInterval
      (⟨hsourceInjective, htargetInjective, hcross⟩ :
        TangentEndpointsDistinct requests source target multiplier)
      hδ hweight hsourceSlack htargetSlack hglobal

example {ι : Type*} {requests : Finset ι}
    {source target multiplier : ι → ℕ} {weight : ι → ℝ}
    {x : ℕ → ℝ} {δ : ℝ}
    (hsourceInjective : Set.InjOn
      (fun e ↦ source e * multiplier e) requests)
    (htargetInjective : Set.InjOn
      (fun e ↦ target e * multiplier e) requests)
    (hcross : ∀ e ∈ requests, ∀ f ∈ requests,
      source e * multiplier e ≠ target f * multiplier f)
    (hδ : 0 ≤ δ)
    (hweight : ∀ e ∈ requests, 0 ≤ weight e ∧ weight e ≤ δ / 4)
    (hsourceSlack : ∀ e ∈ requests,
      δ ≤ x (source e * multiplier e) ∧
        x (source e * multiplier e) ≤ 1 - δ)
    {e : ι} (he : e ∈ requests) :
    3 * δ / 4 ≤
        x (source e * multiplier e) +
          ∑ f ∈ requests, weight f *
            ((if source e * multiplier e = source f * multiplier f
                then (1 : ℝ) else 0) -
              (if source e * multiplier e = target f * multiplier f
                then (1 : ℝ) else 0)) ∧
      x (source e * multiplier e) +
          ∑ f ∈ requests, weight f *
            ((if source e * multiplier e = source f * multiplier f
                then (1 : ℝ) else 0) -
              (if source e * multiplier e = target f * multiplier f
                then (1 : ℝ) else 0)) ≤
        1 - 3 * δ / 4 := by
  simpa only [tangentUpdate, tangentDelta, tangentPointMass] using
    tangentUpdate_source_margin
      (⟨hsourceInjective, htargetInjective, hcross⟩ :
        TangentEndpointsDistinct requests source target multiplier)
      hδ hweight hsourceSlack he

example {E : Type*} [DecidableEq E] (edges : Finset E)
    (source target : E → ℕ) {L sigma : ℝ} (flow : E → ℝ)
    (hflow : ∀ e ∈ edges, 0 < flow e)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (multiplier : TangentSplitRequest edges L sigma flow → ℕ)
    (x : ℕ → ℝ) (A : Finset ℕ)
    (hdistinct : TangentEndpointsDistinct
      (tangentSplitRequests edges L sigma flow)
      (tangentSplitRequestSource source)
      (tangentSplitRequestTarget target) multiplier)
    (hsourceSlack : ∀ request : TangentSplitRequest edges L sigma flow,
      sigma / L ≤ x (source request.1.1 * multiplier request) ∧
        x (source request.1.1 * multiplier request) ≤ 1 - sigma / L)
    (htargetSlack : ∀ request : TangentSplitRequest edges L sigma flow,
      sigma / L ≤ x (target request.1.1 * multiplier request) ∧
        x (target request.1.1 * multiplier request) ≤ 1 - sigma / L)
    (hglobal : ∀ a ∈ A, x a ∈ Set.Icc (0 : ℝ) 1) :
    (∀ a ∈ A,
      tangentUpdate (tangentSplitRequests edges L sigma flow)
          (fun request ↦ source request.1.1)
          (fun request ↦ target request.1.1) multiplier
          (fun request ↦ flow request.1.1 /
            tangentRequestCount L sigma (flow request.1.1)) x a ∈
        Set.Icc (0 : ℝ) 1) ∧
      (∀ request : TangentSplitRequest edges L sigma flow,
        3 * (sigma / L) / 4 ≤
            tangentUpdate (tangentSplitRequests edges L sigma flow)
              (fun request ↦ source request.1.1)
              (fun request ↦ target request.1.1) multiplier
              (fun request ↦ flow request.1.1 /
                tangentRequestCount L sigma (flow request.1.1)) x
              (source request.1.1 * multiplier request) ∧
          tangentUpdate (tangentSplitRequests edges L sigma flow)
              (fun request ↦ source request.1.1)
              (fun request ↦ target request.1.1) multiplier
              (fun request ↦ flow request.1.1 /
                tangentRequestCount L sigma (flow request.1.1)) x
              (source request.1.1 * multiplier request) ≤
            1 - 3 * (sigma / L) / 4) ∧
      ∀ request : TangentSplitRequest edges L sigma flow,
        3 * (sigma / L) / 4 ≤
            tangentUpdate (tangentSplitRequests edges L sigma flow)
              (fun request ↦ source request.1.1)
              (fun request ↦ target request.1.1) multiplier
              (fun request ↦ flow request.1.1 /
                tangentRequestCount L sigma (flow request.1.1)) x
              (target request.1.1 * multiplier request) ∧
          tangentUpdate (tangentSplitRequests edges L sigma flow)
              (fun request ↦ source request.1.1)
              (fun request ↦ target request.1.1) multiplier
              (fun request ↦ flow request.1.1 /
                tangentRequestCount L sigma (flow request.1.1)) x
              (target request.1.1 * multiplier request) ≤
            1 - 3 * (sigma / L) / 4 := by
  have hresult := tangentSplitUpdate_feasible_and_margin edges source target
    flow hflow hL hsigma multiplier x A hdistinct
    (by simpa only [tangentSplitRequestSource, tangentSplitRequestEdge] using
      hsourceSlack)
    (by simpa only [tangentSplitRequestTarget, tangentSplitRequestEdge] using
      htargetSlack)
    hglobal
  simpa only [tangentSplitRequestSource, tangentSplitRequestTarget,
    tangentSplitRequestEdge, tangentSplitRequestWeight,
    tangentRequestPieceMass] using hresult

end

end Erdos390.WholePaper
