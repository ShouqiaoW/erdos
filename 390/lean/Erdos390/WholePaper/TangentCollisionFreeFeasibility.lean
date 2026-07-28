import Erdos390.WholePaper.TangentRequestSplitting

/-!
# Collision-free tangent updates and coordinate feasibility

The probabilistic part of the tangent construction is used only to produce
requests whose numerical endpoints are all distinct.  This file records the
deterministic consequence for the literal finite update: a used coordinate
receives exactly one signed request, and the paper's endpoint slack gives the
claimed post-move margin.

Importantly, `TangentEndpointsDistinct` below is an explicit input, not a
formalization of the paper's common-list estimate or local-lemma argument.
The final theorem connects that visible input to the actual split requests;
it does not claim to construct collision-free multipliers.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- All source endpoints are distinct, all target endpoints are distinct,
and no source endpoint equals any target endpoint. -/
structure TangentEndpointsDistinct {ι : Type*} (requests : Finset ι)
    (source target multiplier : ι → ℕ) : Prop where
  source_injective : Set.InjOn
    (fun e ↦ source e * multiplier e) requests
  target_injective : Set.InjOn
    (fun e ↦ target e * multiplier e) requests
  source_ne_target : ∀ e ∈ requests, ∀ f ∈ requests,
    source e * multiplier e ≠ target f * multiplier f

theorem tangentDelta_eq_weight_of_source
    {ι : Type*} {requests : Finset ι}
    {source target multiplier : ι → ℕ} {weight : ι → ℝ}
    (hdistinct : TangentEndpointsDistinct requests source target multiplier)
    {e : ι} (he : e ∈ requests) :
    tangentDelta requests source target multiplier weight
        (source e * multiplier e) = weight e := by
  classical
  rw [tangentDelta, Finset.sum_eq_single e]
  · have hcross := hdistinct.source_ne_target e he e he
    have hsourceTarget : source e ≠ target e := by
      intro heq
      apply hcross
      rw [heq]
    have hmultiplier : multiplier e ≠ 0 := by
      intro hm
      apply hcross
      simp [hm]
    simp [tangentPointMass, hsourceTarget, hmultiplier]
  · intro f hf hfe
    have hsourceNe :
        source e * multiplier e ≠ source f * multiplier f := by
      intro hEq
      have hef : e = f := hdistinct.source_injective he hf hEq
      exact hfe hef.symm
    have htargetNe :
        source e * multiplier e ≠ target f * multiplier f :=
      hdistinct.source_ne_target e he f hf
    simp [tangentPointMass, hsourceNe, htargetNe]
  · exact fun hnot ↦ (hnot he).elim

theorem tangentDelta_eq_neg_weight_of_target
    {ι : Type*} {requests : Finset ι}
    {source target multiplier : ι → ℕ} {weight : ι → ℝ}
    (hdistinct : TangentEndpointsDistinct requests source target multiplier)
    {e : ι} (he : e ∈ requests) :
    tangentDelta requests source target multiplier weight
        (target e * multiplier e) = -weight e := by
  classical
  rw [tangentDelta, Finset.sum_eq_single e]
  · have hcross := hdistinct.source_ne_target e he e he
    have htargetSource : target e ≠ source e := by
      intro heq
      apply hcross
      rw [heq]
    have hmultiplier : multiplier e ≠ 0 := by
      intro hm
      apply hcross
      simp [hm]
    simp [tangentPointMass, htargetSource, hmultiplier]
  · intro f hf hfe
    have hsourceNe :
        target e * multiplier e ≠ source f * multiplier f :=
      (hdistinct.source_ne_target f hf e he).symm
    have htargetNe :
        target e * multiplier e ≠ target f * multiplier f := by
      intro hEq
      have hef : e = f := hdistinct.target_injective he hf hEq
      exact hfe hef.symm
    simp [tangentPointMass, hsourceNe, htargetNe]
  · exact fun hnot ↦ (hnot he).elim

theorem tangentDelta_eq_zero_of_unused
    {ι : Type*} {requests : Finset ι}
    {source target multiplier : ι → ℕ} {weight : ι → ℝ}
    {a : ℕ}
    (hsource : ∀ e ∈ requests, a ≠ source e * multiplier e)
    (htarget : ∀ e ∈ requests, a ≠ target e * multiplier e) :
    tangentDelta requests source target multiplier weight a = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  simp [tangentPointMass, hsource e he, htarget e he]

theorem tangentUpdate_eq_add_weight_of_source
    {ι : Type*} {requests : Finset ι}
    {source target multiplier : ι → ℕ} {weight : ι → ℝ}
    {x : ℕ → ℝ}
    (hdistinct : TangentEndpointsDistinct requests source target multiplier)
    {e : ι} (he : e ∈ requests) :
    tangentUpdate requests source target multiplier weight x
        (source e * multiplier e) =
      x (source e * multiplier e) + weight e := by
  rw [tangentUpdate, tangentDelta_eq_weight_of_source hdistinct he]

theorem tangentUpdate_eq_sub_weight_of_target
    {ι : Type*} {requests : Finset ι}
    {source target multiplier : ι → ℕ} {weight : ι → ℝ}
    {x : ℕ → ℝ}
    (hdistinct : TangentEndpointsDistinct requests source target multiplier)
    {e : ι} (he : e ∈ requests) :
    tangentUpdate requests source target multiplier weight x
        (target e * multiplier e) =
      x (target e * multiplier e) - weight e := by
  rw [tangentUpdate, tangentDelta_eq_neg_weight_of_target hdistinct he]
  ring

/-- Collision-free requests of size at most `δ` preserve the global box
whenever every used endpoint starts with `δ` two-sided slack. -/
theorem tangentUpdate_mem_unitInterval
    {ι : Type*} {requests : Finset ι}
    {source target multiplier : ι → ℕ} {weight : ι → ℝ}
    {x : ℕ → ℝ} {A : Finset ℕ} {δ : ℝ}
    (hdistinct : TangentEndpointsDistinct requests source target multiplier)
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
      tangentUpdate requests source target multiplier weight x a ∈
        Set.Icc (0 : ℝ) 1 := by
  intro a ha
  by_cases hs : ∃ e ∈ requests, a = source e * multiplier e
  · obtain ⟨e, he, rfl⟩ := hs
    rw [tangentUpdate_eq_add_weight_of_source hdistinct he]
    have hw := hweight e he
    have hx := hsourceSlack e he
    constructor <;> linarith
  · have hsAll : ∀ e ∈ requests, a ≠ source e * multiplier e := by
      intro e he hEq
      exact hs ⟨e, he, hEq⟩
    by_cases ht : ∃ e ∈ requests, a = target e * multiplier e
    · obtain ⟨e, he, rfl⟩ := ht
      rw [tangentUpdate_eq_sub_weight_of_target hdistinct he]
      have hw := hweight e he
      have hx := htargetSlack e he
      constructor <;> linarith
    · have htAll : ∀ e ∈ requests, a ≠ target e * multiplier e := by
        intro e he hEq
        exact ht ⟨e, he, hEq⟩
      rw [tangentUpdate, tangentDelta_eq_zero_of_unused hsAll htAll, add_zero]
      exact hglobal a ha

/-- Paper (9.38): if every request has size at most one quarter of the
available slack, every used endpoint retains three quarters of that slack. -/
theorem tangentUpdate_source_margin
    {ι : Type*} {requests : Finset ι}
    {source target multiplier : ι → ℕ} {weight : ι → ℝ}
    {x : ℕ → ℝ} {δ : ℝ}
    (hdistinct : TangentEndpointsDistinct requests source target multiplier)
    (hδ : 0 ≤ δ)
    (hweight : ∀ e ∈ requests, 0 ≤ weight e ∧ weight e ≤ δ / 4)
    (hsourceSlack : ∀ e ∈ requests,
      δ ≤ x (source e * multiplier e) ∧
        x (source e * multiplier e) ≤ 1 - δ)
    {e : ι} (he : e ∈ requests) :
    3 * δ / 4 ≤
        tangentUpdate requests source target multiplier weight x
          (source e * multiplier e) ∧
      tangentUpdate requests source target multiplier weight x
          (source e * multiplier e) ≤ 1 - 3 * δ / 4 := by
  rw [tangentUpdate_eq_add_weight_of_source hdistinct he]
  have hw := hweight e he
  have hx := hsourceSlack e he
  constructor <;> linarith

theorem tangentUpdate_target_margin
    {ι : Type*} {requests : Finset ι}
    {source target multiplier : ι → ℕ} {weight : ι → ℝ}
    {x : ℕ → ℝ} {δ : ℝ}
    (hdistinct : TangentEndpointsDistinct requests source target multiplier)
    (hδ : 0 ≤ δ)
    (hweight : ∀ e ∈ requests, 0 ≤ weight e ∧ weight e ≤ δ / 4)
    (htargetSlack : ∀ e ∈ requests,
      δ ≤ x (target e * multiplier e) ∧
        x (target e * multiplier e) ≤ 1 - δ)
    {e : ι} (he : e ∈ requests) :
    3 * δ / 4 ≤
        tangentUpdate requests source target multiplier weight x
          (target e * multiplier e) ∧
      tangentUpdate requests source target multiplier weight x
          (target e * multiplier e) ≤ 1 - 3 * δ / 4 := by
  rw [tangentUpdate_eq_sub_weight_of_target hdistinct he]
  have hw := hweight e he
  have hx := htargetSlack e he
  constructor <;> linarith

/-- Deterministic terminal for the two formalized tangent layers.  The
literal requests are the `Fin` pieces of the strictly positive support flow,
their
quarter-slack bound is derived from the splitting formula, and endpoint
distinctness remains the explicit output required from the still-separate
common-list/LLL construction. -/
theorem tangentSplitUpdate_feasible_and_margin
    {E : Type*} [DecidableEq E] (edges : Finset E)
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
      sigma / L ≤ x (tangentSplitRequestSource source request *
          multiplier request) ∧
        x (tangentSplitRequestSource source request * multiplier request) ≤
          1 - sigma / L)
    (htargetSlack : ∀ request : TangentSplitRequest edges L sigma flow,
      sigma / L ≤ x (tangentSplitRequestTarget target request *
          multiplier request) ∧
        x (tangentSplitRequestTarget target request * multiplier request) ≤
          1 - sigma / L)
    (hglobal : ∀ a ∈ A, x a ∈ Set.Icc (0 : ℝ) 1) :
    (∀ a ∈ A,
      tangentUpdate (tangentSplitRequests edges L sigma flow)
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) multiplier
          tangentSplitRequestWeight x a ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ request : TangentSplitRequest edges L sigma flow,
        3 * (sigma / L) / 4 ≤
            tangentUpdate (tangentSplitRequests edges L sigma flow)
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target) multiplier
              tangentSplitRequestWeight x
              (tangentSplitRequestSource source request * multiplier request) ∧
          tangentUpdate (tangentSplitRequests edges L sigma flow)
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target) multiplier
              tangentSplitRequestWeight x
              (tangentSplitRequestSource source request * multiplier request) ≤
            1 - 3 * (sigma / L) / 4) ∧
      ∀ request : TangentSplitRequest edges L sigma flow,
        3 * (sigma / L) / 4 ≤
            tangentUpdate (tangentSplitRequests edges L sigma flow)
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target) multiplier
              tangentSplitRequestWeight x
              (tangentSplitRequestTarget target request * multiplier request) ∧
          tangentUpdate (tangentSplitRequests edges L sigma flow)
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target) multiplier
              tangentSplitRequestWeight x
              (tangentSplitRequestTarget target request * multiplier request) ≤
            1 - 3 * (sigma / L) / 4 := by
  have hflowNonneg : ∀ e ∈ edges, 0 ≤ flow e :=
    fun e he ↦ (hflow e he).le
  have hdelta : 0 ≤ sigma / L := div_nonneg hsigma.le hL.le
  have hweightQuarter : ∀ request : TangentSplitRequest edges L sigma flow,
      0 ≤ tangentSplitRequestWeight request ∧
        tangentSplitRequestWeight request ≤ (sigma / L) / 4 :=
    fun request ↦
      tangentSplitRequestWeight_mem_slackQuarter hflowNonneg hL hsigma request
  have hweightFull : ∀ request : TangentSplitRequest edges L sigma flow,
      0 ≤ tangentSplitRequestWeight request ∧
        tangentSplitRequestWeight request ≤ sigma / L := by
    intro request
    have hw := hweightQuarter request
    exact ⟨hw.1, by linarith⟩
  refine ⟨tangentUpdate_mem_unitInterval hdistinct hdelta
      (fun request _hrequest ↦ hweightFull request)
      (fun request _hrequest ↦ hsourceSlack request)
      (fun request _hrequest ↦ htargetSlack request) hglobal, ?_, ?_⟩
  · intro request
    exact tangentUpdate_source_margin hdistinct hdelta
      (fun request _hrequest ↦ hweightQuarter request)
      (fun request _hrequest ↦ hsourceSlack request)
      (by simp only [tangentSplitRequests, Finset.mem_univ])
  · intro request
    exact tangentUpdate_target_margin hdistinct hdelta
      (fun request _hrequest ↦ hweightQuarter request)
      (fun request _hrequest ↦ htargetSlack request)
      (by simp only [tangentSplitRequests, Finset.mem_univ])

end

end Erdos390.WholePaper
