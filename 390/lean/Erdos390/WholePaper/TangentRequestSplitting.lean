import Erdos390.WholePaper.TangentFlowAlgebra

/-!
# Literal finite splitting of tangent-flow requests

This file formalizes only the algebra in the paper's request splitting.
It assumes concrete nonnegative edge masses and forms explicit `Fin k`
families of equal pieces.  It contains no flow-existence, list-capacity,
or collision-avoidance assertion.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Number of requests used to split a nonnegative edge mass. -/
def tangentRequestCount (L sigma f : ℝ) : ℕ :=
  max 1 (Nat.ceil (4 * L * f / sigma))

/-- Common mass of every request obtained from the edge. -/
def tangentRequestPieceMass (L sigma f : ℝ) : ℝ :=
  f / tangentRequestCount L sigma f

@[simp] theorem tangentRequestCount_zero (L sigma : ℝ) :
    tangentRequestCount L sigma 0 = 1 := by
  simp [tangentRequestCount]

theorem one_le_tangentRequestCount (L sigma f : ℝ) :
    1 ≤ tangentRequestCount L sigma f := by
  exact le_max_left 1 (Nat.ceil (4 * L * f / sigma))

theorem tangentRequestCount_pos (L sigma f : ℝ) :
    0 < tangentRequestCount L sigma f := by
  exact lt_of_lt_of_le Nat.zero_lt_one (one_le_tangentRequestCount L sigma f)

/-- The ceiling definition dominates the normalized edge mass. -/
theorem normalizedMass_le_tangentRequestCount
    (L sigma f : ℝ) :
    4 * L * f / sigma ≤ (tangentRequestCount L sigma f : ℝ) := by
  have hceil : 4 * L * f / sigma ≤
      (Nat.ceil (4 * L * f / sigma) : ℝ) :=
    Nat.le_ceil (4 * L * f / sigma)
  have hceilMax : Nat.ceil (4 * L * f / sigma) ≤
      tangentRequestCount L sigma f := by
    exact le_max_right 1 (Nat.ceil (4 * L * f / sigma))
  exact hceil.trans (by exact_mod_cast hceilMax)

/-- Every equal request piece has the paper's size bound. -/
theorem tangentRequestPieceMass_le
    {L sigma f : ℝ} (_hf : 0 ≤ f) (hL : 0 < L) (hsigma : 0 < sigma) :
    tangentRequestPieceMass L sigma f ≤ sigma / (4 * L) := by
  have hk : 0 < (tangentRequestCount L sigma f : ℝ) := by
    exact_mod_cast tangentRequestCount_pos L sigma f
  have hfourL : 0 < 4 * L := by positivity
  have hnormalized := normalizedMass_le_tangentRequestCount L sigma f
  have hmul : 4 * L * f ≤
      (tangentRequestCount L sigma f : ℝ) * sigma :=
    (div_le_iff₀ hsigma).1 hnormalized
  unfold tangentRequestPieceMass
  apply (div_le_div_iff₀ hk hfourL).2
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul

/-- Equivalent real edge-load form of the piece-size bound. -/
theorem tangentMass_le_count_mul
    {L sigma f : ℝ} (_hf : 0 ≤ f) (hL : 0 < L) (hsigma : 0 < sigma) :
    f ≤ sigma * tangentRequestCount L sigma f / (4 * L) := by
  have hfourL : 0 < 4 * L := by positivity
  have hnormalized := normalizedMass_le_tangentRequestCount L sigma f
  have hmul : 4 * L * f ≤
      (tangentRequestCount L sigma f : ℝ) * sigma :=
    (div_le_iff₀ hsigma).1 hnormalized
  apply (le_div_iff₀ hfourL).2
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul

/-- The request count is at most normalized mass plus one.  Equality can
occur at `f=0`, so the globally valid form is non-strict. -/
theorem cast_tangentRequestCount_le
    {L sigma f : ℝ} (hf : 0 ≤ f) (hL : 0 < L) (hsigma : 0 < sigma) :
    (tangentRequestCount L sigma f : ℝ) ≤
      4 * L * f / sigma + 1 := by
  have hnormalized : 0 ≤ 4 * L * f / sigma := by positivity
  have hceil : (Nat.ceil (4 * L * f / sigma) : ℝ) ≤
      4 * L * f / sigma + 1 :=
    (Nat.ceil_lt_add_one hnormalized).le
  have hone : (1 : ℝ) ≤ 4 * L * f / sigma + 1 := by
    linarith
  unfold tangentRequestCount
  push_cast
  exact max_le hone hceil

/-- For a genuinely positive edge mass the count bound is strict. -/
theorem cast_tangentRequestCount_lt
    {L sigma f : ℝ} (hf : 0 < f) (hL : 0 < L) (hsigma : 0 < sigma) :
    (tangentRequestCount L sigma f : ℝ) <
      4 * L * f / sigma + 1 := by
  have hnormalized : 0 < 4 * L * f / sigma := by positivity
  have hceilPos : 1 ≤ Nat.ceil (4 * L * f / sigma) := by
    have := Nat.ceil_pos.mpr hnormalized
    omega
  rw [tangentRequestCount, max_eq_right hceilPos]
  exact Nat.ceil_lt_add_one hnormalized.le

/-- The `Fin k` equal pieces of one edge sum exactly to its original mass. -/
theorem sum_tangentRequestPieceMass
    (L sigma f : ℝ) :
    (∑ _i : Fin (tangentRequestCount L sigma f),
        tangentRequestPieceMass L sigma f) = f := by
  have hk : (tangentRequestCount L sigma f : ℝ) ≠ 0 := by
    exact_mod_cast (tangentRequestCount_pos L sigma f).ne'
  simp only [tangentRequestPieceMass, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Actual request indices obtained by splitting every edge in a finite set.
For the literal paper support, the caller should take `edges` to consist
exactly of the strictly positive-flow edges; otherwise a zero-flow edge
contributes one harmless zero-mass request because of the totalized `max 1`
definition. -/
abbrev TangentSplitRequest {E : Type*} (edges : Finset E)
    (L sigma : ℝ) (flow : E → ℝ) :=
  Σ e : ↑edges, Fin (tangentRequestCount L sigma (flow e.1))

/-- Underlying directed support edge of a literal split request. -/
def tangentSplitRequestEdge {E : Type*} {edges : Finset E}
    {L sigma : ℝ} {flow : E → ℝ}
    (request : TangentSplitRequest edges L sigma flow) : E :=
  request.1.1

/-- Lift an edge-source label to every request split from that edge. -/
def tangentSplitRequestSource {E P : Type*} {edges : Finset E}
    {L sigma : ℝ} {flow : E → ℝ} (source : E → P) :
    TangentSplitRequest edges L sigma flow → P :=
  fun request ↦ source (tangentSplitRequestEdge request)

/-- Lift an edge-target label to every request split from that edge. -/
def tangentSplitRequestTarget {E P : Type*} {edges : Finset E}
    {L sigma : ℝ} {flow : E → ℝ} (target : E → P) :
    TangentSplitRequest edges L sigma flow → P :=
  fun request ↦ target (tangentSplitRequestEdge request)

/-- The actual finite set of all split requests. -/
def tangentSplitRequests {E : Type*} [DecidableEq E] (edges : Finset E)
    (L sigma : ℝ) (flow : E → ℝ) :
    Finset (TangentSplitRequest edges L sigma flow) :=
  Finset.univ

/-- Weight of one literal split request. -/
def tangentSplitRequestWeight {E : Type*} {edges : Finset E}
    {L sigma : ℝ} {flow : E → ℝ}
    (_request : TangentSplitRequest edges L sigma flow) : ℝ :=
  tangentRequestPieceMass L sigma (flow _request.1.1)

theorem tangentSplitRequestWeight_nonneg
    {E : Type*} {edges : Finset E} {L sigma : ℝ} {flow : E → ℝ}
    (hflow : ∀ e ∈ edges, 0 ≤ flow e)
    (request : TangentSplitRequest edges L sigma flow) :
    0 ≤ tangentSplitRequestWeight request := by
  unfold tangentSplitRequestWeight tangentRequestPieceMass
  exact div_nonneg (hflow request.1.1 request.1.2) (by positivity)

theorem tangentSplitRequestWeight_pos
    {E : Type*} {edges : Finset E} {L sigma : ℝ} {flow : E → ℝ}
    (hflow : ∀ e ∈ edges, 0 < flow e)
    (request : TangentSplitRequest edges L sigma flow) :
    0 < tangentSplitRequestWeight request := by
  unfold tangentSplitRequestWeight tangentRequestPieceMass
  exact div_pos (hflow request.1.1 request.1.2) (by
    exact_mod_cast tangentRequestCount_pos L sigma (flow request.1.1))

theorem tangentSplitRequestWeight_le
    {E : Type*} {edges : Finset E} {L sigma : ℝ} {flow : E → ℝ}
    (hflow : ∀ e ∈ edges, 0 ≤ flow e)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (request : TangentSplitRequest edges L sigma flow) :
    tangentSplitRequestWeight request ≤ sigma / (4 * L) := by
  exact tangentRequestPieceMass_le
    (hflow request.1.1 request.1.2) hL hsigma

/-- Paper normalization of the preceding bound: with endpoint slack
`sigma / L`, every split request uses at most one quarter of that slack. -/
theorem tangentSplitRequestWeight_mem_slackQuarter
    {E : Type*} {edges : Finset E} {L sigma : ℝ} {flow : E → ℝ}
    (hflow : ∀ e ∈ edges, 0 ≤ flow e)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (request : TangentSplitRequest edges L sigma flow) :
    0 ≤ tangentSplitRequestWeight request ∧
      tangentSplitRequestWeight request ≤ (sigma / L) / 4 := by
  refine ⟨tangentSplitRequestWeight_nonneg hflow request, ?_⟩
  calc
    tangentSplitRequestWeight request ≤ sigma / (4 * L) :=
      tangentSplitRequestWeight_le hflow hL hsigma request
    _ = (sigma / L) / 4 := by
      field_simp [hL.ne']

/-- Total number of split requests, as the literal sum of edge counts. -/
def tangentRequestTotal {E : Type*} (edges : Finset E)
    (L sigma : ℝ) (flow : E → ℝ) : ℕ :=
  ∑ e ∈ edges, tangentRequestCount L sigma (flow e)

theorem card_tangentSplitRequest
    {E : Type*} (edges : Finset E) (L sigma : ℝ) (flow : E → ℝ) :
    Fintype.card (TangentSplitRequest edges L sigma flow) =
      tangentRequestTotal edges L sigma flow := by
  classical
  unfold tangentRequestTotal
  simp only [TangentSplitRequest, Fintype.card_sigma, Fintype.card_fin]
  simpa using Finset.sum_attach edges
    (fun e ↦ tangentRequestCount L sigma (flow e))

@[simp] theorem card_tangentSplitRequests
    {E : Type*} [DecidableEq E] (edges : Finset E)
    (L sigma : ℝ) (flow : E → ℝ) :
    (tangentSplitRequests edges L sigma flow).card =
      tangentRequestTotal edges L sigma flow := by
  rw [tangentSplitRequests, Finset.card_univ]
  exact card_tangentSplitRequest edges L sigma flow

/-- Splitting all edges preserves their total real mass exactly. -/
theorem sum_tangentSplitRequestWeight
    {E : Type*} (edges : Finset E) (L sigma : ℝ) (flow : E → ℝ) :
    (∑ request : TangentSplitRequest edges L sigma flow,
        tangentSplitRequestWeight request) =
      ∑ e ∈ edges, flow e := by
  classical
  simp only [TangentSplitRequest, tangentSplitRequestWeight,
    Fintype.sum_sigma]
  calc
    (∑ e : ↑edges,
        ∑ _i : Fin (tangentRequestCount L sigma (flow e.1)),
          tangentRequestPieceMass L sigma (flow e.1)) =
        ∑ e : ↑edges, flow e.1 := by
      apply Finset.sum_congr rfl
      intro e _he
      exact sum_tangentRequestPieceMass L sigma (flow e.1)
    _ = ∑ e ∈ edges, flow e := by
      simpa using Finset.sum_attach edges flow

/-- Request splitting preserves the complete directed edge boundary when
tested against any label function.  This is the exact bridge from the
paper's edge flow to the request family consumed by `tangentUpdate`. -/
theorem sum_tangentSplitRequestWeight_mul_sub
    {E P : Type*} (edges : Finset E) (source target : E → P)
    (L sigma : ℝ) (flow : E → ℝ) (value : P → ℝ) :
    (∑ request : TangentSplitRequest edges L sigma flow,
        tangentSplitRequestWeight request *
          (value (tangentSplitRequestSource source request) -
            value (tangentSplitRequestTarget target request))) =
      ∑ e ∈ edges, flow e * (value (source e) - value (target e)) := by
  classical
  simp only [TangentSplitRequest, tangentSplitRequestWeight,
    tangentSplitRequestSource, tangentSplitRequestTarget,
    tangentSplitRequestEdge, Fintype.sum_sigma]
  calc
    (∑ e : ↑edges,
        ∑ _i : Fin (tangentRequestCount L sigma (flow e.1)),
          tangentRequestPieceMass L sigma (flow e.1) *
            (value (source e.1) - value (target e.1))) =
      ∑ e : ↑edges,
        flow e.1 * (value (source e.1) - value (target e.1)) := by
      apply Finset.sum_congr rfl
      intro e _he
      rw [← Finset.sum_mul, sum_tangentRequestPieceMass]
    _ = ∑ e ∈ edges,
        flow e * (value (source e) - value (target e)) := by
      simpa using Finset.sum_attach edges
        (fun e ↦ flow e * (value (source e) - value (target e)))

/-- The literal split request family, with any subsequently chosen common
multiplier for each request, produces exactly the valuation boundary of the
original edge flow.  Multiplier valuations cancel through
`tangentUpdate_valuation`; no coprimality hypothesis is present. -/
theorem tangentSplitUpdate_valuation
    {E : Type*} [DecidableEq E] (edges : Finset E)
    (source target : E → ℕ) (L sigma : ℝ) (flow : E → ℝ)
    (multiplier : TangentSplitRequest edges L sigma flow → ℕ)
    (x : ℕ → ℝ) (A : Finset ℕ) (p : ℕ)
    (hsourceMem : ∀ request : TangentSplitRequest edges L sigma flow,
      tangentSplitRequestSource source request * multiplier request ∈ A)
    (htargetMem : ∀ request : TangentSplitRequest edges L sigma flow,
      tangentSplitRequestTarget target request * multiplier request ∈ A)
    (hsourcePos : ∀ request : TangentSplitRequest edges L sigma flow,
      tangentSplitRequestSource source request ≠ 0)
    (htargetPos : ∀ request : TangentSplitRequest edges L sigma flow,
      tangentSplitRequestTarget target request ≠ 0)
    (hmultiplierPos : ∀ request : TangentSplitRequest edges L sigma flow,
      multiplier request ≠ 0) :
    ∑ a ∈ A,
        tangentUpdate (tangentSplitRequests edges L sigma flow)
            (tangentSplitRequestSource source)
            (tangentSplitRequestTarget target) multiplier
            tangentSplitRequestWeight x a * (a.factorization p : ℝ) =
      (∑ a ∈ A, x a * (a.factorization p : ℝ)) +
        ∑ e ∈ edges, flow e *
          ((source e).factorization p - (target e).factorization p : ℝ) := by
  rw [tangentUpdate_valuation
    (tangentSplitRequests edges L sigma flow)
    (tangentSplitRequestSource source) (tangentSplitRequestTarget target)
    multiplier tangentSplitRequestWeight x A p
    (fun request _hrequest ↦ hsourceMem request)
    (fun request _hrequest ↦ htargetMem request)
    (fun request _hrequest ↦ hsourcePos request)
    (fun request _hrequest ↦ htargetPos request)
    (fun request _hrequest ↦ hmultiplierPos request)]
  apply congrArg (fun z : ℝ ↦
    (∑ a ∈ A, x a * (a.factorization p : ℝ)) + z)
  simpa only [tangentSplitRequests] using
    sum_tangentSplitRequestWeight_mul_sub edges source target L sigma flow
      (fun q ↦ (q.factorization p : ℝ))

/-- Literal finite form of the total request-count estimate. -/
theorem cast_tangentRequestTotal_le
    {E : Type*} (edges : Finset E) {L sigma : ℝ} (flow : E → ℝ)
    (hflow : ∀ e ∈ edges, 0 ≤ flow e)
    (hL : 0 < L) (hsigma : 0 < sigma) :
    (tangentRequestTotal edges L sigma flow : ℝ) ≤
      (4 * L / sigma) * (∑ e ∈ edges, flow e) + edges.card := by
  classical
  unfold tangentRequestTotal
  push_cast
  calc
    (∑ e ∈ edges, (tangentRequestCount L sigma (flow e) : ℝ)) ≤
        ∑ e ∈ edges, (4 * L * flow e / sigma + 1) := by
      apply Finset.sum_le_sum
      intro e he
      exact cast_tangentRequestCount_le (hflow e he) hL hsigma
    _ = (∑ e ∈ edges, 4 * L * flow e / sigma) + edges.card := by
      rw [Finset.sum_add_distrib]
      simp
    _ = (4 * L / sigma) * (∑ e ∈ edges, flow e) + edges.card := by
      apply congrArg (fun z : ℝ ↦ z + (edges.card : ℝ))
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _he
      ring

/-- The concrete support edges incident to one label. -/
def tangentIncidentEdges {E P : Type*} [DecidableEq E] [DecidableEq P]
    (edges : Finset E) (source target : E → P) (p : P) : Finset E :=
  edges.filter fun e ↦ source e = p ∨ target e = p

def tangentIncidentRequestCount
    {E P : Type*} [DecidableEq E] [DecidableEq P]
    (edges : Finset E) (source target : E → P)
    (L sigma : ℝ) (flow : E → ℝ) (p : P) : ℕ :=
  tangentRequestTotal (tangentIncidentEdges edges source target p)
    L sigma flow

def tangentIncidentFlowMass
    {E P : Type*} [DecidableEq E] [DecidableEq P]
    (edges : Finset E) (source target : E → P)
    (flow : E → ℝ) (p : P) : ℝ :=
  ∑ e ∈ tangentIncidentEdges edges source target p, flow e

def tangentSupportDegree
    {E P : Type*} [DecidableEq E] [DecidableEq P]
    (edges : Finset E) (source target : E → P) (p : P) : ℕ :=
  (tangentIncidentEdges edges source target p).card

/-- Per-label request count bounded by normalized incident mass plus the
literal support degree. -/
theorem cast_tangentIncidentRequestCount_le
    {E P : Type*} [DecidableEq E] [DecidableEq P]
    (edges : Finset E) (source target : E → P)
    {L sigma : ℝ} (flow : E → ℝ)
    (hflow : ∀ e ∈ edges, 0 ≤ flow e)
    (hL : 0 < L) (hsigma : 0 < sigma) (p : P) :
    (tangentIncidentRequestCount edges source target L sigma flow p : ℝ) ≤
      (4 * L / sigma) *
          tangentIncidentFlowMass edges source target flow p +
        tangentSupportDegree edges source target p := by
  unfold tangentIncidentRequestCount tangentIncidentFlowMass
    tangentSupportDegree
  apply cast_tangentRequestTotal_le
  · intro e he
    exact hflow e (Finset.mem_filter.mp he).1
  · exact hL
  · exact hsigma

end

end Erdos390.WholePaper
