import Erdos390.WholePaper.TangentCollisionLocalLemma

/-! # Expanded statement audit for the tangent collision experiment -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! The probability space is the genuine product of independent uniform
choices from the request-indexed finite lists. -/
example {Request : Type*} [Fintype Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty) :
    iIndepFun
      (fun request
          (outcome : ∀ r, {a : ℕ // a ∈ lists r}) ↦ outcome request)
      (tangentUniformMultiplierMeasure lists hlist) :=
  tangentUniformMultiplierCoordinates_iIndep lists hlist

/-! The dependency factorization is obtained from disjoint request
coordinates, rather than supplied as a local-lemma hypothesis. -/
example {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request)
    (collisions : Finset (TangentCollisionIndex Request))
    (hcollision : collision ∉ collisions)
    (hdisjoint : Disjoint collisions
      (tangentCollisionNeighbors collision)) :
    let μ := tangentUniformMultiplierMeasure lists hlist
    μ.real (tangentCollisionEvent source target collision ∩
        (⋂ other ∈ collisions,
          (tangentCollisionEvent source target other)ᶜ)) =
      μ.real (tangentCollisionEvent source target collision) *
        μ.real (⋂ other ∈ collisions,
          (tangentCollisionEvent source target other)ᶜ) := by
  simpa only [avoidEvents] using
    tangentCollisionEvent_independent_of_nonNeighbors
      lists hlist source target collision collisions
        hcollision hdisjoint

/-! Literal factor-two bookkeeping: two incident request sums of size
`1/8` cover every dependency neighborhood. -/
example {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ)
    (hrequestMass : ∀ request,
      tangentRequestCollisionMass lists hlist source target request ≤ 1 / 8)
    (collision : TangentCollisionIndex Request) :
    ∑ other ∈ tangentCollisionNeighbors collision,
        (tangentUniformMultiplierMeasure lists hlist).real
          (tangentCollisionEvent source target other) ≤ 1 / 4 := by
  exact tangentCollisionNeighborhoodMass_le_quarter_of_requestMass
    lists hlist source target hrequestMass collision

/-! The local lemma now constructs the collision-free outcome. -/
example {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ)
    (hrequestMass : ∀ request,
      tangentRequestCollisionMass lists hlist source target request ≤ 1 / 8) :
    ∃ outcome : ∀ request, {a : ℕ // a ∈ lists request},
      ∀ collision : {support : Finset Request // support.card = 2},
        outcome ∉ tangentCollisionEvent source target collision := by
  exact tangentCollisionFreeOutcome_of_requestMass
    lists hlist source target hrequestMass

/-! Specialization to the literal clean lists returns numerical multipliers,
their list-membership certificates, and the endpoint-distinctness structure
required by the deterministic feasibility theorem. -/
example {Request : Type*} [Fintype Request] [DecidableEq Request]
    (n K h Phead X0 y : ℕ) (source target : Request → ℕ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (hsourceTarget : ∀ request, source request ≠ target request)
    (hlist : ∀ request,
      (tangentCleanCommonMultiplierList
        n K h Phead X0 y
          (max (source request) (target request))
          (min (source request) (target request))
          dedicatedRows numericalGuards).Nonempty)
    (hrequestMass : ∀ request,
      tangentRequestCollisionMass
        (fun r ↦ tangentCleanCommonMultiplierList
          n K h Phead X0 y
            (max (source r) (target r))
            (min (source r) (target r))
            dedicatedRows numericalGuards)
        hlist source target request ≤ 1 / 8) :
    ∃ multiplier : Request → ℕ,
      (∀ request,
        multiplier request ∈ tangentCleanCommonMultiplierList
          n K h Phead X0 y
            (max (source request) (target request))
            (min (source request) (target request))
            dedicatedRows numericalGuards) ∧
      TangentEndpointsDistinct Finset.univ source target multiplier := by
  exact tangentCleanCommonMultiplier_collisionFree_of_requestMass
    n K h Phead X0 y source target dedicatedRows numericalGuards
      hsourceTarget hlist hrequestMass

/-! The same output is aligned with the literal split-request finset used by
the feasibility terminal. -/
example {E : Type*} [DecidableEq E] (edges : Finset E)
    (source target : E → ℕ) (L sigma : ℝ) (flow : E → ℝ)
    (n K h Phead X0 y : ℕ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (hsourceTarget : ∀ request : TangentSplitRequest edges L sigma flow,
      source request.1.1 ≠ target request.1.1)
    (hlist : ∀ request : TangentSplitRequest edges L sigma flow,
      (tangentSplitCleanMultiplierLists edges source target L sigma flow
        n K h Phead X0 y dedicatedRows numericalGuards request).Nonempty)
    (hrequestMass : ∀ request : TangentSplitRequest edges L sigma flow,
      tangentRequestCollisionMass
        (tangentSplitCleanMultiplierLists edges source target L sigma flow
          n K h Phead X0 y dedicatedRows numericalGuards)
        hlist (fun r ↦ source r.1.1) (fun r ↦ target r.1.1) request ≤ 1 / 8) :
    ∃ multiplier : TangentSplitRequest edges L sigma flow → ℕ,
      (∀ request,
        multiplier request ∈
          tangentSplitCleanMultiplierLists edges source target L sigma flow
            n K h Phead X0 y dedicatedRows numericalGuards request) ∧
      TangentEndpointsDistinct
        (tangentSplitRequests edges L sigma flow)
        (fun request ↦ source request.1.1)
        (fun request ↦ target request.1.1) multiplier := by
  simpa only [tangentSplitRequestSource, tangentSplitRequestTarget,
    tangentSplitRequestEdge] using
    tangentSplitEndpointsDistinct_of_cleanRequestMass
      edges source target L sigma flow n K h Phead X0 y
        dedicatedRows numericalGuards hsourceTarget hlist hrequestMass

end

end Erdos390.WholePaper
