import Erdos390.WholePaper.TangentCollisionCounting

/-! # Expanded statement audit for tangent collision counting -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! The implementation-level finite uniform law has the expected cardinality
formula without exposing a particular `Fintype` instance. -/
example (α : Type*) [MeasurableSpace α] [MeasurableSingletonClass α]
    [Finite α] (hα : Nonempty α) (s : Set α) (hs : MeasurableSet s) :
    tangentFiniteUniformMeasure α hα s = Nat.card s / Nat.card α :=
  tangentFiniteUniformMeasure_apply α hα s hs

/-! The actual finite product experiment is uniform after restriction to a
finite request support. -/
example {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (support : Finset Request) :
    (tangentUniformMultiplierMeasure lists hlist).map
        (fun outcome (request : ↑support) ↦ outcome request.1) =
      tangentUniformMultiplierRestrictionMeasure lists hlist support :=
  tangentUniformMultiplierRestriction_map_eq_uniformOfFintype
    lists hlist support

/-! Hence the probability of one genuine collision cylinder is exactly a
finite configuration count divided by the product of its two list sizes. -/
example {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request) :
    tangentCollisionProbability lists hlist source target collision =
      ((tangentCollisionConfigurations
          (lists := lists) source target collision).card : ℝ) /
        (∏ request : ↑collision.1, (lists request.1).card) := by
  simpa only [tangentCollisionChoiceCount] using
    tangentCollisionProbability_eq_configurationCount_div
      lists hlist source target collision

/-! The raw equation count has the paper's two literal cases. -/
example {leftList rightList : Finset ℕ} {p q N : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hupper : ∀ a ∈ leftList, p * a ≤ N) :
    (tangentEndpointEquationSolutions leftList rightList p q).card ≤
      if p = q then N / p + 1 else N / (p * q) + 1 := by
  simpa only [tangentEndpointEquationBudget] using
    card_tangentEndpointEquationSolutions_prime_le_budget
      hp hq hupper

/-! Incident two-request events are reindexed exactly by other requests. -/
example {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ) (request : Request) :
    tangentRequestCollisionMass lists hlist source target request =
      ∑ other ∈ Finset.univ.erase request,
        tangentPairCollisionProbability lists hlist source target
          request other :=
  tangentRequestCollisionMass_eq_sum_otherRequests
    lists hlist source target request

/-! The displayed quotient for a distinct ordered pair has no hidden support
ordering: its denominator is exactly the product of the two lower sizes. -/
example {Request : Type*} [DecidableEq Request]
    (lowerCard : Request → ℕ) (N : ℕ)
    (source target : Request → ℕ) (left right : Request)
    (hne : left ≠ right) :
    tangentPairEndpointBudgetQuotient
        lowerCard N source target left right =
      (tangentOrderedPairEndpointBudget N source target left right : ℝ) /
        (lowerCard left * lowerCard right) := by
  rw [tangentPairEndpointBudgetQuotient, dif_pos hne]

/-! Request-wise list cardinality lower bounds and the four endpoint counts
give the exact pair-budget sum; no probability estimate is an input. -/
example {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (lowerCard : Request → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request, lowerCard request ≤ (lists request).card)
    (N : ℕ) (source target : Request → ℕ)
    (hprime : ∀ request side,
      (tangentEndpointLabel source target side request).Prime)
    (hupper : ∀ request side multiplier,
      multiplier ∈ lists request →
        tangentEndpointLabel source target side request * multiplier ≤ N)
    (request : Request) :
    tangentRequestCollisionMass lists hlist source target request ≤
      ∑ other ∈ Finset.univ.erase request,
        tangentPairEndpointBudgetQuotient
          lowerCard N source target request other :=
  tangentRequestCollisionMass_le_sum_endpointBudgetQuotients
    lists hlist lowerCard hlowerPos hlower N source target
      hprime hupper request

/-! The same sum can be bounded by the total request count and the two
endpoint-label loads of the fixed request. -/
example {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ)
    (disjointCharge : ℝ) (sharedCharge : ℕ → ℝ)
    (hdisjointNonneg : 0 ≤ disjointCharge)
    (hsharedNonneg : ∀ label, 0 ≤ sharedCharge label)
    (hpair : ∀ left right, left ≠ right →
      tangentPairCollisionProbability lists hlist source target left right ≤
        disjointCharge +
          (if tangentRequestHasLabel source target (source left) right
            then sharedCharge (source left) else 0) +
          (if tangentRequestHasLabel source target (target left) right
            then sharedCharge (target left) else 0))
    (request : Request) :
    tangentRequestCollisionMass lists hlist source target request ≤
      (tangentTotalRequestCount Request : ℝ) * disjointCharge +
        (tangentRequestLabelLoad source target
          (source request) : ℝ) * sharedCharge (source request) +
        (tangentRequestLabelLoad source target
          (target request) : ℝ) * sharedCharge (target request) :=
  tangentRequestCollisionMass_le_fullLoadBudget
    lists hlist source target disjointCharge sharedCharge
      hdisjointNonneg hsharedNonneg hpair request

end

end Erdos390.WholePaper
