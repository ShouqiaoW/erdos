import Erdos390.WholePaper.BankMarkerDonorCombinatorics
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.DeriveFintype

/-!
# Finite matching for the eight oriented bottom pools

The four bottom moves and their two orientations give eight literal pool
labels.  This file assumes only actual finite request and occurrence pools,
pointwise cardinality bounds, and pairwise disjointness of the occurrence
pools.  It then chooses an injective occurrence assignment.  No analytic
estimate asserting that the capacity hypotheses hold appears here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The four bottom moves in the bank descent. -/
inductive BankBottomMove where
  | fiveToFour
  | fourToThree
  | threeToTwo
  | twoToOne
  deriving DecidableEq, Fintype

/-- The two copies used for opposite path orientations. -/
inductive BankBottomOrientation where
  | downward
  | upward
  deriving DecidableEq, Fintype

/-- One of the eight bottom move/orientation pools. -/
abbrev BankBottomOrientationPool := BankBottomMove × BankBottomOrientation

/-- Actual requests routed to one bottom orientation pool. -/
def bankBottomRequestsInPool
    {Request : Type*} [DecidableEq Request]
    (requests : Finset Request)
    (poolOf : Request → BankBottomOrientationPool)
    (pool : BankBottomOrientationPool) : Finset Request :=
  requests.filter fun request ↦ poolOf request = pool

/-- Literal demand of one bottom orientation pool. -/
def bankBottomPoolDemand
    {Request : Type*} [DecidableEq Request]
    (requests : Finset Request)
    (poolOf : Request → BankBottomOrientationPool)
    (pool : BankBottomOrientationPool) : ℕ :=
  (bankBottomRequestsInPool requests poolOf pool).card

/-- Literal number of available occurrences in one bottom orientation pool. -/
def bankBottomPoolCapacity
    {Occurrence : Type*}
    (available : BankBottomOrientationPool → Finset Occurrence)
    (pool : BankBottomOrientationPool) : ℕ :=
  (available pool).card

/-- An assignment consists of an embedding from each request fiber into its
actual finite occurrence pool.  Membership and within-pool injectivity are
carried by the subtype embedding itself. -/
structure BankBottomPoolMatching
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    (requests : Finset Request)
    (poolOf : Request → BankBottomOrientationPool)
    (available : BankBottomOrientationPool → Finset Occurrence) where
  toEmbedding : (pool : BankBottomOrientationPool) →
    ↑(bankBottomRequestsInPool requests poolOf pool) ↪
      ↑(available pool)

/-- Pointwise capacity is sufficient to choose a matching in every pool. -/
theorem bankBottomPoolMatching_nonempty
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    (requests : Finset Request)
    (poolOf : Request → BankBottomOrientationPool)
    (available : BankBottomOrientationPool → Finset Occurrence)
    (hcapacity : ∀ pool,
      bankBottomPoolDemand requests poolOf pool ≤
        bankBottomPoolCapacity available pool) :
    Nonempty (BankBottomPoolMatching requests poolOf available) := by
  let embedding : (pool : BankBottomOrientationPool) →
      ↑(bankBottomRequestsInPool requests poolOf pool) ↪
        ↑(available pool) := fun pool ↦
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_coe, bankBottomPoolDemand,
        bankBottomPoolCapacity] using hcapacity pool))
  exact ⟨⟨embedding⟩⟩

/-- Regard an original request as a member of the fiber bearing its label. -/
def bankBottomRequestInItsPool
    {Request : Type*} [DecidableEq Request]
    {requests : Finset Request}
    (poolOf : Request → BankBottomOrientationPool)
    (request : ↑requests) :
    ↑(bankBottomRequestsInPool requests poolOf (poolOf request.1)) :=
  ⟨request.1, Finset.mem_filter.mpr ⟨request.property, rfl⟩⟩

/-- The sigma type that keeps the pool label attached to a request fiber. -/
abbrev BankBottomLabeledRequest
    {Request : Type*} [DecidableEq Request]
    (requests : Finset Request)
    (poolOf : Request → BankBottomOrientationPool) :=
  Σ pool : BankBottomOrientationPool,
    ↑(bankBottomRequestsInPool requests poolOf pool)

/-- Attach the prescribed pool label to an original request. -/
def bankBottomLabelRequest
    {Request : Type*} [DecidableEq Request]
    {requests : Finset Request}
    (poolOf : Request → BankBottomOrientationPool)
    (request : ↑requests) :
    BankBottomLabeledRequest requests poolOf :=
  ⟨poolOf request.1, bankBottomRequestInItsPool poolOf request⟩

theorem bankBottomLabelRequest_injective
    {Request : Type*} [DecidableEq Request]
    {requests : Finset Request}
    (poolOf : Request → BankBottomOrientationPool) :
    Function.Injective
      (bankBottomLabelRequest (requests := requests) poolOf) := by
  intro request request' heq
  apply Subtype.ext
  exact congrArg
    (fun labeled : BankBottomLabeledRequest requests poolOf ↦ labeled.2.1) heq

/-- Evaluate the poolwise matching while retaining the pool label. -/
def BankBottomPoolMatching.slotOfLabeledRequest
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    {requests : Finset Request}
    {poolOf : Request → BankBottomOrientationPool}
    {available : BankBottomOrientationPool → Finset Occurrence}
    (matching : BankBottomPoolMatching requests poolOf available)
    (request : BankBottomLabeledRequest requests poolOf) : Occurrence :=
  (matching.toEmbedding request.1 request.2).1

theorem BankBottomPoolMatching.slotOfLabeledRequest_mem
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    {requests : Finset Request}
    {poolOf : Request → BankBottomOrientationPool}
    {available : BankBottomOrientationPool → Finset Occurrence}
    (matching : BankBottomPoolMatching requests poolOf available)
    (request : BankBottomLabeledRequest requests poolOf) :
    matching.slotOfLabeledRequest request ∈ available request.1 :=
  (matching.toEmbedding request.1 request.2).property

/-- Disjoint actual pools make the sigma-level assignment globally injective. -/
theorem BankBottomPoolMatching.slotOfLabeledRequest_injective
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    {requests : Finset Request}
    {poolOf : Request → BankBottomOrientationPool}
    {available : BankBottomOrientationPool → Finset Occurrence}
    (matching : BankBottomPoolMatching requests poolOf available)
    (hpools : ∀ {pool pool' : BankBottomOrientationPool},
      pool ≠ pool' → Disjoint (available pool) (available pool')) :
    Function.Injective matching.slotOfLabeledRequest := by
  rintro ⟨pool, request⟩ ⟨pool', request'⟩ heq
  by_cases hp : pool = pool'
  · subst pool'
    have hembedding : matching.toEmbedding pool request =
        matching.toEmbedding pool request' := by
      apply Subtype.ext
      exact heq
    have hrequest := (matching.toEmbedding pool).injective hembedding
    subst request'
    rfl
  · have hleft : matching.slotOfLabeledRequest ⟨pool, request⟩ ∈
        available pool :=
      matching.slotOfLabeledRequest_mem ⟨pool, request⟩
    have hright : matching.slotOfLabeledRequest ⟨pool, request⟩ ∈
        available pool' := by
      rw [heq]
      exact matching.slotOfLabeledRequest_mem ⟨pool', request'⟩
    exact False.elim ((Finset.disjoint_left.mp (hpools hp)) hleft hright)

/-- The actual occurrence assigned to an original request. -/
def BankBottomPoolMatching.matchedSlot
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    {requests : Finset Request}
    {poolOf : Request → BankBottomOrientationPool}
    {available : BankBottomOrientationPool → Finset Occurrence}
    (matching : BankBottomPoolMatching requests poolOf available)
    (request : ↑requests) : Occurrence :=
  matching.slotOfLabeledRequest (bankBottomLabelRequest poolOf request)

theorem BankBottomPoolMatching.matchedSlot_mem
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    {requests : Finset Request}
    {poolOf : Request → BankBottomOrientationPool}
    {available : BankBottomOrientationPool → Finset Occurrence}
    (matching : BankBottomPoolMatching requests poolOf available)
    (request : ↑requests) :
    matching.matchedSlot request ∈ available (poolOf request.1) :=
  matching.slotOfLabeledRequest_mem (bankBottomLabelRequest poolOf request)

theorem BankBottomPoolMatching.matchedSlot_injective
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    {requests : Finset Request}
    {poolOf : Request → BankBottomOrientationPool}
    {available : BankBottomOrientationPool → Finset Occurrence}
    (matching : BankBottomPoolMatching requests poolOf available)
    (hpools : ∀ {pool pool' : BankBottomOrientationPool},
      pool ≠ pool' → Disjoint (available pool) (available pool')) :
    Function.Injective matching.matchedSlot :=
  (matching.slotOfLabeledRequest_injective hpools).comp
    (bankBottomLabelRequest_injective (requests := requests) poolOf)

/-- The actual occurrences used by one pool. -/
def BankBottomPoolMatching.usedSlots
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    {requests : Finset Request}
    {poolOf : Request → BankBottomOrientationPool}
    {available : BankBottomOrientationPool → Finset Occurrence}
    (matching : BankBottomPoolMatching requests poolOf available)
    (pool : BankBottomOrientationPool) : Finset Occurrence :=
  (Finset.univ :
      Finset ↑(bankBottomRequestsInPool requests poolOf pool)).image
    (fun request ↦ (matching.toEmbedding pool request).1)

theorem BankBottomPoolMatching.usedSlots_subset
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    {requests : Finset Request}
    {poolOf : Request → BankBottomOrientationPool}
    {available : BankBottomOrientationPool → Finset Occurrence}
    (matching : BankBottomPoolMatching requests poolOf available)
    (pool : BankBottomOrientationPool) :
    matching.usedSlots pool ⊆ available pool := by
  rw [BankBottomPoolMatching.usedSlots, Finset.image_subset_iff]
  intro request _hrequest
  exact (matching.toEmbedding pool request).property

theorem BankBottomPoolMatching.card_usedSlots
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    {requests : Finset Request}
    {poolOf : Request → BankBottomOrientationPool}
    {available : BankBottomOrientationPool → Finset Occurrence}
    (matching : BankBottomPoolMatching requests poolOf available)
    (pool : BankBottomOrientationPool) :
    (matching.usedSlots pool).card =
      bankBottomPoolDemand requests poolOf pool := by
  unfold BankBottomPoolMatching.usedSlots bankBottomPoolDemand
  have hinjective : Function.Injective
      (fun request ↦ (matching.toEmbedding pool request).1) := by
    intro request request' heq
    apply (matching.toEmbedding pool).injective
    apply Subtype.ext
    exact heq
  rw [Finset.card_image_of_injective _ hinjective]
  simp

theorem BankBottomPoolMatching.card_unusedSlots
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    {requests : Finset Request}
    {poolOf : Request → BankBottomOrientationPool}
    {available : BankBottomOrientationPool → Finset Occurrence}
    (matching : BankBottomPoolMatching requests poolOf available)
    (pool : BankBottomOrientationPool) :
    (available pool \ matching.usedSlots pool).card =
      bankBottomPoolCapacity available pool -
        bankBottomPoolDemand requests poolOf pool := by
  rw [Finset.card_sdiff_of_subset (matching.usedSlots_subset pool),
    matching.card_usedSlots]
  rfl

/-- Concrete finite greedy/matching conclusion for all eight pools at once. -/
theorem exists_bankBottomPool_injective_assignment
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    (requests : Finset Request)
    (poolOf : Request → BankBottomOrientationPool)
    (available : BankBottomOrientationPool → Finset Occurrence)
    (hcapacity : ∀ pool,
      bankBottomPoolDemand requests poolOf pool ≤
        bankBottomPoolCapacity available pool)
    (hpools : ∀ {pool pool' : BankBottomOrientationPool},
      pool ≠ pool' → Disjoint (available pool) (available pool')) :
    ∃ matching : BankBottomPoolMatching requests poolOf available,
      Function.Injective matching.matchedSlot ∧
        ∀ request : ↑requests,
          matching.matchedSlot request ∈ available (poolOf request.1) := by
  let matching := Classical.choice
    (bankBottomPoolMatching_nonempty requests poolOf available hcapacity)
  exact ⟨matching, matching.matchedSlot_injective hpools,
    matching.matchedSlot_mem⟩

end

end Erdos390.WholePaper
