import Erdos390.WholePaper.BankBottomPoolMatching

/-! # Expanded literal statement audit for bottom-pool matching -/

namespace Erdos390.WholePaper

noncomputable section

example {Request : Type*} [DecidableEq Request]
    (requests : Finset Request)
    (poolOf : Request → BankBottomOrientationPool)
    (pool : BankBottomOrientationPool) :
    bankBottomRequestsInPool requests poolOf pool =
      requests.filter (fun request ↦ poolOf request = pool) := rfl

example {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    (requests : Finset Request)
    (poolOf : Request → BankBottomOrientationPool)
    (available : BankBottomOrientationPool → Finset Occurrence)
    (hcapacity : ∀ pool,
      (requests.filter (fun request ↦ poolOf request = pool)).card ≤
        (available pool).card) :
    Nonempty (BankBottomPoolMatching requests poolOf available) := by
  apply bankBottomPoolMatching_nonempty
  intro pool
  simpa only [bankBottomPoolDemand, bankBottomPoolCapacity,
    bankBottomRequestsInPool] using hcapacity pool

example {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    {requests : Finset Request}
    {poolOf : Request → BankBottomOrientationPool}
    {available : BankBottomOrientationPool → Finset Occurrence}
    (matching : BankBottomPoolMatching requests poolOf available)
    (pool : BankBottomOrientationPool) :
    ((Finset.univ : Finset
        ↑(requests.filter (fun request ↦ poolOf request = pool))).image
      (fun request ↦ (matching.toEmbedding pool request).1)).card =
        (requests.filter (fun request ↦ poolOf request = pool)).card := by
  simpa only [BankBottomPoolMatching.usedSlots,
    bankBottomRequestsInPool, bankBottomPoolDemand] using
      matching.card_usedSlots pool

example {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    {requests : Finset Request}
    {poolOf : Request → BankBottomOrientationPool}
    {available : BankBottomOrientationPool → Finset Occurrence}
    (matching : BankBottomPoolMatching requests poolOf available)
    (pool : BankBottomOrientationPool) :
    (available pool \
        ((Finset.univ : Finset
          ↑(requests.filter (fun request ↦ poolOf request = pool))).image
            (fun request ↦ (matching.toEmbedding pool request).1))).card =
      (available pool).card -
        (requests.filter (fun request ↦ poolOf request = pool)).card := by
  simpa only [BankBottomPoolMatching.usedSlots,
    bankBottomRequestsInPool, bankBottomPoolDemand,
    bankBottomPoolCapacity] using
      matching.card_unusedSlots pool

example {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    (requests : Finset Request)
    (poolOf : Request → BankBottomOrientationPool)
    (available : BankBottomOrientationPool → Finset Occurrence)
    (hcapacity : ∀ pool,
      (requests.filter (fun request ↦ poolOf request = pool)).card ≤
        (available pool).card)
    (hpools : ∀ {pool pool' : BankBottomOrientationPool},
      pool ≠ pool' → Disjoint (available pool) (available pool')) :
    ∃ matching : BankBottomPoolMatching requests poolOf available,
      Function.Injective
          (fun request : ↑requests ↦
            (matching.toEmbedding (poolOf request.1)
              ⟨request.1, Finset.mem_filter.mpr
                ⟨request.property, rfl⟩⟩).1) ∧
        ∀ request : ↑requests,
          (matching.toEmbedding (poolOf request.1)
              ⟨request.1, Finset.mem_filter.mpr
                ⟨request.property, rfl⟩⟩).1 ∈
            available (poolOf request.1) := by
  have hcapacity' : ∀ pool,
      bankBottomPoolDemand requests poolOf pool ≤
        bankBottomPoolCapacity available pool := by
    intro pool
    simpa only [bankBottomPoolDemand, bankBottomPoolCapacity,
      bankBottomRequestsInPool] using hcapacity pool
  simpa only [BankBottomPoolMatching.matchedSlot,
    BankBottomPoolMatching.slotOfLabeledRequest,
    bankBottomLabelRequest, bankBottomRequestInItsPool,
    bankBottomRequestsInPool] using
      exists_bankBottomPool_injective_assignment
        requests poolOf available hcapacity' hpools

end

end Erdos390.WholePaper
