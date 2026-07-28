import Erdos390.WholePaper.BankBottomMarkerPoolScale
import Erdos390.WholePaper.BankPaperCanonicalSectionNineFinalGeometry

/-!
# Fixed exceptional factors avoid the actual component census

The fixed exceptional factors lie in the strict upper tail and are defined
by removing every realized donor.  Thus an intersection with the actual bank
census can only come from a bottom-component state which itself lies above
`2n`.  Ordinary states are always at most `2n`, and every ordinary or bottom
donor belongs to `prechargeDonorSet`.

This file records that exact finite reduction.  It then closes the reduction
under the paper's standard narrow-endpoint inequality

`5 * M ≤ 12 * n`.

For the literal endpoint `M = upperEndpoint n (upperTailLength c n)`, that
inequality holds eventually when `0 < c`.  Consequently the collision premise
left explicit in `BankPaperCanonicalSectionNineFinalGeometry` is an eventual
theorem, uniformly in the realization and in `deltaStar`.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-- The only state values which can possibly meet the fixed exceptional set.

All bottom lower states are listed.  An upper state is listed only when it is
not already the component's donor, since donors are removed in the literal
definition of `paperFixedExceptionalFactors`. -/
def BankPaperCanonicalSectionNineBottomStateCollisionExclusions
    {c : Real} {n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (deltaStar : Real) : Prop :=
  ∀ request : ↑(bankBottomRelevantPaperRequests n),
    let fullRequest :=
      bankBottomRelevantRequestToPaperRequest request
    R.bottom.lowerStateFactor fullRequest ∉
        R.paperFixedExceptionalFactors deltaStar ∧
      (R.bottom.upperStateFactor fullRequest ≠
          R.bottom.donorFactor fullRequest →
        R.bottom.upperStateFactor fullRequest ∉
          R.paperFixedExceptionalFactors deltaStar)

private theorem paperFixedExceptionalFactors_disjoint_ordinaryComponentOccurrences
    {n h : Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : Real) :
    Disjoint (R.paperFixedExceptionalFactors deltaStar)
      R.ordinaryComponentOccurrences := by
  classical
  rw [Finset.disjoint_left]
  intro occurrence hfixed hordinary
  rw [ordinaryComponentOccurrences, Finset.mem_biUnion] at hordinary
  obtain ⟨request, _hrequest, hrequestOccurrence⟩ := hordinary
  rw [BankOrdinaryPaperRealization.componentOccurrences,
    Finset.mem_image] at hrequestOccurrence
  obtain ⟨kind, _hkind, rfl⟩ := hrequestOccurrence
  cases kind with
  | sourceState =>
      have htail :=
        R.paperFixedExceptionalFactors_subset_tail deltaStar hfixed
      have hsource :=
        R.ordinary.sourceStateValue_le_two_mul_n request
      simp only [BankOrdinaryPaperRealization.occurrenceValue_sourceState,
        Finset.mem_Ioc] at htail
      omega
  | targetState =>
      have htail :=
        R.paperFixedExceptionalFactors_subset_tail deltaStar hfixed
      have htargetSource :=
        R.ordinary.targetStateValue_lt_sourceStateValue request
      have hsource :=
        R.ordinary.sourceStateValue_le_two_mul_n request
      simp only [BankOrdinaryPaperRealization.occurrenceValue_targetState,
        Finset.mem_Ioc] at htail
      omega
  | donor =>
      have hdonor :
          R.ordinary.occurrenceValue request
              BankOrdinaryPaperOccurrenceKind.donor ∈
            R.prechargeDonorSet := by
        simpa only [BankOrdinaryPaperRealization.occurrenceValue_donor,
          prechargeDonorValue] using
          R.prechargeDonorValue_mem_prechargeDonorSet
            (Sum.inr request : BankPaperMarkerRequest n)
      exact (Finset.disjoint_left.mp
        (R.paperFixedExceptionalFactors_disjoint_prechargeDonorSet
          deltaStar)) hfixed hdonor

private theorem bottomComponentOccurrence_mem_allComponentOccurrences
    {n M : Nat} (R : BankPaperRealization n M)
    (request : ↑(bankBottomRelevantPaperRequests n))
    {occurrence : Nat}
    (hoccurrence :
      occurrence ∈
        R.bottom.componentOccurrences
          (bankBottomRelevantRequestToPaperRequest request)) :
    occurrence ∈ R.allComponentOccurrences := by
  rw [allComponentOccurrences, Finset.mem_union]
  right
  rw [bottomComponentOccurrences,
    BankBottomPaperRealization.relevantComponentOccurrences,
    Finset.mem_biUnion]
  exact ⟨request, Finset.mem_attach _ _, hoccurrence⟩

/-- Exact finite collision reduction.

There are no hidden ordinary-component or donor exclusions: those follow
from the strict-tail interval and the set difference in the definition of
the fixed factors.  The displayed bottom-state exclusions are therefore
equivalent to disjointness from the full actual occurrence census. -/
theorem bankPaperCanonicalSectionNineFixedComponentCollisionFree_iff_bottomStateExclusions
    {c : Real} {n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (deltaStar : Real) :
    R.BankPaperCanonicalSectionNineFixedComponentCollisionFree deltaStar ↔
      R.BankPaperCanonicalSectionNineBottomStateCollisionExclusions
        deltaStar := by
  classical
  constructor
  · intro hcollision request
    let fullRequest :=
      bankBottomRelevantRequestToPaperRequest request
    change Disjoint (R.paperFixedExceptionalFactors deltaStar)
      R.allComponentOccurrences at hcollision
    constructor
    · intro hlowerFixed
      apply (Finset.disjoint_left.mp hcollision) hlowerFixed
      apply R.bottomComponentOccurrence_mem_allComponentOccurrences request
      rw [R.bottom.componentOccurrences_eq_states_insert_donor fullRequest]
      exact Finset.mem_insert_self _ _
    · intro _hupperNeDonor hupperFixed
      apply (Finset.disjoint_left.mp hcollision) hupperFixed
      apply R.bottomComponentOccurrence_mem_allComponentOccurrences request
      rw [R.bottom.componentOccurrences_eq_states_insert_donor fullRequest]
      exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert_self _ _))
  · intro hexclusions
    unfold BankPaperCanonicalSectionNineFixedComponentCollisionFree
    rw [Finset.disjoint_left]
    intro occurrence hfixed hoccurrence
    rw [allComponentOccurrences, Finset.mem_union] at hoccurrence
    rcases hoccurrence with hordinary | hbottom
    · exact (Finset.disjoint_left.mp
        (paperFixedExceptionalFactors_disjoint_ordinaryComponentOccurrences
          R deltaStar)) hfixed hordinary
    · rw [bottomComponentOccurrences,
        BankBottomPaperRealization.relevantComponentOccurrences,
        Finset.mem_biUnion] at hbottom
      obtain ⟨request, _hrequest, hrequestOccurrence⟩ := hbottom
      let fullRequest :=
        bankBottomRelevantRequestToPaperRequest request
      have hstateExclusions := hexclusions request
      rw [R.bottom.componentOccurrences_eq_states_insert_donor fullRequest]
        at hrequestOccurrence
      simp only [Finset.mem_insert, Finset.mem_singleton]
        at hrequestOccurrence
      rcases hrequestOccurrence with hlower | hupper | hdonor
      · subst occurrence
        exact hstateExclusions.1 hfixed
      · subst occurrence
        by_cases hupperDonor :
            R.bottom.upperStateFactor fullRequest =
              R.bottom.donorFactor fullRequest
        · have hdonorMem :
              R.bottom.upperStateFactor fullRequest ∈
                R.prechargeDonorSet := by
            rw [hupperDonor]
            simpa only [prechargeDonorValue, fullRequest] using
              R.prechargeDonorValue_mem_prechargeDonorSet
                (Sum.inl request : BankPaperMarkerRequest n)
          exact (Finset.disjoint_left.mp
            (R.paperFixedExceptionalFactors_disjoint_prechargeDonorSet
              deltaStar)) hfixed hdonorMem
        · exact (hstateExclusions.2 hupperDonor) hfixed
      · subst occurrence
        have hdonorMem :
            R.bottom.donorFactor fullRequest ∈ R.prechargeDonorSet := by
          simpa only [prechargeDonorValue, fullRequest] using
            R.prechargeDonorValue_mem_prechargeDonorSet
              (Sum.inl request : BankPaperMarkerRequest n)
        exact (Finset.disjoint_left.mp
          (R.paperFixedExceptionalFactors_disjoint_prechargeDonorSet
            deltaStar)) hfixed hdonorMem

private theorem bottomLowerStateFactor_le_two_mul_n_of_scaledEndpoint_narrow
    {n M : Nat} (R : BankPaperRealization n M)
    (hnarrow : 5 * M ≤ 12 * n)
    (request : ↑(bankBottomRelevantPaperRequests n)) :
    R.bottom.lowerStateFactor
        (bankBottomRelevantRequestToPaperRequest request) ≤
      2 * n := by
  let fullRequest :=
    bankBottomRelevantRequestToPaperRequest request
  change R.bottom.lowerStateFactor fullRequest ≤ 2 * n
  have hrow := R.bottom.marker_mem_row
    R.ordinary.two_mul_n_le_M fullRequest
  cases hmove : R.bottom.move fullRequest <;>
    simp only [hmove, bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc,
      BankBottomPaperRealization.lowerStateFactor, bankBottomLowerState,
      bankBottomLowerStateMultiplier] at hrow ⊢ <;>
    omega

private theorem bottomUpperStateFactor_le_two_mul_n_or_eq_donor_of_scaledEndpoint_narrow
    {n M : Nat} (R : BankPaperRealization n M)
    (hnarrow : 5 * M ≤ 12 * n)
    (request : ↑(bankBottomRelevantPaperRequests n)) :
    let fullRequest :=
      bankBottomRelevantRequestToPaperRequest request
    R.bottom.upperStateFactor fullRequest ≤ 2 * n ∨
      R.bottom.upperStateFactor fullRequest =
        R.bottom.donorFactor fullRequest := by
  let fullRequest :=
    bankBottomRelevantRequestToPaperRequest request
  change R.bottom.upperStateFactor fullRequest ≤ 2 * n ∨
    R.bottom.upperStateFactor fullRequest =
      R.bottom.donorFactor fullRequest
  have hrow := R.bottom.marker_mem_row
    R.ordinary.two_mul_n_le_M fullRequest
  cases hmove : R.bottom.move fullRequest
  · left
    simp only [hmove, bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc,
      BankBottomPaperRealization.upperStateFactor, bankBottomUpperState,
      bankBottomUpperStateMultiplier] at hrow ⊢
    omega
  · left
    simp only [hmove, bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc,
      BankBottomPaperRealization.upperStateFactor, bankBottomUpperState,
      bankBottomUpperStateMultiplier] at hrow ⊢
    omega
  · right
    exact (R.bottom.donorFactor_eq_upperStateFactor_of_terminalMove
      fullRequest (Or.inl hmove)).symm
  · right
    exact (R.bottom.donorFactor_eq_upperStateFactor_of_terminalMove
      fullRequest (Or.inr hmove)).symm

/-- The paper's narrow-endpoint inequality rules out every remaining finite
collision, so the literal fixed factors avoid the full component census. -/
theorem bankPaperCanonicalSectionNineFixedComponentCollisionFree_of_scaledEndpoint_narrow
    {c : Real} {n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (deltaStar : Real)
    (hnarrow :
      5 * upperEndpoint n (upperTailLength c n) ≤ 12 * n) :
    R.BankPaperCanonicalSectionNineFixedComponentCollisionFree
      deltaStar := by
  rw [R.bankPaperCanonicalSectionNineFixedComponentCollisionFree_iff_bottomStateExclusions
    deltaStar]
  intro request
  let fullRequest :=
    bankBottomRelevantRequestToPaperRequest request
  constructor
  · intro hlowerFixed
    have hlowerTail :=
      R.paperFixedExceptionalFactors_subset_tail deltaStar hlowerFixed
    have hlowerBound :=
      bottomLowerStateFactor_le_two_mul_n_of_scaledEndpoint_narrow
        R hnarrow request
    simp only [Finset.mem_Ioc] at hlowerTail
    omega
  · intro hupperNeDonor hupperFixed
    have hupperTail :=
      R.paperFixedExceptionalFactors_subset_tail deltaStar hupperFixed
    rcases
        bottomUpperStateFactor_le_two_mul_n_or_eq_donor_of_scaledEndpoint_narrow
          R hnarrow request with hupperBound | hupperDonor
    · simp only [Finset.mem_Ioc] at hupperTail
      omega
    · exact hupperNeDonor hupperDonor

end BankPaperRealization

/-- At the literal paper endpoint the fixed/component collision premise is
eventually automatic, uniformly over every realized bank and every value of
the exceptional exponent. -/
theorem eventually_bankPaperCanonicalSectionNineFixedComponentCollisionFree
    {c : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (deltaStar : Real),
        R.BankPaperCanonicalSectionNineFixedComponentCollisionFree
          deltaStar := by
  filter_upwards [eventually_bankBottom_scaledEndpoint_narrow hc]
    with n hnarrow
  intro R deltaStar
  exact
    R.bankPaperCanonicalSectionNineFixedComponentCollisionFree_of_scaledEndpoint_narrow
      deltaStar hnarrow

end

end Erdos390.WholePaper
