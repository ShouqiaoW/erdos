import Erdos390.WholePaper.BankPaperComponents

/-!
# Actual full bank paths

For one signed rounding slot, the component index is the disjoint union of
the ordinary `p→5` sources and the relevant truncated bottom rows.  Each
index contributes exactly one state-zero endpoint and one state-one endpoint;
markers and donors belong to the component census, but never to either path
state.  Global occurrence disjointness makes both endpoint maps injective.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- Actual component indices of one full signed bank path. -/
abbrev BankPaperPathComponent
    {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :=
  ↑(bankOrdinaryCoreSources slot.1.1) ⊕
    ↑(bankBottomRelevantMoves slot.1.1)

/-- The full rectangular-family request belonging to a slot and bottom row. -/
def bankPaperBottomRequestOfMove
    {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (move : ↑(bankBottomRelevantMoves slot.1.1)) :
    ↑(bankBottomPaperRequests n) :=
  ⟨(slot, move.1), Finset.mem_univ _⟩

/-- The same request with its path relevance retained in the type. -/
def bankPaperBottomRelevantRequestOfMove
    {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (move : ↑(bankBottomRelevantMoves slot.1.1)) :
    ↑(bankBottomRelevantPaperRequests n) :=
  ⟨(slot, move.1), by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [bankBottomPaperRequestRelevant_iff_mem_moves]
    simpa only [bankBottomPaperRequestPrime] using move.property⟩

@[simp] theorem bankBottomRelevantRequestToPaperRequest_ofMove
    {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (move : ↑(bankBottomRelevantMoves slot.1.1)) :
    bankBottomRelevantRequestToPaperRequest
        (bankPaperBottomRelevantRequestOfMove slot move) =
      bankPaperBottomRequestOfMove slot move := rfl

/-- Embed a path component into the globally injective marker-request type. -/
def bankPaperPathComponentRequest
    {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    BankPaperPathComponent slot → BankPaperMarkerRequest n
  | .inl source =>
      .inr (BankOrdinaryPaperRealization.requestOfSource slot source)
  | .inr move =>
      .inl (bankPaperBottomRelevantRequestOfMove slot move)

theorem bankPaperPathComponentRequest_injective
    {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    Function.Injective (bankPaperPathComponentRequest slot) := by
  intro component component' hrequest
  cases component with
  | inl source =>
      cases component' with
      | inl source' =>
          have hordinary :
              BankOrdinaryPaperRealization.requestOfSource slot source =
                BankOrdinaryPaperRealization.requestOfSource slot source' := by
            simpa only [bankPaperPathComponentRequest, Sum.inr.injEq] using
              hrequest
          have hsource : source = source' := by
            apply Subtype.ext
            exact congrArg
              (fun request : ↑(bankOrdinaryPaperRequests n) ↦
                request.1.2.1) hordinary
          exact congrArg Sum.inl hsource
      | inr move =>
          simp [bankPaperPathComponentRequest] at hrequest
  | inr move =>
      cases component' with
      | inl source =>
          simp [bankPaperPathComponentRequest] at hrequest
      | inr move' =>
          have hbottom :
              bankPaperBottomRelevantRequestOfMove slot move =
                bankPaperBottomRelevantRequestOfMove slot move' := by
            simpa only [bankPaperPathComponentRequest, Sum.inl.injEq] using
              hrequest
          have hmove : move = move' := by
            apply Subtype.ext
            exact congrArg
              (fun request : ↑(bankBottomRelevantPaperRequests n) ↦
                request.1.2) hbottom
          exact congrArg Sum.inr hmove

namespace BankPaperRealization

/-- The three actual occurrences carried by one component index.  Terminal
bottom rows may have only two distinct values because donor and upper state
coincide. -/
def pathComponentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    BankPaperPathComponent slot → Finset ℕ
  | .inl source => R.ordinary.componentOccurrences
      (BankOrdinaryPaperRealization.requestOfSource slot source)
  | .inr move => R.bottom.componentOccurrences
      (bankPaperBottomRequestOfMove slot move)

/-- State zero is the source side of a downward path and the target side of
its reversed path. -/
def pathStateZeroValue
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    BankPaperPathComponent slot → ℕ
  | .inl source => R.ordinary.fromStateValue
      (BankOrdinaryPaperRealization.requestOfSource slot source)
  | .inr move => R.bottom.fromStateValue
      (bankPaperBottomRequestOfMove slot move)

/-- State one is the opposite endpoint in every realized component. -/
def pathStateOneValue
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    BankPaperPathComponent slot → ℕ
  | .inl source => R.ordinary.toStateValue
      (BankOrdinaryPaperRealization.requestOfSource slot source)
  | .inr move => R.bottom.toStateValue
      (bankPaperBottomRequestOfMove slot move)

theorem pathStateZeroValue_mem_componentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (component : BankPaperPathComponent slot) :
    R.pathStateZeroValue slot component ∈
      R.pathComponentOccurrences slot component := by
  cases component with
  | inl source =>
      cases hslot : slot.2
      · simpa [pathStateZeroValue, pathComponentOccurrences, hslot,
          BankOrdinaryPaperRealization.fromStateValue,
          BankOrdinaryPaperRealization.requestOfSource,
          bankOrdinaryPaperRequestPool, bankSignedSlotOrientation] using
          R.ordinary.occurrenceValue_mem_componentOccurrences
            (BankOrdinaryPaperRealization.requestOfSource slot source)
            .sourceState
      · simpa [pathStateZeroValue, pathComponentOccurrences, hslot,
          BankOrdinaryPaperRealization.fromStateValue,
          BankOrdinaryPaperRealization.requestOfSource,
          bankOrdinaryPaperRequestPool, bankSignedSlotOrientation] using
          R.ordinary.occurrenceValue_mem_componentOccurrences
            (BankOrdinaryPaperRealization.requestOfSource slot source)
            .targetState
  | inr move =>
      rw [pathComponentOccurrences,
        R.bottom.componentOccurrences_eq_states_insert_donor]
      cases hslot : slot.2 <;>
        simp [pathStateZeroValue, BankBottomPaperRealization.fromStateValue,
          bankSignedSlotOrientation, bankPaperBottomRequestOfMove, hslot]

theorem pathStateOneValue_mem_componentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (component : BankPaperPathComponent slot) :
    R.pathStateOneValue slot component ∈
      R.pathComponentOccurrences slot component := by
  cases component with
  | inl source =>
      cases hslot : slot.2
      · simpa [pathStateOneValue, pathComponentOccurrences, hslot,
          BankOrdinaryPaperRealization.toStateValue,
          BankOrdinaryPaperRealization.requestOfSource,
          bankOrdinaryPaperRequestPool, bankSignedSlotOrientation] using
          R.ordinary.occurrenceValue_mem_componentOccurrences
            (BankOrdinaryPaperRealization.requestOfSource slot source)
            .targetState
      · simpa [pathStateOneValue, pathComponentOccurrences, hslot,
          BankOrdinaryPaperRealization.toStateValue,
          BankOrdinaryPaperRealization.requestOfSource,
          bankOrdinaryPaperRequestPool, bankSignedSlotOrientation] using
          R.ordinary.occurrenceValue_mem_componentOccurrences
            (BankOrdinaryPaperRealization.requestOfSource slot source)
            .sourceState
  | inr move =>
      rw [pathComponentOccurrences,
        R.bottom.componentOccurrences_eq_states_insert_donor]
      cases hslot : slot.2 <;>
        simp [pathStateOneValue, BankBottomPaperRealization.toStateValue,
          bankSignedSlotOrientation, bankPaperBottomRequestOfMove, hslot]

/-- Different path components have disjoint actual occurrence sets, including
across the ordinary/bottom boundary. -/
theorem pathComponentOccurrences_disjoint
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    {component component' : BankPaperPathComponent slot}
    (hcomponent : component ≠ component') :
    Disjoint (R.pathComponentOccurrences slot component)
      (R.pathComponentOccurrences slot component') := by
  have hrequest :
      bankPaperPathComponentRequest slot component ≠
        bankPaperPathComponentRequest slot component' := by
    intro heq
    exact hcomponent (bankPaperPathComponentRequest_injective slot heq)
  cases component with
  | inl source =>
      cases component' with
      | inl source' =>
          apply R.ordinary.componentOccurrences_disjoint
          intro heq
          apply hrequest
          simpa only [bankPaperPathComponentRequest] using
            congrArg Sum.inr heq
      | inr move =>
          exact R.ordinaryComponent_disjoint_bottomComponent
            (BankOrdinaryPaperRealization.requestOfSource slot source)
            (bankPaperBottomRequestOfMove slot move)
  | inr move =>
      cases component' with
      | inl source =>
          exact (R.ordinaryComponent_disjoint_bottomComponent
            (BankOrdinaryPaperRealization.requestOfSource slot source)
            (bankPaperBottomRequestOfMove slot move)).symm
      | inr move' =>
          apply R.bottom.componentOccurrences_disjoint_of_request_ne
            R.ordinary.two_mul_n_le_M R.six_le_yNat
            R.three_mul_yNat_le_n
          intro heq
          apply hrequest
          have hrelevant :
              bankPaperBottomRelevantRequestOfMove slot move =
                bankPaperBottomRelevantRequestOfMove slot move' :=
            bankBottomRelevantRequestToPaperRequest_injective
              (by simpa only [
                bankBottomRelevantRequestToPaperRequest_ofMove] using heq)
          simpa only [bankPaperPathComponentRequest] using
            congrArg Sum.inl hrelevant

private theorem pathStateValue_injective_of_mem
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (state : BankPaperPathComponent slot → ℕ)
    (hstate : ∀ component, state component ∈
      R.pathComponentOccurrences slot component) :
    Function.Injective state := by
  intro component component' heq
  by_contra hcomponent
  have hdisjoint := R.pathComponentOccurrences_disjoint slot hcomponent
  apply (Finset.disjoint_left.mp hdisjoint) (hstate component)
  rw [heq]
  exact hstate component'

theorem pathStateZeroValue_injective
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    Function.Injective (R.pathStateZeroValue slot) :=
  R.pathStateValue_injective_of_mem slot _
    (R.pathStateZeroValue_mem_componentOccurrences slot)

theorem pathStateOneValue_injective
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    Function.Injective (R.pathStateOneValue slot) :=
  R.pathStateValue_injective_of_mem slot _
    (R.pathStateOneValue_mem_componentOccurrences slot)

/-- The two actual path states.  Each contains one endpoint per component and
contains neither bare markers nor donor-only occurrences. -/
def pathStateZero
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) : Finset ℕ :=
  indexedPathState (R.pathStateZeroValue slot)

def pathStateOne
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) : Finset ℕ :=
  indexedPathState (R.pathStateOneValue slot)

/-- The full actual component census, including states and donors but no bare
marker. -/
def pathComponentCensus
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) : Finset ℕ :=
  Finset.univ.biUnion (R.pathComponentOccurrences slot)

theorem pathStateZero_card
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    (R.pathStateZero slot).card = Fintype.card (BankPaperPathComponent slot) := by
  rw [pathStateZero, indexedPathState,
    Finset.card_image_of_injective _ (R.pathStateZeroValue_injective slot)]
  simp

theorem pathStateOne_card
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    (R.pathStateOne slot).card = Fintype.card (BankPaperPathComponent slot) := by
  rw [pathStateOne, indexedPathState,
    Finset.card_image_of_injective _ (R.pathStateOneValue_injective slot)]
  simp

theorem pathStateZero_subset_componentCensus
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.pathStateZero slot ⊆ R.pathComponentCensus slot := by
  intro occurrence hoccurrence
  rw [pathStateZero, indexedPathState, Finset.mem_image] at hoccurrence
  obtain ⟨component, _hcomponent, rfl⟩ := hoccurrence
  rw [pathComponentCensus, Finset.mem_biUnion]
  exact ⟨component, Finset.mem_univ _,
    R.pathStateZeroValue_mem_componentOccurrences slot component⟩

theorem pathStateOne_subset_componentCensus
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.pathStateOne slot ⊆ R.pathComponentCensus slot := by
  intro occurrence hoccurrence
  rw [pathStateOne, indexedPathState, Finset.mem_image] at hoccurrence
  obtain ⟨component, _hcomponent, rfl⟩ := hoccurrence
  rw [pathComponentCensus, Finset.mem_biUnion]
  exact ⟨component, Finset.mem_univ _,
    R.pathStateOneValue_mem_componentOccurrences slot component⟩

theorem pathComponentCensus_mem_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    {occurrence : ℕ}
    (hoccurrence : occurrence ∈ R.pathComponentCensus slot) :
    occurrence ∈ factorInterval n M := by
  rw [pathComponentCensus, Finset.mem_biUnion] at hoccurrence
  obtain ⟨component, _hcomponent, hvalue⟩ := hoccurrence
  cases component with
  | inl source =>
      exact R.ordinary.componentOccurrence_mem_factorInterval
        (BankOrdinaryPaperRealization.requestOfSource slot source) hvalue
  | inr move =>
      exact R.bottom.componentOccurrence_mem_factorInterval
        R.ordinary.two_mul_n_le_M
        (bankPaperBottomRequestOfMove slot move) hvalue

/-- The paired endpoints of every component have the same complete rough
signature. -/
theorem pathComponent_completeRoughSignature_eq
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (component : BankPaperPathComponent slot) :
    completeRoughSignature (yNat n) (R.pathStateZeroValue slot component) =
      completeRoughSignature (yNat n) (R.pathStateOneValue slot component) := by
  cases component with
  | inl source =>
      have hsignature :=
        (R.ordinary.state_donor_completeRoughSignature_eq
          (BankOrdinaryPaperRealization.requestOfSource slot source)).1
      cases hslot : slot.2
      · simpa [pathStateZeroValue, pathStateOneValue,
          BankOrdinaryPaperRealization.fromStateValue,
          BankOrdinaryPaperRealization.toStateValue,
          BankOrdinaryPaperRealization.requestOfSource,
          bankOrdinaryPaperRequestPool, bankSignedSlotOrientation, hslot] using
          hsignature
      · simpa [pathStateZeroValue, pathStateOneValue,
          BankOrdinaryPaperRealization.fromStateValue,
          BankOrdinaryPaperRealization.toStateValue,
          BankOrdinaryPaperRealization.requestOfSource,
          bankOrdinaryPaperRequestPool, bankSignedSlotOrientation, hslot] using
          hsignature.symm
  | inr move =>
      let request := bankPaperBottomRequestOfMove slot move
      have hlower := R.bottom.occurrenceValue_completeRoughSignature
        R.six_le_yNat request .lowerState
      have hupper := R.bottom.occurrenceValue_completeRoughSignature
        R.six_le_yNat request .upperState
      have hstates :
          completeRoughSignature (yNat n)
              (R.bottom.lowerStateFactor request) =
            completeRoughSignature (yNat n)
              (R.bottom.upperStateFactor request) := by
        simpa only [BankBottomPaperRealization.occurrenceValue_lowerState,
          BankBottomPaperRealization.occurrenceValue_upperState] using
            hlower.trans hupper.symm
      cases hslot : slot.2
      · simpa [pathStateZeroValue, pathStateOneValue,
          BankBottomPaperRealization.fromStateValue,
          BankBottomPaperRealization.toStateValue, bankSignedSlotOrientation,
          bankPaperBottomRequestOfMove, request, hslot] using
          hstates.symm
      · simpa [pathStateZeroValue, pathStateOneValue,
          BankBottomPaperRealization.fromStateValue,
          BankBottomPaperRealization.toStateValue, bankSignedSlotOrientation,
          bankPaperBottomRequestOfMove, request, hslot] using
          hstates

/-- Exact equality of every complete-signature row multiplicity in the two
full path states. -/
theorem path_completeSignatureMultiplicity_eq
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (signature : ℕ →₀ ℕ) :
    completeSignatureMultiplicity (yNat n) (R.pathStateZero slot) signature =
      completeSignatureMultiplicity (yNat n) (R.pathStateOne slot) signature := by
  simpa only [pathStateZero, pathStateOne] using
    componentwise_signature_eq_implies_path_multiplicity_eq
      (yNat n) (R.pathStateZeroValue slot) (R.pathStateOneValue slot)
      (R.pathStateZeroValue_injective slot)
      (R.pathStateOneValue_injective slot)
      (R.pathComponent_completeRoughSignature_eq slot) signature

/-- Actual valuation change of the complete realized path. -/
def realizedFullPathChange
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) : BankVector ℕ :=
  ∑ component : BankPaperPathComponent slot,
    factorMoveChange (R.pathStateZeroValue slot component)
      (R.pathStateOneValue slot component)

theorem realizedFullPathChange_eq_ordinary_add_bottom
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.realizedFullPathChange slot =
      R.ordinary.realizedSlotChange slot +
        R.bottom.realizedSlotChange slot := by
  rw [realizedFullPathChange, Fintype.sum_sum_type]
  congr 1
  calc
      (∑ move : ↑(bankBottomRelevantMoves slot.1.1),
          factorMoveChange
            (R.pathStateZeroValue slot (Sum.inr move))
            (R.pathStateOneValue slot (Sum.inr move))) =
          ∑ move : ↑(bankBottomRelevantMoves slot.1.1),
            R.bottom.realizedComponentChange
              (bankBottomPaperRequestOfMove slot move.1) := by
                apply Finset.sum_congr rfl
                intro move _hmove
                rfl
      _ = ∑ move ∈ bankBottomRelevantMoves slot.1.1,
          R.bottom.realizedComponentChange
            (bankBottomPaperRequestOfMove slot move) := by
              simpa only using
                (Finset.sum_attach (bankBottomRelevantMoves slot.1.1)
                  (fun move ↦ R.bottom.realizedComponentChange
                    (bankBottomPaperRequestOfMove slot move)))
      _ = R.bottom.realizedSlotChange slot := rfl

/-- Uniform signed unit represented by a full path: downward slots contribute
`-e_p`, and reversed slots contribute `+e_p`. -/
def signedFullPathChange
    {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    BankVector ℕ :=
  match slot.2 with
  | .inl _copy => -coordinateUnit slot.1.1
  | .inr _copy => coordinateUnit slot.1.1

/-- The actual ordinary and truncated-bottom components telescope exactly to
the signed unit at the slot's source prime, including the exceptional source
primes two and three. -/
theorem realizedFullPathChange_eq_signedUnit
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.realizedFullPathChange slot = signedFullPathChange slot := by
  rw [R.realizedFullPathChange_eq_ordinary_add_bottom]
  let p := slot.1.1
  have hp : p.Prime := bankRoundingPrimeSupport_prime slot.1.property
  by_cases hp5 : 5 ≤ p
  · rw [R.ordinary.realizedSlotChange_eq_signedPrimeToFiveChange slot hp5,
      R.bottom.realizedSlotChange_eq_signedUnit_five_of_five_le slot hp5]
    cases hslot : slot.2
    · simp only [BankOrdinaryPaperRealization.signedPrimeToFiveChange,
        signedFullPathChange, hslot]
      funext q
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, coordinateUnit]
      ring
    · simp only [BankOrdinaryPaperRealization.signedPrimeToFiveChange,
        signedFullPathChange, hslot]
      funext q
      simp only [Pi.add_apply, Pi.sub_apply, coordinateUnit]
      ring
  · have hpTwo : 2 ≤ p := hp.two_le
    have hpLt : p < 5 := by omega
    have hpCases : p = 2 ∨ p = 3 := by
      interval_cases p
      · exact Or.inl rfl
      · exact Or.inr rfl
      · norm_num at hp
    have hordZero : R.ordinary.realizedSlotChange slot = 0 := by
      rw [R.ordinary.realizedSlotChange_eq_signedFinitePathChange]
      have hsources : bankOrdinaryCoreSources p = ∅ :=
        bankOrdinaryCoreSources_of_le_five (by omega)
      have hfinite : bankOrdinaryFinitePathChange p = 0 := by
        simp [bankOrdinaryFinitePathChange, hsources]
      cases hslot : slot.2 <;>
        simp [BankOrdinaryPaperRealization.signedFinitePathChange,
          p, hfinite, hslot]
    rw [hordZero, zero_add]
    rcases hpCases with hpTwoEq | hpThreeEq
    · have hprime : slot.1.1 = 2 := by simpa only [p] using hpTwoEq
      rw [R.bottom.realizedSlotChange_eq_signedUnit_two slot hprime]
      cases hslot : slot.2 <;>
        simp [signedFullPathChange, hprime, hslot]
    · have hprime : slot.1.1 = 3 := by simpa only [p] using hpThreeEq
      rw [R.bottom.realizedSlotChange_eq_signedUnit_three slot hprime]
      cases hslot : slot.2 <;>
        simp [signedFullPathChange, hprime, hslot]

end BankPaperRealization

end

end Erdos390.WholePaper
