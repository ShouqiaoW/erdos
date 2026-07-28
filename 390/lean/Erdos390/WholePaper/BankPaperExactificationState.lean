import Erdos390.WholePaper.BankPaperPaths
import Erdos390.WholePaper.GuardedIntegralExactification

/-!
# The actual paper bank as a two-state exactification bank

`BankPaperPaths` orients a downward slot from state zero to state one, so its
change is `-e_p`; the generic exactification interface instead calls the
left-hand signed family `+e_p`.  We therefore pair each generic slot with the
actual slot of the opposite orientation.  Boolean state `false` remains the
paper's precharged path state zero and state `true` remains path state one.
This simultaneously aligns signs and keeps the base product equal to the
one reserved in the tail.  The file proves the required product change,
complete-row invariance, positivity, and pairwise cross-slot disjointness.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- Swap the two copies with the same prime and copy index. -/
def bankPaperOppositeSlot {P : Type*} {beta : P → ℕ} :
    SignedBankSlot beta → SignedBankSlot beta
  | ⟨p, .inl copy⟩ => ⟨p, .inr copy⟩
  | ⟨p, .inr copy⟩ => ⟨p, .inl copy⟩

@[simp] theorem bankPaperOppositeSlot_fst
    {P : Type*} {beta : P → ℕ} (slot : SignedBankSlot beta) :
    (bankPaperOppositeSlot slot).1 = slot.1 := by
  rcases slot with ⟨p, copy | copy⟩ <;> rfl

@[simp] theorem bankPaperOppositeSlot_involutive
    {P : Type*} {beta : P → ℕ} (slot : SignedBankSlot beta) :
    bankPaperOppositeSlot (bankPaperOppositeSlot slot) = slot := by
  rcases slot with ⟨p, copy | copy⟩ <;> rfl

theorem bankPaperOppositeSlot_injective
    {P : Type*} {beta : P → ℕ} :
    Function.Injective (bankPaperOppositeSlot (P := P) (beta := beta)) := by
  intro slot slot' heq
  have := congrArg bankPaperOppositeSlot heq
  simpa only [bankPaperOppositeSlot_involutive] using this

/-- The orientation swap as an explicit finite equivalence. -/
def bankPaperOppositeSlotEquiv {P : Type*} {beta : P → ℕ} :
    SignedBankSlot beta ≃ SignedBankSlot beta where
  toFun := bankPaperOppositeSlot
  invFun := bankPaperOppositeSlot
  left_inv := bankPaperOppositeSlot_involutive
  right_inv := bankPaperOppositeSlot_involutive

/-- Boolean state convention used by `guarded_integral_exactification`.
The opposite-orientation reindexing aligns signs while state `false` is still
the literal precharged base state. -/
def BankPaperRealization.exactificationState
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (selected : Bool) : Finset ℕ :=
  if selected then R.pathStateOne (bankPaperOppositeSlot slot)
  else R.pathStateZero (bankPaperOppositeSlot slot)

@[simp] theorem BankPaperRealization.exactificationState_false
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.exactificationState slot false =
      R.pathStateZero (bankPaperOppositeSlot slot) := by
  simp [BankPaperRealization.exactificationState]

@[simp] theorem BankPaperRealization.exactificationState_true
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.exactificationState slot true =
      R.pathStateOne (bankPaperOppositeSlot slot) := by
  simp [BankPaperRealization.exactificationState]

/-- Factorization of an injectively indexed positive path state is the sum
of the factorization vectors of its component values. -/
theorem integerValuationVector_indexedPathState_prod
    {C : Type*} [Fintype C] [DecidableEq C]
    (state : C → ℕ) (hstate : Function.Injective state)
    (hpositive : ∀ c, 0 < state c) :
    integerValuationVector ((indexedPathState state).prod id) =
      ∑ c : C, integerValuationVector (state c) := by
  classical
  funext p
  simp only [integerValuationVector, Finset.sum_apply]
  rw [Nat.factorization_prod_apply]
  · push_cast
    rw [indexedPathState, Finset.sum_image]
    rfl
    intro c _hc c' _hc' heq
    exact hstate heq
  · intro a ha
    obtain ⟨c, _hc, rfl⟩ := Finset.mem_image.mp ha
    exact (hpositive c).ne'

namespace BankPaperRealization

theorem pathStateZeroValue_pos
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (component : BankPaperPathComponent slot) :
    0 < R.pathStateZeroValue slot component := by
  have hmem := R.pathComponentCensus_mem_factorInterval slot
    (R.pathStateZero_subset_componentCensus slot
      (by
        rw [pathStateZero, indexedPathState]
        exact Finset.mem_image.mpr ⟨component, Finset.mem_univ _, rfl⟩))
  exact lt_of_le_of_lt (Nat.zero_le n) (Finset.mem_Ioc.mp hmem).1

theorem pathStateOneValue_pos
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (component : BankPaperPathComponent slot) :
    0 < R.pathStateOneValue slot component := by
  have hmem := R.pathComponentCensus_mem_factorInterval slot
    (R.pathStateOne_subset_componentCensus slot
      (by
        rw [pathStateOne, indexedPathState]
        exact Finset.mem_image.mpr ⟨component, Finset.mem_univ _, rfl⟩))
  exact lt_of_le_of_lt (Nat.zero_le n) (Finset.mem_Ioc.mp hmem).1

/-- Every factor in either Boolean state is an actual interval factor. -/
theorem exactificationState_subset_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) (selected : Bool) :
    R.exactificationState slot selected ⊆ factorInterval n M := by
  intro a ha
  apply R.pathComponentCensus_mem_factorInterval (bankPaperOppositeSlot slot)
  cases selected
  · exact R.pathStateZero_subset_componentCensus
      (bankPaperOppositeSlot slot)
      (by simpa only [exactificationState_false] using ha)
  · exact R.pathStateOne_subset_componentCensus
      (bankPaperOppositeSlot slot)
      (by simpa only [exactificationState_true] using ha)

theorem exactificationState_positive
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) (selected : Bool)
    {a : ℕ} (ha : a ∈ R.exactificationState slot selected) :
    0 < a := by
  have hinterval := R.exactificationState_subset_factorInterval
    slot selected ha
  exact lt_of_le_of_lt (Nat.zero_le n) (Finset.mem_Ioc.mp hinterval).1

/-- Swapping the slot orientation aligns the actual product change with the
generic signed-slot convention exactly. -/
theorem exactificationState_productChange
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    integerValuationVector ((R.exactificationState slot true).prod id) -
        integerValuationVector ((R.exactificationState slot false).prod id) =
      embeddedSignedBankSlotChange (fun p :
        ↑(bankRoundingPrimeSupport n) ↦ p.1) slot := by
  rw [R.exactificationState_true, R.exactificationState_false,
    pathStateZero, pathStateOne,
    integerValuationVector_indexedPathState_prod
      (R.pathStateOneValue (bankPaperOppositeSlot slot))
      (R.pathStateOneValue_injective (bankPaperOppositeSlot slot))
      (R.pathStateOneValue_pos (bankPaperOppositeSlot slot)),
    integerValuationVector_indexedPathState_prod
      (R.pathStateZeroValue (bankPaperOppositeSlot slot))
      (R.pathStateZeroValue_injective (bankPaperOppositeSlot slot))
      (R.pathStateZeroValue_pos (bankPaperOppositeSlot slot))]
  calc
    (∑ component : BankPaperPathComponent (bankPaperOppositeSlot slot),
          integerValuationVector
            (R.pathStateOneValue (bankPaperOppositeSlot slot) component)) -
        ∑ component : BankPaperPathComponent (bankPaperOppositeSlot slot),
          integerValuationVector
            (R.pathStateZeroValue (bankPaperOppositeSlot slot) component) =
      R.realizedFullPathChange (bankPaperOppositeSlot slot) := by
        rw [realizedFullPathChange]
        simp only [factorMoveChange]
        rw [← Finset.sum_sub_distrib]
    _ = signedFullPathChange (bankPaperOppositeSlot slot) := by
      rw [R.realizedFullPathChange_eq_signedUnit
        (bankPaperOppositeSlot slot)]
    _ = embeddedSignedBankSlotChange
        (fun p : ↑(bankRoundingPrimeSupport n) ↦ p.1) slot := by
      rcases slot with ⟨p, copy | copy⟩ <;>
        simp [bankPaperOppositeSlot, signedFullPathChange,
          embeddedSignedBankSlotChange]

/-- Both Boolean states have exactly the same complete rough-row counts. -/
theorem exactificationState_completeSignatureMultiplicity_eq
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (signature : ℕ →₀ ℕ) :
    completeSignatureMultiplicity (yNat n)
        (R.exactificationState slot false) signature =
      completeSignatureMultiplicity (yNat n)
        (R.exactificationState slot true) signature := by
  rw [R.exactificationState_false, R.exactificationState_true]
  exact R.path_completeSignatureMultiplicity_eq
    (bankPaperOppositeSlot slot) signature

/-- A request belonging to a path component recovers the signed slot. -/
theorem pathComponentRequest_ne_of_slot_ne
    {n M : ℕ} (_R : BankPaperRealization n M)
    {slot slot' : SignedBankSlot (bankRoundingBetaOnSupport n)}
    (hslot : slot ≠ slot')
    (component : BankPaperPathComponent slot)
    (component' : BankPaperPathComponent slot') :
    bankPaperPathComponentRequest slot component ≠
      bankPaperPathComponentRequest slot' component' := by
  intro hrequest
  apply hslot
  cases component with
  | inl source =>
      cases component' with
      | inl source' =>
          have hordinary :
              BankOrdinaryPaperRealization.requestOfSource slot source =
                BankOrdinaryPaperRealization.requestOfSource slot' source' := by
            simpa only [bankPaperPathComponentRequest, Sum.inr.injEq] using
              hrequest
          exact congrArg
            (fun request : ↑(bankOrdinaryPaperRequests n) ↦ request.1.1)
            hordinary
      | inr move => simp [bankPaperPathComponentRequest] at hrequest
  | inr move =>
      cases component' with
      | inl source => simp [bankPaperPathComponentRequest] at hrequest
      | inr move' =>
          have hbottom :
              bankPaperBottomRelevantRequestOfMove slot move =
                bankPaperBottomRelevantRequestOfMove slot' move' := by
            simpa only [bankPaperPathComponentRequest, Sum.inl.injEq] using
              hrequest
          exact congrArg
            (fun request : ↑(bankBottomRelevantPaperRequests n) ↦
              request.1.1) hbottom

/-- Actual occurrence sets of components belonging to different signed slots
are disjoint, including across the ordinary/bottom boundary. -/
theorem pathComponentOccurrences_disjoint_of_slot_ne
    {n M : ℕ} (R : BankPaperRealization n M)
    {slot slot' : SignedBankSlot (bankRoundingBetaOnSupport n)}
    (hslot : slot ≠ slot')
    (component : BankPaperPathComponent slot)
    (component' : BankPaperPathComponent slot') :
    Disjoint (R.pathComponentOccurrences slot component)
      (R.pathComponentOccurrences slot' component') := by
  have hrequest := R.pathComponentRequest_ne_of_slot_ne hslot
    component component'
  cases component with
  | inl source =>
      cases component' with
      | inl source' =>
          apply R.ordinary.componentOccurrences_disjoint
          intro heq
          apply hrequest
          simpa only [bankPaperPathComponentRequest] using congrArg Sum.inr heq
      | inr move =>
          exact R.ordinaryComponent_disjoint_bottomComponent
            (BankOrdinaryPaperRealization.requestOfSource slot source)
            (bankPaperBottomRequestOfMove slot' move)
  | inr move =>
      cases component' with
      | inl source =>
          exact (R.ordinaryComponent_disjoint_bottomComponent
            (BankOrdinaryPaperRealization.requestOfSource slot' source)
            (bankPaperBottomRequestOfMove slot move)).symm
      | inr move' =>
          apply R.bottom.componentOccurrences_disjoint_of_request_ne
            R.ordinary.two_mul_n_le_M R.six_le_yNat
            R.three_mul_yNat_le_n
          intro heq
          apply hrequest
          have hrelevant :
              bankPaperBottomRelevantRequestOfMove slot move =
                bankPaperBottomRelevantRequestOfMove slot' move' :=
            bankBottomRelevantRequestToPaperRequest_injective
              (by simpa only [
                bankBottomRelevantRequestToPaperRequest_ofMove] using heq)
          simpa only [bankPaperPathComponentRequest] using
            congrArg Sum.inl hrelevant

/-- Any choices of Boolean states in two different signed slots are
disjoint.  This is the exact `hcross` input of guarded exactification. -/
theorem exactificationState_disjoint_of_slot_ne
    {n M : ℕ} (R : BankPaperRealization n M)
    {slot slot' : SignedBankSlot (bankRoundingBetaOnSupport n)}
    (hslot : slot ≠ slot') (selected selected' : Bool) :
    Disjoint (R.exactificationState slot selected)
      (R.exactificationState slot' selected') := by
  rw [Finset.disjoint_left]
  intro a ha ha'
  have hOpposite :
      bankPaperOppositeSlot slot ≠ bankPaperOppositeSlot slot' :=
    fun heq ↦ hslot (bankPaperOppositeSlot_injective heq)
  have haCensus :
      a ∈ R.pathComponentCensus (bankPaperOppositeSlot slot) := by
    cases selected
    · exact R.pathStateZero_subset_componentCensus
        (bankPaperOppositeSlot slot)
        (by simpa only [exactificationState_false] using ha)
    · exact R.pathStateOne_subset_componentCensus
        (bankPaperOppositeSlot slot)
        (by simpa only [exactificationState_true] using ha)
  have haCensus' :
      a ∈ R.pathComponentCensus (bankPaperOppositeSlot slot') := by
    cases selected'
    · exact R.pathStateZero_subset_componentCensus
        (bankPaperOppositeSlot slot')
        (by simpa only [exactificationState_false] using ha')
    · exact R.pathStateOne_subset_componentCensus
        (bankPaperOppositeSlot slot')
        (by simpa only [exactificationState_true] using ha')
  rw [pathComponentCensus, Finset.mem_biUnion] at haCensus haCensus'
  obtain ⟨component, _hcomponent, haComponent⟩ := haCensus
  obtain ⟨component', _hcomponent', haComponent'⟩ := haCensus'
  exact (Finset.disjoint_left.mp
    (R.pathComponentOccurrences_disjoint_of_slot_ne hOpposite
      component component')) haComponent haComponent'

end BankPaperRealization

end

end Erdos390.WholePaper
