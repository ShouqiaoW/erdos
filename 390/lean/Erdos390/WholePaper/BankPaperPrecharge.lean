import Erdos390.WholePaper.BankPaperComponents
import Erdos390.WholePaper.BankPaperAnchorChangeBudget

/-!
# The actual precharged bank state

This module is independent of the eventual path selector.  Its component
index is the already realized global request type: every relevant bottom row
and every ordinary row occurs exactly once.  For each component we expose its
orientation-aware base and alternate states and its actual donor occurrence.

The proofs below use only the explicit component geometry.  In particular,
there is no abstract capacity or compatibility hypothesis: global
injectivity follows from the realized occurrence-set disjointness, and the
donor tail is the literal interval `(2n,M]`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-- The two state endpoints of a precharged component. -/
inductive BankPaperPrechargeEndpoint where
  | base
  | alternate
  deriving DecidableEq, Fintype

namespace BankBottomPaperRealization

/-- Every actual bottom donor is in the strict tail above `2n`. -/
theorem two_mul_n_lt_donorFactor
    {n M : ℕ} (R : BankBottomPaperRealization n M)
    (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) :
    2 * n < R.donorFactor request := by
  have hrow := R.marker_mem_row hTwoN request
  cases hmove : R.move request <;>
    simp only [hmove, bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc, donorFactor,
      bankBottomDonor, bankBottomDonorMultiplier] at hrow ⊢ <;> omega

end BankBottomPaperRealization

namespace BankPaperRealization

local instance bankPaperMarkerRequestDecidableEq (n : ℕ) :
    DecidableEq (BankPaperMarkerRequest n) :=
  Classical.decEq _

/-! ## Global component data -/

/-- Orientation-aware state occupied before the component move. -/
def prechargeBaseStateValue
    {n M : ℕ} (R : BankPaperRealization n M) :
    BankPaperMarkerRequest n → ℕ
  | .inl request =>
      R.bottom.fromStateValue
        (bankBottomRelevantRequestToPaperRequest request)
  | .inr request => R.ordinary.fromStateValue request

/-- Orientation-aware state occupied after the component move. -/
def prechargeAlternateStateValue
    {n M : ℕ} (R : BankPaperRealization n M) :
    BankPaperMarkerRequest n → ℕ
  | .inl request =>
      R.bottom.toStateValue
        (bankBottomRelevantRequestToPaperRequest request)
  | .inr request => R.ordinary.toStateValue request

/-- The actual donor occurrence backing a component. -/
def prechargeDonorValue
    {n M : ℕ} (R : BankPaperRealization n M) :
    BankPaperMarkerRequest n → ℕ
  | .inl request =>
      R.bottom.donorFactor
        (bankBottomRelevantRequestToPaperRequest request)
  | .inr request => R.ordinary.donorValue request

/-- The actual state/donor occurrences belonging to a component.  Bottom
terminal rows retain donor=upper as one `Finset` occurrence. -/
def prechargeComponentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M) :
    BankPaperMarkerRequest n → Finset ℕ
  | .inl request =>
      R.bottom.componentOccurrences
        (bankBottomRelevantRequestToPaperRequest request)
  | .inr request => R.ordinary.componentOccurrences request

theorem prechargeBaseStateValue_mem_componentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeBaseStateValue request ∈
      R.prechargeComponentOccurrences request := by
  cases request with
  | inl request =>
      let fullRequest := bankBottomRelevantRequestToPaperRequest request
      rw [prechargeBaseStateValue, prechargeComponentOccurrences,
        R.bottom.componentOccurrences_eq_states_insert_donor]
      cases horientation : bankSignedSlotOrientation fullRequest.1.1 <;>
        simp [BankBottomPaperRealization.fromStateValue,
          fullRequest, horientation]
  | inr request =>
      cases horientation :
          (bankOrdinaryPaperRequestPool n request.1).2
      · simpa only [prechargeBaseStateValue,
          prechargeComponentOccurrences,
          BankOrdinaryPaperRealization.fromStateValue, horientation,
          BankOrdinaryPaperRealization.occurrenceValue_sourceState] using
          R.ordinary.occurrenceValue_mem_componentOccurrences
            request .sourceState
      · simpa only [prechargeBaseStateValue,
          prechargeComponentOccurrences,
          BankOrdinaryPaperRealization.fromStateValue, horientation,
          BankOrdinaryPaperRealization.occurrenceValue_targetState] using
          R.ordinary.occurrenceValue_mem_componentOccurrences
            request .targetState

theorem prechargeAlternateStateValue_mem_componentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeAlternateStateValue request ∈
      R.prechargeComponentOccurrences request := by
  cases request with
  | inl request =>
      let fullRequest := bankBottomRelevantRequestToPaperRequest request
      rw [prechargeAlternateStateValue, prechargeComponentOccurrences,
        R.bottom.componentOccurrences_eq_states_insert_donor]
      cases horientation : bankSignedSlotOrientation fullRequest.1.1 <;>
        simp [BankBottomPaperRealization.toStateValue,
          fullRequest, horientation]
  | inr request =>
      cases horientation :
          (bankOrdinaryPaperRequestPool n request.1).2
      · simpa only [prechargeAlternateStateValue,
          prechargeComponentOccurrences,
          BankOrdinaryPaperRealization.toStateValue, horientation,
          BankOrdinaryPaperRealization.occurrenceValue_targetState] using
          R.ordinary.occurrenceValue_mem_componentOccurrences
            request .targetState
      · simpa only [prechargeAlternateStateValue,
          prechargeComponentOccurrences,
          BankOrdinaryPaperRealization.toStateValue, horientation,
          BankOrdinaryPaperRealization.occurrenceValue_sourceState] using
          R.ordinary.occurrenceValue_mem_componentOccurrences
            request .sourceState

theorem prechargeDonorValue_mem_componentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeDonorValue request ∈
      R.prechargeComponentOccurrences request := by
  cases request with
  | inl request =>
      rw [prechargeDonorValue, prechargeComponentOccurrences,
        R.bottom.componentOccurrences_eq_states_insert_donor]
      simp
  | inr request =>
      simpa only [prechargeDonorValue, prechargeComponentOccurrences,
        BankOrdinaryPaperRealization.occurrenceValue_donor] using
        R.ordinary.occurrenceValue_mem_componentOccurrences request .donor

/-- Actual occurrence sets of different global components are disjoint. -/
theorem prechargeComponentOccurrences_disjoint
    {n M : ℕ} (R : BankPaperRealization n M)
    {request request' : BankPaperMarkerRequest n}
    (hrequest : request ≠ request') :
    Disjoint (R.prechargeComponentOccurrences request)
      (R.prechargeComponentOccurrences request') := by
  cases request with
  | inl bottomRequest =>
      cases request' with
      | inl bottomRequest' =>
          apply R.bottom.componentOccurrences_disjoint_of_request_ne
            R.ordinary.two_mul_n_le_M R.six_le_yNat
            R.three_mul_yNat_le_n
          intro hfull
          apply hrequest
          apply congrArg Sum.inl
          exact bankBottomRelevantRequestToPaperRequest_injective hfull
      | inr ordinaryRequest =>
          exact (R.ordinaryComponent_disjoint_bottomComponent
            ordinaryRequest
            (bankBottomRelevantRequestToPaperRequest bottomRequest)).symm
  | inr ordinaryRequest =>
      cases request' with
      | inl bottomRequest =>
          exact R.ordinaryComponent_disjoint_bottomComponent
            ordinaryRequest
            (bankBottomRelevantRequestToPaperRequest bottomRequest)
      | inr ordinaryRequest' =>
          apply R.ordinary.componentOccurrences_disjoint
          intro hordinary
          exact hrequest (congrArg Sum.inr hordinary)

/-- Every named occurrence of every component lies in the factor interval. -/
theorem prechargeComponentOccurrence_mem_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) {occurrence : ℕ}
    (hoccurrence : occurrence ∈
      R.prechargeComponentOccurrences request) :
    occurrence ∈ factorInterval n M := by
  cases request with
  | inl request =>
      exact R.bottom.componentOccurrence_mem_factorInterval
        R.ordinary.two_mul_n_le_M
        (bankBottomRelevantRequestToPaperRequest request) hoccurrence
  | inr request =>
      exact R.ordinary.componentOccurrence_mem_factorInterval
        request hoccurrence

theorem prechargeBaseStateValue_mem_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeBaseStateValue request ∈ factorInterval n M :=
  R.prechargeComponentOccurrence_mem_factorInterval request
    (R.prechargeBaseStateValue_mem_componentOccurrences request)

theorem prechargeAlternateStateValue_mem_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeAlternateStateValue request ∈ factorInterval n M :=
  R.prechargeComponentOccurrence_mem_factorInterval request
    (R.prechargeAlternateStateValue_mem_componentOccurrences request)

theorem prechargeDonorValue_mem_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeDonorValue request ∈ factorInterval n M :=
  R.prechargeComponentOccurrence_mem_factorInterval request
    (R.prechargeDonorValue_mem_componentOccurrences request)

/-! ## Complete rough signatures -/

/-- Base, alternate, and donor are three tokens in one complete-signature
row.  In a terminal bottom row two of these numerical occurrences may agree. -/
theorem precharge_completeRoughSignature_eq
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n)
        (R.prechargeBaseStateValue request) =
        completeRoughSignature (yNat n)
          (R.prechargeAlternateStateValue request) ∧
      completeRoughSignature (yNat n)
          (R.prechargeAlternateStateValue request) =
        completeRoughSignature (yNat n)
          (R.prechargeDonorValue request) := by
  cases request with
  | inl request =>
      let fullRequest := bankBottomRelevantRequestToPaperRequest request
      have hlower := R.bottom.occurrenceValue_completeRoughSignature
        R.six_le_yNat fullRequest .lowerState
      have hupper := R.bottom.occurrenceValue_completeRoughSignature
        R.six_le_yNat fullRequest .upperState
      have hdonor := R.bottom.occurrenceValue_completeRoughSignature
        R.six_le_yNat fullRequest .donor
      have hlower' :
          completeRoughSignature (yNat n)
              (R.bottom.lowerStateFactor fullRequest) =
            completeRoughSignature (yNat n)
              (R.bottom.marker fullRequest) := by
        simpa only [BankBottomPaperRealization.occurrenceValue_lowerState]
          using hlower
      have hupper' :
          completeRoughSignature (yNat n)
              (R.bottom.upperStateFactor fullRequest) =
            completeRoughSignature (yNat n)
              (R.bottom.marker fullRequest) := by
        simpa only [BankBottomPaperRealization.occurrenceValue_upperState]
          using hupper
      have hdonor' :
          completeRoughSignature (yNat n)
              (R.bottom.donorFactor fullRequest) =
            completeRoughSignature (yNat n)
              (R.bottom.marker fullRequest) := by
        simpa only [BankBottomPaperRealization.occurrenceValue_donor]
          using hdonor
      cases horientation : bankSignedSlotOrientation fullRequest.1.1
      · simpa [prechargeBaseStateValue, prechargeAlternateStateValue,
          prechargeDonorValue, BankBottomPaperRealization.fromStateValue,
          BankBottomPaperRealization.toStateValue, fullRequest,
          horientation] using
          ⟨hupper'.trans hlower'.symm,
            hlower'.trans hdonor'.symm⟩
      · simpa [prechargeBaseStateValue, prechargeAlternateStateValue,
          prechargeDonorValue, BankBottomPaperRealization.fromStateValue,
          BankBottomPaperRealization.toStateValue, fullRequest,
          horientation] using
          ⟨hlower'.trans hupper'.symm,
            hupper'.trans hdonor'.symm⟩
  | inr request =>
      have hsignature :=
        R.ordinary.state_donor_completeRoughSignature_eq request
      cases horientation :
          (bankOrdinaryPaperRequestPool n request.1).2
      · simpa only [prechargeBaseStateValue,
          prechargeAlternateStateValue, prechargeDonorValue,
          BankOrdinaryPaperRealization.fromStateValue,
          BankOrdinaryPaperRealization.toStateValue, horientation] using
          hsignature
      · simpa only [prechargeBaseStateValue,
          prechargeAlternateStateValue, prechargeDonorValue,
          BankOrdinaryPaperRealization.fromStateValue,
          BankOrdinaryPaperRealization.toStateValue, horientation] using
          ⟨hsignature.1.symm,
            hsignature.1.trans hsignature.2⟩

theorem prechargeBase_donor_completeRoughSignature_eq
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n)
        (R.prechargeBaseStateValue request) =
      completeRoughSignature (yNat n)
        (R.prechargeDonorValue request) :=
  (R.precharge_completeRoughSignature_eq request).1.trans
    (R.precharge_completeRoughSignature_eq request).2

/-- Above the rough cutoff, a component's base token and its actual donor
have exactly the same prime exponent. -/
theorem prechargeBase_donor_factorization_eq_of_yNat_lt
    {n M p : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) (hp : yNat n < p) :
    (R.prechargeBaseStateValue request).factorization p =
      (R.prechargeDonorValue request).factorization p := by
  have hcoordinate := congrArg (fun signature : ℕ →₀ ℕ ↦ signature p)
    (R.prechargeBase_donor_completeRoughSignature_eq request)
  simpa only [completeRoughSignature_apply, if_pos hp] using hcoordinate

/-! ## Endpoint and donor injectivity -/

def prechargeEndpointValue
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    BankPaperPrechargeEndpoint → ℕ
  | .base => R.prechargeBaseStateValue request
  | .alternate => R.prechargeAlternateStateValue request

theorem prechargeEndpointValue_mem_componentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n)
    (endpoint : BankPaperPrechargeEndpoint) :
    R.prechargeEndpointValue request endpoint ∈
      R.prechargeComponentOccurrences request := by
  cases endpoint
  · exact R.prechargeBaseStateValue_mem_componentOccurrences request
  · exact R.prechargeAlternateStateValue_mem_componentOccurrences request

/-- Arbitrary state endpoints belonging to different components cannot
collide. -/
theorem prechargeEndpointValue_ne_of_request_ne
    {n M : ℕ} (R : BankPaperRealization n M)
    {request request' : BankPaperMarkerRequest n}
    (hrequest : request ≠ request')
    (endpoint endpoint' : BankPaperPrechargeEndpoint) :
    R.prechargeEndpointValue request endpoint ≠
      R.prechargeEndpointValue request' endpoint' := by
  intro heq
  have hdisjoint := R.prechargeComponentOccurrences_disjoint hrequest
  exact (Finset.disjoint_left.mp hdisjoint)
    (R.prechargeEndpointValue_mem_componentOccurrences request endpoint)
    (by
      rw [heq]
      exact R.prechargeEndpointValue_mem_componentOccurrences
        request' endpoint')

/-- A donor cannot collide with either state endpoint of a different
component. -/
theorem prechargeDonorValue_ne_endpointValue_of_request_ne
    {n M : ℕ} (R : BankPaperRealization n M)
    {request request' : BankPaperMarkerRequest n}
    (hrequest : request ≠ request')
    (endpoint' : BankPaperPrechargeEndpoint) :
    R.prechargeDonorValue request ≠
      R.prechargeEndpointValue request' endpoint' := by
  intro heq
  have hdisjoint := R.prechargeComponentOccurrences_disjoint hrequest
  exact (Finset.disjoint_left.mp hdisjoint)
    (R.prechargeDonorValue_mem_componentOccurrences request)
    (by
      rw [heq]
      exact R.prechargeEndpointValue_mem_componentOccurrences
        request' endpoint')

/-- The two endpoint states within one component are distinct. -/
theorem prechargeBaseStateValue_ne_alternateStateValue
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeBaseStateValue request ≠
      R.prechargeAlternateStateValue request := by
  cases request with
  | inl request =>
      let fullRequest := bankBottomRelevantRequestToPaperRequest request
      have hstates :=
        R.bottom.lowerStateFactor_ne_upperStateFactor fullRequest
      cases horientation : bankSignedSlotOrientation fullRequest.1.1
      · simpa [prechargeBaseStateValue, prechargeAlternateStateValue,
          BankBottomPaperRealization.fromStateValue,
          BankBottomPaperRealization.toStateValue,
          fullRequest, horientation] using hstates.symm
      · simpa [prechargeBaseStateValue, prechargeAlternateStateValue,
          BankBottomPaperRealization.fromStateValue,
          BankBottomPaperRealization.toStateValue,
          fullRequest, horientation] using hstates
  | inr request =>
      have hstates := R.ordinary.targetStateValue_lt_sourceStateValue request
      cases horientation :
          (bankOrdinaryPaperRequestPool n request.1).2
      · simpa only [prechargeBaseStateValue,
          prechargeAlternateStateValue,
          BankOrdinaryPaperRealization.fromStateValue,
          BankOrdinaryPaperRealization.toStateValue, horientation] using
          (ne_of_gt hstates)
      · simpa only [prechargeBaseStateValue,
          prechargeAlternateStateValue,
          BankOrdinaryPaperRealization.fromStateValue,
          BankOrdinaryPaperRealization.toStateValue, horientation] using
          (ne_of_lt hstates)

/-- The globally indexed pair `(component, endpoint)` is recovered from its
actual state occurrence. -/
theorem prechargeStateOccurrence_injective
    {n M : ℕ} (R : BankPaperRealization n M) :
    Function.Injective
      (fun indexed : BankPaperMarkerRequest n ×
          BankPaperPrechargeEndpoint =>
        R.prechargeEndpointValue indexed.1 indexed.2) := by
  intro indexed indexed' heq
  rcases indexed with ⟨request, endpoint⟩
  rcases indexed' with ⟨request', endpoint'⟩
  by_cases hrequest : request = request'
  · subst request'
    have hendpoint : endpoint = endpoint' := by
      cases endpoint <;> cases endpoint'
      · rfl
      · have hvalue : R.prechargeBaseStateValue request =
            R.prechargeAlternateStateValue request := by
          simpa only [prechargeEndpointValue] using heq
        exact (R.prechargeBaseStateValue_ne_alternateStateValue request
          hvalue).elim
      · have hvalue : R.prechargeBaseStateValue request =
            R.prechargeAlternateStateValue request := by
          simpa only [prechargeEndpointValue] using heq.symm
        exact (R.prechargeBaseStateValue_ne_alternateStateValue request
          hvalue).elim
      · rfl
    subst endpoint'
    rfl
  · exact (R.prechargeEndpointValue_ne_of_request_ne
      hrequest endpoint endpoint' heq).elim

theorem prechargeBaseStateValue_injective
    {n M : ℕ} (R : BankPaperRealization n M) :
    Function.Injective R.prechargeBaseStateValue := by
  intro request request' heq
  by_contra hrequest
  exact R.prechargeEndpointValue_ne_of_request_ne
    hrequest .base .base heq

theorem prechargeAlternateStateValue_injective
    {n M : ℕ} (R : BankPaperRealization n M) :
    Function.Injective R.prechargeAlternateStateValue := by
  intro request request' heq
  by_contra hrequest
  exact R.prechargeEndpointValue_ne_of_request_ne
    hrequest .alternate .alternate heq

/-- Donors are globally injective even though, within a terminal bottom
component, the donor is literally the same occurrence as one endpoint. -/
theorem prechargeDonorValue_injective
    {n M : ℕ} (R : BankPaperRealization n M) :
    Function.Injective R.prechargeDonorValue := by
  intro request request' heq
  by_contra hrequest
  have hdisjoint := R.prechargeComponentOccurrences_disjoint hrequest
  exact (Finset.disjoint_left.mp hdisjoint)
    (R.prechargeDonorValue_mem_componentOccurrences request)
    (by
      rw [heq]
      exact R.prechargeDonorValue_mem_componentOccurrences request')

/-- In a terminal bottom row the donor is not a second tagged token: it is
literally whichever orientation-aware endpoint is the upper state. -/
theorem prechargeBottomTerminalDonor_eq_endpoint
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : ↑(bankBottomRelevantPaperRequests n))
    (hmove : R.bottom.move
        (bankBottomRelevantRequestToPaperRequest request) = .threeToTwo ∨
      R.bottom.move
        (bankBottomRelevantRequestToPaperRequest request) = .twoToOne) :
    R.prechargeDonorValue (.inl request) =
        R.prechargeBaseStateValue (.inl request) ∨
      R.prechargeDonorValue (.inl request) =
        R.prechargeAlternateStateValue (.inl request) := by
  let fullRequest := bankBottomRelevantRequestToPaperRequest request
  change R.bottom.move fullRequest = .threeToTwo ∨
    R.bottom.move fullRequest = .twoToOne at hmove
  have hdonor :=
    R.bottom.donorFactor_eq_upperStateFactor_of_terminalMove
      fullRequest hmove
  cases horientation : bankSignedSlotOrientation fullRequest.1.1
  · left
    simpa [prechargeDonorValue, prechargeBaseStateValue,
      BankBottomPaperRealization.fromStateValue,
      fullRequest, horientation] using hdonor
  · right
    simpa [prechargeDonorValue, prechargeAlternateStateValue,
      BankBottomPaperRealization.toStateValue,
      fullRequest, horientation] using hdonor

/-! ## Literal finite states, donor tail, and replacement map -/

def prechargeBaseState
    {n M : ℕ} (R : BankPaperRealization n M) : Finset ℕ :=
  indexedPathState R.prechargeBaseStateValue

def prechargeAlternateState
    {n M : ℕ} (R : BankPaperRealization n M) : Finset ℕ :=
  indexedPathState R.prechargeAlternateStateValue

def prechargeDonorSet
    {n M : ℕ} (R : BankPaperRealization n M) : Finset ℕ :=
  indexedPathState R.prechargeDonorValue

@[simp] theorem prechargeBaseStateValue_mem_prechargeBaseState
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeBaseStateValue request ∈ R.prechargeBaseState := by
  simp [prechargeBaseState, indexedPathState]

@[simp] theorem prechargeAlternateStateValue_mem_prechargeAlternateState
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeAlternateStateValue request ∈
      R.prechargeAlternateState := by
  simp [prechargeAlternateState, indexedPathState]

@[simp] theorem prechargeDonorValue_mem_prechargeDonorSet
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeDonorValue request ∈ R.prechargeDonorSet := by
  simp [prechargeDonorSet, indexedPathState]

theorem prechargeBaseState_card
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeBaseState.card =
      Fintype.card (BankPaperMarkerRequest n) := by
  rw [prechargeBaseState, indexedPathState,
    Finset.card_image_of_injective _ R.prechargeBaseStateValue_injective]
  simp

theorem prechargeAlternateState_card
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeAlternateState.card =
      Fintype.card (BankPaperMarkerRequest n) := by
  rw [prechargeAlternateState, indexedPathState,
    Finset.card_image_of_injective _
      R.prechargeAlternateStateValue_injective]
  simp

theorem prechargeDonorSet_card
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeDonorSet.card =
      Fintype.card (BankPaperMarkerRequest n) := by
  rw [prechargeDonorSet, indexedPathState,
    Finset.card_image_of_injective _ R.prechargeDonorValue_injective]
  simp

/-- The two global endpoint sets are disjoint, including the endpoints of the
same component. -/
theorem prechargeBaseState_disjoint_prechargeAlternateState
    {n M : ℕ} (R : BankPaperRealization n M) :
    Disjoint R.prechargeBaseState R.prechargeAlternateState := by
  rw [Finset.disjoint_left]
  intro value hbase halternate
  rw [prechargeBaseState, indexedPathState, Finset.mem_image] at hbase
  rw [prechargeAlternateState, indexedPathState,
    Finset.mem_image] at halternate
  obtain ⟨request, _hrequest, hbaseValue⟩ := hbase
  obtain ⟨request', _hrequest', halternateValue⟩ := halternate
  have heq : R.prechargeBaseStateValue request =
      R.prechargeAlternateStateValue request' :=
    hbaseValue.trans halternateValue.symm
  by_cases hrequestEq : request = request'
  · subst request'
    exact R.prechargeBaseStateValue_ne_alternateStateValue request heq
  · exact R.prechargeEndpointValue_ne_of_request_ne
      hrequestEq .base .alternate heq

theorem prechargeBaseState_subset_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeBaseState ⊆ factorInterval n M := by
  intro value hvalue
  rw [prechargeBaseState, indexedPathState, Finset.mem_image] at hvalue
  obtain ⟨request, _hrequest, rfl⟩ := hvalue
  exact R.prechargeBaseStateValue_mem_factorInterval request

theorem prechargeAlternateState_subset_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeAlternateState ⊆ factorInterval n M := by
  intro value hvalue
  rw [prechargeAlternateState, indexedPathState, Finset.mem_image] at hvalue
  obtain ⟨request, _hrequest, rfl⟩ := hvalue
  exact R.prechargeAlternateStateValue_mem_factorInterval request

/-- Every donor, ordinary or bottom, is an actual factor in `(2n,M]`. -/
theorem prechargeDonorValue_mem_tail
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeDonorValue request ∈ Finset.Ioc (2 * n) M := by
  cases request with
  | inl request =>
      let fullRequest := bankBottomRelevantRequestToPaperRequest request
      have hlower := R.bottom.two_mul_n_lt_donorFactor
        R.ordinary.two_mul_n_le_M fullRequest
      have hupper : R.bottom.donorFactor fullRequest ≤ M := by
        have hdata : n < R.bottom.donorFactor fullRequest ∧
            R.bottom.donorFactor fullRequest ≤ M := by
          simpa only [factorInterval, Finset.mem_Ioc] using
            (R.bottom.states_donor_mem_factorInterval
              R.ordinary.two_mul_n_le_M fullRequest).2.2
        exact hdata.2
      simpa only [prechargeDonorValue, fullRequest,
        Finset.mem_Ioc] using And.intro hlower hupper
  | inr request =>
      have hlower := R.ordinary.two_mul_n_lt_donorValue request
      have hupper : R.ordinary.donorValue request ≤ M := by
        have hdata : n < R.ordinary.donorValue request ∧
            R.ordinary.donorValue request ≤ M := by
          simpa only [factorInterval, Finset.mem_Ioc] using
            (R.ordinary.donorValue_mem_factorInterval request)
        exact hdata.2
      simpa only [prechargeDonorValue, Finset.mem_Ioc] using
        And.intro hlower hupper

theorem prechargeDonorSet_subset_tail
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeDonorSet ⊆ Finset.Ioc (2 * n) M := by
  intro donor hdonor
  rw [prechargeDonorSet, indexedPathState, Finset.mem_image] at hdonor
  obtain ⟨request, _hrequest, rfl⟩ := hdonor
  exact R.prechargeDonorValue_mem_tail request

/-- At the literal endpoint `upperEndpoint n h`, the product of all actual
bank donors divides the central tail product. -/
theorem prechargeDonorSet_prod_dvd_centralTailProduct
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h)) :
    R.prechargeDonorSet.prod id ∣ centralTailProduct n h := by
  change R.prechargeDonorSet.prod id ∣
    (Finset.Ioc (2 * n) (upperEndpoint n h)).prod id
  exact Finset.prod_dvd_prod_of_subset
    R.prechargeDonorSet (Finset.Ioc (2 * n) (upperEndpoint n h)) id
      R.prechargeDonorSet_subset_tail

theorem prechargeDonor_existsUnique_request
    {n M donor : ℕ} (R : BankPaperRealization n M)
    (hdonor : donor ∈ R.prechargeDonorSet) :
    ∃! request : BankPaperMarkerRequest n,
      R.prechargeDonorValue request = donor := by
  rw [prechargeDonorSet, indexedPathState, Finset.mem_image] at hdonor
  obtain ⟨request, _hrequest, hvalue⟩ := hdonor
  refine ⟨request, hvalue, ?_⟩
  intro request' hvalue'
  exact R.prechargeDonorValue_injective
    (hvalue'.trans hvalue.symm)

def requestForPrechargeDonor
    {n M : ℕ} (R : BankPaperRealization n M)
    (donor : ↑R.prechargeDonorSet) : BankPaperMarkerRequest n :=
  Classical.choose (R.prechargeDonor_existsUnique_request donor.property)

@[simp] theorem prechargeDonorValue_requestForPrechargeDonor
    {n M : ℕ} (R : BankPaperRealization n M)
    (donor : ↑R.prechargeDonorSet) :
    R.prechargeDonorValue (R.requestForPrechargeDonor donor) = donor.1 :=
  (Classical.choose_spec
    (R.prechargeDonor_existsUnique_request donor.property)).1

theorem requestForPrechargeDonor_unique
    {n M : ℕ} (R : BankPaperRealization n M)
    (donor : ↑R.prechargeDonorSet)
    (request : BankPaperMarkerRequest n)
    (hdonor : R.prechargeDonorValue request = donor.1) :
    request = R.requestForPrechargeDonor donor := by
  exact R.prechargeDonorValue_injective
    (hdonor.trans
      (R.prechargeDonorValue_requestForPrechargeDonor donor).symm)

/-- Replace a donor token by the orientation-aware base token of its unique
component. -/
def prechargeDonorToBase
    {n M : ℕ} (R : BankPaperRealization n M) :
    ↑R.prechargeDonorSet → ↑R.prechargeBaseState :=
  fun donor =>
    ⟨R.prechargeBaseStateValue (R.requestForPrechargeDonor donor),
      R.prechargeBaseStateValue_mem_prechargeBaseState _⟩

theorem prechargeDonorToBase_injective
    {n M : ℕ} (R : BankPaperRealization n M) :
    Function.Injective R.prechargeDonorToBase := by
  intro donor donor' hbase
  have hrequest : R.requestForPrechargeDonor donor =
      R.requestForPrechargeDonor donor' :=
    R.prechargeBaseStateValue_injective
      (congrArg Subtype.val hbase)
  apply Subtype.ext
  calc
    donor.1 = R.prechargeDonorValue
        (R.requestForPrechargeDonor donor) :=
      (R.prechargeDonorValue_requestForPrechargeDonor donor).symm
    _ = R.prechargeDonorValue
        (R.requestForPrechargeDonor donor') := by rw [hrequest]
    _ = donor'.1 :=
      R.prechargeDonorValue_requestForPrechargeDonor donor'

theorem prechargeDonorToBase_surjective
    {n M : ℕ} (R : BankPaperRealization n M) :
    Function.Surjective R.prechargeDonorToBase := by
  intro base
  have hbaseMem := base.property
  change base.1 ∈ Finset.univ.image R.prechargeBaseStateValue at hbaseMem
  rw [Finset.mem_image] at hbaseMem
  obtain ⟨request, _hrequest, hbase⟩ := hbaseMem
  let donor : ↑R.prechargeDonorSet :=
    ⟨R.prechargeDonorValue request,
      R.prechargeDonorValue_mem_prechargeDonorSet request⟩
  refine ⟨donor, ?_⟩
  apply Subtype.ext
  have hrequestFor : R.requestForPrechargeDonor donor = request := by
    symm
    exact R.requestForPrechargeDonor_unique donor request rfl
  change R.prechargeBaseStateValue
      (R.requestForPrechargeDonor donor) = base.1
  rw [hrequestFor, hbase]

/-- The donor-to-base replacement is a literal bijection of actual finite
token sets. -/
def prechargeDonorBaseEquiv
    {n M : ℕ} (R : BankPaperRealization n M) :
    ↑R.prechargeDonorSet ≃ ↑R.prechargeBaseState :=
  Equiv.ofBijective R.prechargeDonorToBase
    ⟨R.prechargeDonorToBase_injective,
      R.prechargeDonorToBase_surjective⟩

theorem prechargeDonorToBase_completeRoughSignature
    {n M : ℕ} (R : BankPaperRealization n M)
    (donor : ↑R.prechargeDonorSet) :
    completeRoughSignature (yNat n)
        (R.prechargeDonorToBase donor).1 =
      completeRoughSignature (yNat n) donor.1 := by
  change completeRoughSignature (yNat n)
      (R.prechargeBaseStateValue (R.requestForPrechargeDonor donor)) =
    completeRoughSignature (yNat n) donor.1
  rw [← R.prechargeDonorValue_requestForPrechargeDonor donor]
  exact R.prechargeBase_donor_completeRoughSignature_eq
    (R.requestForPrechargeDonor donor)

/-! ## Component counts and the base product -/

def prechargeBaseStateProduct
    {n M : ℕ} (R : BankPaperRealization n M) : ℕ :=
  R.prechargeBaseState.prod id

theorem card_bankPaperMarkerRequest (n : ℕ) :
    Fintype.card (BankPaperMarkerRequest n) =
      (bankBottomRelevantPaperRequests n).card +
        (bankOrdinaryPaperRequests n).card := by
  change Fintype.card
      (↑(bankBottomRelevantPaperRequests n) ⊕
        ↑(bankOrdinaryPaperRequests n)) = _
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]

/-- The global component index has a realization-independent coarse bound.
The bottom contribution is a filtered subfamily of the full eight-row
request rectangle. -/
theorem card_bankPaperMarkerRequest_le_anchorMarkerBudget (n : ℕ) :
    Fintype.card (BankPaperMarkerRequest n) ≤
      bankPaperAnchorMarkerBudget n := by
  rw [card_bankPaperMarkerRequest, bankPaperAnchorMarkerBudget]
  have hbottom : (bankBottomRelevantPaperRequests n).card ≤
      8 * bankBottomPaperDemand n := by
    calc
      (bankBottomRelevantPaperRequests n).card ≤
          (bankBottomPaperRequests n).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 8 * bankBottomPaperDemand n :=
        card_bankBottomPaperRequests n
  omega

theorem prechargeComponentCount_le_anchorMarkerBudget
    {n M : ℕ} (_R : BankPaperRealization n M) :
    Fintype.card (BankPaperMarkerRequest n) ≤
      bankPaperAnchorMarkerBudget n := by
  exact card_bankPaperMarkerRequest_le_anchorMarkerBudget n

theorem prechargeBaseState_card_le_anchorMarkerBudget
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeBaseState.card ≤ bankPaperAnchorMarkerBudget n := by
  rw [R.prechargeBaseState_card]
  exact R.prechargeComponentCount_le_anchorMarkerBudget

/-- Exact product after forgetting the injective component labels. -/
theorem prechargeBaseStateProduct_eq_componentProduct
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeBaseStateProduct =
      ∏ request : BankPaperMarkerRequest n,
        R.prechargeBaseStateValue request := by
  rw [prechargeBaseStateProduct, prechargeBaseState, indexedPathState,
    Finset.prod_image (R.prechargeBaseStateValue_injective).injOn]
  simp

/-- Exact donor-set product after forgetting its injective component
labels. -/
theorem prechargeDonorSet_prod_eq_componentProduct
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeDonorSet.prod id =
      ∏ request : BankPaperMarkerRequest n,
        R.prechargeDonorValue request := by
  rw [prechargeDonorSet, indexedPathState,
    Finset.prod_image (R.prechargeDonorValue_injective).injOn]
  simp

/-- Replacing every actual donor by its base token preserves the valuation
of the full product at every prime above the rough cutoff. -/
theorem prechargeBaseStateProduct_factorization_eq_donorSet_prod
    {n M p : ℕ} (R : BankPaperRealization n M)
    (hp : yNat n < p) :
    (R.prechargeBaseStateProduct).factorization p =
      (R.prechargeDonorSet.prod id).factorization p := by
  have hbaseNe : ∀ request : BankPaperMarkerRequest n,
      R.prechargeBaseStateValue request ≠ 0 := by
    intro request
    have hinterval := R.prechargeBaseStateValue_mem_factorInterval request
    have hdata : n < R.prechargeBaseStateValue request ∧
        R.prechargeBaseStateValue request ≤ M := by
      simpa only [factorInterval, Finset.mem_Ioc] using hinterval
    omega
  have hdonorNe : ∀ request : BankPaperMarkerRequest n,
      R.prechargeDonorValue request ≠ 0 := by
    intro request
    have hinterval := R.prechargeDonorValue_mem_factorInterval request
    have hdata : n < R.prechargeDonorValue request ∧
        R.prechargeDonorValue request ≤ M := by
      simpa only [factorInterval, Finset.mem_Ioc] using hinterval
    omega
  have hbaseFactorization :
      (∏ request : BankPaperMarkerRequest n,
          R.prechargeBaseStateValue request).factorization p =
        ∑ request : BankPaperMarkerRequest n,
          (R.prechargeBaseStateValue request).factorization p :=
    Nat.factorization_prod_apply
      (fun request _hrequest ↦ hbaseNe request)
  have hdonorFactorization :
      (∏ request : BankPaperMarkerRequest n,
          R.prechargeDonorValue request).factorization p =
        ∑ request : BankPaperMarkerRequest n,
          (R.prechargeDonorValue request).factorization p :=
    Nat.factorization_prod_apply
      (fun request _hrequest ↦ hdonorNe request)
  rw [R.prechargeBaseStateProduct_eq_componentProduct,
    R.prechargeDonorSet_prod_eq_componentProduct,
    hbaseFactorization, hdonorFactorization]
  apply Finset.sum_congr rfl
  intro request _hrequest
  exact R.prechargeBase_donor_factorization_eq_of_yNat_lt request hp

/-- The number of globally indexed precharge components has the same coarse
`O(yNat²)` bound as the anchor-marker budget. -/
theorem prechargeComponentCount_isBigO_yNat_sq :
    (fun n : ℕ ↦ (Fintype.card (BankPaperMarkerRequest n) : ℝ))
      =O[atTop] (fun n : ℕ ↦ (yNat n : ℝ) ^ 2) := by
  have hbudget :
      (fun n : ℕ ↦ (Fintype.card (BankPaperMarkerRequest n) : ℝ))
        =O[atTop]
          (fun n : ℕ ↦ (bankPaperAnchorMarkerBudget n : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ Fintype.card (BankPaperMarkerRequest n)),
      Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ bankPaperAnchorMarkerBudget n), one_mul]
    exact_mod_cast card_bankPaperMarkerRequest_le_anchorMarkerBudget n
  exact hbudget.trans bankPaperAnchorMarkerBudget_isBigO_yNat_sq

/-- Uniform prime-by-prime valuation bound for the complete precharged base
product.  It is stated for every prime, hence in particular for every small
prime used by the central reserve. -/
theorem prechargeBaseStateProduct_factorization_le
    {n M ℓ : ℕ} (R : BankPaperRealization n M) (hℓ : ℓ.Prime) :
    (R.prechargeBaseStateProduct).factorization ℓ ≤
      Fintype.card (BankPaperMarkerRequest n) * Nat.log 2 M := by
  rw [prechargeBaseStateProduct, Nat.factorization_prod_apply]
  · calc
      (∑ value ∈ R.prechargeBaseState, value.factorization ℓ) ≤
          ∑ _value ∈ R.prechargeBaseState, Nat.log 2 M := by
        apply Finset.sum_le_sum
        intro value hvalue
        have hinterval := R.prechargeBaseState_subset_factorInterval hvalue
        have hintervalData : n < value ∧ value ≤ M := by
          simpa only [factorInterval, Finset.mem_Ioc] using hinterval
        have hvaluePos : 0 < value := by omega
        have hvalueLe : value ≤ M := hintervalData.2
        exact (factorization_le_log_of_pos_le
          hvaluePos hvalueLe hℓ).trans
            (Nat.log_anti_left Nat.one_lt_two hℓ.two_le)
      _ = R.prechargeBaseState.card * Nat.log 2 M := by simp
      _ = Fintype.card (BankPaperMarkerRequest n) * Nat.log 2 M := by
        rw [R.prechargeBaseState_card]
  · intro value hvalue
    have hinterval := R.prechargeBaseState_subset_factorInterval hvalue
    have hintervalData : n < value ∧ value ≤ M := by
      simpa only [factorInterval, Finset.mem_Ioc] using hinterval
    have hvaluePos : 0 < value :=
      lt_of_le_of_lt (Nat.zero_le n) hintervalData.1
    simpa only [id_eq] using hvaluePos.ne'

theorem prechargeBaseStateProduct_factorization_le_anchorMarkerBudget
    {n M ℓ : ℕ} (R : BankPaperRealization n M) (hℓ : ℓ.Prime) :
    (R.prechargeBaseStateProduct).factorization ℓ ≤
      bankPaperAnchorMarkerBudget n * Nat.log 2 M := by
  exact (R.prechargeBaseStateProduct_factorization_le hℓ).trans
    (Nat.mul_le_mul_right _ R.prechargeComponentCount_le_anchorMarkerBudget)

end BankPaperRealization

end

end Erdos390.WholePaper
