import Erdos390.WholePaper.BankBottomConcreteDemand
import Erdos390.WholePaper.BankRoughSignatures
import Erdos390.WholePaper.CentralCarryAnchors

/-!
# Actual bottom-bank components from the concrete marker matching

The capacity argument deliberately matches the rectangular upper-bound family
consisting of every signed slot and all four bottom rows.  The path belonging
to a small source prime does not use every one of those rows: source `3` uses
only `3→2→1`, and source `2` uses only `2→1`.  This file therefore separates
the full matched family from the literal relevant subfamily before forming any
set of used occurrences.

For every matched request we retain its actual prime marker, the two state
factors in the corresponding row, and its donor occurrence.  A finite set of
occurrence values is used, so in the last two rows the donor and the upper
state are literally one occurrence, rather than two tagged copies.  The only
global input is the already constructed injective marker matching.  All other
claims below are explicit interval, factorization, and large-prime arithmetic.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal relevant subfamily -/

/-- Source prime carried by a concrete bottom request. -/
def bankBottomPaperRequestPrime {n : ℕ}
    (request : BankBottomPaperRequest n) : ℕ :=
  request.1.1.1

theorem bankBottomPaperRequestPrime_prime {n : ℕ}
    (request : BankBottomPaperRequest n) :
    (bankBottomPaperRequestPrime request).Prime :=
  bankRoundingPrimeSupport_prime request.1.1.property

/-- The two small state cores in each displayed bottom row. -/
def bankBottomIncidentStateCores (move : BankBottomMove) : ℕ × ℕ :=
  (bankBottomLowerStateMultiplier move,
    bankBottomUpperStateMultiplier move)

@[simp] theorem bankBottomIncidentStateCores_fiveToFour :
    bankBottomIncidentStateCores .fiveToFour = (4, 5) := rfl

@[simp] theorem bankBottomIncidentStateCores_fourToThree :
    bankBottomIncidentStateCores .fourToThree = (3, 4) := rfl

@[simp] theorem bankBottomIncidentStateCores_threeToTwo :
    bankBottomIncidentStateCores .threeToTwo = (2, 3) := rfl

@[simp] theorem bankBottomIncidentStateCores_twoToOne :
    bankBottomIncidentStateCores .twoToOne = (2, 4) := rfl

/-- Relevance of one displayed row to a source prime. -/
def bankBottomMoveRelevantForPrime (prime : ℕ) : BankBottomMove → Prop
  | .fiveToFour => 5 ≤ prime
  | .fourToThree => 5 ≤ prime
  | .threeToTwo => 3 ≤ prime
  | .twoToOne => 2 ≤ prime

instance bankBottomMoveRelevantForPrime_decidable (prime : ℕ)
    (move : BankBottomMove) :
    Decidable (bankBottomMoveRelevantForPrime prime move) := by
  cases move <;> unfold bankBottomMoveRelevantForPrime <;> infer_instance

/-- The literal finite row set in the truncated bottom path. -/
def bankBottomRelevantMoves (prime : ℕ) : Finset BankBottomMove :=
  Finset.univ.filter (bankBottomMoveRelevantForPrime prime)

theorem bankBottomRelevantMoves_of_five_le
    {prime : ℕ} (hprime : 5 ≤ prime) :
    bankBottomRelevantMoves prime = Finset.univ := by
  ext move
  cases move <;>
    simp [bankBottomRelevantMoves, bankBottomMoveRelevantForPrime] <;> omega

/-- An explicit version of the preceding theorem, convenient when evaluating
the finite sum of all four bottom rows. -/
theorem bankBottomRelevantMoves_eq_allMoves_of_five_le
    {prime : ℕ} (hprime : 5 ≤ prime) :
    bankBottomRelevantMoves prime =
      {.fiveToFour, .fourToThree, .threeToTwo, .twoToOne} := by
  ext move
  cases move <;>
    simp [bankBottomRelevantMoves, bankBottomMoveRelevantForPrime] <;> omega

@[simp] theorem bankBottomRelevantMoves_three :
    bankBottomRelevantMoves 3 = {.threeToTwo, .twoToOne} := by
  ext move
  cases move <;>
    simp [bankBottomRelevantMoves, bankBottomMoveRelevantForPrime]

@[simp] theorem bankBottomRelevantMoves_two :
    bankBottomRelevantMoves 2 = {.twoToOne} := by
  ext move
  cases move <;>
    simp [bankBottomRelevantMoves, bankBottomMoveRelevantForPrime]

/-- A row is used precisely when it lies on the source prime's truncated
bottom path.  Thus primes at least five use all four rows, prime three uses
the last two, and prime two uses only the last row. -/
def bankBottomPaperRequestRelevant {n : ℕ}
    (request : BankBottomPaperRequest n) : Prop :=
  bankBottomMoveRelevantForPrime (bankBottomPaperRequestPrime request)
    request.2

instance bankBottomPaperRequestRelevant_decidable {n : ℕ}
    (request : BankBottomPaperRequest n) :
    Decidable (bankBottomPaperRequestRelevant request) := by
  unfold bankBottomPaperRequestRelevant
  infer_instance

theorem bankBottomPaperRequestRelevant_iff_mem_moves
    {n : ℕ} (request : BankBottomPaperRequest n) :
    bankBottomPaperRequestRelevant request ↔
      request.2 ∈ bankBottomRelevantMoves
        (bankBottomPaperRequestPrime request) := by
  simp [bankBottomPaperRequestRelevant, bankBottomRelevantMoves]

/-- The requests that really occur in their source prime's bottom path. -/
def bankBottomRelevantPaperRequests (n : ℕ) :
    Finset (BankBottomPaperRequest n) :=
  (bankBottomPaperRequests n).filter bankBottomPaperRequestRelevant

/-- Matched solely for the rectangular capacity upper bound, but not used in
the source prime's actual path. -/
def bankBottomUnusedPaperRequests (n : ℕ) :
    Finset (BankBottomPaperRequest n) :=
  (bankBottomPaperRequests n).filter
    (fun request ↦ ¬bankBottomPaperRequestRelevant request)

theorem bankBottom_relevant_unused_disjoint (n : ℕ) :
    Disjoint (bankBottomRelevantPaperRequests n)
      (bankBottomUnusedPaperRequests n) := by
  rw [Finset.disjoint_left]
  intro request hrelevant hunused
  exact (Finset.mem_filter.mp hunused).2
    (Finset.mem_filter.mp hrelevant).2

theorem bankBottom_relevant_union_unused (n : ℕ) :
    bankBottomRelevantPaperRequests n ∪ bankBottomUnusedPaperRequests n =
      bankBottomPaperRequests n := by
  unfold bankBottomRelevantPaperRequests bankBottomUnusedPaperRequests
  exact Finset.filter_union_filter_not_eq
    (p := fun request : BankBottomPaperRequest n ↦
      bankBottomPaperRequestRelevant request)
    (bankBottomPaperRequests n)

theorem bankBottomPaperRequestRelevant_of_five_le
    {n : ℕ} {request : BankBottomPaperRequest n}
    (hprime : 5 ≤ bankBottomPaperRequestPrime request) :
    bankBottomPaperRequestRelevant request := by
  cases hmove : request.2 <;>
    simp only [bankBottomPaperRequestRelevant, hmove,
      bankBottomMoveRelevantForPrime] <;> omega

theorem bankBottomPaperRequestRelevant_iff_of_prime_eq_three
    {n : ℕ} {request : BankBottomPaperRequest n}
    (hprime : bankBottomPaperRequestPrime request = 3) :
    bankBottomPaperRequestRelevant request ↔
      request.2 = .threeToTwo ∨ request.2 = .twoToOne := by
  cases hmove : request.2 <;>
    simp [bankBottomPaperRequestRelevant, hmove,
      bankBottomMoveRelevantForPrime, hprime]

theorem bankBottomPaperRequestRelevant_iff_of_prime_eq_two
    {n : ℕ} {request : BankBottomPaperRequest n}
    (hprime : bankBottomPaperRequestPrime request = 2) :
    bankBottomPaperRequestRelevant request ↔ request.2 = .twoToOne := by
  cases hmove : request.2 <;>
    simp [bankBottomPaperRequestRelevant, hmove,
      bankBottomMoveRelevantForPrime, hprime]

/-- Forget relevance while retaining membership in the full matched family. -/
def bankBottomRelevantRequestToPaperRequest {n : ℕ}
    (request : ↑(bankBottomRelevantPaperRequests n)) :
    ↑(bankBottomPaperRequests n) :=
  ⟨request.1, (Finset.mem_filter.mp request.property).1⟩

theorem bankBottomRelevantRequestToPaperRequest_injective {n : ℕ} :
    Function.Injective
      (bankBottomRelevantRequestToPaperRequest (n := n)) := by
  intro request request' heq
  apply Subtype.ext
  exact congrArg (fun x : ↑(bankBottomPaperRequests n) ↦ x.1) heq

/-! ## The deterministic truncated bottom path -/

/-- Valuation change of one downward bottom row.  The last row is represented
by its actual state factors `4P -> 2P`; after cancelling the common marker its
change is the paper's `2 -> 1` vector `-e_2`. -/
def bankBottomMoveChange (move : BankBottomMove) : BankVector ℕ :=
  factorMoveChange (bankBottomUpperStateMultiplier move)
    (bankBottomLowerStateMultiplier move)

@[simp] theorem bankBottomMoveChange_fiveToFour :
    bankBottomMoveChange .fiveToFour = bottomFiveToFourChange := by
  simpa [bankBottomMoveChange, bankBottomUpperStateMultiplier,
    bankBottomLowerStateMultiplier] using factorMoveChange_five_to_four

@[simp] theorem bankBottomMoveChange_fourToThree :
    bankBottomMoveChange .fourToThree = bottomFourToThreeChange := by
  simpa [bankBottomMoveChange, bankBottomUpperStateMultiplier,
    bankBottomLowerStateMultiplier] using factorMoveChange_four_to_three

@[simp] theorem bankBottomMoveChange_threeToTwo :
    bankBottomMoveChange .threeToTwo = bottomThreeToTwoChange := by
  simpa [bankBottomMoveChange, bankBottomUpperStateMultiplier,
    bankBottomLowerStateMultiplier] using factorMoveChange_three_to_two

theorem factorMoveChange_four_to_two :
    factorMoveChange 4 2 = bottomTwoToOneChange := by
  have htwo : Nat.Prime 2 := by norm_num
  rw [factorMoveChange, show 4 = 2 ^ 2 by norm_num,
    integerValuationVector_prime_pow htwo,
    integerValuationVector_prime htwo,
    bottomTwoToOneChange]
  abel

@[simp] theorem bankBottomMoveChange_twoToOne :
    bankBottomMoveChange .twoToOne = bottomTwoToOneChange := by
  simpa [bankBottomMoveChange, bankBottomUpperStateMultiplier,
    bankBottomLowerStateMultiplier] using factorMoveChange_four_to_two

/-- The unsigned downward change obtained by traversing exactly the bottom
rows relevant to `prime`.  Padding requests from the rectangular matching do
not occur in this sum. -/
def bankBottomPathChange (prime : ℕ) : BankVector ℕ :=
  ∑ move ∈ bankBottomRelevantMoves prime, bankBottomMoveChange move

theorem bankBottomPathChange_eq_neg_unit_five_of_five_le
    {prime : ℕ} (hprime : 5 ≤ prime) :
    bankBottomPathChange prime = -coordinateUnit 5 := by
  calc
    bankBottomPathChange prime = fourBottomMovesChange := by
      rw [bankBottomPathChange,
        bankBottomRelevantMoves_eq_allMoves_of_five_le hprime]
      simp [fourBottomMovesChange]; abel
    _ = -coordinateUnit 5 := fourBottomMovesChange_eq_neg_unit_five

@[simp] theorem bankBottomPathChange_three :
    bankBottomPathChange 3 = -coordinateUnit 3 := by
  calc
    bankBottomPathChange 3 =
        bottomThreeToTwoChange + bottomTwoToOneChange := by
      rw [bankBottomPathChange, bankBottomRelevantMoves_three]
      simp
    _ = -coordinateUnit 3 := three_to_one_change_eq_neg_unit_three

@[simp] theorem bankBottomPathChange_two :
    bankBottomPathChange 2 = -coordinateUnit 2 := by
  calc
    bankBottomPathChange 2 = bottomTwoToOneChange := by
      rw [bankBottomPathChange, bankBottomRelevantMoves_two]
      simp
    _ = -coordinateUnit 2 := two_to_one_change_eq_neg_unit_two

/-- The full-family matched request attached to a slot and a row.  A separate
membership theorem below records when this request belongs to the literal
truncated path. -/
def bankBottomPaperRequestOfMove {n : ℕ}
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (move : BankBottomMove) : ↑(bankBottomPaperRequests n) :=
  ⟨(slot, move), Finset.mem_univ _⟩

theorem bankBottomPaperRequestOfMove_mem_relevant
    {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    {move : BankBottomMove}
    (hmove : move ∈ bankBottomRelevantMoves slot.1.1) :
    (bankBottomPaperRequestOfMove slot move).1 ∈
      bankBottomRelevantPaperRequests n := by
  rw [bankBottomRelevantPaperRequests]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (bankBottomPaperRequestRelevant_iff_mem_moves _).2 hmove⟩

/-! ## A realization obtained from the actual matching -/

/-- An actual marker realization for the complete rectangular request family.
Only `bankBottomRelevantPaperRequests` is used when forming the final bank. -/
structure BankBottomPaperRealization (n M : ℕ) where
  marker : ↑(bankBottomPaperRequests n) → ℕ
  marker_mem : ∀ request,
    marker request ∈ bankBottomOrientedMarkerPrimes n M
      (bankBottomPaperRequestPool n request.1)
  marker_injective : Function.Injective marker

/-- Turn the concrete pool matching into component data. -/
def BankBottomPaperRealization.ofMatching
    {n M : ℕ}
    (matching : BankBottomPoolMatching
      (bankBottomPaperRequests n) (bankBottomPaperRequestPool n)
      (fun pool ↦ bankBottomOrientedMarkerPrimes n M pool))
    (hinjective : Function.Injective matching.matchedSlot) :
    BankBottomPaperRealization n M where
  marker := matching.matchedSlot
  marker_mem := matching.matchedSlot_mem
  marker_injective := hinjective

namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)

def move (_realization : BankBottomPaperRealization n M)
    (request : ↑(bankBottomPaperRequests n)) : BankBottomMove :=
  request.1.2

def lowerStateFactor (request : ↑(bankBottomPaperRequests n)) : ℕ :=
  bankBottomLowerState (realization.move request) (realization.marker request)

def upperStateFactor (request : ↑(bankBottomPaperRequests n)) : ℕ :=
  bankBottomUpperState (realization.move request) (realization.marker request)

def donorFactor (request : ↑(bankBottomPaperRequests n)) : ℕ :=
  bankBottomDonor (realization.move request) (realization.marker request)

/-- The pair of incident state cores before multiplication by the marker. -/
def incidentStateCores (request : ↑(bankBottomPaperRequests n)) : ℕ × ℕ :=
  bankBottomIncidentStateCores (realization.move request)

theorem marker_prime (request : ↑(bankBottomPaperRequests n)) :
    (realization.marker request).Prime :=
  (Finset.mem_filter.mp (realization.marker_mem request)).2

theorem marker_mem_row (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) :
    realization.marker request ∈
      bankBottomMarkerInterval n M (realization.move request) := by
  have horiented : realization.marker request ∈
      bankBottomOrientedMarkerInterval n M
        (bankBottomPaperRequestPool n request.1) :=
    (Finset.mem_filter.mp (realization.marker_mem request)).1
  have hrow := bankBottomOrientedMarkerInterval_subset hTwoN
    (bankBottomPaperRequestPool n request.1) horiented
  simpa only [move, bankBottomPaperRequestPool] using hrow

/-- Endpoint-only marker geometry used to separate bottom markers from the
ordinary marker intervals: every bottom marker lies strictly above `n/3`. -/
theorem n_lt_three_mul_marker (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) :
    n < 3 * realization.marker request := by
  have hrow := realization.marker_mem_row hTwoN request
  cases hmove : realization.move request <;>
    simp only [hmove, bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc] at hrow <;> omega

/-- A companion endpoint bound independent of asymptotic estimates. -/
theorem three_mul_marker_le_M (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) :
    3 * realization.marker request ≤ M := by
  have hrow := realization.marker_mem_row hTwoN request
  cases hmove : realization.move request <;>
    simp only [hmove, bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc] at hrow <;> omega

/-- At the final paper endpoint `M ≤ 3n`, every bottom marker itself is at
most `n`.  Together with `n < 3P`, this is the marker guard needed by the
combined ordinary/bottom layer. -/
theorem marker_le_n (hTwoN : 2 * n ≤ M) (hMThree : M ≤ 3 * n)
    (request : ↑(bankBottomPaperRequests n)) :
    realization.marker request ≤ n := by
  have hrow := realization.marker_mem_row hTwoN request
  cases hmove : realization.move request <;>
    simp only [hmove, bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc] at hrow <;> omega

/-- Both row endpoints and the donor are actual factors in `(n,M]`. -/
theorem states_donor_mem_factorInterval (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) :
    realization.lowerStateFactor request ∈ factorInterval n M ∧
      realization.upperStateFactor request ∈ factorInterval n M ∧
      realization.donorFactor request ∈ factorInterval n M := by
  simpa only [lowerStateFactor, upperStateFactor, donorFactor] using
    bankBottom_states_donor_mem_factorInterval
      (realization.marker_mem_row hTwoN request)

/-- The state endpoint as an actual occurrence in the factor interval. -/
def lowerStateOccurrence (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) : ↑(factorInterval n M) :=
  ⟨realization.lowerStateFactor request,
    (realization.states_donor_mem_factorInterval hTwoN request).1⟩

def upperStateOccurrence (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) : ↑(factorInterval n M) :=
  ⟨realization.upperStateFactor request,
    (realization.states_donor_mem_factorInterval hTwoN request).2.1⟩

def donorOccurrence (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) : ↑(factorInterval n M) :=
  ⟨realization.donorFactor request,
    (realization.states_donor_mem_factorInterval hTwoN request).2.2⟩

/-! The four paper rows, with the marker made explicit. -/

theorem row_fiveToFour
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .fiveToFour) :
    realization.lowerStateFactor request = 4 * realization.marker request ∧
      realization.upperStateFactor request = 5 * realization.marker request ∧
      realization.donorFactor request = 6 * realization.marker request := by
  simp [lowerStateFactor, upperStateFactor, donorFactor, hmove,
    bankBottomLowerState, bankBottomUpperState, bankBottomDonor,
    bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
    bankBottomDonorMultiplier]

theorem row_fourToThree
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .fourToThree) :
    realization.lowerStateFactor request = 3 * realization.marker request ∧
      realization.upperStateFactor request = 4 * realization.marker request ∧
      realization.donorFactor request = 5 * realization.marker request := by
  simp [lowerStateFactor, upperStateFactor, donorFactor, hmove,
    bankBottomLowerState, bankBottomUpperState, bankBottomDonor,
    bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
    bankBottomDonorMultiplier]

theorem row_threeToTwo
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .threeToTwo) :
    realization.lowerStateFactor request = 2 * realization.marker request ∧
      realization.upperStateFactor request = 3 * realization.marker request ∧
      realization.donorFactor request = 3 * realization.marker request := by
  simp [lowerStateFactor, upperStateFactor, donorFactor, hmove,
    bankBottomLowerState, bankBottomUpperState, bankBottomDonor,
    bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
    bankBottomDonorMultiplier]

theorem row_twoToOne
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .twoToOne) :
    realization.lowerStateFactor request = 2 * realization.marker request ∧
      realization.upperStateFactor request = 4 * realization.marker request ∧
      realization.donorFactor request = 4 * realization.marker request := by
  simp [lowerStateFactor, upperStateFactor, donorFactor, hmove,
    bankBottomLowerState, bankBottomUpperState, bankBottomDonor,
    bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
    bankBottomDonorMultiplier]

/-- In both terminal rows the donor value is the upper state value. -/
theorem donorFactor_eq_upperStateFactor_of_terminalMove
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .threeToTwo ∨
      realization.move request = .twoToOne) :
    realization.donorFactor request =
      realization.upperStateFactor request := by
  rcases hmove with hmove | hmove
  · simpa only [donorFactor, upperStateFactor, hmove] using
      bankBottomDonor_threeToTwo_eq_upperState
        (realization.marker request)
  · simpa only [donorFactor, upperStateFactor, hmove] using
      bankBottomDonor_twoToOne_eq_upperState
        (realization.marker request)

/-- More strongly, after interval membership is attached, the donor and upper
state in the last two rows are the very same subtype occurrence. -/
theorem donorOccurrence_eq_upperStateOccurrence_of_terminalMove
    (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .threeToTwo ∨
      realization.move request = .twoToOne) :
    realization.donorOccurrence hTwoN request =
      realization.upperStateOccurrence hTwoN request := by
  apply Subtype.ext
  exact realization.donorFactor_eq_upperStateFactor_of_terminalMove
    request hmove

/-! ## Orientation-aware realized row and slot changes -/

/-- The state occupied before traversing a realized bottom row.  Downward
slots start at the larger state; upward slots start at the smaller state. -/
def fromStateValue (request : ↑(bankBottomPaperRequests n)) : ℕ :=
  match bankSignedSlotOrientation request.1.1 with
  | .downward => realization.upperStateFactor request
  | .upward => realization.lowerStateFactor request

/-- The state occupied after traversing a realized bottom row. -/
def toStateValue (request : ↑(bankBottomPaperRequests n)) : ℕ :=
  match bankSignedSlotOrientation request.1.1 with
  | .downward => realization.lowerStateFactor request
  | .upward => realization.upperStateFactor request

/-- Actual valuation change of one realized bottom component. -/
def realizedComponentChange
    (request : ↑(bankBottomPaperRequests n)) : BankVector ℕ :=
  factorMoveChange (realization.fromStateValue request)
    (realization.toStateValue request)

theorem factorMoveChange_mul_right
    {source target P : ℕ}
    (hsource : source ≠ 0) (htarget : target ≠ 0) (hP : P ≠ 0) :
    factorMoveChange (source * P) (target * P) =
      factorMoveChange source target := by
  funext prime
  simp only [factorMoveChange, integerValuationVector, Pi.sub_apply]
  rw [Nat.factorization_mul hsource hP,
    Nat.factorization_mul htarget hP,
    Finsupp.add_apply, Finsupp.add_apply]
  push_cast
  ring

/-- Cancelling the matched marker recovers the deterministic row change;
reversing the row negates it. -/
theorem realizedComponentChange_eq_signedMoveChange
    (request : ↑(bankBottomPaperRequests n)) :
    realization.realizedComponentChange request =
      match bankSignedSlotOrientation request.1.1 with
      | .downward => bankBottomMoveChange (realization.move request)
      | .upward => -bankBottomMoveChange (realization.move request) := by
  have hmarker : realization.marker request ≠ 0 :=
    (realization.marker_prime request).ne_zero
  have hlower : bankBottomLowerStateMultiplier
      (realization.move request) ≠ 0 := by
    cases hmove : realization.move request <;>
      simp [bankBottomLowerStateMultiplier]
  have hupper : bankBottomUpperStateMultiplier
      (realization.move request) ≠ 0 := by
    cases hmove : realization.move request <;>
      simp [bankBottomUpperStateMultiplier]
  cases horientation : bankSignedSlotOrientation request.1.1
  · rw [realizedComponentChange, fromStateValue, toStateValue,
      horientation, lowerStateFactor, upperStateFactor,
      bankBottomLowerState, bankBottomUpperState,
      factorMoveChange_mul_right hupper hlower hmarker,
      bankBottomMoveChange]
  · rw [realizedComponentChange, fromStateValue, toStateValue,
      horientation, lowerStateFactor, upperStateFactor,
      bankBottomLowerState, bankBottomUpperState,
      factorMoveChange_mul_right hlower hupper hmarker,
      bankBottomMoveChange]
    unfold factorMoveChange
    abel

/-- Total actual bottom change of a signed slot.  The sum is deliberately
indexed by `bankBottomRelevantMoves`, so unused rectangular-family matches
cannot enter the realized path. -/
def realizedSlotChange
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) : BankVector ℕ :=
  ∑ move ∈ bankBottomRelevantMoves slot.1.1,
    realization.realizedComponentChange
      (bankBottomPaperRequestOfMove slot move)

/-- Deterministic signed version of the truncated bottom path. -/
def signedBottomPathChange
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) : BankVector ℕ :=
  match slot.2 with
  | .inl _copy => bankBottomPathChange slot.1.1
  | .inr _copy => -bankBottomPathChange slot.1.1

/-- The matched component rows telescope to the deterministic truncated path,
with the orientation prescribed by the signed slot. -/
theorem realizedSlotChange_eq_signedBottomPathChange
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    realization.realizedSlotChange slot = signedBottomPathChange slot := by
  rcases slot with ⟨prime, signedCopy⟩
  cases signedCopy with
  | inl copy =>
      rw [realizedSlotChange, signedBottomPathChange, bankBottomPathChange]
      apply Finset.sum_congr rfl
      intro move _hmove
      simpa [bankBottomPaperRequestOfMove, bankSignedSlotOrientation,
        BankBottomPaperRealization.move] using
        realization.realizedComponentChange_eq_signedMoveChange
          (bankBottomPaperRequestOfMove ⟨prime, Sum.inl copy⟩ move)
  | inr copy =>
      rw [realizedSlotChange, signedBottomPathChange, bankBottomPathChange,
        ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro move _hmove
      simpa [bankBottomPaperRequestOfMove, bankSignedSlotOrientation,
        BankBottomPaperRealization.move] using
        realization.realizedComponentChange_eq_signedMoveChange
          (bankBottomPaperRequestOfMove ⟨prime, Sum.inr copy⟩ move)

/-- For source primes at least five, the bottom portion contributes `-e_5`
in the downward orientation and `+e_5` in the reverse orientation. -/
theorem realizedSlotChange_eq_signedUnit_five_of_five_le
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (hprime : 5 ≤ slot.1.1) :
    realization.realizedSlotChange slot =
      match slot.2 with
      | .inl _copy => -coordinateUnit 5
      | .inr _copy => coordinateUnit 5 := by
  rcases slot with ⟨prime, signedCopy⟩
  cases signedCopy <;>
    simp [realization.realizedSlotChange_eq_signedBottomPathChange,
      signedBottomPathChange,
      bankBottomPathChange_eq_neg_unit_five_of_five_le hprime]

/-- The truncated source-three path contributes exactly the signed unit at
three, with downward sign negative and reverse sign positive. -/
theorem realizedSlotChange_eq_signedUnit_three
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (hprime : slot.1.1 = 3) :
    realization.realizedSlotChange slot =
      match slot.2 with
      | .inl _copy => -coordinateUnit 3
      | .inr _copy => coordinateUnit 3 := by
  have hpath : bankBottomPathChange slot.1.1 = -coordinateUnit 3 :=
    (congrArg bankBottomPathChange hprime).trans bankBottomPathChange_three
  rw [realization.realizedSlotChange_eq_signedBottomPathChange]
  cases hsigned : slot.2
  · simpa only [signedBottomPathChange, hsigned] using hpath
  · simpa only [signedBottomPathChange, hsigned, neg_neg] using
      congrArg Neg.neg hpath

/-- The one-row source-two path contributes exactly the signed unit at two. -/
theorem realizedSlotChange_eq_signedUnit_two
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (hprime : slot.1.1 = 2) :
    realization.realizedSlotChange slot =
      match slot.2 with
      | .inl _copy => -coordinateUnit 2
      | .inr _copy => coordinateUnit 2 := by
  have hpath : bankBottomPathChange slot.1.1 = -coordinateUnit 2 :=
    (congrArg bankBottomPathChange hprime).trans bankBottomPathChange_two
  rw [realization.realizedSlotChange_eq_signedBottomPathChange]
  cases hsigned : slot.2
  · simpa only [signedBottomPathChange, hsigned] using hpath
  · simpa only [signedBottomPathChange, hsigned, neg_neg] using
      congrArg Neg.neg hpath

end BankBottomPaperRealization

/-! ## Complete occurrence sets and rough signatures -/

/-- The four named roles.  Their images form a `Finset`, so equal roles such
as terminal-row donor/upper-state are represented by one occurrence. -/
inductive BankBottomPaperOccurrenceKind where
  | marker
  | lowerState
  | upperState
  | donor
  deriving DecidableEq, Fintype

def bankBottomPaperOccurrenceMultiplier
    (move : BankBottomMove) : BankBottomPaperOccurrenceKind → ℕ
  | .marker => 1
  | .lowerState => bankBottomLowerStateMultiplier move
  | .upperState => bankBottomUpperStateMultiplier move
  | .donor => bankBottomDonorMultiplier move

theorem bankBottomPaperOccurrenceMultiplier_pos
    (move : BankBottomMove) (kind : BankBottomPaperOccurrenceKind) :
    0 < bankBottomPaperOccurrenceMultiplier move kind := by
  cases kind <;> cases move <;>
    norm_num [bankBottomPaperOccurrenceMultiplier,
      bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
      bankBottomDonorMultiplier]

theorem bankBottomPaperOccurrenceMultiplier_le_six
    (move : BankBottomMove) (kind : BankBottomPaperOccurrenceKind) :
    bankBottomPaperOccurrenceMultiplier move kind ≤ 6 := by
  cases kind <;> cases move <;>
    norm_num [bankBottomPaperOccurrenceMultiplier,
      bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
      bankBottomDonorMultiplier]

namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)

/-- Numerical value of one named occurrence in a realized component. -/
def occurrenceValue (request : ↑(bankBottomPaperRequests n))
    (kind : BankBottomPaperOccurrenceKind) : ℕ :=
  bankBottomPaperOccurrenceMultiplier (realization.move request) kind *
    realization.marker request

@[simp] theorem occurrenceValue_marker
    (request : ↑(bankBottomPaperRequests n)) :
    realization.occurrenceValue request .marker = realization.marker request := by
  simp [occurrenceValue, bankBottomPaperOccurrenceMultiplier]

@[simp] theorem occurrenceValue_lowerState
    (request : ↑(bankBottomPaperRequests n)) :
    realization.occurrenceValue request .lowerState =
      realization.lowerStateFactor request := rfl

@[simp] theorem occurrenceValue_upperState
    (request : ↑(bankBottomPaperRequests n)) :
    realization.occurrenceValue request .upperState =
      realization.upperStateFactor request := rfl

@[simp] theorem occurrenceValue_donor
    (request : ↑(bankBottomPaperRequests n)) :
    realization.occurrenceValue request .donor =
      realization.donorFactor request := rfl

/-- Diagnostic carrier set used for marker recovery and cross-family collision
checks.  This is deliberately not the bank-factor census: the bare marker is
usually below `n` and is not a factor occurrence. -/
def carrierValueSet (request : ↑(bankBottomPaperRequests n)) : Finset ℕ :=
  (Finset.univ : Finset BankBottomPaperOccurrenceKind).image
    (realization.occurrenceValue request)

theorem occurrenceValue_mem_carrierValueSet
    (request : ↑(bankBottomPaperRequests n))
    (kind : BankBottomPaperOccurrenceKind) :
    realization.occurrenceValue request kind ∈
      realization.carrierValueSet request := by
  exact Finset.mem_image.mpr ⟨kind, Finset.mem_univ kind, rfl⟩

/-- The two actual endpoint-state factors of the component. -/
def stateFactors (request : ↑(bankBottomPaperRequests n)) : Finset ℕ :=
  {realization.lowerStateFactor request,
    realization.upperStateFactor request}

theorem lowerStateFactor_ne_upperStateFactor
    (request : ↑(bankBottomPaperRequests n)) :
    realization.lowerStateFactor request ≠
      realization.upperStateFactor request := by
  have hmarker : 0 < realization.marker request :=
    (realization.marker_prime request).pos
  cases hmove : realization.move request <;>
    simp only [lowerStateFactor, upperStateFactor, hmove,
      bankBottomLowerState, bankBottomUpperState,
      bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier] <;>
    omega

theorem card_stateFactors
    (request : ↑(bankBottomPaperRequests n)) :
    (realization.stateFactors request).card = 2 := by
  simp [stateFactors,
    realization.lowerStateFactor_ne_upperStateFactor request]

/-- The actual factor occurrences of a component.  In particular, this does
not contain the bare marker.  The `Finset` identifies the terminal-row donor
with the equal upper-state occurrence. -/
def componentOccurrences
    (request : ↑(bankBottomPaperRequests n)) : Finset ℕ :=
  bankBottomComponentOccurrences (realization.move request)
    (realization.marker request)

theorem componentOccurrences_eq_states_insert_donor
    (request : ↑(bankBottomPaperRequests n)) :
    realization.componentOccurrences request =
      insert (realization.lowerStateFactor request)
        (insert (realization.upperStateFactor request)
          {realization.donorFactor request}) := rfl

theorem marker_not_mem_componentOccurrences
    (request : ↑(bankBottomPaperRequests n)) :
    realization.marker request ∉ realization.componentOccurrences request := by
  have hmarker : 0 < realization.marker request :=
    (realization.marker_prime request).pos
  cases hmove : realization.move request <;>
    simp [componentOccurrences, hmove, bankBottomComponentOccurrences,
      bankBottomLowerState, bankBottomUpperState, bankBottomDonor,
      bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
      bankBottomDonorMultiplier] <;> omega

theorem componentOccurrences_subset_carrierValueSet
    (request : ↑(bankBottomPaperRequests n)) :
    realization.componentOccurrences request ⊆
      realization.carrierValueSet request := by
  intro occurrence hoccurrence
  rw [componentOccurrences_eq_states_insert_donor] at hoccurrence
  simp only [Finset.mem_insert, Finset.mem_singleton] at hoccurrence
  rcases hoccurrence with hoccurrence | hoccurrence | hoccurrence
  · subst occurrence
    simpa only [occurrenceValue_lowerState] using
      realization.occurrenceValue_mem_carrierValueSet request .lowerState
  · subst occurrence
    simpa only [occurrenceValue_upperState] using
      realization.occurrenceValue_mem_carrierValueSet request .upperState
  · subst occurrence
    simpa only [occurrenceValue_donor] using
      realization.occurrenceValue_mem_carrierValueSet request .donor

theorem componentOccurrence_mem_factorInterval
    (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n))
    {occurrence : ℕ}
    (hoccurrence : occurrence ∈ realization.componentOccurrences request) :
    occurrence ∈ factorInterval n M := by
  rw [realization.componentOccurrences_eq_states_insert_donor request]
    at hoccurrence
  simp only [Finset.mem_insert, Finset.mem_singleton] at hoccurrence
  have hinterval := realization.states_donor_mem_factorInterval hTwoN request
  rcases hoccurrence with hoccurrence | hoccurrence | hoccurrence
  · simpa only [hoccurrence] using hinterval.1
  · simpa only [hoccurrence] using hinterval.2.1
  · simpa only [hoccurrence] using hinterval.2.2

theorem componentOccurrences_fiveToFour
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .fiveToFour) :
    realization.componentOccurrences request =
      {4 * realization.marker request, 5 * realization.marker request,
        6 * realization.marker request} := by
  simp [componentOccurrences, hmove, bankBottomComponentOccurrences,
    bankBottomLowerState, bankBottomUpperState, bankBottomDonor,
    bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
    bankBottomDonorMultiplier]

theorem componentOccurrences_fourToThree
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .fourToThree) :
    realization.componentOccurrences request =
      {3 * realization.marker request, 4 * realization.marker request,
        5 * realization.marker request} := by
  simp [componentOccurrences, hmove, bankBottomComponentOccurrences,
    bankBottomLowerState, bankBottomUpperState, bankBottomDonor,
    bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
    bankBottomDonorMultiplier]

theorem componentOccurrences_threeToTwo
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .threeToTwo) :
    realization.componentOccurrences request =
      {2 * realization.marker request, 3 * realization.marker request} := by
  simpa only [componentOccurrences, hmove] using
    bankBottomComponentOccurrences_threeToTwo
      (realization.marker request)

theorem componentOccurrences_twoToOne
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .twoToOne) :
    realization.componentOccurrences request =
      {2 * realization.marker request, 4 * realization.marker request} := by
  simpa only [componentOccurrences, hmove] using
    bankBottomComponentOccurrences_twoToOne
      (realization.marker request)

theorem card_componentOccurrences_fiveToFour
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .fiveToFour) :
    (realization.componentOccurrences request).card = 3 := by
  rw [realization.componentOccurrences_fiveToFour request hmove]
  have hmarker : 0 < realization.marker request :=
    (realization.marker_prime request).pos
  have hfourFive : 4 * realization.marker request ≠
      5 * realization.marker request := by omega
  have hfourSix : 4 * realization.marker request ≠
      6 * realization.marker request := by omega
  have hfiveSix : 5 * realization.marker request ≠
      6 * realization.marker request := by omega
  simp [hfourFive, hfourSix, hfiveSix]

theorem card_componentOccurrences_fourToThree
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .fourToThree) :
    (realization.componentOccurrences request).card = 3 := by
  rw [realization.componentOccurrences_fourToThree request hmove]
  have hmarker : 0 < realization.marker request :=
    (realization.marker_prime request).pos
  have hthreeFour : 3 * realization.marker request ≠
      4 * realization.marker request := by omega
  have hthreeFive : 3 * realization.marker request ≠
      5 * realization.marker request := by omega
  have hfourFive : 4 * realization.marker request ≠
      5 * realization.marker request := by omega
  simp [hthreeFour, hthreeFive, hfourFive]

theorem card_componentOccurrences_threeToTwo
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .threeToTwo) :
    (realization.componentOccurrences request).card = 2 := by
  rw [realization.componentOccurrences_threeToTwo request hmove]
  have hmarker : 0 < realization.marker request :=
    (realization.marker_prime request).pos
  have htwoThree : 2 * realization.marker request ≠
      3 * realization.marker request := by omega
  simp [htwoThree]

theorem card_componentOccurrences_twoToOne
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .twoToOne) :
    (realization.componentOccurrences request).card = 2 := by
  rw [realization.componentOccurrences_twoToOne request hmove]
  have hmarker : 0 < realization.marker request :=
    (realization.marker_prime request).pos
  have htwoFour : 2 * realization.marker request ≠
      4 * realization.marker request := by omega
  simp [htwoFour]

theorem card_componentOccurrences_le_three
    (request : ↑(bankBottomPaperRequests n)) :
    (realization.componentOccurrences request).card ≤ 3 := by
  cases hmove : realization.move request
  · rw [realization.card_componentOccurrences_fiveToFour request hmove]
  · rw [realization.card_componentOccurrences_fourToThree request hmove]
  · rw [realization.card_componentOccurrences_threeToTwo request hmove]
    omega
  · rw [realization.card_componentOccurrences_twoToOne request hmove]
    omega

/-- Multiplication by a positive cofactor at most `y` does not change any
prime-power coordinate above `y`. -/
theorem completeRoughSignature_small_mul
    {y cofactor marker : ℕ} (hcofactorPos : 0 < cofactor)
    (hcofactorLe : cofactor ≤ y) (hmarker : marker ≠ 0) :
    completeRoughSignature y (cofactor * marker) =
      completeRoughSignature y marker := by
  ext p
  rw [completeRoughSignature_apply, completeRoughSignature_apply]
  by_cases hp : y < p
  · rw [if_pos hp, if_pos hp,
      Nat.factorization_mul hcofactorPos.ne' hmarker]
    simp only [Finsupp.add_apply,
      Nat.factorization_eq_zero_of_lt (hcofactorLe.trans_lt hp), zero_add]
  · simp only [if_neg hp]

theorem occurrenceValue_completeRoughSignature
    (hySix : 6 ≤ yNat n)
    (request : ↑(bankBottomPaperRequests n))
    (kind : BankBottomPaperOccurrenceKind) :
    completeRoughSignature (yNat n)
        (realization.occurrenceValue request kind) =
      completeRoughSignature (yNat n) (realization.marker request) := by
  apply completeRoughSignature_small_mul
  · exact bankBottomPaperOccurrenceMultiplier_pos _ _
  · exact (bankBottomPaperOccurrenceMultiplier_le_six _ _).trans hySix
  · exact (realization.marker_prime request).pos.ne'

/-- Every actual state/donor occurrence of a component has the marker's full
prime-power signature above `yNat`; the diagnostic bare marker is not being
counted as a factor here. -/
theorem componentOccurrence_completeRoughSignature
    (hySix : 6 ≤ yNat n)
    (request : ↑(bankBottomPaperRequests n))
    {occurrence : ℕ}
    (hoccurrence : occurrence ∈ realization.componentOccurrences request) :
    completeRoughSignature (yNat n) occurrence =
      completeRoughSignature (yNat n) (realization.marker request) := by
  rw [realization.componentOccurrences_eq_states_insert_donor request]
    at hoccurrence
  simp only [Finset.mem_insert, Finset.mem_singleton] at hoccurrence
  rcases hoccurrence with hoccurrence | hoccurrence | hoccurrence
  · subst occurrence
    simpa only [occurrenceValue_lowerState] using
      realization.occurrenceValue_completeRoughSignature
        hySix request .lowerState
  · subst occurrence
    simpa only [occurrenceValue_upperState] using
      realization.occurrenceValue_completeRoughSignature
        hySix request .upperState
  · subst occurrence
    simpa only [occurrenceValue_donor] using
      realization.occurrenceValue_completeRoughSignature
        hySix request .donor

end BankBottomPaperRealization

/-! ## Explicit local geometry and collision freedom -/

theorem yNat_le_bankBottomMarkerLower_of_three_mul_le
    {n : ℕ} (hgeometry : 3 * yNat n ≤ n) (move : BankBottomMove) :
    yNat n ≤ bankBottomMarkerLower n move := by
  cases move <;> simp only [bankBottomMarkerLower] <;> omega

namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)

theorem yNat_lt_marker (hTwoN : 2 * n ≤ M)
    (hgeometry : 3 * yNat n ≤ n)
    (request : ↑(bankBottomPaperRequests n)) :
    yNat n < realization.marker request := by
  have hrow := realization.marker_mem_row hTwoN request
  have hlower : bankBottomMarkerLower n (realization.move request) <
      realization.marker request := (Finset.mem_Ioc.mp hrow).1
  exact (yNat_le_bankBottomMarkerLower_of_three_mul_le
    hgeometry (realization.move request)).trans_lt hlower

/-- Any marker/state/donor value from one request is distinct from every such
value belonging to a different request. -/
theorem occurrenceValue_ne_of_request_ne
    (hTwoN : 2 * n ≤ M) (hySix : 6 ≤ yNat n)
    (hgeometry : 3 * yNat n ≤ n)
    {request request' : ↑(bankBottomPaperRequests n)}
    (hrequest : request ≠ request')
    (kind kind' : BankBottomPaperOccurrenceKind) :
    realization.occurrenceValue request kind ≠
      realization.occurrenceValue request' kind' := by
  intro heq
  have hlarge : 6 < realization.marker request :=
    hySix.trans_lt (realization.yNat_lt_marker hTwoN hgeometry request)
  have hproduct :
      realization.marker request *
          bankBottomPaperOccurrenceMultiplier (realization.move request) kind =
        realization.marker request' *
          bankBottomPaperOccurrenceMultiplier (realization.move request') kind' := by
    simpa only [occurrenceValue, Nat.mul_comm] using heq
  have hmarkers := prime_mul_cofactor_eq_iff_of_marker_large
    (X := 6) (realization.marker_prime request)
      (realization.marker_prime request') hlarge
      (bankBottomPaperOccurrenceMultiplier_pos _ _)
      (bankBottomPaperOccurrenceMultiplier_le_six _ _) hproduct
  exact hrequest (realization.marker_injective hmarkers.1)

theorem carrierValueSets_disjoint_of_request_ne
    (hTwoN : 2 * n ≤ M) (hySix : 6 ≤ yNat n)
    (hgeometry : 3 * yNat n ≤ n)
    {request request' : ↑(bankBottomPaperRequests n)}
    (hrequest : request ≠ request') :
    Disjoint (realization.carrierValueSet request)
      (realization.carrierValueSet request') := by
  rw [Finset.disjoint_left]
  intro occurrence hoccurrence hoccurrence'
  rcases Finset.mem_image.mp hoccurrence with ⟨kind, _hkind, hvalue⟩
  rcases Finset.mem_image.mp hoccurrence' with ⟨kind', _hkind', hvalue'⟩
  exact (realization.occurrenceValue_ne_of_request_ne
    hTwoN hySix hgeometry hrequest kind kind')
      (hvalue.trans hvalue'.symm)

/-- Consequently the actual factor-occurrence sets, which exclude the bare
markers, are pairwise disjoint as well. -/
theorem componentOccurrences_disjoint_of_request_ne
    (hTwoN : 2 * n ≤ M) (hySix : 6 ≤ yNat n)
    (hgeometry : 3 * yNat n ≤ n)
    {request request' : ↑(bankBottomPaperRequests n)}
    (hrequest : request ≠ request') :
    Disjoint (realization.componentOccurrences request)
      (realization.componentOccurrences request') := by
  exact (realization.carrierValueSets_disjoint_of_request_ne
    hTwoN hySix hgeometry hrequest).mono
      (realization.componentOccurrences_subset_carrierValueSet request)
      (realization.componentOccurrences_subset_carrierValueSet request')

/-! ## Relevant markers and marker-to-component uniqueness -/

/-- Only markers of path-relevant requests are exposed to downstream anchor
guards.  Markers assigned to rectangular-family padding requests are absent. -/
def relevantMarkers : Finset ℕ :=
  (bankBottomRelevantPaperRequests n).attach.image
    (fun request ↦ realization.marker
      (bankBottomRelevantRequestToPaperRequest request))

/-- Actual bottom-bank factor census.  It unions only path-relevant
components, and each component contributes only its two states and donor;
bare marker primes and rectangular-family padding requests are excluded. -/
def relevantComponentOccurrences : Finset ℕ :=
  (bankBottomRelevantPaperRequests n).attach.biUnion
    (fun request ↦ realization.componentOccurrences
      (bankBottomRelevantRequestToPaperRequest request))

theorem relevantMarkerMap_injective : Function.Injective
    (fun request : ↑(bankBottomRelevantPaperRequests n) ↦
      realization.marker (bankBottomRelevantRequestToPaperRequest request)) :=
  realization.marker_injective.comp
    bankBottomRelevantRequestToPaperRequest_injective

@[simp] theorem relevantMarker_mem_relevantMarkers
    (request : ↑(bankBottomRelevantPaperRequests n)) :
    realization.marker (bankBottomRelevantRequestToPaperRequest request) ∈
      realization.relevantMarkers := by
  rw [relevantMarkers]
  exact Finset.mem_image.mpr ⟨request, Finset.mem_attach _ _, rfl⟩

theorem relevantMarker_existsUnique_request
    {marker : ℕ} (hmarker : marker ∈ realization.relevantMarkers) :
    ∃! request : ↑(bankBottomRelevantPaperRequests n),
      realization.marker (bankBottomRelevantRequestToPaperRequest request) =
        marker := by
  rw [relevantMarkers] at hmarker
  rcases Finset.mem_image.mp hmarker with
    ⟨request, _hrequest, hrequestMarker⟩
  refine ⟨request, hrequestMarker, ?_⟩
  intro request' hrequest'Marker
  exact realization.relevantMarkerMap_injective
    (hrequest'Marker.trans hrequestMarker.symm)

/-- The unique relevant request carried by a marker in the realized marker
set. -/
def requestForRelevantMarker (marker : ↑realization.relevantMarkers) :
    ↑(bankBottomRelevantPaperRequests n) :=
  Classical.choose
    (realization.relevantMarker_existsUnique_request marker.property)

@[simp] theorem marker_requestForRelevantMarker
    (marker : ↑realization.relevantMarkers) :
    realization.marker (bankBottomRelevantRequestToPaperRequest
      (realization.requestForRelevantMarker marker)) = marker.1 :=
  (Classical.choose_spec
    (realization.relevantMarker_existsUnique_request marker.property)).1

theorem requestForRelevantMarker_unique
    (marker : ↑realization.relevantMarkers)
    (request : ↑(bankBottomRelevantPaperRequests n))
    (hmarker : realization.marker
      (bankBottomRelevantRequestToPaperRequest request) = marker.1) :
    request = realization.requestForRelevantMarker marker := by
  exact realization.relevantMarkerMap_injective
    (hmarker.trans (realization.marker_requestForRelevantMarker marker).symm)

/-- The two incident cores as a function of an actual relevant marker. -/
def relevantMarkerIncidentStateCores
    (marker : ↑realization.relevantMarkers) : ℕ × ℕ :=
  realization.incidentStateCores
    (bankBottomRelevantRequestToPaperRequest
      (realization.requestForRelevantMarker marker))

@[simp] theorem relevantMarkerIncidentStateCores_of_request
    (request : ↑(bankBottomRelevantPaperRequests n)) :
    realization.relevantMarkerIncidentStateCores
        ⟨realization.marker (bankBottomRelevantRequestToPaperRequest request),
          realization.relevantMarker_mem_relevantMarkers request⟩ =
      realization.incidentStateCores
        (bankBottomRelevantRequestToPaperRequest request) := by
  unfold relevantMarkerIncidentStateCores
  have hrequest : realization.requestForRelevantMarker
      ⟨realization.marker (bankBottomRelevantRequestToPaperRequest request),
        realization.relevantMarker_mem_relevantMarkers request⟩ = request := by
    symm
    exact realization.requestForRelevantMarker_unique _ request rfl
  rw [hrequest]

theorem card_relevantMarkers :
    realization.relevantMarkers.card =
      (bankBottomRelevantPaperRequests n).card := by
  rw [relevantMarkers, Finset.card_image_of_injective _
    realization.relevantMarkerMap_injective]
  simp

theorem relevant_marker_incident_data_unique
    {request request' : ↑(bankBottomRelevantPaperRequests n)}
    (hmarker : realization.marker
        (bankBottomRelevantRequestToPaperRequest request) =
      realization.marker
        (bankBottomRelevantRequestToPaperRequest request')) :
    request = request' ∧
      realization.move (bankBottomRelevantRequestToPaperRequest request) =
        realization.move (bankBottomRelevantRequestToPaperRequest request') ∧
      realization.incidentStateCores
          (bankBottomRelevantRequestToPaperRequest request) =
        realization.incidentStateCores
          (bankBottomRelevantRequestToPaperRequest request') ∧
      realization.lowerStateFactor
          (bankBottomRelevantRequestToPaperRequest request) =
        realization.lowerStateFactor
          (bankBottomRelevantRequestToPaperRequest request') ∧
      realization.upperStateFactor
          (bankBottomRelevantRequestToPaperRequest request) =
        realization.upperStateFactor
          (bankBottomRelevantRequestToPaperRequest request') ∧
      realization.donorFactor
          (bankBottomRelevantRequestToPaperRequest request) =
        realization.donorFactor
          (bankBottomRelevantRequestToPaperRequest request') := by
  have hrequest : request = request' :=
    realization.relevantMarkerMap_injective hmarker
  subst request'
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Bare markers are disjoint from the actual factor census.  This combines
within-component positivity with the cross-request marker/cofactor recovery
and is often the most convenient downstream separation interface. -/
theorem relevantMarkers_disjoint_relevantComponentOccurrences
    (hTwoN : 2 * n ≤ M) (hySix : 6 ≤ yNat n)
    (hgeometry : 3 * yNat n ≤ n) :
    Disjoint realization.relevantMarkers
      realization.relevantComponentOccurrences := by
  classical
  rw [Finset.disjoint_left]
  intro occurrence hmarker hcomponent
  rw [relevantMarkers] at hmarker
  rcases Finset.mem_image.mp hmarker with
    ⟨request, _hrequest, hrequestMarker⟩
  rw [relevantComponentOccurrences] at hcomponent
  rcases Finset.mem_biUnion.mp hcomponent with
    ⟨request', _hrequest', hrequest'Component⟩
  subst occurrence
  by_cases hrequests : request = request'
  · subst request'
    exact (realization.marker_not_mem_componentOccurrences
      (bankBottomRelevantRequestToPaperRequest request)) hrequest'Component
  · have hfullRequests :
        bankBottomRelevantRequestToPaperRequest request ≠
          bankBottomRelevantRequestToPaperRequest request' := by
      intro heq
      exact hrequests
        (bankBottomRelevantRequestToPaperRequest_injective heq)
    have hdisjoint := realization.carrierValueSets_disjoint_of_request_ne
      hTwoN hySix hgeometry hfullRequests
    exact (Finset.disjoint_left.mp hdisjoint)
      (by simpa only [occurrenceValue_marker] using
        (realization.occurrenceValue_mem_carrierValueSet
          (bankBottomRelevantRequestToPaperRequest request)
          BankBottomPaperOccurrenceKind.marker))
      (realization.componentOccurrences_subset_carrierValueSet
        (bankBottomRelevantRequestToPaperRequest request')
          hrequest'Component)

end BankBottomPaperRealization

/-! ## Cardinality bound for the actual relevant marker set -/

theorem card_bankBottomPaperRequests (n : ℕ) :
    (bankBottomPaperRequests n).card = 8 * bankBottomPaperDemand n := by
  have hsigned :
      Fintype.card (SignedBankSlot (bankRoundingBetaOnSupport n)) =
        2 * bankBottomPaperDemand n := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_sum, Fintype.card_fin,
      bankRoundingBetaOnSupport]
    calc
      (∑ p : ↑(bankRoundingPrimeSupport n),
          (bankRoundingBeta n p.1 + bankRoundingBeta n p.1)) =
          2 * ∑ p : ↑(bankRoundingPrimeSupport n),
            bankRoundingBeta n p.1 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro p _hp
              omega
      _ = 2 * bankBottomPaperDemand n := by
        congr 1
        simpa only [bankBottomPaperDemand] using
          (Finset.sum_attach (bankRoundingPrimeSupport n)
            (fun p ↦ bankRoundingBeta n p))
  rw [bankBottomPaperRequests, Finset.card_univ, Fintype.card_prod,
    hsigned, show Fintype.card BankBottomMove = 4 by decide]
  ring

theorem BankBottomPaperRealization.card_relevantMarkers_le_demand
    {n M : ℕ} (realization : BankBottomPaperRealization n M) :
    realization.relevantMarkers.card ≤ 8 * bankBottomPaperDemand n := by
  rw [realization.card_relevantMarkers, ← card_bankBottomPaperRequests n]
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem BankBottomPaperRealization.card_relevantComponentOccurrences_le_demand
    {n M : ℕ} (realization : BankBottomPaperRealization n M) :
    realization.relevantComponentOccurrences.card ≤
      24 * bankBottomPaperDemand n := by
  calc
    realization.relevantComponentOccurrences.card ≤
        (bankBottomRelevantPaperRequests n).attach.card * 3 := by
      exact Finset.card_biUnion_le_card_mul _ _ 3
        (fun request _hrequest ↦
          realization.card_componentOccurrences_le_three
            (bankBottomRelevantRequestToPaperRequest request))
    _ = 3 * (bankBottomRelevantPaperRequests n).card := by
      simp [Nat.mul_comm]
    _ ≤ 3 * (8 * bankBottomPaperDemand n) := by
      exact Nat.mul_le_mul_left 3 (by
        rw [← realization.card_relevantMarkers]
        exact realization.card_relevantMarkers_le_demand)
    _ = 24 * bankBottomPaperDemand n := by ring

/-! ## Eventual local geometry and the terminal realized family -/

private theorem bankBottom_yNat_tendsto_atTop : Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_nat_floor_atTop.comp hy

theorem eventually_bankBottom_six_le_yNat :
    ∀ᶠ n : ℕ in atTop, 6 ≤ yNat n :=
  bankBottom_yNat_tendsto_atTop.eventually (eventually_ge_atTop 6)

/-- Verifiable local geometry sufficient both for rough-signature equality and
large-prime marker recovery. -/
theorem eventually_bankBottom_three_mul_yNat_le_self :
    ∀ᶠ n : ℕ in atTop, 3 * yNat n ≤ n := by
  have hmodel : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ (-(7 / 9 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop
      (by norm_num : (0 : ℝ) < 7 / 9)).comp
        tendsto_natCast_atTop_atTop
  have hratio : Tendsto
      (fun n : ℕ ↦ y n / (n : ℝ)) atTop (nhds 0) := by
    apply hmodel.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    symm
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [y]
    calc
      (n : ℝ) ^ (2 / 9 : ℝ) / (n : ℝ) =
          (n : ℝ) ^ ((2 / 9 : ℝ) - 1) := by
        rw [Real.rpow_sub hnR, Real.rpow_one]
      _ = (n : ℝ) ^ (-(7 / 9 : ℝ)) := by norm_num
  have hsmall := hratio.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 3))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hratioN hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (by positivity) _
  have hyFloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
  have hySmall : 3 * y n < (n : ℝ) := by
    have := (div_lt_iff₀ hnR).mp hratioN
    nlinarith
  have hcast : ((3 * yNat n : ℕ) : ℝ) ≤ (n : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast hcast

/-- Terminal bottom-component realization.  The displayed interval and
signature conclusions concern actual matched values; the global occurrence
set and marker set used downstream are restricted to relevant requests. -/
theorem eventually_exists_bankBottomPaper_component_realization
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ∃ realization : BankBottomPaperRealization n
          (upperEndpoint n (upperTailLength c n)),
        (∀ request : ↑(bankBottomPaperRequests n),
          realization.marker request ∈
              bankBottomOrientedMarkerPrimes n
                (upperEndpoint n (upperTailLength c n))
                (bankBottomPaperRequestPool n request.1) ∧
            realization.lowerStateFactor request ∈
              factorInterval n (upperEndpoint n (upperTailLength c n)) ∧
            realization.upperStateFactor request ∈
              factorInterval n (upperEndpoint n (upperTailLength c n)) ∧
            realization.donorFactor request ∈
              factorInterval n (upperEndpoint n (upperTailLength c n))) ∧
        (∀ request : ↑(bankBottomPaperRequests n),
          ∀ kind : BankBottomPaperOccurrenceKind,
            completeRoughSignature (yNat n)
                (realization.occurrenceValue request kind) =
              completeRoughSignature (yNat n)
                (realization.marker request)) ∧
        (∀ {request request' : ↑(bankBottomPaperRequests n)},
          request ≠ request' →
            Disjoint (realization.carrierValueSet request)
              (realization.carrierValueSet request') ∧
            Disjoint (realization.componentOccurrences request)
              (realization.componentOccurrences request')) ∧
        realization.relevantMarkers.card =
            (bankBottomRelevantPaperRequests n).card ∧
        realization.relevantMarkers.card ≤ 8 * bankBottomPaperDemand n ∧
        realization.relevantComponentOccurrences.card ≤
          24 * bankBottomPaperDemand n := by
  filter_upwards [eventually_exists_bankBottomPaper_injective_assignment hc,
      eventually_bankBottom_six_le_yNat,
      eventually_bankBottom_three_mul_yNat_le_self]
      with n hmatching hySix hgeometry
  rcases hmatching with ⟨matching, hinjective, _hmem⟩
  let realization : BankBottomPaperRealization n
      (upperEndpoint n (upperTailLength c n)) :=
    BankBottomPaperRealization.ofMatching matching hinjective
  have hTwoN : 2 * n ≤ upperEndpoint n (upperTailLength c n) :=
    two_mul_le_upperEndpoint n (upperTailLength c n)
  refine ⟨realization, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro request
    have hinterval := realization.states_donor_mem_factorInterval
      hTwoN request
    exact ⟨realization.marker_mem request, hinterval.1,
      hinterval.2.1, hinterval.2.2⟩
  · intro request kind
    exact realization.occurrenceValue_completeRoughSignature
      hySix request kind
  · intro request request' hrequest
    exact ⟨realization.carrierValueSets_disjoint_of_request_ne
        hTwoN hySix hgeometry hrequest,
      realization.componentOccurrences_disjoint_of_request_ne
        hTwoN hySix hgeometry hrequest⟩
  · exact realization.card_relevantMarkers
  · exact realization.card_relevantMarkers_le_demand
  · exact realization.card_relevantComponentOccurrences_le_demand

end

end Erdos390.WholePaper
