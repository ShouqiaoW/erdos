import Erdos390.WholePaper.BankOrdinaryPaperComponents

/-! # Expanded statement audit for realized ordinary components -/

open Filter Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! The constructor audit deliberately names all three realization fields. -/
example {n M : ℕ}
    (matching : BankOrdinaryPoolMatching n M)
    (hn : 1 ≤ n) (hM : 2 * n ≤ M) :
    (BankOrdinaryPaperRealization.mk matching hn hM).matching = matching ∧
      (BankOrdinaryPaperRealization.mk matching hn hM).one_le_n = hn ∧
      (BankOrdinaryPaperRealization.mk matching hn hM).two_mul_n_le_M = hM :=
  ⟨rfl, rfl, rfl⟩

example {p : ℕ} (hp : p.Prime) :
    (bankOrdinaryCoreSources p).card ≤ p :=
  bankOrdinaryPrimeCoreSources_card_le hp

example (n : ℕ) :
    Fintype.card (SignedBankSlot (bankRoundingBetaOnSupport n)) =
      2 * bankBottomPaperDemand n :=
  bankOrdinarySignedSlots_card_eq_two_mul_demand n

example (n : ℕ) :
    (bankOrdinaryPaperRequests n).card ≤
      2 * yNat n * bankBottomPaperDemand n :=
  bankOrdinaryPaperRequests_card_le_two_mul_yNat_mul_demand n

example :
    (fun n : ℕ ↦ ((bankOrdinaryPaperRequests n).card : ℝ))
      =O[atTop] (fun n : ℕ ↦ (yNat n : ℝ) ^ 2) :=
  bankOrdinaryPaperRequests_card_isBigO_yNat_sq

example :
    Tendsto
      (fun n : ℕ ↦ (yNat n : ℝ) ^ 2 / secondOrderScale n)
      atTop (nhds 0) :=
  yNat_sq_div_secondOrderScale_tendsto_zero

example {y P P' a a' : ℕ}
    (hP : P.Prime) (hP' : P'.Prime)
    (hPy : y < P) (hP'y : y < P')
    (ha : a ∈ Nat.smoothNumbers (y + 1))
    (ha' : a' ∈ Nat.smoothNumbers (y + 1))
    (heq : P * a = P' * a') :
    (P, a) = (P', a') :=
  primeMarker_mul_smooth_pair_eq hP hP' hPy hP'y ha ha' heq

example {n M : ℕ} (R : BankOrdinaryPaperRealization n M) :
    Function.Injective R.marker :=
  R.marker_injective

example {n M : ℕ} (R : BankOrdinaryPaperRealization n M) :
    Function.Injective R.markerDonorPair :=
  R.markerDonorPair_injective

example {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    3 * R.marker request < n :=
  R.three_mul_marker_lt_n request

example {n M : ℕ} (R : BankOrdinaryPaperRealization n M) :
    R.markers.card = (bankOrdinaryPaperRequests n).card :=
  R.markers_card_eq_paperRequests_card

example {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (P : ↑R.markers) :
    R.marker (R.requestForMarker P) = P.1 :=
  R.marker_requestForMarker P

example {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (P : ↑R.markers)
    (request : ↑(bankOrdinaryPaperRequests n))
    (hmarker : R.marker request = P.1) :
    request = R.requestForMarker P :=
  R.requestForMarker_unique P request hmarker

example {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.markerSourceCore
        ⟨R.marker request, R.marker_mem_markers request⟩ =
      bankOrdinaryPaperRequestSource request.1 :=
  R.markerSourceCore_of_request request

example {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    {request request' : ↑(bankOrdinaryPaperRequests n)}
    (hmarker : R.marker request = R.marker request') :
    bankOrdinaryPaperRequestSource request.1 =
      bankOrdinaryPaperRequestSource request'.1 :=
  R.sourceCore_eq_of_marker_eq hmarker

example {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.targetStateValue request < R.sourceStateValue request ∧
      R.sourceStateValue request ≤ 2 * n ∧
      2 * n < R.donorValue request :=
  ⟨R.targetStateValue_lt_sourceStateValue request,
    R.sourceStateValue_le_two_mul_n request,
    R.two_mul_n_lt_donorValue request⟩

example {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    completeRoughSignature (yNat n) (R.sourceStateValue request) =
        completeRoughSignature (yNat n) (R.targetStateValue request) ∧
      completeRoughSignature (yNat n) (R.targetStateValue request) =
        completeRoughSignature (yNat n) (R.donorValue request) :=
  R.state_donor_completeRoughSignature_eq request

example {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    (R.componentOccurrences request).card = 3 :=
  R.componentOccurrences_card request

example {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n))
    {occurrence : ℕ}
    (hoccurrence : occurrence ∈ R.componentOccurrences request) :
    occurrence ∈ factorInterval n M :=
  R.componentOccurrence_mem_factorInterval request hoccurrence

example {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    {request request' : ↑(bankOrdinaryPaperRequests n)}
    (hrequest : request ≠ request') :
    Disjoint (R.componentOccurrences request)
      (R.componentOccurrences request') :=
  R.componentOccurrences_disjoint hrequest

example {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    {request request' : ↑(bankOrdinaryPaperRequests n)}
    (hpools : bankOrdinaryPaperRequestPool n request.1 ≠
      bankOrdinaryPaperRequestPool n request'.1)
    (kind kind' : BankOrdinaryPaperOccurrenceKind) :
    R.occurrenceValue request kind ≠
      R.occurrenceValue request' kind' :=
  R.occurrenceValue_ne_of_pool_ne hpools kind kind'

example {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    {request request' : ↑(bankOrdinaryPaperRequests n)}
    {kind kind' : BankOrdinaryPaperOccurrenceKind}
    (heq : R.occurrenceValue request kind =
      R.occurrenceValue request' kind') :
    request = request' :=
  R.occurrenceValue_eq_marker_implies_request_eq heq

example {P source target : ℕ}
    (hP : P ≠ 0) (hsource : source ≠ 0) (htarget : target ≠ 0) :
    factorMoveChange (P * source) (P * target) =
      factorMoveChange source target :=
  BankOrdinaryPaperRealization.factorMoveChange_mul_left
    hP hsource htarget

example {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.realizedComponentChange request =
      match (bankOrdinaryPaperRequestPool n request.1).2 with
      | .downward =>
          factorMoveChange
            (bankOrdinaryPaperRequestSource request.1)
            (bankOrdinaryPaperRequestTarget request.1)
      | .upward =>
          -factorMoveChange
            (bankOrdinaryPaperRequestSource request.1)
            (bankOrdinaryPaperRequestTarget request.1) :=
  R.realizedComponentChange_eq request

example {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.realizedSlotChange slot =
      BankOrdinaryPaperRealization.signedFinitePathChange slot :=
  R.realizedSlotChange_eq_signedFinitePathChange slot

example {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (hp5 : 5 ≤ slot.1.1) :
    R.realizedSlotChange slot =
      BankOrdinaryPaperRealization.signedPrimeToFiveChange slot :=
  R.realizedSlotChange_eq_signedPrimeToFiveChange slot hp5

example {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      Nonempty (BankOrdinaryPaperRealization n
        (upperEndpoint n (upperTailLength c n))) :=
  eventually_exists_bankOrdinaryPaperRealization hc

end

end Erdos390.WholePaper
