import Erdos390.WholePaper.BankBottomPaperComponents

/-! # Expanded statement audit for actual bottom-bank components -/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! The realization constructor must expose exactly the matching's assigned
marker, its pool-membership certificate, and the supplied injectivity. -/

example {n M : ℕ}
    (matching : BankBottomPoolMatching
      (bankBottomPaperRequests n) (bankBottomPaperRequestPool n)
      (fun pool ↦ bankBottomOrientedMarkerPrimes n M pool))
    (hinjective : Function.Injective matching.matchedSlot) :
    BankBottomPaperRealization n M :=
  BankBottomPaperRealization.ofMatching matching hinjective

example {n M : ℕ}
    (matching : BankBottomPoolMatching
      (bankBottomPaperRequests n) (bankBottomPaperRequestPool n)
      (fun pool ↦ bankBottomOrientedMarkerPrimes n M pool))
    (hinjective : Function.Injective matching.matchedSlot) :
    (BankBottomPaperRealization.ofMatching matching hinjective).marker =
      matching.matchedSlot :=
  rfl

example {n M : ℕ}
    (matching : BankBottomPoolMatching
      (bankBottomPaperRequests n) (bankBottomPaperRequestPool n)
      (fun pool ↦ bankBottomOrientedMarkerPrimes n M pool))
    (hinjective : Function.Injective matching.matchedSlot) :
    Function.Injective
      (BankBottomPaperRealization.ofMatching matching hinjective).marker :=
  (BankBottomPaperRealization.ofMatching matching hinjective).marker_injective

example {n M : ℕ}
    (matching : BankBottomPoolMatching
      (bankBottomPaperRequests n) (bankBottomPaperRequestPool n)
      (fun pool ↦ bankBottomOrientedMarkerPrimes n M pool))
    (hinjective : Function.Injective matching.matchedSlot)
    (request : ↑(bankBottomPaperRequests n)) :
    (BankBottomPaperRealization.ofMatching matching hinjective).marker request ∈
      bankBottomOrientedMarkerPrimes n M
        (bankBottomPaperRequestPool n request.1) :=
  (BankBottomPaperRealization.ofMatching matching hinjective).marker_mem request

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    (request : ↑(bankBottomPaperRequests n)) :
    realization.marker request ∈
      bankBottomOrientedMarkerPrimes n M
        (bankBottomPaperRequestPool n request.1) :=
  realization.marker_mem request

example :
    bankBottomIncidentStateCores .fiveToFour = (4, 5) ∧
      bankBottomIncidentStateCores .fourToThree = (3, 4) ∧
      bankBottomIncidentStateCores .threeToTwo = (2, 3) ∧
      bankBottomIncidentStateCores .twoToOne = (2, 4) := by
  simp

example :
    bankBottomRelevantMoves 3 = {.threeToTwo, .twoToOne} ∧
      bankBottomRelevantMoves 2 = {.twoToOne} := by
  simp

example {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    {move : BankBottomMove}
    (hmove : move ∈ bankBottomRelevantMoves slot.1.1) :
    (bankBottomPaperRequestOfMove slot move).1 ∈
      bankBottomRelevantPaperRequests n :=
  bankBottomPaperRequestOfMove_mem_relevant slot hmove

example {n : ℕ} {request : BankBottomPaperRequest n}
    (hprime : bankBottomPaperRequestPrime request = 3) :
    bankBottomPaperRequestRelevant request ↔
      request.2 = .threeToTwo ∨ request.2 = .twoToOne :=
  bankBottomPaperRequestRelevant_iff_of_prime_eq_three hprime

example {n : ℕ} {request : BankBottomPaperRequest n}
    (hprime : bankBottomPaperRequestPrime request = 2) :
    bankBottomPaperRequestRelevant request ↔ request.2 = .twoToOne :=
  bankBottomPaperRequestRelevant_iff_of_prime_eq_two hprime

example (n : ℕ) :
    Disjoint (bankBottomRelevantPaperRequests n)
        (bankBottomUnusedPaperRequests n) ∧
      bankBottomRelevantPaperRequests n ∪
          bankBottomUnusedPaperRequests n =
        bankBottomPaperRequests n :=
  ⟨bankBottom_relevant_unused_disjoint n,
    bankBottom_relevant_union_unused n⟩

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .fiveToFour) :
    realization.componentOccurrences request =
        {4 * realization.marker request, 5 * realization.marker request,
          6 * realization.marker request} ∧
      (realization.componentOccurrences request).card = 3 :=
  ⟨realization.componentOccurrences_fiveToFour request hmove,
    realization.card_componentOccurrences_fiveToFour request hmove⟩

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .threeToTwo) :
    realization.componentOccurrences request =
        {2 * realization.marker request, 3 * realization.marker request} ∧
      (realization.componentOccurrences request).card = 2 :=
  ⟨realization.componentOccurrences_threeToTwo request hmove,
    realization.card_componentOccurrences_threeToTwo request hmove⟩

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .threeToTwo ∨
      realization.move request = .twoToOne) :
    realization.donorOccurrence hTwoN request =
      realization.upperStateOccurrence hTwoN request :=
  realization.donorOccurrence_eq_upperStateOccurrence_of_terminalMove
    hTwoN request hmove

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) :
    n < 3 * realization.marker request ∧
      3 * realization.marker request ≤ M :=
  ⟨realization.n_lt_three_mul_marker hTwoN request,
    realization.three_mul_marker_le_M hTwoN request⟩

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) :
    3 * realization.marker request ≤ M :=
  realization.three_mul_marker_le_M hTwoN request

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    (hTwoN : 2 * n ≤ M) (hMThree : M ≤ 3 * n)
    (request : ↑(bankBottomPaperRequests n)) :
    realization.marker request ≤ n :=
  realization.marker_le_n hTwoN hMThree request

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    (request : ↑(bankBottomPaperRequests n)) :
    realization.realizedComponentChange request =
      match bankSignedSlotOrientation request.1.1 with
      | .downward => bankBottomMoveChange (realization.move request)
      | .upward => -bankBottomMoveChange (realization.move request) :=
  realization.realizedComponentChange_eq_signedMoveChange request

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    realization.realizedSlotChange slot =
      BankBottomPaperRealization.signedBottomPathChange slot :=
  realization.realizedSlotChange_eq_signedBottomPathChange slot

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (hprime : 5 ≤ slot.1.1) :
    realization.realizedSlotChange slot =
      match slot.2 with
      | .inl _copy => -coordinateUnit 5
      | .inr _copy => coordinateUnit 5 :=
  realization.realizedSlotChange_eq_signedUnit_five_of_five_le slot hprime

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (hprime : slot.1.1 = 3) :
    realization.realizedSlotChange slot =
      match slot.2 with
      | .inl _copy => -coordinateUnit 3
      | .inr _copy => coordinateUnit 3 :=
  realization.realizedSlotChange_eq_signedUnit_three slot hprime

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (hprime : slot.1.1 = 2) :
    realization.realizedSlotChange slot =
      match slot.2 with
      | .inl _copy => -coordinateUnit 2
      | .inr _copy => coordinateUnit 2 :=
  realization.realizedSlotChange_eq_signedUnit_two slot hprime

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    (hTwoN : 2 * n ≤ M) (hySix : 6 ≤ yNat n)
    (hgeometry : 3 * yNat n ≤ n)
    {request request' : ↑(bankBottomPaperRequests n)}
    (hrequest : request ≠ request') :
    Disjoint (realization.carrierValueSet request)
        (realization.carrierValueSet request') ∧
      Disjoint (realization.componentOccurrences request)
        (realization.componentOccurrences request') :=
  ⟨realization.carrierValueSets_disjoint_of_request_ne
      hTwoN hySix hgeometry hrequest,
    realization.componentOccurrences_disjoint_of_request_ne
      hTwoN hySix hgeometry hrequest⟩

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    (hySix : 6 ≤ yNat n)
    (request : ↑(bankBottomPaperRequests n)) :
    completeRoughSignature (yNat n)
          (realization.lowerStateFactor request) =
        completeRoughSignature (yNat n) (realization.marker request) ∧
      completeRoughSignature (yNat n)
          (realization.upperStateFactor request) =
        completeRoughSignature (yNat n) (realization.marker request) ∧
      completeRoughSignature (yNat n) (realization.donorFactor request) =
        completeRoughSignature (yNat n) (realization.marker request) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [BankBottomPaperRealization.occurrenceValue_lowerState] using
      (realization.occurrenceValue_completeRoughSignature hySix request
        BankBottomPaperOccurrenceKind.lowerState)
  · simpa only [BankBottomPaperRealization.occurrenceValue_upperState] using
      (realization.occurrenceValue_completeRoughSignature hySix request
        BankBottomPaperOccurrenceKind.upperState)
  · simpa only [BankBottomPaperRealization.occurrenceValue_donor] using
      (realization.occurrenceValue_completeRoughSignature hySix request
        BankBottomPaperOccurrenceKind.donor)

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n))
    {occurrence : ℕ}
    (hoccurrence : occurrence ∈ realization.componentOccurrences request) :
    occurrence ∈ factorInterval n M :=
  realization.componentOccurrence_mem_factorInterval
    hTwoN request hoccurrence

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    (hySix : 6 ≤ yNat n)
    (request : ↑(bankBottomPaperRequests n))
    {occurrence : ℕ}
    (hoccurrence : occurrence ∈ realization.componentOccurrences request) :
    completeRoughSignature (yNat n) occurrence =
      completeRoughSignature (yNat n) (realization.marker request) :=
  realization.componentOccurrence_completeRoughSignature
    hySix request hoccurrence

example {n M : ℕ} (realization : BankBottomPaperRealization n M) :
    realization.relevantMarkers.card =
        (bankBottomRelevantPaperRequests n).card ∧
      realization.relevantMarkers.card ≤ 8 * bankBottomPaperDemand n ∧
      realization.relevantComponentOccurrences.card ≤
        24 * bankBottomPaperDemand n :=
  ⟨realization.card_relevantMarkers,
    realization.card_relevantMarkers_le_demand,
    realization.card_relevantComponentOccurrences_le_demand⟩

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    (request : ↑(bankBottomRelevantPaperRequests n)) :
    realization.relevantMarkerIncidentStateCores
        ⟨realization.marker (bankBottomRelevantRequestToPaperRequest request),
          realization.relevantMarker_mem_relevantMarkers request⟩ =
      realization.incidentStateCores
        (bankBottomRelevantRequestToPaperRequest request) :=
  realization.relevantMarkerIncidentStateCores_of_request request

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    {request request' : ↑(bankBottomRelevantPaperRequests n)}
    (hmarker : realization.marker
        (bankBottomRelevantRequestToPaperRequest request) =
      realization.marker
        (bankBottomRelevantRequestToPaperRequest request')) :
    request = request' ∧
      realization.incidentStateCores
          (bankBottomRelevantRequestToPaperRequest request) =
        realization.incidentStateCores
          (bankBottomRelevantRequestToPaperRequest request') := by
  have hdata := realization.relevant_marker_incident_data_unique hmarker
  exact ⟨hdata.1, hdata.2.2.1⟩

example {n M : ℕ} (realization : BankBottomPaperRealization n M) :
    Function.Injective
      (fun request : ↑(bankBottomRelevantPaperRequests n) ↦
        realization.marker
          (bankBottomRelevantRequestToPaperRequest request)) :=
  realization.relevantMarkerMap_injective

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    {marker : ℕ} (hmarker : marker ∈ realization.relevantMarkers) :
    ∃! request : ↑(bankBottomRelevantPaperRequests n),
      realization.marker (bankBottomRelevantRequestToPaperRequest request) =
        marker :=
  realization.relevantMarker_existsUnique_request hmarker

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    (marker : ↑realization.relevantMarkers)
    (request : ↑(bankBottomRelevantPaperRequests n))
    (hmarker : realization.marker
      (bankBottomRelevantRequestToPaperRequest request) = marker.1) :
    request = realization.requestForRelevantMarker marker :=
  realization.requestForRelevantMarker_unique marker request hmarker

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
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
          (bankBottomRelevantRequestToPaperRequest request') :=
  realization.relevant_marker_incident_data_unique hmarker

example {n M : ℕ} (realization : BankBottomPaperRealization n M)
    (hTwoN : 2 * n ≤ M) (hySix : 6 ≤ yNat n)
    (hgeometry : 3 * yNat n ≤ n) :
    Disjoint realization.relevantMarkers
      realization.relevantComponentOccurrences :=
  realization.relevantMarkers_disjoint_relevantComponentOccurrences
    hTwoN hySix hgeometry

example {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ∃ realization : BankBottomPaperRealization n
          (upperEndpoint n (upperTailLength c n)),
        realization.relevantMarkers.card =
            (bankBottomRelevantPaperRequests n).card ∧
          realization.relevantMarkers.card ≤ 8 * bankBottomPaperDemand n ∧
          realization.relevantComponentOccurrences.card ≤
            24 * bankBottomPaperDemand n := by
  filter_upwards [eventually_exists_bankBottomPaper_component_realization hc]
      with n hrealization
  rcases hrealization with
    ⟨realization, _hinterval, _hsignature, _hcollision,
      hcard, hmarkers, hoccurrences⟩
  exact ⟨realization, hcard, hmarkers, hoccurrences⟩

/-! Public eventual geometry is audited independently of the terminal
realization theorem, so neither prerequisite can silently disappear. -/

example : ∀ᶠ n : ℕ in atTop, 6 ≤ yNat n :=
  eventually_bankBottom_six_le_yNat

example : ∀ᶠ n : ℕ in atTop, 3 * yNat n ≤ n :=
  eventually_bankBottom_three_mul_yNat_le_self

/-! Literal full-statement lock for the terminal component theorem.  This
retains every pool/interval membership field, every signature and collision
field, and all three cardinality conclusions. -/

example {c : ℝ} (hc : 0 < c) :
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
          24 * bankBottomPaperDemand n :=
  eventually_exists_bankBottomPaper_component_realization hc

end

end Erdos390.WholePaper
