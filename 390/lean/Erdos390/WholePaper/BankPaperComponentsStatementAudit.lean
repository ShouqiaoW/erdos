import Erdos390.WholePaper.BankPaperComponents

/-! # Expanded statement audit for the combined bank realization -/

open Filter

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! The constructor audit names all four retained realization fields. -/

example {n M : ℕ}
    (bottom : BankBottomPaperRealization n M)
    (ordinary : BankOrdinaryPaperRealization n M)
    (hySix : 6 ≤ yNat n) (hgeometry : 3 * yNat n ≤ n) :
    (BankPaperRealization.mk bottom ordinary hySix hgeometry).bottom = bottom ∧
      (BankPaperRealization.mk bottom ordinary hySix hgeometry).ordinary =
        ordinary ∧
      (BankPaperRealization.mk bottom ordinary hySix hgeometry).six_le_yNat =
        hySix ∧
      (BankPaperRealization.mk bottom ordinary hySix hgeometry).three_mul_yNat_le_n =
        hgeometry :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! The joint marker map uses only relevant bottom requests on the left and
all ordinary requests on the right. -/

example {n M : ℕ} (R : BankPaperRealization n M)
    (bottomRequest : ↑(bankBottomRelevantPaperRequests n)) :
    R.marker (.inl bottomRequest) =
      R.bottom.marker
        (bankBottomRelevantRequestToPaperRequest bottomRequest) :=
  rfl

example {n M : ℕ} (R : BankPaperRealization n M)
    (ordinaryRequest : ↑(bankOrdinaryPaperRequests n)) :
    R.marker (.inr ordinaryRequest) = R.ordinary.marker ordinaryRequest :=
  rfl

example {n M : ℕ} (R : BankPaperRealization n M)
    (ordinaryRequest : ↑(bankOrdinaryPaperRequests n))
    (bottomRequest : ↑(bankBottomPaperRequests n)) :
    R.ordinary.marker ordinaryRequest < R.bottom.marker bottomRequest :=
  R.ordinaryMarker_lt_bottomMarker ordinaryRequest bottomRequest

example {n M : ℕ} (R : BankPaperRealization n M) :
    Function.Injective R.marker :=
  R.marker_injective

example {n M : ℕ} (R : BankPaperRealization n M) :
    Disjoint R.ordinaryMarkers R.bottomMarkers :=
  R.ordinaryMarkers_disjoint_bottomMarkers

example {n M : ℕ} (R : BankPaperRealization n M) :
    R.allMarkers.card =
      (bankOrdinaryPaperRequests n).card +
        (bankBottomRelevantPaperRequests n).card :=
  R.allMarkers_card

/-! The combined object retains both component families' interval and rough
signature interfaces.  These are projection audits of existing public API;
the composition file does not assert a separate unified theorem. -/

example {n M : ℕ} (R : BankPaperRealization n M)
    (ordinaryRequest : ↑(bankOrdinaryPaperRequests n))
    {occurrence : ℕ}
    (hoccurrence : occurrence ∈
      R.ordinary.componentOccurrences ordinaryRequest) :
    occurrence ∈ factorInterval n M :=
  R.ordinary.componentOccurrence_mem_factorInterval
    ordinaryRequest hoccurrence

example {n M : ℕ} (R : BankPaperRealization n M)
    (bottomRequest : ↑(bankBottomPaperRequests n))
    {occurrence : ℕ}
    (hoccurrence : occurrence ∈
      R.bottom.componentOccurrences bottomRequest) :
    occurrence ∈ factorInterval n M :=
  R.bottom.componentOccurrence_mem_factorInterval
    R.ordinary.two_mul_n_le_M bottomRequest hoccurrence

example {n M : ℕ} (R : BankPaperRealization n M)
    (ordinaryRequest : ↑(bankOrdinaryPaperRequests n)) :
    completeRoughSignature (yNat n)
          (R.ordinary.sourceStateValue ordinaryRequest) =
        completeRoughSignature (yNat n)
          (R.ordinary.targetStateValue ordinaryRequest) ∧
      completeRoughSignature (yNat n)
          (R.ordinary.targetStateValue ordinaryRequest) =
        completeRoughSignature (yNat n)
          (R.ordinary.donorValue ordinaryRequest) :=
  R.ordinary.state_donor_completeRoughSignature_eq ordinaryRequest

example {n M : ℕ} (R : BankPaperRealization n M)
    (bottomRequest : ↑(bankBottomPaperRequests n))
    {occurrence : ℕ}
    (hoccurrence : occurrence ∈
      R.bottom.componentOccurrences bottomRequest) :
    completeRoughSignature (yNat n) occurrence =
      completeRoughSignature (yNat n)
        (R.bottom.marker bottomRequest) :=
  R.bottom.componentOccurrence_completeRoughSignature
    R.six_le_yNat bottomRequest hoccurrence

/-! Within-family collision freedom remains available through the two
realization projections. -/

example {n M : ℕ} (R : BankPaperRealization n M)
    {ordinaryRequest ordinaryRequest' :
      ↑(bankOrdinaryPaperRequests n)}
    (hrequest : ordinaryRequest ≠ ordinaryRequest')
    (kind kind' : BankOrdinaryPaperOccurrenceKind) :
    R.ordinary.occurrenceValue ordinaryRequest kind ≠
      R.ordinary.occurrenceValue ordinaryRequest' kind' :=
  R.ordinary.occurrenceValue_ne_of_request_ne hrequest kind kind'

example {n M : ℕ} (R : BankPaperRealization n M)
    {ordinaryRequest ordinaryRequest' :
      ↑(bankOrdinaryPaperRequests n)}
    (hrequest : ordinaryRequest ≠ ordinaryRequest') :
    Disjoint
      (R.ordinary.componentOccurrences ordinaryRequest)
      (R.ordinary.componentOccurrences ordinaryRequest') :=
  R.ordinary.componentOccurrences_disjoint hrequest

example {n M : ℕ} (R : BankPaperRealization n M)
    {bottomRequest bottomRequest' : ↑(bankBottomPaperRequests n)}
    (hrequest : bottomRequest ≠ bottomRequest')
    (kind kind' : BankBottomPaperOccurrenceKind) :
    R.bottom.occurrenceValue bottomRequest kind ≠
      R.bottom.occurrenceValue bottomRequest' kind' :=
  R.bottom.occurrenceValue_ne_of_request_ne
    R.ordinary.two_mul_n_le_M R.six_le_yNat
      R.three_mul_yNat_le_n hrequest kind kind'

example {n M : ℕ} (R : BankPaperRealization n M)
    {bottomRequest bottomRequest' : ↑(bankBottomPaperRequests n)}
    (hrequest : bottomRequest ≠ bottomRequest') :
    Disjoint (R.bottom.carrierValueSet bottomRequest)
        (R.bottom.carrierValueSet bottomRequest') ∧
      Disjoint (R.bottom.componentOccurrences bottomRequest)
        (R.bottom.componentOccurrences bottomRequest') :=
  ⟨R.bottom.carrierValueSets_disjoint_of_request_ne
      R.ordinary.two_mul_n_le_M R.six_le_yNat
        R.three_mul_yNat_le_n hrequest,
    R.bottom.componentOccurrences_disjoint_of_request_ne
      R.ordinary.two_mul_n_le_M R.six_le_yNat
        R.three_mul_yNat_le_n hrequest⟩

/-! Cross-family collision freedom, first at the named-value level and then
at the actual component-occurrence level. -/

example {n M : ℕ} (R : BankPaperRealization n M)
    (ordinaryRequest : ↑(bankOrdinaryPaperRequests n))
    (ordinaryKind : BankOrdinaryPaperOccurrenceKind)
    (bottomRequest : ↑(bankBottomPaperRequests n))
    (bottomKind : BankBottomPaperOccurrenceKind) :
    R.ordinary.occurrenceValue ordinaryRequest ordinaryKind ≠
      R.bottom.occurrenceValue bottomRequest bottomKind :=
  R.ordinaryOccurrence_ne_bottomCarrier ordinaryRequest ordinaryKind
    bottomRequest bottomKind

example {n M : ℕ} (R : BankPaperRealization n M)
    (ordinaryRequest : ↑(bankOrdinaryPaperRequests n))
    (bottomRequest : ↑(bankBottomPaperRequests n)) :
    Disjoint (R.ordinary.componentOccurrences ordinaryRequest)
      (R.bottom.componentOccurrences bottomRequest) :=
  R.ordinaryComponent_disjoint_bottomComponent ordinaryRequest bottomRequest

example {n M : ℕ} (R : BankPaperRealization n M) :
    Disjoint R.ordinaryComponentOccurrences
      R.bottomComponentOccurrences :=
  R.ordinaryComponentOccurrences_disjoint_bottomComponentOccurrences

example {n M : ℕ} (R : BankPaperRealization n M) :
    R.ordinaryComponentOccurrences.card ≤
      3 * (bankOrdinaryPaperRequests n).card :=
  R.ordinaryComponentOccurrences_card_le

example {n M : ℕ} (R : BankPaperRealization n M) :
    R.allComponentOccurrences.card ≤
      3 * (bankOrdinaryPaperRequests n).card +
        24 * bankBottomPaperDemand n :=
  R.allComponentOccurrences_card_le

example {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      Nonempty (BankPaperRealization n
        (upperEndpoint n (upperTailLength c n))) :=
  eventually_exists_bankPaperRealization hc

end

end Erdos390.WholePaper
