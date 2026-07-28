import Erdos390.WholePaper.BankBottomPaperComponents
import Erdos390.WholePaper.BankOrdinaryPaperComponents

/-!
# Combined bottom and ordinary bank realization

This file is only the composition layer.  The two allocation mechanisms stay
independent, but their marker ranges are strictly separated:

`3 * ordinaryMarker < n < 3 * bottomMarker`.

Consequently the marker maps remain injective after the two request families
are joined.  Prime-marker recovery also turns this strict separation into
cross-family disjointness of the actual state/donor occurrence sets.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-- The joint marker-request type: relevant bottom components on the left and
all ordinary path components on the right. -/
abbrev BankPaperMarkerRequest (n : ℕ) :=
  ↑(bankBottomRelevantPaperRequests n) ⊕
    ↑(bankOrdinaryPaperRequests n)

/-- A complete bank realization, with the eventual local geometry retained
as fields because it is precisely what cross-family marker recovery uses. -/
structure BankPaperRealization (n M : ℕ) where
  bottom : BankBottomPaperRealization n M
  ordinary : BankOrdinaryPaperRealization n M
  six_le_yNat : 6 ≤ yNat n
  three_mul_yNat_le_n : 3 * yNat n ≤ n

namespace BankPaperRealization

def marker
    {n M : ℕ} (R : BankPaperRealization n M) :
    BankPaperMarkerRequest n → ℕ
  | .inl request =>
      R.bottom.marker (bankBottomRelevantRequestToPaperRequest request)
  | .inr request => R.ordinary.marker request

/-- The two marker ranges are separated before any factorization argument is
needed. -/
theorem ordinaryMarker_lt_bottomMarker
    {n M : ℕ} (R : BankPaperRealization n M)
    (ordinaryRequest : ↑(bankOrdinaryPaperRequests n))
    (bottomRequest : ↑(bankBottomPaperRequests n)) :
    R.ordinary.marker ordinaryRequest <
      R.bottom.marker bottomRequest := by
  have hordinary :=
    R.ordinary.three_mul_marker_lt_n ordinaryRequest
  have hbottom := R.bottom.n_lt_three_mul_marker
    R.ordinary.two_mul_n_le_M bottomRequest
  omega

/-- Marker assignment is globally injective after adjoining the relevant
bottom requests and all ordinary requests. -/
theorem marker_injective
    {n M : ℕ} (R : BankPaperRealization n M) :
    Function.Injective R.marker := by
  intro request request' hmarker
  cases request with
  | inl bottomRequest =>
      cases request' with
      | inl bottomRequest' =>
          have hrequest : bottomRequest = bottomRequest' :=
            R.bottom.relevantMarkerMap_injective
              (by simpa only [marker] using hmarker)
          exact congrArg Sum.inl hrequest
      | inr ordinaryRequest =>
          exfalso
          have hlt := R.ordinaryMarker_lt_bottomMarker ordinaryRequest
            (bankBottomRelevantRequestToPaperRequest bottomRequest)
          simp only [marker] at hmarker
          omega
  | inr ordinaryRequest =>
      cases request' with
      | inl bottomRequest =>
          exfalso
          have hlt := R.ordinaryMarker_lt_bottomMarker ordinaryRequest
            (bankBottomRelevantRequestToPaperRequest bottomRequest)
          simp only [marker] at hmarker
          omega
      | inr ordinaryRequest' =>
          have hrequest : ordinaryRequest = ordinaryRequest' :=
            R.ordinary.marker_injective
              (by simpa only [marker] using hmarker)
          exact congrArg Sum.inr hrequest

def ordinaryMarkers
    {n M : ℕ} (R : BankPaperRealization n M) : Finset ℕ :=
  R.ordinary.markers

def bottomMarkers
    {n M : ℕ} (R : BankPaperRealization n M) : Finset ℕ :=
  R.bottom.relevantMarkers

def allMarkers
    {n M : ℕ} (R : BankPaperRealization n M) : Finset ℕ :=
  R.ordinaryMarkers ∪ R.bottomMarkers

theorem ordinaryMarkers_disjoint_bottomMarkers
    {n M : ℕ} (R : BankPaperRealization n M) :
    Disjoint R.ordinaryMarkers R.bottomMarkers := by
  rw [Finset.disjoint_left]
  intro P hordinary hbottom
  rw [ordinaryMarkers, BankOrdinaryPaperRealization.markers,
    Finset.mem_image] at hordinary
  obtain ⟨ordinaryRequest, _hrequest, hordinaryP⟩ := hordinary
  rw [bottomMarkers, BankBottomPaperRealization.relevantMarkers,
    Finset.mem_image] at hbottom
  obtain ⟨bottomRequest, _hrequest, hbottomP⟩ := hbottom
  have hlt := R.ordinaryMarker_lt_bottomMarker ordinaryRequest
    (bankBottomRelevantRequestToPaperRequest bottomRequest)
  omega

theorem allMarkers_card
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.allMarkers.card =
      (bankOrdinaryPaperRequests n).card +
        (bankBottomRelevantPaperRequests n).card := by
  rw [allMarkers,
    Finset.card_union_of_disjoint R.ordinaryMarkers_disjoint_bottomMarkers,
    ordinaryMarkers, bottomMarkers,
    R.ordinary.markers_card_eq_paperRequests_card,
    R.bottom.card_relevantMarkers]

/-! ## Cross-family actual occurrence disjointness -/

/-- One ordinary actual occurrence cannot equal any named bottom carrier
value.  The bottom carrier is intentionally slightly larger than its actual
factor set, so this theorem immediately covers every actual bottom factor. -/
theorem ordinaryOccurrence_ne_bottomCarrier
    {n M : ℕ} (R : BankPaperRealization n M)
    (ordinaryRequest : ↑(bankOrdinaryPaperRequests n))
    (ordinaryKind : BankOrdinaryPaperOccurrenceKind)
    (bottomRequest : ↑(bankBottomPaperRequests n))
    (bottomKind : BankBottomPaperOccurrenceKind) :
    R.ordinary.occurrenceValue ordinaryRequest ordinaryKind ≠
      R.bottom.occurrenceValue bottomRequest bottomKind := by
  intro heq
  have hbottomSmooth :
      bankBottomPaperOccurrenceMultiplier
          (R.bottom.move bottomRequest) bottomKind ∈
        Nat.smoothNumbers (yNat n + 1) := by
    apply Nat.mem_smoothNumbers_of_lt
      (bankBottomPaperOccurrenceMultiplier_pos _ _)
    exact lt_of_le_of_lt
      (bankBottomPaperOccurrenceMultiplier_le_six _ _)
      (Nat.lt_succ_of_le R.six_le_yNat)
  have hproduct :
      R.ordinary.marker ordinaryRequest *
          R.ordinary.occurrenceCofactor ordinaryRequest ordinaryKind =
        R.bottom.marker bottomRequest *
          bankBottomPaperOccurrenceMultiplier
            (R.bottom.move bottomRequest) bottomKind := by
    calc
      R.ordinary.marker ordinaryRequest *
          R.ordinary.occurrenceCofactor ordinaryRequest ordinaryKind =
          bankBottomPaperOccurrenceMultiplier
              (R.bottom.move bottomRequest) bottomKind *
            R.bottom.marker bottomRequest := by
              simpa only [BankOrdinaryPaperRealization.occurrenceValue,
                BankBottomPaperRealization.occurrenceValue] using heq
      _ = R.bottom.marker bottomRequest *
          bankBottomPaperOccurrenceMultiplier
            (R.bottom.move bottomRequest) bottomKind := Nat.mul_comm _ _
  have hmarkers := primeMarker_mul_smooth_marker_eq
    (R.ordinary.marker_prime ordinaryRequest)
    (R.bottom.marker_prime bottomRequest)
    (R.ordinary.yNat_lt_marker ordinaryRequest)
    (R.bottom.yNat_lt_marker R.ordinary.two_mul_n_le_M
      R.three_mul_yNat_le_n bottomRequest)
    (R.ordinary.occurrenceCofactor_smooth ordinaryRequest ordinaryKind)
    hbottomSmooth hproduct
  exact (ne_of_lt (R.ordinaryMarker_lt_bottomMarker
    ordinaryRequest bottomRequest)) hmarkers

theorem ordinaryComponent_disjoint_bottomComponent
    {n M : ℕ} (R : BankPaperRealization n M)
    (ordinaryRequest : ↑(bankOrdinaryPaperRequests n))
    (bottomRequest : ↑(bankBottomPaperRequests n)) :
    Disjoint (R.ordinary.componentOccurrences ordinaryRequest)
      (R.bottom.componentOccurrences bottomRequest) := by
  rw [Finset.disjoint_left]
  intro occurrence hordinary hbottom
  rw [BankOrdinaryPaperRealization.componentOccurrences,
    Finset.mem_image] at hordinary
  obtain ⟨ordinaryKind, _hkind, hordinaryValue⟩ := hordinary
  have hbottomCarrier :=
    R.bottom.componentOccurrences_subset_carrierValueSet bottomRequest hbottom
  rw [BankBottomPaperRealization.carrierValueSet,
    Finset.mem_image] at hbottomCarrier
  obtain ⟨bottomKind, _hkind, hbottomValue⟩ := hbottomCarrier
  exact (R.ordinaryOccurrence_ne_bottomCarrier ordinaryRequest ordinaryKind
    bottomRequest bottomKind)
      (hordinaryValue.trans hbottomValue.symm)

/-- The union of all ordinary actual component occurrences. -/
def ordinaryComponentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M) : Finset ℕ :=
  (bankOrdinaryPaperRequests n).attach.biUnion
    (fun request ↦ R.ordinary.componentOccurrences request)

def bottomComponentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M) : Finset ℕ :=
  R.bottom.relevantComponentOccurrences

def allComponentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M) : Finset ℕ :=
  R.ordinaryComponentOccurrences ∪ R.bottomComponentOccurrences

theorem ordinaryComponentOccurrences_disjoint_bottomComponentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M) :
    Disjoint R.ordinaryComponentOccurrences
      R.bottomComponentOccurrences := by
  rw [Finset.disjoint_left]
  intro occurrence hordinary hbottom
  rw [ordinaryComponentOccurrences, Finset.mem_biUnion] at hordinary
  obtain ⟨ordinaryRequest, _hrequest, hordinaryOccurrence⟩ := hordinary
  rw [bottomComponentOccurrences,
    BankBottomPaperRealization.relevantComponentOccurrences,
    Finset.mem_biUnion] at hbottom
  obtain ⟨bottomRequest, _hrequest, hbottomOccurrence⟩ := hbottom
  exact (Finset.disjoint_left.mp
    (R.ordinaryComponent_disjoint_bottomComponent ordinaryRequest
      (bankBottomRelevantRequestToPaperRequest bottomRequest)))
        hordinaryOccurrence hbottomOccurrence

theorem ordinaryComponentOccurrences_card_le
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.ordinaryComponentOccurrences.card ≤
      3 * (bankOrdinaryPaperRequests n).card := by
  calc
    R.ordinaryComponentOccurrences.card ≤
        (bankOrdinaryPaperRequests n).attach.card * 3 := by
      exact Finset.card_biUnion_le_card_mul _ _ 3
        (fun request _hrequest ↦ by
          rw [R.ordinary.componentOccurrences_card request])
    _ = 3 * (bankOrdinaryPaperRequests n).card := by
      simp [Nat.mul_comm]

theorem allComponentOccurrences_card_le
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.allComponentOccurrences.card ≤
      3 * (bankOrdinaryPaperRequests n).card +
        24 * bankBottomPaperDemand n := by
  rw [allComponentOccurrences,
    Finset.card_union_of_disjoint
      R.ordinaryComponentOccurrences_disjoint_bottomComponentOccurrences]
  exact Nat.add_le_add R.ordinaryComponentOccurrences_card_le
    R.bottom.card_relevantComponentOccurrences_le_demand

end BankPaperRealization

/-! ## Terminal combined realization -/

theorem eventually_exists_bankPaperRealization
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      Nonempty (BankPaperRealization n
        (upperEndpoint n (upperTailLength c n))) := by
  filter_upwards [eventually_exists_bankBottomPaper_component_realization hc,
      eventually_exists_bankOrdinaryPaperRealization hc,
      eventually_bankBottom_six_le_yNat,
      eventually_bankBottom_three_mul_yNat_le_self]
      with n hbottom hordinary hySix hgeometry
  obtain ⟨bottom, _hinterval, _hsignature, _hdisjoint,
    _hmarkerCard, _hmarkerBound, _hoccurrenceBound⟩ := hbottom
  exact ⟨⟨bottom, Classical.choice hordinary, hySix, hgeometry⟩⟩

end

end Erdos390.WholePaper
