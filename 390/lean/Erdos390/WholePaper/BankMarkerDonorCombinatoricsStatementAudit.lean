import Erdos390.WholePaper.BankMarkerDonorCombinatorics

/-! # Expanded literal statement audit for finite marker--donor combinatorics -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example {Marker Donor : Type*} [DecidableEq Marker]
    (eligible : Finset (Marker × Donor)) (marker : Marker) :
    bankDonorMultiplicity eligible marker =
      (eligible.filter fun pair ↦ pair.1 = marker).card := rfl

example {Marker Donor : Type*} [DecidableEq Marker]
    (eligible : Finset (Marker × Donor)) :
    bankEligibleMarkers eligible = eligible.image Prod.fst := rfl

example {Marker Donor : Type*} [DecidableEq Marker]
    (eligible : Finset (Marker × Donor)) :
    (∑ marker ∈ eligible.image Prod.fst,
        (eligible.filter fun pair ↦ pair.1 = marker).card) =
      eligible.card := by
  simpa only [bankEligibleMarkers, bankDonorMultiplicity,
    bankMarkerOccurrenceTotal] using
      sum_bankDonorMultiplicity_eq_occurrenceTotal eligible

example {Marker Donor : Type*} [DecidableEq Marker]
    (eligible : Finset (Marker × Donor)) (m : ℕ)
    (hmultiplicity : ∀ marker ∈ eligible.image Prod.fst,
      (eligible.filter fun pair ↦ pair.1 = marker).card ≤ m) :
    eligible.card ≤ m * (eligible.image Prod.fst).card := by
  simpa only [bankEligibleMarkers, bankDonorMultiplicity,
    bankMarkerOccurrenceTotal, bankEligibleMarkerCount] using
      bankMarkerOccurrenceTotal_le_mul_markerCount
        eligible m hmultiplicity

example {Marker Donor : Type*} [DecidableEq Marker]
    (eligible : Finset (Marker × Donor)) (m : ℕ) (hm : 0 < m)
    (hmultiplicity : ∀ marker ∈ eligible.image Prod.fst,
      (eligible.filter fun pair ↦ pair.1 = marker).card ≤ m) :
    eligible.card ⌈/⌉ m ≤ (eligible.image Prod.fst).card := by
  simpa only [bankEligibleMarkers, bankDonorMultiplicity,
    bankMarkerOccurrenceTotal, bankEligibleMarkerCount] using
      bankOccurrenceCeilDiv_le_markerCount
        eligible m hm hmultiplicity

example {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor))
    (marker : ↑(eligible.image Prod.fst)) :
    (marker.1, bankChosenDonor eligible marker) ∈ eligible := by
  simpa only [bankEligibleMarkers, bankChosenMarkerDonor] using
    bankChosenMarkerDonor_mem eligible marker

example {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    Function.Injective
      (fun marker : ↑(eligible.image Prod.fst) ↦
        (marker.1, bankChosenDonor eligible marker)) := by
  simpa only [bankEligibleMarkers, bankChosenMarkerDonor] using
    bankChosenMarkerDonor_injective eligible

example {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    ((eligible.image Prod.fst).attach.image
        (fun marker ↦ (marker.1, bankChosenDonor eligible marker))).card =
      (eligible.image Prod.fst).card := by
  simpa only [bankEligibleMarkers, bankChosenMarkerDonor,
    bankMarkerDonorPairs, bankEligibleMarkerCount] using
      card_bankMarkerDonorPairs eligible

example {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    ((eligible.image Prod.fst).attach.image
        (fun marker ↦ (marker.1, bankChosenDonor eligible marker))).image
          Prod.fst = eligible.image Prod.fst := by
  simpa only [bankEligibleMarkers, bankChosenMarkerDonor,
    bankMarkerDonorPairs] using
      image_fst_bankMarkerDonorPairs eligible

example {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    (eligible.image Prod.fst).attach.image
        (fun marker ↦ (marker.1, bankChosenDonor eligible marker)) ⊆
      eligible := by
  simpa only [bankEligibleMarkers, bankChosenMarkerDonor,
    bankMarkerDonorPairs] using
      bankMarkerDonorPairs_subset_eligible eligible

example {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor))
    {pair pair' : Marker × Donor}
    (hpair : pair ∈ bankMarkerDonorPairs eligible)
    (hpair' : pair' ∈ bankMarkerDonorPairs eligible)
    (hmarker : pair.1 = pair'.1) :
    pair = pair' :=
  bankMarkerDonorPairs_injective_by_marker eligible hpair hpair' hmarker

example {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    Disjoint (bankOrientationPoolFirst eligible)
        (bankMarkerDonorPairs eligible \ bankOrientationPoolFirst eligible) ∧
      bankOrientationPoolFirst eligible ∪
          (bankMarkerDonorPairs eligible \ bankOrientationPoolFirst eligible) =
        bankMarkerDonorPairs eligible ∧
      (bankOrientationPoolFirst eligible).card ≤
          (bankMarkerDonorPairs eligible \
            bankOrientationPoolFirst eligible).card ∧
      (bankMarkerDonorPairs eligible \
          bankOrientationPoolFirst eligible).card ≤
        (bankOrientationPoolFirst eligible).card + 1 := by
  constructor
  · simpa only [bankOrientationPoolSecond] using
      bankOrientationPools_disjoint eligible
  constructor
  · simpa only [bankOrientationPoolSecond] using
      bankOrientationPools_union eligible
  · simpa only [bankOrientationPoolSecond] using
      bankOrientationPools_card_balanced eligible

example {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    bankOrientationPoolFirst eligible ⊆ eligible ∧
      (bankMarkerDonorPairs eligible \ bankOrientationPoolFirst eligible) ⊆
        eligible := by
  exact ⟨bankOrientationPoolFirst_subset_eligible eligible,
    by simpa only [bankOrientationPoolSecond] using
      bankOrientationPoolSecond_subset_eligible eligible⟩

end

end Erdos390.WholePaper
