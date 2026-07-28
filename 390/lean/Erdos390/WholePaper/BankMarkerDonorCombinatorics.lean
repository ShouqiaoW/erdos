import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Finset.Card

/-!
# Finite marker--donor combinatorics

This file treats eligibility as an actual finite relation of marker--donor
pairs.  It proves only finite double counting, bounded-multiplicity counting,
choice of one donor already present in the relation, and a balanced split of
the chosen pairs into two orientation pools.  It makes no prime-number-theorem
or asymptotic supply assertion.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Multiplicity of a marker in a finite marker--donor eligibility relation. -/
def bankDonorMultiplicity {Marker Donor : Type*} [DecidableEq Marker]
    (eligible : Finset (Marker × Donor)) (marker : Marker) : ℕ :=
  (eligible.filter fun pair ↦ pair.1 = marker).card

/-- The actual markers occurring in at least one eligible pair. -/
def bankEligibleMarkers {Marker Donor : Type*} [DecidableEq Marker]
    (eligible : Finset (Marker × Donor)) : Finset Marker :=
  eligible.image Prod.fst

/-- Total number of eligible marker--donor occurrences. -/
def bankMarkerOccurrenceTotal {Marker Donor : Type*}
    (eligible : Finset (Marker × Donor)) : ℕ :=
  eligible.card

/-- Number of markers having at least one eligible donor. -/
def bankEligibleMarkerCount {Marker Donor : Type*} [DecidableEq Marker]
    (eligible : Finset (Marker × Donor)) : ℕ :=
  (bankEligibleMarkers eligible).card

/-- Literal double count of the finite marker--donor relation by marker fibers. -/
theorem sum_bankDonorMultiplicity_eq_occurrenceTotal
    {Marker Donor : Type*} [DecidableEq Marker]
    (eligible : Finset (Marker × Donor)) :
    ∑ marker ∈ bankEligibleMarkers eligible,
        bankDonorMultiplicity eligible marker =
      bankMarkerOccurrenceTotal eligible := by
  unfold bankEligibleMarkers bankDonorMultiplicity bankMarkerOccurrenceTotal
  exact (Finset.card_eq_sum_card_image Prod.fst eligible).symm

/-- A uniform fiber bound gives the literal occurrence bound `C ≤ m * K`. -/
theorem bankMarkerOccurrenceTotal_le_mul_markerCount
    {Marker Donor : Type*} [DecidableEq Marker]
    (eligible : Finset (Marker × Donor)) (m : ℕ)
    (hmultiplicity : ∀ marker ∈ bankEligibleMarkers eligible,
      bankDonorMultiplicity eligible marker ≤ m) :
    bankMarkerOccurrenceTotal eligible ≤
      m * bankEligibleMarkerCount eligible := by
  rw [← sum_bankDonorMultiplicity_eq_occurrenceTotal eligible]
  unfold bankEligibleMarkerCount
  calc
    (∑ marker ∈ bankEligibleMarkers eligible,
        bankDonorMultiplicity eligible marker) ≤
        ∑ _marker ∈ bankEligibleMarkers eligible, m := by
      exact Finset.sum_le_sum fun marker hmarker ↦
        hmultiplicity marker hmarker
    _ = m * (bankEligibleMarkers eligible).card := by
      simp [mul_comm]

/-- Dividing the occurrence bound by a positive multiplicity bound gives
the exact ceiling lower bound on the number of eligible markers. -/
theorem bankOccurrenceCeilDiv_le_markerCount
    {Marker Donor : Type*} [DecidableEq Marker]
    (eligible : Finset (Marker × Donor)) (m : ℕ) (hm : 0 < m)
    (hmultiplicity : ∀ marker ∈ bankEligibleMarkers eligible,
      bankDonorMultiplicity eligible marker ≤ m) :
    bankMarkerOccurrenceTotal eligible ⌈/⌉ m ≤
      bankEligibleMarkerCount eligible := by
  rw [ceilDiv_le_iff_le_mul hm]
  exact bankMarkerOccurrenceTotal_le_mul_markerCount eligible m hmultiplicity

private theorem eligibleMarker_exists_donor
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor))
    {marker : Marker} (hmarker : marker ∈ bankEligibleMarkers eligible) :
    ∃ donor, (marker, donor) ∈ eligible := by
  rcases Finset.mem_image.mp hmarker with ⟨⟨marker', donor⟩, hpair, hmarker'⟩
  subst marker
  exact ⟨donor, hpair⟩

/-- An actual eligible donor chosen for a marker in the finite support. -/
def bankChosenDonor
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor))
    (marker : ↑(bankEligibleMarkers eligible)) : Donor :=
  Classical.choose (eligibleMarker_exists_donor eligible marker.property)

/-- The chosen marker together with its chosen actual donor. -/
def bankChosenMarkerDonor
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor))
    (marker : ↑(bankEligibleMarkers eligible)) : Marker × Donor :=
  (marker.1, bankChosenDonor eligible marker)

theorem bankChosenMarkerDonor_mem
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor))
    (marker : ↑(bankEligibleMarkers eligible)) :
    bankChosenMarkerDonor eligible marker ∈ eligible := by
  exact Classical.choose_spec
    (eligibleMarker_exists_donor eligible marker.property)

/-- Chosen pairs are injective because their marker coordinates are distinct. -/
theorem bankChosenMarkerDonor_injective
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    Function.Injective (bankChosenMarkerDonor eligible) := by
  intro marker marker' hpairs
  apply Subtype.ext
  exact congrArg Prod.fst hpairs

/-- The finite set consisting of one actual donor pair for every eligible marker. -/
def bankMarkerDonorPairs
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) : Finset (Marker × Donor) :=
  (bankEligibleMarkers eligible).attach.image
    (bankChosenMarkerDonor eligible)

theorem bankMarkerDonorPairs_subset_eligible
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    bankMarkerDonorPairs eligible ⊆ eligible := by
  rw [bankMarkerDonorPairs, Finset.image_subset_iff]
  intro marker _hmarker
  exact bankChosenMarkerDonor_mem eligible marker

theorem card_bankMarkerDonorPairs
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    (bankMarkerDonorPairs eligible).card =
      bankEligibleMarkerCount eligible := by
  unfold bankMarkerDonorPairs bankEligibleMarkerCount
  rw [Finset.card_image_of_injective _
    (bankChosenMarkerDonor_injective eligible)]
  simp

/-- The selected pairs contain exactly the original eligible marker support. -/
theorem image_fst_bankMarkerDonorPairs
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    (bankMarkerDonorPairs eligible).image Prod.fst =
      bankEligibleMarkers eligible := by
  ext marker
  simp [bankMarkerDonorPairs, bankChosenMarkerDonor]

/-- No two selected pairs with the same marker can differ in their donor. -/
theorem bankMarkerDonorPairs_injective_by_marker
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor))
    {pair pair' : Marker × Donor}
    (hpair : pair ∈ bankMarkerDonorPairs eligible)
    (hpair' : pair' ∈ bankMarkerDonorPairs eligible)
    (hmarker : pair.1 = pair'.1) :
    pair = pair' := by
  unfold bankMarkerDonorPairs at hpair hpair'
  rcases Finset.mem_image.mp hpair with ⟨marker, _hmarkerMem, rfl⟩
  rcases Finset.mem_image.mp hpair' with ⟨marker', _hmarkerMem', rfl⟩
  have hmarkers : marker = marker' := by
    apply Subtype.ext
    exact hmarker
  subst marker'
  rfl

private theorem half_card_subset_exists {Pair : Type*} [DecidableEq Pair]
    (pairs : Finset Pair) :
    ∃ pool ⊆ pairs, pool.card = pairs.card / 2 := by
  exact Finset.exists_subset_card_eq (Nat.div_le_self pairs.card 2)

/-- One orientation pool, chosen to contain exactly half the selected pairs,
rounded down. -/
def bankOrientationPoolFirst
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) : Finset (Marker × Donor) :=
  Classical.choose (half_card_subset_exists (bankMarkerDonorPairs eligible))

/-- The complementary orientation pool. -/
def bankOrientationPoolSecond
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) : Finset (Marker × Donor) :=
  bankMarkerDonorPairs eligible \ bankOrientationPoolFirst eligible

theorem bankOrientationPoolFirst_subset_pairs
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    bankOrientationPoolFirst eligible ⊆ bankMarkerDonorPairs eligible := by
  exact (Classical.choose_spec
    (half_card_subset_exists (bankMarkerDonorPairs eligible))).1

theorem card_bankOrientationPoolFirst
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    (bankOrientationPoolFirst eligible).card =
      (bankMarkerDonorPairs eligible).card / 2 := by
  exact (Classical.choose_spec
    (half_card_subset_exists (bankMarkerDonorPairs eligible))).2

theorem bankOrientationPools_disjoint
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    Disjoint (bankOrientationPoolFirst eligible)
      (bankOrientationPoolSecond eligible) := by
  rw [Finset.disjoint_left]
  intro pair hfirst hsecond
  exact (Finset.mem_sdiff.mp hsecond).2 hfirst

theorem bankOrientationPools_union
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    bankOrientationPoolFirst eligible ∪ bankOrientationPoolSecond eligible =
      bankMarkerDonorPairs eligible := by
  unfold bankOrientationPoolSecond
  exact Finset.union_sdiff_of_subset
    (bankOrientationPoolFirst_subset_pairs eligible)

theorem card_bankOrientationPoolSecond
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    (bankOrientationPoolSecond eligible).card =
      (bankMarkerDonorPairs eligible).card -
        (bankMarkerDonorPairs eligible).card / 2 := by
  unfold bankOrientationPoolSecond
  rw [Finset.card_sdiff_of_subset
    (bankOrientationPoolFirst_subset_pairs eligible),
    card_bankOrientationPoolFirst]

/-- The two orientation-pool cardinalities differ by at most one.  The first
pool is the smaller one when the total cardinality is odd. -/
theorem bankOrientationPools_card_balanced
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    (bankOrientationPoolFirst eligible).card ≤
        (bankOrientationPoolSecond eligible).card ∧
      (bankOrientationPoolSecond eligible).card ≤
        (bankOrientationPoolFirst eligible).card + 1 := by
  rw [card_bankOrientationPoolFirst, card_bankOrientationPoolSecond]
  omega

theorem bankOrientationPoolFirst_subset_eligible
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    bankOrientationPoolFirst eligible ⊆ eligible :=
  (bankOrientationPoolFirst_subset_pairs eligible).trans
    (bankMarkerDonorPairs_subset_eligible eligible)

theorem bankOrientationPoolSecond_subset_eligible
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    bankOrientationPoolSecond eligible ⊆ eligible := by
  intro pair hpair
  exact bankMarkerDonorPairs_subset_eligible eligible
    (Finset.mem_sdiff.mp hpair).1

/-- Every pair in either orientation pool remains an actual member of the
original finite eligibility relation. -/
theorem bankOrientationPool_pair_eligible
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor))
    {pair : Marker × Donor}
    (hpair : pair ∈ bankOrientationPoolFirst eligible ∨
      pair ∈ bankOrientationPoolSecond eligible) :
    pair ∈ eligible := by
  rcases hpair with hfirst | hsecond
  · exact bankOrientationPoolFirst_subset_eligible eligible hfirst
  · exact bankOrientationPoolSecond_subset_eligible eligible hsecond

end

end Erdos390.WholePaper
