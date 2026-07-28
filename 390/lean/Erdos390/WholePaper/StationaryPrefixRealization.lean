import Erdos390.WholePaper.ExactFinitePartition
import Erdos390.WholePaper.InfiniteAllocationCore
import Erdos390.WholePaper.StationaryLayers
import Erdos390.WholePaper.UpperScale

/-!
# Exact realization of a fixed stationary prefix

For a fixed row, this module realizes every positive coordinate of the
infinite allocation by an actual part of the stationary prime layer.
Non-distinguished coordinates are rounded down at the second-order scale;
one fixed positive coordinate absorbs the complete rounding remainder.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The finite set of strictly positive cofactor coordinates in row r. -/
def infiniteAllocationPositiveSupport (r : ℕ) : Finset ℕ :=
  (Finset.Icc (r + 1) (2 * r + 1)).filter fun q ↦
    0 < infiniteAllocation r q

@[simp]
theorem mem_infiniteAllocationPositiveSupport {r q : ℕ} :
    q ∈ infiniteAllocationPositiveSupport r ↔
      q ∈ Finset.Icc (r + 1) (2 * r + 1) ∧
        0 < infiniteAllocation r q := by
  simp only [infiniteAllocationPositiveSupport, Finset.mem_filter]

/-- Removing the zero coordinates does not change the exact row mass. -/
theorem infiniteAllocationPositiveSupport_sum
    (r : ℕ) (hr : 1 ≤ r) :
    (∑ q ∈ infiniteAllocationPositiveSupport r,
        infiniteAllocation r q) = alpha r := by
  rw [← infiniteAllocation_row_identity hr]
  apply Finset.sum_subset
  · intro q hq
    exact (mem_infiniteAllocationPositiveSupport.mp hq).1
  · intro q hq hqNotSupport
    have hnotPos : ¬0 < infiniteAllocation r q := by
      intro hpos
      exact hqNotSupport
        (mem_infiniteAllocationPositiveSupport.mpr ⟨hq, hpos⟩)
    exact le_antisymm (not_lt.mp hnotPos)
      (infiniteAllocation_nonneg r q)

theorem infiniteAllocationPositiveSupport_nonempty
    (r : ℕ) (hr : 1 ≤ r) :
    (infiniteAllocationPositiveSupport r).Nonempty := by
  by_contra h
  have hempty : infiniteAllocationPositiveSupport r = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp h
  have hsum := infiniteAllocationPositiveSupport_sum r hr
  rw [hempty] at hsum
  simp only [Finset.sum_empty] at hsum
  exact (alpha_pos r).ne' hsum.symm

/-- The real-valued positive-support mass is the cast of alpha r. -/
theorem infiniteAllocationPositiveSupport_sum_real
    (r : ℕ) (hr : 1 ≤ r) :
    (∑ q ∈ infiniteAllocationPositiveSupport r,
        (infiniteAllocation r q : ℝ)) = (alpha r : ℝ) := by
  simpa only [Rat.cast_sum] using
    congrArg (fun x : ℚ ↦ (x : ℝ))
      (infiniteAllocationPositiveSupport_sum r hr)

/-- A positive distinguished coordinate leaves strict mass slack after it
is erased from the row support. -/
theorem infiniteAllocationPositiveSupport_erase_sum_lt
    (r distinguished : ℕ) (hr : 1 ≤ r)
    (hdistinguished :
      distinguished ∈ infiniteAllocationPositiveSupport r) :
    (∑ q ∈ (infiniteAllocationPositiveSupport r).erase distinguished,
        (infiniteAllocation r q : ℝ)) < (alpha r : ℝ) := by
  have hdistinguishedPositive :
      0 < (infiniteAllocation r distinguished : ℝ) := by
    exact_mod_cast
      (mem_infiniteAllocationPositiveSupport.mp hdistinguished).2
  have hsplit :
      (∑ q ∈ (infiniteAllocationPositiveSupport r).erase distinguished,
          (infiniteAllocation r q : ℝ)) +
          (infiniteAllocation r distinguished : ℝ) =
        (alpha r : ℝ) := by
    calc
      (∑ q ∈ (infiniteAllocationPositiveSupport r).erase distinguished,
          (infiniteAllocation r q : ℝ)) +
          (infiniteAllocation r distinguished : ℝ) =
          ∑ q ∈ infiniteAllocationPositiveSupport r,
            (infiniteAllocation r q : ℝ) :=
        Finset.sum_erase_add _ _ hdistinguished
      _ = (alpha r : ℝ) :=
        infiniteAllocationPositiveSupport_sum_real r hr
  exact (lt_add_of_pos_right _ hdistinguishedPositive).trans_eq hsplit

/-- The raw floor target before the distinguished coordinate absorbs the
remainder. -/
def stationaryPrefixRawCount (n r q : ℕ) : ℕ :=
  scaledFloorCount (secondOrderScale n)
    (fun j ↦ (infiniteAllocation r j : ℝ)) q

/-- The exact exhaustive target counts in row r. -/
def stationaryPrefixCount
    (n r distinguished q : ℕ) : ℕ :=
  distinguishedRemainderCount (infiniteAllocationPositiveSupport r)
    distinguished (stationaryPrefixRawCount n r)
    (stationaryPrimeLayer n r).card q

theorem stationaryPrefixCount_eq_raw_of_ne
    {n r distinguished q : ℕ} (hq : q ≠ distinguished) :
    stationaryPrefixCount n r distinguished q =
      stationaryPrefixRawCount n r q := by
  simp only [stationaryPrefixCount, distinguishedRemainderCount, hq,
    if_false]

theorem stationaryPrefixCount_eq_remainder
    (n r distinguished : ℕ) :
    stationaryPrefixCount n r distinguished distinguished =
      (stationaryPrimeLayer n r).card -
        ∑ q ∈ (infiniteAllocationPositiveSupport r).erase distinguished,
          stationaryPrefixRawCount n r q := by
  simp only [stationaryPrefixCount, distinguishedRemainderCount, if_pos]

/-- Each unadjusted floor has the intended normalized limit. -/
theorem stationaryPrefixRawCount_normalized_tendsto
    (r q : ℕ) :
    Tendsto
      (fun n : ℕ ↦
        (stationaryPrefixRawCount n r q : ℝ) /
          secondOrderScale n)
      atTop (nhds (infiniteAllocation r q : ℝ)) := by
  have hweight : 0 ≤ (infiniteAllocation r q : ℝ) := by
    exact_mod_cast infiniteAllocation_nonneg r q
  have hfloor :=
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) hweight).comp
      secondOrderScale_tendsto_atTop
  apply hfloor.congr'
  exact Eventually.of_forall fun n ↦ by
    simp only [Function.comp_apply, stationaryPrefixRawCount,
      scaledFloorCount]
    rw [mul_comm]

/-- Strict distinguished mass slack and the layer-cardinality asymptotic
make all non-distinguished floor targets fit eventually. -/
theorem eventually_stationaryPrefixRawCount_sum_le
    (r distinguished : ℕ) (hr : 1 ≤ r)
    (hdistinguished :
      distinguished ∈ infiniteAllocationPositiveSupport r) :
    ∀ᶠ n : ℕ in atTop,
      (∑ q ∈ (infiniteAllocationPositiveSupport r).erase distinguished,
          stationaryPrefixRawCount n r q) ≤
        (stationaryPrimeLayer n r).card := by
  have hcard :
      Tendsto
        (fun n : ℕ ↦
          ((stationaryPrimeLayer n r).card : ℝ) /
            secondOrderScale n)
        atTop (nhds (alpha r : ℝ)) := by
    simpa only [secondOrderScale] using
      stationaryPrimeLayer_card_normalized_tendsto r hr
  have hgap :=
    infiniteAllocationPositiveSupport_erase_sum_lt
      r distinguished hr hdistinguished
  have hratio := hcard.eventually (eventually_gt_nhds hgap)
  filter_upwards [hratio, eventually_secondOrderScale_pos] with n
    hratioN hscale
  apply sum_scaledFloorCount_le
    ((infiniteAllocationPositiveSupport r).erase distinguished)
    (secondOrderScale n)
    (fun q ↦ (infiniteAllocation r q : ℝ))
    (stationaryPrimeLayer n r).card hscale.le
  · intro q _hq
    exact_mod_cast infiniteAllocation_nonneg r q
  · have hstrict :
        secondOrderScale n *
            (∑ q ∈
              (infiniteAllocationPositiveSupport r).erase distinguished,
              (infiniteAllocation r q : ℝ)) <
          ((stationaryPrimeLayer n r).card : ℝ) := by
      have hmul := (lt_div_iff₀ hscale).mp hratioN
      simpa only [mul_comm] using hmul
    exact hstrict.le

/-- Consequently the distinguished-remainder counts exhaust the layer
cardinality eventually. -/
theorem eventually_stationaryPrefixCount_sum_eq
    (r distinguished : ℕ) (hr : 1 ≤ r)
    (hdistinguished :
      distinguished ∈ infiniteAllocationPositiveSupport r) :
    ∀ᶠ n : ℕ in atTop,
      (∑ q ∈ infiniteAllocationPositiveSupport r,
          stationaryPrefixCount n r distinguished q) =
        (stationaryPrimeLayer n r).card := by
  filter_upwards [
    eventually_stationaryPrefixRawCount_sum_le
      r distinguished hr hdistinguished] with n hfit
  exact sum_distinguishedRemainderCount
    (infiniteAllocationPositiveSupport r) distinguished
    (stationaryPrefixRawCount n r) (stationaryPrimeLayer n r).card
    hdistinguished hfit

/-- The absorbing distinguished count has its intended normalized limit. -/
theorem stationaryPrefixCount_distinguished_normalized_tendsto
    (r distinguished : ℕ) (hr : 1 ≤ r)
    (hdistinguished :
      distinguished ∈ infiniteAllocationPositiveSupport r) :
    Tendsto
      (fun n : ℕ ↦
        (stationaryPrefixCount n r distinguished distinguished : ℝ) /
          secondOrderScale n)
      atTop
      (nhds (infiniteAllocation r distinguished : ℝ)) := by
  have hcard :
      Tendsto
        (fun n : ℕ ↦
          ((stationaryPrimeLayer n r).card : ℝ) /
            secondOrderScale n)
        atTop (nhds (alpha r : ℝ)) := by
    simpa only [secondOrderScale] using
      stationaryPrimeLayer_card_normalized_tendsto r hr
  have hfloorSum :
      Tendsto
        (fun n : ℕ ↦
          ∑ q ∈
            (infiniteAllocationPositiveSupport r).erase distinguished,
            (stationaryPrefixRawCount n r q : ℝ) /
              secondOrderScale n)
        atTop
        (nhds
          (∑ q ∈
            (infiniteAllocationPositiveSupport r).erase distinguished,
            (infiniteAllocation r q : ℝ))) := by
    apply tendsto_finset_sum
    intro q _hq
    exact stationaryPrefixRawCount_normalized_tendsto r q
  have hlimit :
      (alpha r : ℝ) -
          (∑ q ∈
            (infiniteAllocationPositiveSupport r).erase distinguished,
            (infiniteAllocation r q : ℝ)) =
        (infiniteAllocation r distinguished : ℝ) := by
    have hsplit :
        (∑ q ∈
          (infiniteAllocationPositiveSupport r).erase distinguished,
          (infiniteAllocation r q : ℝ)) +
            (infiniteAllocation r distinguished : ℝ) =
          (alpha r : ℝ) := by
      calc
        (∑ q ∈
          (infiniteAllocationPositiveSupport r).erase distinguished,
          (infiniteAllocation r q : ℝ)) +
            (infiniteAllocation r distinguished : ℝ) =
            ∑ q ∈ infiniteAllocationPositiveSupport r,
              (infiniteAllocation r q : ℝ) :=
          Finset.sum_erase_add _ _ hdistinguished
        _ = (alpha r : ℝ) :=
          infiniteAllocationPositiveSupport_sum_real r hr
    rw [← hsplit]
    ring
  have hdifference := hcard.sub hfloorSum
  rw [hlimit] at hdifference
  apply hdifference.congr'
  filter_upwards [
    eventually_stationaryPrefixRawCount_sum_le
      r distinguished hr hdistinguished] with n hfit
  rw [stationaryPrefixCount_eq_remainder]
  rw [Nat.cast_sub hfit, Nat.cast_sum]
  rw [← Finset.sum_div]
  ring

/-- Every positive coordinate, including the absorbing one, has the
prescribed normalized cardinality. -/
theorem stationaryPrefixCount_normalized_tendsto
    (r distinguished q : ℕ) (hr : 1 ≤ r)
    (hdistinguished :
      distinguished ∈ infiniteAllocationPositiveSupport r)
    (_hq : q ∈ infiniteAllocationPositiveSupport r) :
    Tendsto
      (fun n : ℕ ↦
        (stationaryPrefixCount n r distinguished q : ℝ) /
          secondOrderScale n)
      atTop (nhds (infiniteAllocation r q : ℝ)) := by
  by_cases hqd : q = distinguished
  · subst q
    exact stationaryPrefixCount_distinguished_normalized_tendsto
      r distinguished hr hdistinguished
  · apply (stationaryPrefixRawCount_normalized_tendsto r q).congr'
    exact Eventually.of_forall fun n ↦ by
      change
        (stationaryPrefixRawCount n r q : ℝ) / secondOrderScale n =
          (stationaryPrefixCount n r distinguished q : ℝ) /
            secondOrderScale n
      rw [stationaryPrefixCount_eq_raw_of_ne hqd]

/-- An actual exhaustive indexed partition of one stationary layer. -/
structure StationaryPrefixPartition
    (n r distinguished : ℕ) where
  parts : ℕ → Finset ℕ
  parts_subset :
    ∀ q ∈ infiniteAllocationPositiveSupport r,
      parts q ⊆ stationaryPrimeLayer n r
  parts_card :
    ∀ q ∈ infiniteAllocationPositiveSupport r,
      (parts q).card = stationaryPrefixCount n r distinguished q
  parts_pairwiseDisjoint :
    (infiniteAllocationPositiveSupport r : Set ℕ).PairwiseDisjoint parts
  union_parts :
    (infiniteAllocationPositiveSupport r).biUnion parts =
      stationaryPrimeLayer n r

/-- Eventually the exact target counts are realized by an exhaustive
partition of the stationary layer. -/
theorem eventually_stationaryPrefixPartition_nonempty
    (r distinguished : ℕ) (hr : 1 ≤ r)
    (hdistinguished :
      distinguished ∈ infiniteAllocationPositiveSupport r) :
    ∀ᶠ n : ℕ in atTop,
      Nonempty (StationaryPrefixPartition n r distinguished) := by
  filter_upwards [
    eventually_stationaryPrefixRawCount_sum_le
      r distinguished hr hdistinguished] with n hfit
  obtain ⟨partition⟩ :=
    exists_exactFinitePartition_distinguishedRemainder
      (stationaryPrimeLayer n r)
      (infiniteAllocationPositiveSupport r) distinguished
      (stationaryPrefixRawCount n r) hdistinguished hfit
  have hsum :
      (∑ q ∈ infiniteAllocationPositiveSupport r,
          stationaryPrefixCount n r distinguished q) =
        (stationaryPrimeLayer n r).card :=
    sum_distinguishedRemainderCount
      (infiniteAllocationPositiveSupport r) distinguished
      (stationaryPrefixRawCount n r) (stationaryPrimeLayer n r).card
      hdistinguished hfit
  have hremainderCard : partition.remainder.card = 0 := by
    rw [partition.remainder_card]
    simpa only [stationaryPrefixCount, Nat.sub_self] using
      congrArg
        (fun total ↦ (stationaryPrimeLayer n r).card - total)
        hsum
  have hremainder : partition.remainder = ∅ :=
    Finset.card_eq_zero.mp hremainderCard
  refine ⟨{
    parts := partition.parts
    parts_subset := partition.parts_subset
    parts_card := ?_
    parts_pairwiseDisjoint := partition.parts_pairwiseDisjoint
    union_parts := ?_
  }⟩
  · intro q hq
    simpa only [stationaryPrefixCount] using partition.parts_card q hq
  · simpa only [hremainder, Finset.union_empty] using
      partition.union_remainder

/-- Terminal fixed-row realization: one family of actual parts is
eventually exhaustive and disjoint, and every positive part has the exact
rational asymptotic weight. -/
theorem exists_stationaryPrefixParts
    (r distinguished : ℕ) (hr : 1 ≤ r)
    (hdistinguished :
      distinguished ∈ infiniteAllocationPositiveSupport r) :
    ∃ parts : ℕ → ℕ → Finset ℕ,
      (∀ᶠ n : ℕ in atTop,
        (∀ q ∈ infiniteAllocationPositiveSupport r,
          parts n q ⊆ stationaryPrimeLayer n r) ∧
        (∀ q ∈ infiniteAllocationPositiveSupport r,
          (parts n q).card =
            stationaryPrefixCount n r distinguished q) ∧
        (infiniteAllocationPositiveSupport r : Set ℕ).PairwiseDisjoint
          (parts n) ∧
        (infiniteAllocationPositiveSupport r).biUnion (parts n) =
          stationaryPrimeLayer n r) ∧
      ∀ q ∈ infiniteAllocationPositiveSupport r,
        Tendsto
          (fun n : ℕ ↦
            ((parts n q).card : ℝ) / secondOrderScale n)
          atTop (nhds (infiniteAllocation r q : ℝ)) := by
  classical
  let parts : ℕ → ℕ → Finset ℕ := fun n ↦
    if h : Nonempty (StationaryPrefixPartition n r distinguished) then
      (Classical.choice h).parts
    else
      fun _ ↦ ∅
  have hexists :=
    eventually_stationaryPrefixPartition_nonempty
      r distinguished hr hdistinguished
  have hparts :
      ∀ᶠ n : ℕ in atTop,
        (∀ q ∈ infiniteAllocationPositiveSupport r,
          parts n q ⊆ stationaryPrimeLayer n r) ∧
        (∀ q ∈ infiniteAllocationPositiveSupport r,
          (parts n q).card =
            stationaryPrefixCount n r distinguished q) ∧
        (infiniteAllocationPositiveSupport r : Set ℕ).PairwiseDisjoint
          (parts n) ∧
        (infiniteAllocationPositiveSupport r).biUnion (parts n) =
          stationaryPrimeLayer n r := by
    filter_upwards [hexists] with n hn
    have hpartsEq :
        parts n = (Classical.choice hn).parts := by
      dsimp only [parts]
      rw [dif_pos hn]
    rw [hpartsEq]
    exact ⟨(Classical.choice hn).parts_subset,
      (Classical.choice hn).parts_card,
      (Classical.choice hn).parts_pairwiseDisjoint,
      (Classical.choice hn).union_parts⟩
  refine ⟨parts, hparts, ?_⟩
  intro q hq
  apply
    (stationaryPrefixCount_normalized_tendsto
      r distinguished q hr hdistinguished hq).congr'
  filter_upwards [hparts] with n hn
  rw [hn.2.1 q hq]

end

end Erdos390.WholePaper
