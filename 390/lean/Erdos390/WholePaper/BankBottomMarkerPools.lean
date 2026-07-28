import Erdos390.WholePaper.BankBottomPoolMatching
import Erdos390.WholePaper.UpperScale
import Mathlib.Order.Interval.Finset.Nat

/-!
# Literal marker pools for the four bottom bank moves

The four rows below are the natural-number half-open intervals appearing in
the paper.  Each is split at its integer midpoint into two fixed one-half
orientation subintervals.  This file proves only exact finite interval and
factor arithmetic; prime supply is deliberately kept separate.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- Open lower endpoint of a bottom marker interval. -/
def bankBottomMarkerLower (n : ℕ) : BankBottomMove → ℕ
  | .fiveToFour => n / 3
  | .fourToThree => 2 * n / 5
  | .threeToTwo => 2 * n / 3
  | .twoToOne => n / 2

/-- Closed upper endpoint of a bottom marker interval. -/
def bankBottomMarkerUpper (M : ℕ) : BankBottomMove → ℕ
  | .fiveToFour => M / 6
  | .fourToThree => M / 5
  | .threeToTwo => M / 3
  | .twoToOne => M / 4

/-- The four literal marker intervals from the bottom-pool table. -/
def bankBottomMarkerInterval (n M : ℕ)
    (move : BankBottomMove) : Finset ℕ :=
  Finset.Ioc (bankBottomMarkerLower n move)
    (bankBottomMarkerUpper M move)

/-- Integer midpoint used for the fixed one-half orientation split. -/
def bankBottomOrientationCut (n M : ℕ)
    (move : BankBottomMove) : ℕ :=
  bankBottomMarkerLower n move +
    (bankBottomMarkerUpper M move - bankBottomMarkerLower n move) / 2

/-- The two adjacent orientation subintervals of one bottom marker pool. -/
def bankBottomOrientedMarkerInterval (n M : ℕ)
    (pool : BankBottomOrientationPool) : Finset ℕ :=
  match pool.2 with
  | .downward => Finset.Ioc (bankBottomMarkerLower n pool.1)
      (bankBottomOrientationCut n M pool.1)
  | .upward => Finset.Ioc (bankBottomOrientationCut n M pool.1)
      (bankBottomMarkerUpper M pool.1)

/-- Prime markers in one oriented bottom pool. -/
def bankBottomOrientedMarkerPrimes (n M : ℕ)
    (pool : BankBottomOrientationPool) : Finset ℕ :=
  (bankBottomOrientedMarkerInterval n M pool).filter Nat.Prime

/-- Prime markers in an unsplit bottom row. -/
def bankBottomMarkerPrimes (n M : ℕ)
    (move : BankBottomMove) : Finset ℕ :=
  (bankBottomMarkerInterval n M move).filter Nat.Prime

/-- Multiplier of the smaller endpoint state in each row. -/
def bankBottomLowerStateMultiplier : BankBottomMove → ℕ
  | .fiveToFour => 4
  | .fourToThree => 3
  | .threeToTwo => 2
  | .twoToOne => 2

/-- Multiplier of the larger endpoint state in each row. -/
def bankBottomUpperStateMultiplier : BankBottomMove → ℕ
  | .fiveToFour => 5
  | .fourToThree => 4
  | .threeToTwo => 3
  | .twoToOne => 4

/-- Multiplier of the backing donor occurrence in each row. -/
def bankBottomDonorMultiplier : BankBottomMove → ℕ
  | .fiveToFour => 6
  | .fourToThree => 5
  | .threeToTwo => 3
  | .twoToOne => 4

def bankBottomLowerState (move : BankBottomMove) (marker : ℕ) : ℕ :=
  bankBottomLowerStateMultiplier move * marker

def bankBottomUpperState (move : BankBottomMove) (marker : ℕ) : ℕ :=
  bankBottomUpperStateMultiplier move * marker

def bankBottomDonor (move : BankBottomMove) (marker : ℕ) : ℕ :=
  bankBottomDonorMultiplier move * marker

/-- The actual occurrences named by one bottom component.  A donor equal to
a state is represented once because this is a `Finset`. -/
def bankBottomComponentOccurrences
    (move : BankBottomMove) (marker : ℕ) : Finset ℕ :=
  {bankBottomLowerState move marker,
    bankBottomUpperState move marker,
    bankBottomDonor move marker}

theorem bankBottomMarkerLower_le_upper
    {n M : ℕ} (hM : 2 * n ≤ M) (move : BankBottomMove) :
    bankBottomMarkerLower n move ≤ bankBottomMarkerUpper M move := by
  cases move <;>
    simp only [bankBottomMarkerLower, bankBottomMarkerUpper] <;> omega

theorem bankBottomMarkerLower_le_cut
    (n M : ℕ) (move : BankBottomMove) :
    bankBottomMarkerLower n move ≤ bankBottomOrientationCut n M move := by
  simp only [bankBottomOrientationCut, Nat.le_add_right]

theorem bankBottomOrientationCut_le_upper
    {n M : ℕ} (hM : 2 * n ≤ M) (move : BankBottomMove) :
    bankBottomOrientationCut n M move ≤ bankBottomMarkerUpper M move := by
  have hlower := bankBottomMarkerLower_le_upper hM move
  unfold bankBottomOrientationCut
  omega

/-- The two oriented subintervals are disjoint. -/
theorem bankBottomOrientationIntervals_disjoint
    (n M : ℕ) (move : BankBottomMove) :
    Disjoint
      (bankBottomOrientedMarkerInterval n M (move, .downward))
      (bankBottomOrientedMarkerInterval n M (move, .upward)) := by
  simp only [bankBottomOrientedMarkerInterval]
  exact Finset.Ioc_disjoint_Ioc_of_le le_rfl

/-- The two oriented subintervals exhaust their original row. -/
theorem bankBottomOrientationIntervals_union
    {n M : ℕ} (hM : 2 * n ≤ M) (move : BankBottomMove) :
    bankBottomOrientedMarkerInterval n M (move, .downward) ∪
        bankBottomOrientedMarkerInterval n M (move, .upward) =
      bankBottomMarkerInterval n M move := by
  simp only [bankBottomOrientedMarkerInterval, bankBottomMarkerInterval]
  exact Finset.Ioc_union_Ioc_eq_Ioc
    (bankBottomMarkerLower_le_cut n M move)
    (bankBottomOrientationCut_le_upper hM move)

theorem bankBottomOrientedMarkerInterval_subset
    {n M : ℕ} (hM : 2 * n ≤ M)
    (pool : BankBottomOrientationPool) :
    bankBottomOrientedMarkerInterval n M pool ⊆
      bankBottomMarkerInterval n M pool.1 := by
  rcases pool with ⟨move, orientation⟩
  cases orientation
  · intro marker hmarker
    have hcut := bankBottomOrientationCut_le_upper hM move
    simp only [bankBottomOrientedMarkerInterval, bankBottomMarkerInterval,
      Finset.mem_Ioc] at hmarker ⊢
    exact ⟨hmarker.1, hmarker.2.trans hcut⟩
  · intro marker hmarker
    have hlower := bankBottomMarkerLower_le_cut n M move
    simp only [bankBottomOrientedMarkerInterval, bankBottomMarkerInterval,
      Finset.mem_Ioc] at hmarker ⊢
    exact ⟨lt_of_le_of_lt hlower hmarker.1, hmarker.2⟩

/-- The midpoint split has cardinalities differing by at most one. -/
theorem bankBottomOrientationIntervals_card_balanced
    {n M : ℕ} (hM : 2 * n ≤ M) (move : BankBottomMove) :
    (bankBottomOrientedMarkerInterval n M (move, .downward)).card ≤
        (bankBottomOrientedMarkerInterval n M (move, .upward)).card ∧
      (bankBottomOrientedMarkerInterval n M (move, .upward)).card ≤
        (bankBottomOrientedMarkerInterval n M (move, .downward)).card + 1 := by
  have hlower := bankBottomMarkerLower_le_upper hM move
  have hcutLower := bankBottomMarkerLower_le_cut n M move
  have hcutUpper := bankBottomOrientationCut_le_upper hM move
  simp only [bankBottomOrientedMarkerInterval, Nat.card_Ioc,
    bankBottomOrientationCut]
  omega

/-- A marker in its row makes both endpoint states and the donor lie in
the factor interval `(n,M]`. -/
theorem bankBottom_states_donor_mem_factorInterval
    {n M marker : ℕ} {move : BankBottomMove}
    (hmarker : marker ∈ bankBottomMarkerInterval n M move) :
    bankBottomLowerState move marker ∈ factorInterval n M ∧
      bankBottomUpperState move marker ∈ factorInterval n M ∧
      bankBottomDonor move marker ∈ factorInterval n M := by
  cases move <;>
    simp only [bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc, bankBottomLowerState,
      bankBottomUpperState, bankBottomDonor,
      bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
      bankBottomDonorMultiplier, factorInterval] at hmarker ⊢ <;>
    omega

/-- In the `3→2` row the donor is literally the upper-state occurrence. -/
@[simp] theorem bankBottomDonor_threeToTwo_eq_upperState (marker : ℕ) :
    bankBottomDonor .threeToTwo marker =
      bankBottomUpperState .threeToTwo marker := rfl

/-- In the terminal `2→1` row the donor is literally the upper-state
occurrence. -/
@[simp] theorem bankBottomDonor_twoToOne_eq_upperState (marker : ℕ) :
    bankBottomDonor .twoToOne marker =
      bankBottomUpperState .twoToOne marker := rfl

@[simp] theorem bankBottomComponentOccurrences_threeToTwo (marker : ℕ) :
    bankBottomComponentOccurrences .threeToTwo marker =
      {2 * marker, 3 * marker} := by
  ext occurrence
  simp [bankBottomComponentOccurrences, bankBottomLowerState,
    bankBottomUpperState, bankBottomDonor,
    bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
    bankBottomDonorMultiplier]

@[simp] theorem bankBottomComponentOccurrences_twoToOne (marker : ℕ) :
    bankBottomComponentOccurrences .twoToOne marker =
      {2 * marker, 4 * marker} := by
  ext occurrence
  simp [bankBottomComponentOccurrences, bankBottomLowerState,
    bankBottomUpperState, bankBottomDonor,
    bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
    bankBottomDonorMultiplier]

/-- Under the eventual narrow-endpoint inequality, the four marker rows are
pairwise disjoint. -/
theorem bankBottomMarkerIntervals_disjoint
    {n M : ℕ} (hM : 5 * M ≤ 12 * n)
    {move move' : BankBottomMove} (hmove : move ≠ move') :
    Disjoint (bankBottomMarkerInterval n M move)
      (bankBottomMarkerInterval n M move') := by
  rw [Finset.disjoint_left]
  intro marker hmarker hmarker'
  cases move <;> cases move' <;>
    simp_all [bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc] <;> omega

/-- Hence any oriented subpools belonging to distinct rows are disjoint. -/
theorem bankBottomOrientedMarkerIntervals_disjoint_of_move_ne
    {n M : ℕ} (hTwoN : 2 * n ≤ M) (hM : 5 * M ≤ 12 * n)
    {pool pool' : BankBottomOrientationPool}
    (hmove : pool.1 ≠ pool'.1) :
    Disjoint (bankBottomOrientedMarkerInterval n M pool)
      (bankBottomOrientedMarkerInterval n M pool') := by
  rw [Finset.disjoint_left]
  intro marker hmarker hmarker'
  exact (Finset.disjoint_left.mp
      (bankBottomMarkerIntervals_disjoint hM hmove))
    (bankBottomOrientedMarkerInterval_subset hTwoN pool hmarker)
    (bankBottomOrientedMarkerInterval_subset hTwoN pool' hmarker')

/-- All eight oriented bottom marker intervals are pairwise disjoint. -/
theorem bankBottomOrientedMarkerIntervals_disjoint
    {n M : ℕ} (hTwoN : 2 * n ≤ M) (hM : 5 * M ≤ 12 * n)
    {pool pool' : BankBottomOrientationPool} (hpools : pool ≠ pool') :
    Disjoint (bankBottomOrientedMarkerInterval n M pool)
      (bankBottomOrientedMarkerInterval n M pool') := by
  by_cases hmove : pool.1 = pool'.1
  · rcases pool with ⟨move, orientation⟩
    rcases pool' with ⟨move', orientation'⟩
    simp only at hmove
    subst move'
    cases orientation <;> cases orientation'
    · simp at hpools
    · exact bankBottomOrientationIntervals_disjoint n M move
    · exact (bankBottomOrientationIntervals_disjoint n M move).symm
    · simp at hpools
  · exact bankBottomOrientedMarkerIntervals_disjoint_of_move_ne
      hTwoN hM hmove

theorem bankBottomOrientedMarkerPrimes_disjoint
    {n M : ℕ} (hTwoN : 2 * n ≤ M) (hM : 5 * M ≤ 12 * n)
    {pool pool' : BankBottomOrientationPool} (hpools : pool ≠ pool') :
    Disjoint (bankBottomOrientedMarkerPrimes n M pool)
      (bankBottomOrientedMarkerPrimes n M pool') := by
  rw [Finset.disjoint_left]
  intro marker hmarker hmarker'
  exact (Finset.disjoint_left.mp
      (bankBottomOrientedMarkerIntervals_disjoint hTwoN hM hpools))
    (Finset.mem_filter.mp hmarker).1
    (Finset.mem_filter.mp hmarker').1

theorem bankBottomOrientedMarkerPrimes_subset
    {n M : ℕ} (hTwoN : 2 * n ≤ M)
    (pool : BankBottomOrientationPool) :
    bankBottomOrientedMarkerPrimes n M pool ⊆
      bankBottomMarkerPrimes n M pool.1 := by
  intro marker hmarker
  exact Finset.mem_filter.mpr ⟨
    bankBottomOrientedMarkerInterval_subset hTwoN pool
      (Finset.mem_filter.mp hmarker).1,
    (Finset.mem_filter.mp hmarker).2⟩

end

end Erdos390.WholePaper
