import Erdos390.Full.ArithmeticModel
import Erdos390.WholePaper.BankMarkerDonorCombinatorics
import Erdos390.WholePaper.BankSmallDescentTable
import Erdos390.WholePaper.UpperScale

/-!
# The ordinary-bank marker--donor relation

This file defines the literal finite relation used by the nonbottom bank in
Section 5.3.  The scale is rational, so the grid `Q_j = 4(4/3)^j` and all four
interval endpoints are represented without rounding.  The wider relation is
the actual relation from which marker--donor pairs are selected.  The narrow
relation is the bulk subrelation used in the analytic supply proof.

There is no prime-distribution input here.  In particular, the fiber bound is
an exact injection into the natural quotient interval
`(2n / P, M / P]`.  The five fixed small-scale donors are also recorded here,
including their literal rational interval checks.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- The exact rational geometric grid `Q_j = 4(4/3)^j`. -/
def bankOrdinaryScale (j : ℕ) : ℚ :=
  4 * (4 / 3 : ℚ) ^ j

theorem bankOrdinaryScale_pos (j : ℕ) :
    0 < bankOrdinaryScale j := by
  unfold bankOrdinaryScale
  positivity

theorem bankOrdinaryScale_succ (j : ℕ) :
    bankOrdinaryScale (j + 1) = 4 * bankOrdinaryScale j / 3 := by
  unfold bankOrdinaryScale
  rw [pow_succ]
  ring

/-- Literal membership in the marker interval
`I_Q = (4n/(3Q), 3n/(2Q)]`, written without division. -/
def InOrdinaryBankMarkerInterval (n : ℕ) (Q : ℚ) (P : ℕ) : Prop :=
  4 * (n : ℚ) < 3 * Q * (P : ℚ) ∧
    2 * Q * (P : ℚ) ≤ 3 * (n : ℚ)

/-- The full cofactor window `[4Q/3, 3Q/2]` allowed by the two legal
lower-factor states. -/
def InOrdinaryBankDonorWindow (Q : ℚ) (u : ℕ) : Prop :=
  4 * Q ≤ 3 * (u : ℚ) ∧
    2 * (u : ℚ) ≤ 3 * Q

/-- The shrunken cofactor window `[7Q/5, 29Q/20]` used for bulk supply. -/
def InOrdinaryBankBulkDonorWindow (Q : ℚ) (u : ℕ) : Prop :=
  7 * Q ≤ 5 * (u : ℚ) ∧
    20 * (u : ℚ) ≤ 29 * Q

theorem ordinaryBankBulkDonorWindow_subset
    {Q : ℚ} {u : ℕ} (hu : InOrdinaryBankBulkDonorWindow Q u) :
    InOrdinaryBankDonorWindow Q u := by
  unfold InOrdinaryBankBulkDonorWindow at hu
  unfold InOrdinaryBankDonorWindow
  constructor <;> linarith

/-- One actual ordinary-bank marker--donor pair at endpoint `M`. -/
def IsOrdinaryBankEligiblePair
    (n M : ℕ) (Q : ℚ) (pair : ℕ × ℕ) : Prop :=
  0 < Q ∧
    pair.1.Prime ∧
    0 < pair.2 ∧
    InOrdinaryBankMarkerInterval n Q pair.1 ∧
    InOrdinaryBankDonorWindow Q pair.2 ∧
    pair.2 ∈ Nat.smoothNumbers (yNat n + 1) ∧
    2 * n < pair.1 * pair.2 ∧
    pair.1 * pair.2 ≤ M

/-- A bulk occurrence only asks for the shrunken donor window and the actual
tail occurrence.  When `M ≤ 21n/10`, its marker automatically lies in
`I_Q`, so it belongs to the full relation. -/
def IsOrdinaryBankBulkPair
    (n M : ℕ) (Q : ℚ) (pair : ℕ × ℕ) : Prop :=
  0 < Q ∧
    pair.1.Prime ∧
    0 < pair.2 ∧
    InOrdinaryBankBulkDonorWindow Q pair.2 ∧
    pair.2 ∈ Nat.smoothNumbers (yNat n + 1) ∧
    2 * n < pair.1 * pair.2 ∧
    pair.1 * pair.2 ≤ M

/-- A common finite ambient box.  Product eligibility makes both coordinate
bounds redundant, but retaining the box keeps the relations computational
finsets. -/
def ordinaryBankPairBox (M : ℕ) : Finset (ℕ × ℕ) :=
  Finset.Icc 1 M ×ˢ Finset.Icc 1 M

/-- The actual finite marker--donor relation at rational scale `Q`. -/
def bankOrdinaryEligibleRelation
    (n M : ℕ) (Q : ℚ) : Finset (ℕ × ℕ) :=
  by
    classical
    exact (ordinaryBankPairBox M).filter (IsOrdinaryBankEligiblePair n M Q)

/-- The finite bulk relation used to prove supply. -/
def bankOrdinaryBulkRelation
    (n M : ℕ) (Q : ℚ) : Finset (ℕ × ℕ) :=
  by
    classical
    exact (ordinaryBankPairBox M).filter (IsOrdinaryBankBulkPair n M Q)

private theorem pair_mem_box_of_product_le
    {P u M : ℕ} (hP : 0 < P) (hu : 0 < u) (hPu : P * u ≤ M) :
    (P, u) ∈ ordinaryBankPairBox M := by
  have hPle : P ≤ P * u := Nat.le_mul_of_pos_right P hu
  have hule : u ≤ P * u := by
    simpa only [Nat.mul_comm] using Nat.le_mul_of_pos_right u hP
  simp only [ordinaryBankPairBox, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨hP, hPle.trans hPu⟩, ⟨hu, hule.trans hPu⟩⟩

@[simp] theorem mem_bankOrdinaryEligibleRelation
    {n M P u : ℕ} {Q : ℚ} :
    (P, u) ∈ bankOrdinaryEligibleRelation n M Q ↔
      IsOrdinaryBankEligiblePair n M Q (P, u) := by
  classical
  constructor
  · exact fun h ↦ (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    exact ⟨pair_mem_box_of_product_le h.2.1.pos h.2.2.1 h.2.2.2.2.2.2.2,
      h⟩

@[simp] theorem mem_bankOrdinaryBulkRelation
    {n M P u : ℕ} {Q : ℚ} :
    (P, u) ∈ bankOrdinaryBulkRelation n M Q ↔
      IsOrdinaryBankBulkPair n M Q (P, u) := by
  classical
  constructor
  · exact fun h ↦ (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    exact ⟨pair_mem_box_of_product_le h.2.1.pos h.2.2.1 h.2.2.2.2.2.2,
      h⟩

/-- The constants `7/5` and `29/20` put every bulk tail occurrence in the
actual marker interval as soon as the upper endpoint is at most `2.1n`. -/
theorem ordinaryBankBulkPair_isEligible
    {n M : ℕ} {Q : ℚ} {pair : ℕ × ℕ}
    (hM : 10 * M ≤ 21 * n)
    (hpair : IsOrdinaryBankBulkPair n M Q pair) :
    IsOrdinaryBankEligiblePair n M Q pair := by
  rcases pair with ⟨P, u⟩
  rcases hpair with ⟨hQ, hP, hu, huBulk, huSmooth, htailLower,
    htailUpper⟩
  have hPnonneg : (0 : ℚ) ≤ P := by positivity
  have huBulkPLeft := mul_le_mul_of_nonneg_right huBulk.1 hPnonneg
  have huBulkPRight := mul_le_mul_of_nonneg_right huBulk.2 hPnonneg
  have htailLowerQ : 2 * (n : ℚ) < (P : ℚ) * (u : ℚ) := by
    exact_mod_cast htailLower
  have htailUpperQ : (P : ℚ) * (u : ℚ) ≤ M := by
    exact_mod_cast htailUpper
  have hMQ : 10 * (M : ℚ) ≤ 21 * (n : ℚ) := by
    exact_mod_cast hM
  have hmarker : InOrdinaryBankMarkerInterval n Q P := by
    unfold InOrdinaryBankMarkerInterval
    constructor <;> nlinarith
  exact ⟨hQ, hP, hu, hmarker,
    ordinaryBankBulkDonorWindow_subset huBulk, huSmooth,
    htailLower, htailUpper⟩

/-- Hence the bulk finite relation is literally a subrelation of the actual
one in the endpoint range used by the paper. -/
theorem bankOrdinaryBulkRelation_subset_eligible
    {n M : ℕ} {Q : ℚ} (hM : 10 * M ≤ 21 * n) :
    bankOrdinaryBulkRelation n M Q ⊆
      bankOrdinaryEligibleRelation n M Q := by
  intro pair hpair
  rw [mem_bankOrdinaryEligibleRelation]
  exact ordinaryBankBulkPair_isEligible hM
    (mem_bankOrdinaryBulkRelation.mp hpair)

/-- Exact marker-fiber bound: admissible donors inject into the quotient
interval `(2n/P, M/P]`. -/
theorem bankOrdinary_donorMultiplicity_le_div_sub_div
    {n M P : ℕ} {Q : ℚ} (hP : 0 < P) :
    bankDonorMultiplicity (bankOrdinaryEligibleRelation n M Q) P ≤
      M / P - (2 * n) / P := by
  unfold bankDonorMultiplicity
  have hmap : Set.MapsTo Prod.snd
      (↑((bankOrdinaryEligibleRelation n M Q).filter
        fun pair ↦ pair.1 = P) : Set (ℕ × ℕ))
      (↑(Finset.Ioc ((2 * n) / P) (M / P)) : Set ℕ) := by
    intro pair hpair
    have hfilter := Finset.mem_filter.mp hpair
    have heligible := mem_bankOrdinaryEligibleRelation.mp hfilter.1
    have hfirst : pair.1 = P := hfilter.2
    change pair.2 ∈ Finset.Ioc ((2 * n) / P) (M / P)
    rw [Finset.mem_Ioc]
    constructor
    · apply (Nat.div_lt_iff_lt_mul hP).2
      simpa only [hfirst, Nat.mul_comm] using heligible.2.2.2.2.2.2.1
    · apply (Nat.le_div_iff_mul_le hP).2
      simpa only [hfirst, Nat.mul_comm] using heligible.2.2.2.2.2.2.2
  have hinj : Set.InjOn Prod.snd
      (↑((bankOrdinaryEligibleRelation n M Q).filter
        fun pair ↦ pair.1 = P) : Set (ℕ × ℕ)) := by
    intro pair hpair pair' hpair' hsnd
    have hp := (Finset.mem_filter.mp hpair).2
    have hp' := (Finset.mem_filter.mp hpair').2
    apply Prod.ext
    · exact hp.trans hp'.symm
    · exact hsnd
  have hcard := Finset.card_le_card_of_injOn Prod.snd hmap hinj
  simpa only [Nat.card_Ioc] using hcard

/-! ## The five exceptional fixed donors -/

/-- The five fixed cofactors in the small-scale table of Section 5.3. -/
def bankOrdinarySmallDonor : SmallDescentScale → ℕ
  | .one => 8
  | .two => 10
  | .three => 13
  | .four => 17
  | .five => 23

theorem bankOrdinarySmallDonor_pos (scale : SmallDescentScale) :
    0 < bankOrdinarySmallDonor scale := by
  cases scale <;> decide

theorem bankOrdinarySmallDonor_le_twentyThree (scale : SmallDescentScale) :
    bankOrdinarySmallDonor scale ≤ 23 := by
  cases scale <;> decide

theorem bankOrdinarySmallDonor_mem_window (scale : SmallDescentScale) :
    InOrdinaryBankDonorWindow (smallDescentScaleValue scale)
      (bankOrdinarySmallDonor scale) := by
  cases scale <;>
    norm_num [InOrdinaryBankDonorWindow, smallDescentScaleValue,
      smallDescentScaleNumerator, smallDescentScaleDenominator,
      bankOrdinarySmallDonor]

theorem bankOrdinarySmallDonor_smooth
    {n : ℕ} (hY : 23 ≤ yNat n) (scale : SmallDescentScale) :
    bankOrdinarySmallDonor scale ∈ Nat.smoothNumbers (yNat n + 1) := by
  apply Nat.mem_smoothNumbers_of_lt (bankOrdinarySmallDonor_pos scale)
  have hsmall := bankOrdinarySmallDonor_le_twentyThree scale
  omega

/-- At a small scale, primality, marker membership, and the tail-product
condition suffice: the table supplies the fixed donor-window and smoothness
conditions. -/
theorem bankOrdinarySmallPair_mem_eligible
    {n M P : ℕ} (scale : SmallDescentScale)
    (hY : 23 ≤ yNat n) (hP : P.Prime)
    (hmarker : InOrdinaryBankMarkerInterval n
      (smallDescentScaleValue scale) P)
    (htailLower : 2 * n < P * bankOrdinarySmallDonor scale)
    (htailUpper : P * bankOrdinarySmallDonor scale ≤ M) :
    (P, bankOrdinarySmallDonor scale) ∈
      bankOrdinaryEligibleRelation n M (smallDescentScaleValue scale) := by
  rw [mem_bankOrdinaryEligibleRelation]
  refine ⟨?_, hP, bankOrdinarySmallDonor_pos scale, hmarker,
    bankOrdinarySmallDonor_mem_window scale,
    bankOrdinarySmallDonor_smooth hY scale, htailLower, htailUpper⟩
  cases scale <;>
    norm_num [smallDescentScaleValue, smallDescentScaleNumerator,
      smallDescentScaleDenominator]

end

end Erdos390.WholePaper
