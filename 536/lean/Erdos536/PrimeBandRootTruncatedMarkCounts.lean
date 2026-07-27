import Erdos536.PrimeBandRootRankCombinatorics

/-!
# Exact truncated canonical-rank marking counts

This module isolates the finite marking factors left after deleting zero,
one, or two canonical pivots.  It contains no prime summation or factorial
insertion: the support is reindexed by `supportDepthRankEquiv`, and the
resulting independent-coordinate cardinalities are evaluated exactly.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Erdos536

set_option maxHeartbeats 800000

theorem supportRankPrefix_mono
    {R : Finset ℕ} {T : ℝ} {A : Finset ↥R}
    {I J : ℕ} (hIJ : I ≤ J) :
    supportRankPrefix T A I ⊆ supportRankPrefix T A J := by
  intro r hr
  rw [mem_supportRankPrefix] at hr ⊢
  exact lt_of_lt_of_le hr hIJ

/-- A marking with a forced-zero block `B`, a forced line block `C`,
and unrestricted coordinates outside `C`. -/
abbrev TruncatedZeroLineTailMarking
    {α : Type*} [Fintype α] [DecidableEq α]
    (B C : Finset α) (v : NineMark) :=
  {m : α → NineMark //
    (∀ r ∈ B, m r = zeroNineMark) ∧
      ∀ r ∈ C, NineMarkCollinear v (m r)}

/-- The independent coordinates in a zero/line/tail marking. -/
noncomputable def truncatedZeroLineTailMarkingEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (B C : Finset α) (hBC : B ⊆ C) (v : NineMark) :
    TruncatedZeroLineTailMarking B C v ≃
      ({r : α // r ∈ C \ B} →
        {z : NineMark // NineMarkCollinear v z}) ×
      ({r : α // r ∉ C} → NineMark) where
  toFun m :=
    (fun r => ⟨m.1 r.1, m.2.2 r.1
      (Finset.mem_sdiff.mp r.2).1⟩,
    fun r => m.1 r.1)
  invFun data :=
    ⟨fun r =>
      if hrB : r ∈ B then zeroNineMark
      else if hrC : r ∈ C
      then (data.1 ⟨r, Finset.mem_sdiff.mpr
        ⟨hrC, hrB⟩⟩).1
      else data.2 ⟨r, hrC⟩,
    by
      constructor
      · intro r hrB
        dsimp
        simp [hrB]
      · intro r hrC
        dsimp
        by_cases hrB : r ∈ B
        · simp [hrB, nineMark_collinear_zero]
        · simp [hrB, hrC]
          exact (data.1 ⟨r, Finset.mem_sdiff.mpr
            ⟨hrC, hrB⟩⟩).2⟩
  left_inv m := by
    apply Subtype.ext
    funext r
    by_cases hrB : r ∈ B
    · simp [hrB, m.2.1 r hrB]
    · by_cases hrC : r ∈ C
      · simp [hrB, hrC]
      · simp [hrB, hrC]
  right_inv data := by
    apply Prod.ext
    · funext r
      apply Subtype.ext
      have hr := Finset.mem_sdiff.mp r.2
      simp [hr.1, hr.2]
    · funext r
      have hrB : r.1 ∉ B := fun hr =>
        r.2 (hBC hr)
      simp [r.2, hrB]

/-- Exact independent-coordinate count for the three blocks. -/
theorem card_truncatedZeroLineTailMarking
    {α : Type*} [Fintype α] [DecidableEq α]
    (B C : Finset α) (hBC : B ⊆ C)
    (v : NineMark) (hv : v ≠ zeroNineMark) :
    Fintype.card (TruncatedZeroLineTailMarking B C v) =
      3 ^ (C.card - B.card) *
        9 ^ (Fintype.card α - C.card) := by
  classical
  rw [Fintype.card_congr
    (truncatedZeroLineTailMarkingEquiv B C hBC v),
    Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fun, card_nineMarkCollinear v hv]
  have hdiff :
      Fintype.card {r : α // r ∈ C \ B} =
        C.card - B.card := by
    rw [Fintype.card_coe]
    exact Finset.card_sdiff_of_subset hBC
  have hcompl :
      Fintype.card {r : α // r ∉ C} =
        Fintype.card α - C.card := by
    have hmem :
        Fintype.card {r : α // r ∈ C} = C.card := by
      rw [Fintype.card_coe]
    rw [Fintype.card_subtype_compl, hmem]
  rw [hdiff, hcompl]
  norm_num

/-- The residual marking after pivots at full-support ranks `i < j`.
Residual ranks below `i` vanish, ranks from `i` through `j - 2` lie on
the first pivot line, and all later ranks are unrestricted. -/
abbrev TruncatedTwoPivotResidualMarking
    {R : Finset ℕ} (T : ℝ) (A : Finset ↥R)
    (i j : ℕ) (v : NineMark) :=
  TruncatedZeroLineTailMarking
    (supportRankPrefix T A i)
    (supportRankPrefix T A (j - 1)) v

theorem card_truncatedTwoPivotResidualMarking
    {R : Finset ℕ} {T : ℝ} {A : Finset ↥R}
    {i j K : ℕ} (hij : i < j) (hjK : j < K)
    (hK : K ≤ A.card + 2)
    (v : NineMark) (hv : v ≠ zeroNineMark) :
    Fintype.card
        (TruncatedTwoPivotResidualMarking T A i j v) =
      3 ^ (j - 1 - i) * 9 ^ (A.card - (j - 1)) := by
  have hj : j - 1 ≤ A.card := by omega
  have hi : i ≤ A.card := by omega
  rw [card_truncatedZeroLineTailMarking
    (supportRankPrefix T A i)
    (supportRankPrefix T A (j - 1))
    (supportRankPrefix_mono (by omega)) v hv,
    supportRankPrefix_card hi,
    supportRankPrefix_card hj,
    Fintype.card_coe]

/-- Complete two-pivot mark data: a nonzero first pivot, a
noncollinear second pivot, the collinear middle coordinates, and the
unrestricted tail coordinates. -/
abbrev TruncatedTwoPivotMarkData
    {R : Finset ℕ} (A : Finset ↥R) (i j : ℕ) :=
  RankTwoMarkData (j - 1 - i) (A.card - (j - 1))

theorem card_truncatedTwoPivotMarkData
    {R : Finset ℕ} (A : Finset ↥R) (i j : ℕ) :
    Fintype.card (TruncatedTwoPivotMarkData A i j) =
      8 * 6 * (3 ^ (j - 1 - i) *
        9 ^ (A.card - (j - 1))) := by
  classical
  rw [card_rankTwoMarkData]
  ring

/-- After division by the `9^(A.card + 2)` full-marking count, the
two-pivot cardinality is exactly the product of the two canonical rank
decays, with coefficient `16`. -/
theorem truncatedTwoPivotMarkData_normalized
    {R : Finset ℕ} (A : Finset ↥R) {i j K : ℕ}
    (hij : i < j) (hjK : j < K)
    (hK : K ≤ A.card + 2) :
    (Fintype.card (TruncatedTwoPivotMarkData A i j) : ℝ) /
        (9 : ℝ) ^ (A.card + 2) =
      16 * pivotRankDecay i * pivotRankDecay j := by
  have hj : j - 1 ≤ A.card := by omega
  rw [card_truncatedTwoPivotMarkData]
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold pivotRankDecay
  rw [one_div_pow, one_div_pow]
  have hnine (n : ℕ) : (9 : ℝ) ^ n = 3 ^ (2 * n) := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul]
  rw [hnine, hnine]
  field_simp
  calc
    (48 : ℝ) * 3 ^ (j - 1 - i) *
          3 ^ (2 * (A.card - (j - 1))) *
          3 ^ (i + 1) * 3 ^ (j + 1) =
        16 * ((((3 ^ 1 * 3 ^ (j - 1 - i)) *
          3 ^ (2 * (A.card - (j - 1)))) *
          3 ^ (i + 1)) * 3 ^ (j + 1)) := by
      norm_num
      ring
    _ = 16 * 3 ^ ((((1 + (j - 1 - i)) +
          2 * (A.card - (j - 1))) + (i + 1)) +
          (j + 1)) := by
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    _ = 16 * 3 ^ (2 * (A.card + 2)) := by
      congr 2
      omega
    _ = 3 ^ (2 * (A.card + 2)) * 16 := by ring

/-- The residual marking after one pivot at full-support rank `i`, when
the whole full-support prefix below `K` is constrained to the pivot
line. -/
abbrev TruncatedOnePivotResidualMarking
    {R : Finset ℕ} (T : ℝ) (A : Finset ↥R)
    (i K : ℕ) (v : NineMark) :=
  TruncatedZeroLineTailMarking
    (supportRankPrefix T A i)
    (supportRankPrefix T A (K - 1)) v

theorem card_truncatedOnePivotResidualMarking
    {R : Finset ℕ} {T : ℝ} {A : Finset ↥R}
    {i K : ℕ} (hiK : i < K)
    (hK : K ≤ A.card + 1)
    (v : NineMark) (hv : v ≠ zeroNineMark) :
    Fintype.card
        (TruncatedOnePivotResidualMarking T A i K v) =
      3 ^ (K - 1 - i) * 9 ^ (A.card - (K - 1)) := by
  have hKm : K - 1 ≤ A.card := by omega
  have hi : i ≤ A.card := by omega
  rw [card_truncatedZeroLineTailMarking
    (supportRankPrefix T A i)
    (supportRankPrefix T A (K - 1))
    (supportRankPrefix_mono (by omega)) v hv,
    supportRankPrefix_card hi,
    supportRankPrefix_card hKm,
    Fintype.card_coe]

/-- Complete one-pivot mark data: a nonzero pivot and its residual
zero/line/tail marking. -/
abbrev TruncatedOnePivotMarkData
    {R : Finset ℕ} (A : Finset ↥R) (i K : ℕ) :=
  Σ v : {v : NineMark // v ≠ zeroNineMark},
    (Fin (K - 1 - i) →
      {w : NineMark // NineMarkCollinear v.1 w}) ×
    (Fin (A.card - (K - 1)) → NineMark)

theorem card_truncatedOnePivotMarkData
    {R : Finset ℕ} (A : Finset ↥R) (i K : ℕ) :
    Fintype.card (TruncatedOnePivotMarkData A i K) =
      8 * (3 ^ (K - 1 - i) *
        9 ^ (A.card - (K - 1))) := by
  classical
  rw [Fintype.card_sigma]
  calc
    (∑ v : {v : NineMark // v ≠ zeroNineMark},
        Fintype.card
          ((Fin (K - 1 - i) →
              {w : NineMark // NineMarkCollinear v.1 w}) ×
            (Fin (A.card - (K - 1)) → NineMark))) =
        ∑ _v : {v : NineMark // v ≠ zeroNineMark},
          3 ^ (K - 1 - i) *
            9 ^ (A.card - (K - 1)) := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [Fintype.card_prod, Fintype.card_pi_const,
        Fintype.card_pi_const,
        card_nineMarkCollinear v.1 v.2]
      norm_num
    _ = 8 * (3 ^ (K - 1 - i) *
          9 ^ (A.card - (K - 1))) := by
      rw [Finset.sum_const, Finset.card_univ,
        card_nonzeroNineMark]
      ring

/-- After division by the `9^(A.card + 1)` full-marking count, the
one-pivot cardinality is its pivot decay times the probability that the
entire advertised prefix stays on the pivot line. -/
theorem truncatedOnePivotMarkData_normalized
    {R : Finset ℕ} (A : Finset ↥R) {i K : ℕ}
    (hiK : i < K) (hK : K ≤ A.card + 1) :
    (Fintype.card (TruncatedOnePivotMarkData A i K) : ℝ) /
        (9 : ℝ) ^ (A.card + 1) =
      8 * (1 / 3 : ℝ) ^ K * pivotRankDecay i := by
  have hKm : K - 1 ≤ A.card := by omega
  rw [card_truncatedOnePivotMarkData]
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold pivotRankDecay
  rw [one_div_pow, one_div_pow]
  have hnine (n : ℕ) : (9 : ℝ) ^ n = 3 ^ (2 * n) := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul]
  rw [hnine, hnine]
  field_simp
  calc
    (3 : ℝ) ^ (K - 1 - i) *
          3 ^ (2 * (A.card - (K - 1))) *
          3 ^ K * 3 ^ (i + 1) =
        (((3 ^ (K - 1 - i) *
          3 ^ (2 * (A.card - (K - 1)))) *
          3 ^ K) * 3 ^ (i + 1)) := by ring
    _ = 3 ^ ((((K - 1 - i) +
          2 * (A.card - (K - 1))) + K) +
          (i + 1)) := by
      rw [← pow_add, ← pow_add, ← pow_add]
    _ = 3 ^ (2 * (A.card + 1)) := by
      congr 1
      omega

/-- Markings that vanish on a specified coordinate set. -/
abbrev ZeroBlockMarking
    {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) :=
  {m : α → NineMark // ∀ r ∈ B, m r = zeroNineMark}

/-- Deleting the forced-zero coordinates leaves an arbitrary marking on
the complement. -/
noncomputable def zeroBlockMarkingEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) :
    ZeroBlockMarking B ≃
      ({r : α // r ∉ B} → NineMark) where
  toFun m r := m.1 r.1
  invFun data :=
    ⟨fun r => if hr : r ∈ B then zeroNineMark
      else data ⟨r, hr⟩,
    by
      intro r hr
      simp [hr]⟩
  left_inv m := by
    apply Subtype.ext
    funext r
    by_cases hr : r ∈ B
    · simp [hr, m.2 r hr]
    · simp [hr]
  right_inv data := by
    funext r
    simp [r.2]

theorem card_zeroBlockMarking
    {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) :
    Fintype.card (ZeroBlockMarking B) =
      9 ^ (Fintype.card α - B.card) := by
  classical
  rw [Fintype.card_congr (zeroBlockMarkingEquiv B),
    Fintype.card_fun]
  have hcompl :
      Fintype.card {r : α // r ∉ B} =
        Fintype.card α - B.card := by
    have hmem :
        Fintype.card {r : α // r ∈ B} = B.card := by
      rw [Fintype.card_coe]
    rw [Fintype.card_subtype_compl, hmem]
  rw [hcompl]
  norm_num

/-- A full support marking whose first `K` canonical ranks vanish. -/
abbrev TruncatedZeroPrefixMarking
    {R : Finset ℕ} (T : ℝ) (S : Finset ↥R)
    (K : ℕ) :=
  ZeroBlockMarking (supportRankPrefix T S K)

theorem card_truncatedZeroPrefixMarking
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    {K : ℕ} (hK : K ≤ S.card) :
    Fintype.card (TruncatedZeroPrefixMarking T S K) =
      9 ^ (S.card - K) := by
  rw [card_zeroBlockMarking,
    Fintype.card_coe, supportRankPrefix_card hK]

/-- A uniformly random nine-marking vanishes on its first `K`
canonical ranks with exact probability `(1/9)^K`. -/
theorem truncatedZeroPrefixMarking_normalized
    {R : Finset ℕ} {T : ℝ} (S : Finset ↥R)
    {K : ℕ} (hK : K ≤ S.card) :
    (Fintype.card (TruncatedZeroPrefixMarking T S K) : ℝ) /
        (9 : ℝ) ^ S.card =
      (1 / 9 : ℝ) ^ K := by
  rw [card_truncatedZeroPrefixMarking hK]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  rw [one_div_pow]
  field_simp
  rw [← pow_add]
  congr 1
  omega

end Erdos536
