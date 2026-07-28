import Erdos390.WholePaper.NaguraLogBounds

/-!
# The combinatorial half of Nagura's Chebyshev argument

This file expands Nagura's six-term `T` combination into a weighted sum of a
decreasing sequence.  Its prefix weights are explicit floor expressions, so a
finite summation-by-parts identity gives the required lower bound.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

/-- Shift a sum over the positive natural interval `1, ..., n` to a zero-based
range. -/
theorem sum_Ioc_zero_eq_sum_range_succ {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (n : ℕ) :
    (∑ m ∈ Finset.Ioc 0 n, f m) = ∑ i ∈ Finset.range n, f (i + 1) := by
  rw [show Finset.Ioc 0 n = Finset.Ico 1 (n + 1) by ext m; simp; omega,
    Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  omega

/-- There are exactly `n / d` positive multiples of a positive `d` among
`1, ..., n`, expressed as a sum of indicators. -/
theorem sum_dvd_indicator_eq_div (d : ℕ) (n : ℕ) :
    (∑ i ∈ Finset.range n, if d ∣ i + 1 then (1 : ℝ) else 0) = (n / d : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases h : d ∣ n + 1
      · rw [if_pos h, Nat.succ_div_of_dvd h]
        norm_num
      · rw [if_neg h, Nat.succ_div_of_not_dvd h]
        norm_num

/-- Indicator selection of the positive multiples of `d`. -/
theorem sum_dvd_indicator_apply_eq (d : ℕ)
    (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, if d ∣ i + 1 then f (i + 1) else 0) =
      ∑ j ∈ Finset.range (n / d), f (d * (j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases h : d ∣ n + 1
      · rw [if_pos h, Nat.succ_div_of_dvd h, Finset.sum_range_succ]
        congr 1
        apply congrArg f
        have hCancel : (n + 1) / d * d = n + 1 := Nat.div_mul_cancel h
        have hQuot : (n + 1) / d = n / d + 1 := Nat.succ_div_of_dvd h
        calc
          n + 1 = (n + 1) / d * d := hCancel.symm
          _ = d * ((n + 1) / d) := Nat.mul_comm _ _
          _ = d * (n / d + 1) := by rw [hQuot]
      · rw [if_neg h, Nat.succ_div_of_not_dvd h]
        simp

/-- A finite summation-by-parts identity, written in terms of inclusive
partial sums. -/
theorem sum_range_mul_eq_partial_sum
    (c a : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), c i * a i) =
      (∑ j ∈ Finset.range (n + 1), c j) * a n +
        ∑ i ∈ Finset.range n,
          (∑ j ∈ Finset.range (i + 1), c j) * (a i - a (i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hPrefix :
          (∑ j ∈ Finset.range (n + 1 + 1), c j) =
            (∑ j ∈ Finset.range (n + 1), c j) + c (n + 1) :=
        Finset.sum_range_succ c (n + 1)
      have hDiff :
          (∑ i ∈ Finset.range (n + 1),
              (∑ j ∈ Finset.range (i + 1), c j) * (a i - a (i + 1))) =
            (∑ i ∈ Finset.range n,
              (∑ j ∈ Finset.range (i + 1), c j) * (a i - a (i + 1))) +
              (∑ j ∈ Finset.range (n + 1), c j) *
                (a n - a (n + 1)) :=
        Finset.sum_range_succ _ n
      calc
        (∑ i ∈ Finset.range (n + 1 + 1), c i * a i) =
            (∑ i ∈ Finset.range (n + 1), c i * a i) +
              c (n + 1) * a (n + 1) := Finset.sum_range_succ _ (n + 1)
        _ = ((∑ j ∈ Finset.range (n + 1), c j) * a n +
              ∑ i ∈ Finset.range n,
                (∑ j ∈ Finset.range (i + 1), c j) * (a i - a (i + 1))) +
              c (n + 1) * a (n + 1) := by rw [ih]
        _ = (∑ j ∈ Finset.range (n + 1 + 1), c j) * a (n + 1) +
              ∑ i ∈ Finset.range (n + 1),
                (∑ j ∈ Finset.range (i + 1), c j) * (a i - a (i + 1)) := by
          rw [hPrefix, hDiff]
          ring

/-- Nagura's coefficient attached to the `m`th term of the decreasing
Chebyshev sequence. -/
def naguraWeight (m : ℕ) : ℝ :=
  1 - (if 2 ∣ m then 1 else 0) - (if 3 ∣ m then 1 else 0) -
    (if 7 ∣ m then 1 else 0) - (if 43 ∣ m then 1 else 0) -
      (if 1806 ∣ m then 1 else 0)

/-- The exact prefix sum of Nagura's weights. -/
def naguraWeightPrefix (m : ℕ) : ℝ :=
  (m : ℝ) - (m / 2 : ℕ) - (m / 3 : ℕ) - (m / 7 : ℕ) -
    (m / 43 : ℕ) - (m / 1806 : ℕ)

theorem sum_naguraWeight_eq_prefix (m : ℕ) :
    (∑ i ∈ Finset.range m, naguraWeight (i + 1)) = naguraWeightPrefix m := by
  simp only [naguraWeight, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  rw [sum_dvd_indicator_eq_div 2,
    sum_dvd_indicator_eq_div 3,
    sum_dvd_indicator_eq_div 7,
    sum_dvd_indicator_eq_div 43,
    sum_dvd_indicator_eq_div 1806]
  rfl

/-- Every prefix sum of Nagura's weights is nonnegative.  This is the exact
integer content of the reciprocal identity. -/
theorem naguraWeightPrefix_nonneg (m : ℕ) :
    0 ≤ naguraWeightPrefix m := by
  let q := m / 2 + m / 3 + m / 7 + m / 43 + m / 1806
  have h2 := Nat.div_mul_le_self m 2
  have h3 := Nat.div_mul_le_self m 3
  have h7 := Nat.div_mul_le_self m 7
  have h43 := Nat.div_mul_le_self m 43
  have h1806 := Nat.div_mul_le_self m 1806
  have hq : q ≤ m := by
    dsimp only [q]
    omega
  have hqR : (q : ℝ) ≤ (m : ℝ) := by exact_mod_cast hq
  dsimp only [q] at hqR
  push_cast at hqR
  unfold naguraWeightPrefix
  linarith

/-- Before the first complete `1806`-block, every nonempty prefix sum is at
least one. -/
theorem one_le_naguraWeightPrefix {m : ℕ} (hm : 0 < m) (hm1806 : m < 1806) :
    1 ≤ naguraWeightPrefix m := by
  let q := m / 2 + m / 3 + m / 7 + m / 43
  have h2 := Nat.div_mul_le_self m 2
  have h3 := Nat.div_mul_le_self m 3
  have h7 := Nat.div_mul_le_self m 7
  have h43 := Nat.div_mul_le_self m 43
  have hq : q < m := by
    dsimp only [q]
    omega
  have hqR : (q : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hq
  dsimp only [q] at hqR
  push_cast at hqR
  unfold naguraWeightPrefix
  rw [Nat.div_eq_of_lt hm1806]
  norm_num
  linarith

/-- The abstract decreasing-sequence inequality behind Nagura's choice of
denominators.  The right side uses at least one full `1806`-block. -/
theorem first_sub_1806_le_nagura_weighted_sum
    (a : ℕ → ℝ) (ha : Antitone a) (ha0 : ∀ i, 0 ≤ a i)
    {N : ℕ} (hN : 1806 ≤ N) :
    a 0 - a 1805 ≤
      ∑ i ∈ Finset.range N, naguraWeight (i + 1) * a i := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hM : 1805 ≤ M := by omega
  let c : ℕ → ℝ := fun i ↦ naguraWeight (i + 1)
  let P : ℕ → ℝ := fun i ↦ ∑ j ∈ Finset.range (i + 1), c j
  have hP (i : ℕ) : P i = naguraWeightPrefix (i + 1) := by
    exact sum_naguraWeight_eq_prefix (i + 1)
  have hP0 (i : ℕ) : 0 ≤ P i := by
    rw [hP]
    exact naguraWeightPrefix_nonneg (i + 1)
  have hDiff (i : ℕ) : 0 ≤ a i - a (i + 1) := by
    exact sub_nonneg.mpr (ha (Nat.le_succ i))
  have hInitial :
      (∑ i ∈ Finset.range 1805, (a i - a (i + 1))) ≤
        ∑ i ∈ Finset.range 1805, P i * (a i - a (i + 1)) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi1805 : i < 1805 := Finset.mem_range.mp hi
    have hP1 : 1 ≤ P i := by
      rw [hP]
      exact one_le_naguraWeightPrefix (by omega) (by omega)
    nlinarith [mul_le_mul_of_nonneg_right hP1 (hDiff i)]
  have hExtend :
      (∑ i ∈ Finset.range 1805, P i * (a i - a (i + 1))) ≤
        ∑ i ∈ Finset.range M, P i * (a i - a (i + 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hM)
    intro i _ _
    exact mul_nonneg (hP0 i) (hDiff i)
  have hEndpoint : 0 ≤ P M * a M := mul_nonneg (hP0 M) (ha0 M)
  have hAbel := sum_range_mul_eq_partial_sum c a M
  change
    (∑ i ∈ Finset.range (M + 1), naguraWeight (i + 1) * a i) =
      P M * a M +
        ∑ i ∈ Finset.range M, P i * (a i - a (i + 1)) at hAbel
  rw [Finset.sum_range_sub'] at hInitial
  linarith

/-- Zero-based form of Nagura's finite Chebyshev sum. -/
theorem naguraChebyshevSum_eq_sum_range (n : ℕ) :
    naguraChebyshevSum n =
      ∑ i ∈ Finset.range n, Chebyshev.psi ((n / (i + 1) : ℕ) : ℝ) := by
  unfold naguraChebyshevSum
  exact sum_Ioc_zero_eq_sum_range_succ (R := ℝ) _ n

/-- The indicator for multiples of `d` selects exactly the Chebyshev sum at
the divided endpoint. -/
theorem sum_dvd_indicator_psi_eq_chebyshevSum
    (d : ℕ) (n : ℕ) :
    (∑ i ∈ Finset.range n,
      if d ∣ i + 1 then Chebyshev.psi ((n / (i + 1) : ℕ) : ℝ) else 0) =
        naguraChebyshevSum (n / d) := by
  rw [naguraChebyshevSum_eq_sum_range]
  calc
    (∑ i ∈ Finset.range n,
        if d ∣ i + 1 then Chebyshev.psi ((n / (i + 1) : ℕ) : ℝ) else 0) =
      ∑ j ∈ Finset.range (n / d),
        Chebyshev.psi ((n / (d * (j + 1)) : ℕ) : ℝ) :=
      sum_dvd_indicator_apply_eq d
        (fun m ↦ Chebyshev.psi ((n / m : ℕ) : ℝ)) n
    _ = ∑ j ∈ Finset.range (n / d),
        Chebyshev.psi (((n / d) / (j + 1) : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.div_div_eq_div_mul]

/-- Exact expansion of Nagura's weighted decreasing sequence as his six-term
Chebyshev combination, before specializing to a multiple of `1806`. -/
theorem sum_naguraWeight_mul_psi_eq (n : ℕ) :
    (∑ i ∈ Finset.range n,
      naguraWeight (i + 1) * Chebyshev.psi ((n / (i + 1) : ℕ) : ℝ)) =
      naguraChebyshevSum n - naguraChebyshevSum (n / 2) -
        naguraChebyshevSum (n / 3) - naguraChebyshevSum (n / 7) -
          naguraChebyshevSum (n / 43) - naguraChebyshevSum (n / 1806) := by
  simp only [naguraWeight, sub_mul, one_mul, Finset.sum_sub_distrib]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← naguraChebyshevSum_eq_sum_range n,
    sum_dvd_indicator_psi_eq_chebyshevSum 2 n,
    sum_dvd_indicator_psi_eq_chebyshevSum 3 n,
    sum_dvd_indicator_psi_eq_chebyshevSum 7 n,
    sum_dvd_indicator_psi_eq_chebyshevSum 43 n,
    sum_dvd_indicator_psi_eq_chebyshevSum 1806 n]

/-- At an `1806`-multiple, the exact weighted expansion is the named Nagura
combination. -/
theorem sum_naguraWeight_mul_psi_eq_combination (k : ℕ) :
    (∑ i ∈ Finset.range (1806 * k),
      naguraWeight (i + 1) *
        Chebyshev.psi (((1806 * k) / (i + 1) : ℕ) : ℝ)) =
      naguraChebyshevCombination k := by
  rw [sum_naguraWeight_mul_psi_eq]
  have h2 : 1806 * k / 2 = 903 * k := by omega
  have h3 : 1806 * k / 3 = 602 * k := by omega
  have h7 : 1806 * k / 7 = 258 * k := by omega
  have h43 : 1806 * k / 43 = 42 * k := by omega
  have h1806 : 1806 * k / 1806 = k := by omega
  rw [h2, h3, h7, h43, h1806]
  rfl

/-- The exact combinatorial bridge: Nagura's six-term combination controls
the increase of `ψ` across one factor of `1806`. -/
theorem psi_sub_psi_le_naguraChebyshevCombination
    {k : ℕ} (hk : 0 < k) :
    Chebyshev.psi ((1806 * k : ℕ) : ℝ) - Chebyshev.psi (k : ℝ) ≤
      naguraChebyshevCombination k := by
  let a : ℕ → ℝ := fun i ↦
    Chebyshev.psi (((1806 * k) / (i + 1) : ℕ) : ℝ)
  have ha : Antitone a := by
    intro i j hij
    apply Chebyshev.psi_mono
    norm_cast
    apply (Nat.le_div_iff_mul_le (by omega : 0 < i + 1)).2
    calc
      (1806 * k / (j + 1)) * (i + 1) ≤
          (1806 * k / (j + 1)) * (j + 1) := by
        exact Nat.mul_le_mul_left _ (Nat.succ_le_succ hij)
      _ ≤ 1806 * k := Nat.div_mul_le_self _ _
  have ha0 (i : ℕ) : 0 ≤ a i := Chebyshev.psi_nonneg _
  have h := first_sub_1806_le_nagura_weighted_sum a ha ha0
    (by omega : 1806 ≤ 1806 * k)
  dsimp only [a] at h
  rw [sum_naguraWeight_mul_psi_eq_combination] at h
  have hDiv : 1806 * k / 1806 = k := by omega
  simpa [hDiv] using h

/-- Nagura's explicit global upper constant at every positive multiple of
`1806`.  The small recursive `ψ(k)` term is absorbed using Mathlib's coarse
global Chebyshev bound and the gap between `1.083` and `1.086`. -/
theorem psi_mul_1806_lt_1_086 {k : ℕ} (hk : 0 < k) :
    Chebyshev.psi ((1806 * k : ℕ) : ℝ) <
      (543 : ℝ) / 500 * ((1806 * k : ℕ) : ℝ) := by
  have hBridge := psi_sub_psi_le_naguraChebyshevCombination hk
  have hCombination := naguraChebyshevCombination_lt_1_083_mul hk
  have hPsiK := Chebyshev.psi_le_const_mul_self (x := (k : ℝ)) (by positivity)
  have hLogFour : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hCoarseConstant : Real.log 4 + 4 < (2709 : ℝ) / 500 := by
    rw [hLogFour]
    nlinarith [Real.log_two_lt_d9]
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hCoarseTerm := mul_lt_mul_of_pos_right hCoarseConstant hkR
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hBridge hCombination ⊢
  nlinarith

end Erdos390.WholePaper
