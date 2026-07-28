import Mathlib.NumberTheory.AbelSummation

/-!
# Abel summation with a right derivative

The Dickman test function used in the de Bruijn--Saias Stieltjes
functional is continuous, but it has a corner when its logarithmic
coordinate is `1`.  The usual `sum_mul_eq_sub_sub_integral_mul` asks for a
two-sided derivative at every point of the closed interval and therefore
does not apply literally.

This file records the exact variant needed here.  Its proof follows the
unit-cell proof of Mathlib's Abel summation theorem, replacing the ordinary
FTC on a cell by `integral_eq_sub_of_hasDeriv_right_of_le`.  A single corner
(or indeed finitely many corners) is harmless as long as the displayed
right derivative exists and is integrable.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Finset MeasureTheory Set

noncomputable section

namespace RoughSaiasRightAbel

variable (c : ℕ → ℝ)

/-! ## Unit-cell facts -/

private theorem prefix_eq_on_unit_cell {m n : ℕ} :
    ∀ᵐ t : ℝ, t ∈ Set.Icc (n : ℝ) (n + 1) →
      ∑ k ∈ Finset.Icc m ⌊t⌋₊, c k =
        ∑ k ∈ Finset.Icc m n, c k := by
  filter_upwards [MeasureTheory.Ico_ae_eq_Icc] with t ht hmem
  rw [Nat.floor_eq_on_Ico _ _ (ht.mpr hmem)]

private theorem right_integral_mul_prefix
    {f f' : ℝ → ℝ} {a b t₁ t₂ : ℝ} {n : ℕ}
    (_hab : a ≤ b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_right : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt f (f' t) (Set.Ioi t) t)
    (hf'_int : IntegrableOn f' (Set.Icc a b))
    (ht : t₁ ≤ t₂) (hn₁ : (n : ℝ) ≤ t₁)
    (ht₂n : t₂ ≤ (n : ℝ) + 1)
    (hat₁ : a ≤ t₁) (ht₂b : t₂ ≤ b) :
    (∫ t in t₁..t₂,
        f' t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
      (f t₂ - f t₁) * ∑ k ∈ Finset.Icc 0 n, c k := by
  have hcell : Set.uIoc t₁ t₂ ⊆ Set.Icc (n : ℝ) (n + 1) := by
    rw [Set.uIoc_of_le ht]
    exact Set.Ioc_subset_Icc_self.trans
      (Set.Icc_subset_Icc hn₁ ht₂n)
  have hsub : Set.Icc t₁ t₂ ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc hat₁ ht₂b
  have hftc : (∫ t in t₁..t₂, f' t) = f t₂ - f t₁ := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    · exact hf_cont.mono hsub
    · intro t htOpen
      exact hf_right t
        ⟨hat₁.trans_lt htOpen.1, htOpen.2.trans_le ht₂b⟩
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht]
      exact hf'_int.mono_set hsub
  rw [← hftc, ← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [prefix_eq_on_unit_cell c (m := 0) (n := n)] with t hpref htmem
  rw [hpref (hcell htmem)]

private theorem left_floor_bounds {a b : ℝ} {k : ℕ}
    (hk : k ∈ Set.Ico (⌊a⌋₊ + 1) ⌊b⌋₊) :
    a ≤ k ∧ k + 1 ≤ b := by
  constructor
  · have hkleft := (Set.mem_Ico.mp hk).1
    exact le_of_lt ((Nat.floor_lt' (by omega)).mp hkleft)
  · rw [← Nat.cast_add_one, ← Nat.le_floor_iff' (Nat.succ_ne_zero k)]
    exact (Set.mem_Ico.mp hk).2

private theorem left_floor_bounds_finset {a b : ℝ} {k : ℕ}
    (hk : k ∈ Finset.Ico (⌊a⌋₊ + 1) ⌊b⌋₊) :
    a ≤ k ∧ k + 1 ≤ b := by
  exact left_floor_bounds (by simpa only [← Finset.coe_Ico] using hk)

/-! ## The right-derivative Abel identity -/

/-- Abel summation on a compact real interval for a continuous test
function with an integrable right derivative.  This differs from
`sum_mul_eq_sub_sub_integral_mul` only in the regularity datum. -/
theorem sum_mul_eq_sub_sub_integral_mul_right
    {f f' : ℝ → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_right : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt f (f' t) (Set.Ioi t) t)
    (hf'_int : IntegrableOn f' (Set.Icc a b)) :
    (∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k) =
      f b * (∑ k ∈ Finset.Icc 0 ⌊b⌋₊, c k) -
        f a * (∑ k ∈ Finset.Icc 0 ⌊a⌋₊, c k) -
        ∫ t in Set.Ioc a b,
          f' t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k := by
  rw [← intervalIntegral.integral_of_le hab]
  have haFloor : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha
  have hbCeil : b ≤ (⌊b⌋₊ : ℝ) + 1 :=
    (Nat.lt_floor_add_one _).le
  obtain hfloorEq | hfloorLt :=
      eq_or_lt_of_le (Nat.floor_le_floor hab)
  · rw [hfloorEq, Finset.Ioc_eq_empty_of_le le_rfl, Finset.sum_empty,
      ← sub_mul,
      right_integral_mul_prefix c hab hf_cont hf_right hf'_int
        hab (hfloorEq ▸ haFloor) hbCeil le_rfl le_rfl,
      sub_self]
  · have haSucc : a ≤ (⌊a⌋₊ : ℝ) + 1 :=
      (Nat.lt_floor_add_one _).le
    have haSuccB : (⌊a⌋₊ : ℝ) + 1 ≤ b := by
      rw [← Nat.cast_add_one, ← Nat.le_floor_iff (ha.trans hab)]
      exact hfloorLt
    have hbFloor : (⌊b⌋₊ : ℝ) ≤ b :=
      Nat.floor_le (ha.trans hab)
    have haFloorB : a ≤ (⌊b⌋₊ : ℝ) :=
      (Nat.floor_lt ha).mp hfloorLt |>.le
    simp_rw [← smul_eq_mul,
      Finset.sum_Ioc_by_parts (fun k ↦ f k) _ hfloorLt,
      Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc,
      smul_eq_mul]
    have hcells :
        (∑ k ∈ Finset.Ioc ⌊a⌋₊ (⌊b⌋₊ - 1),
            (f ((k + 1 : ℕ) : ℝ) - f k) *
              ∑ n ∈ Finset.Icc 0 k, c n) =
          ∑ k ∈ Finset.Ico (⌊a⌋₊ + 1) ⌊b⌋₊,
            ∫ t in (k : ℝ)..(k + 1 : ℕ),
              f' t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n := by
      rw [← Finset.Ico_add_one_add_one_eq_Ioc,
        Nat.sub_add_cancel (by omega), Eq.comm]
      apply Finset.sum_congr rfl
      intro k hk
      have hkBounds := left_floor_bounds_finset (a := a) (b := b) hk
      exact right_integral_mul_prefix c
        (t₁ := (k : ℝ)) (t₂ := ((k + 1 : ℕ) : ℝ)) (n := k)
        hab hf_cont hf_right hf'_int
        (by exact_mod_cast k.le_succ) le_rfl
        (by norm_num) hkBounds.1
        (by simpa only [Nat.cast_add, Nat.cast_one] using hkBounds.2)
    rw [hcells,
      intervalIntegral.sum_integral_adjacent_intervals_Ico hfloorLt,
      Nat.cast_add, Nat.cast_one,
      ← intervalIntegral.integral_interval_sub_left
        (a := a) (c := (⌊a⌋₊ : ℝ) + 1),
      ← intervalIntegral.integral_add_adjacent_intervals
        (b := (⌊b⌋₊ : ℝ)) (c := b),
      right_integral_mul_prefix c hab hf_cont hf_right hf'_int
        haSucc haFloor le_rfl le_rfl haSuccB,
      right_integral_mul_prefix c hab hf_cont hf_right hf'_int
        hbFloor le_rfl hbCeil haFloorB le_rfl]
    · ring
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le haFloorB]
      exact (integrableOn_mul_sum_Icc c ha hf'_int).mono_set
        (Set.Icc_subset_Icc_right hbFloor)
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hbFloor]
      exact (integrableOn_mul_sum_Icc c ha hf'_int).mono_set
        (Set.Icc_subset_Icc_left haFloorB)
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le haFloorB]
      exact (integrableOn_mul_sum_Icc c ha hf'_int).mono_set
        (Set.Icc_subset_Icc_right hbFloor)
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le haSucc]
      exact (integrableOn_mul_sum_Icc c ha hf'_int).mono_set
        (Set.Icc_subset_Icc_right haSuccB)
    · intro k hk
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le
        (by exact_mod_cast k.le_succ)]
      have hkBounds := left_floor_bounds (a := a) (b := b) hk
      have hkUpper : (((k + 1 : ℕ) : ℝ) ≤ b) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hkBounds.2
      exact (integrableOn_mul_sum_Icc c ha hf'_int).mono_set
        (Set.Icc_subset_Icc hkBounds.1 hkUpper)

/-- Natural-endpoint form of the right-derivative Abel identity. -/
theorem sum_mul_eq_sub_sub_integral_mul_right'
    {f f' : ℝ → ℝ} {n m : ℕ} (hnm : n ≤ m)
    (hf_cont : ContinuousOn f (Set.Icc (n : ℝ) m))
    (hf_right : ∀ t ∈ Set.Ioo (n : ℝ) m,
      HasDerivWithinAt f (f' t) (Set.Ioi t) t)
    (hf'_int : IntegrableOn f' (Set.Icc (n : ℝ) m)) :
    (∑ k ∈ Finset.Ioc n m, f k * c k) =
      f m * (∑ k ∈ Finset.Icc 0 m, c k) -
        f n * (∑ k ∈ Finset.Icc 0 n, c k) -
        ∫ t in Set.Ioc (n : ℝ) m,
          f' t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k := by
  simpa only [Nat.floor_natCast] using
    (sum_mul_eq_sub_sub_integral_mul_right c
      (a := (n : ℝ)) (b := (m : ℝ))
      n.cast_nonneg (Nat.cast_le.mpr hnm) hf_cont hf_right hf'_int)

end RoughSaiasRightAbel

end

end Erdos390.WholePaper
