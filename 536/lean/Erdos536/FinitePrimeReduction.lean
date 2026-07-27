import Erdos536.UnitExponentDeletion
import Erdos536.FiniteProbability
import Erdos536.Statement

/-!
# From unit-exponent deletion to a finite-prime density bound

This module supplies the finite summation-by-parts layer after
`f_le_unitExponentDeletion`.  The main ingredients are:

* monotonicity and saturation of the squarefree prefix extremum;
* its equivalent positive-increment expression;
* periodic counting for each arithmetic core category.

All statements are finite.  The final asymptotic formulation is obtained
by letting the explicit `O(1) / N` remainder tend to zero.
-/

open scoped BigOperators
open Filter Finset Nat

namespace Erdos536

/-! ## Squarefree-prefix increments -/

theorem squarefreeExtremal_mono (R : Finset ℕ) :
    Monotone (squarefreeExtremal R) := by
  intro n N hnN
  obtain ⟨𝓕, hsub, hadm, hcard⟩ := exists_squarefreeExtremal R n
  rw [← hcard]
  apply card_le_squarefreeExtremal
  · exact hsub.trans (fun S hS => by
      rw [mem_squarefreePrefix_iff] at hS ⊢
      exact ⟨hS.1, hS.2.trans hnN⟩)
  · exact hadm

theorem squarefreeExtremal_zero
    (R : Finset ℕ) (hR : IsPrimeSupport R) :
    squarefreeExtremal R 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  calc
    squarefreeExtremal R 0 ≤ (squarefreePrefix R 0).card :=
      squarefreeExtremal_le_prefix_card R 0
    _ = 0 := by
      rw [Finset.card_eq_zero]
      ext S
      simp only [mem_squarefreePrefix_iff, Finset.notMem_empty, iff_false]
      intro hS
      have hpos := primeProduct_pos (isPrimeSupport_mono hR hS.1)
      omega

theorem squarefreePrefix_eq_powerset_of_total_le
    {R : Finset ℕ} (hR : IsPrimeSupport R) {n : ℕ}
    (hn : primeProduct R ≤ n) :
    squarefreePrefix R n = R.powerset := by
  ext S
  rw [mem_squarefreePrefix_iff, Finset.mem_powerset]
  exact ⟨fun h => h.1, fun h =>
    ⟨h, (primeProduct_le_total hR h).trans hn⟩⟩

theorem squarefreeExtremal_eq_total_of_total_le
    {R : Finset ℕ} (hR : IsPrimeSupport R) {n : ℕ}
    (hn : primeProduct R ≤ n) :
    squarefreeExtremal R n =
      squarefreeExtremal R (primeProduct R) := by
  have hnPrefix := squarefreePrefix_eq_powerset_of_total_le hR hn
  have htotalPrefix := squarefreePrefix_at_total R hR
  unfold squarefreeExtremal squarefreeAdmissibleFamilies
  rw [hnPrefix, htotalPrefix]

/-- Telescoping a monotone natural-valued prefix function by its positive
increments. -/
theorem sum_Icc_nat_increments
    (b : ℕ → ℕ) (hb : Monotone b) (hb0 : b 0 = 0) (q : ℕ) :
    ∑ t ∈ Finset.Icc 1 q, (b t - b (t - 1)) = b q := by
  induction q with
  | zero => simp [hb0]
  | succ q ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      rw [show q + 1 - 1 = q by omega]
      exact Nat.add_sub_of_le (hb (Nat.le_succ q))

/-- Abel's finite identity converting positive increments into the
step-integral expression used by `squarefreeI`. -/
theorem sum_Icc_cast_increments_div
    (b : ℕ → ℕ) (hb : Monotone b) (hb0 : b 0 = 0) (D : ℕ) :
    (∑ t ∈ Finset.Icc 1 D,
        ((b t - b (t - 1) : ℕ) : ℝ) / (t : ℝ)) =
      (∑ n ∈ Finset.Ico 1 D,
          (b n : ℝ) *
            ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹)) +
        (b D : ℝ) / (D : ℝ) := by
  induction D with
  | zero => simp [hb0]
  | succ D ih =>
      cases D with
      | zero => simp [hb0]
      | succ D =>
          rw [Finset.sum_Icc_succ_top (by omega),
            Finset.sum_Ico_succ_top (by omega), ih]
          simp only [Nat.add_sub_cancel]
          have hmono : b (D + 1) ≤ b (D + 1 + 1) :=
            hb (by omega)
          rw [Nat.cast_sub hmono]
          have hD1 : ((D + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          have hD2 : ((D + 2 : ℕ) : ℝ) ≠ 0 := by positivity
          field_simp
          ring

/-- The manuscript's finite squarefree capacity is exactly the sum of
positive prefix increments divided by their cutoff. -/
theorem squarefreeI_eq_increment_sum
    (R : Finset ℕ) (hR : IsPrimeSupport R) :
    squarefreeI R =
      ∑ t ∈ Finset.Icc 1 (primeProduct R),
        ((squarefreeExtremal R t -
          squarefreeExtremal R (t - 1) : ℕ) : ℝ) / (t : ℝ) := by
  rw [squarefreeI]
  symm
  exact sum_Icc_cast_increments_div (squarefreeExtremal R)
    (squarefreeExtremal_mono R) (squarefreeExtremal_zero R hR)
    (primeProduct R)

/-! ## Layer-cake summation over a core category -/

theorem mem_unitCoreCategory_iff
    {E R : Finset ℕ} (hE : IsPrimeSupport E) {N m : ℕ} :
    m ∈ unitCoreCategory E R N ↔
      ∃ k : ℕ,
        1 ≤ k ∧ (primeProduct R).Coprime k ∧
          m = primeProduct (E \ R) ^ 2 * k ∧ m ≤ N := by
  let D2 := primeProduct (E \ R) ^ 2
  have hD2pos : 0 < D2 := by
    dsimp [D2]
    exact pow_pos (primeProduct_pos
      (isPrimeSupport_mono hE Finset.sdiff_subset)) 2
  rw [unitCoreCategory]
  constructor
  · intro hm
    obtain ⟨k, hk, hkm⟩ := Finset.mem_image.mp hm
    have hkData := Finset.mem_filter.mp hk
    have hkIcc := Finset.mem_Icc.mp hkData.1
    refine ⟨k, hkIcc.1, hkData.2, hkm.symm, ?_⟩
    rw [← hkm]
    rw [Nat.le_div_iff_mul_le hD2pos] at hkIcc
    simpa [D2, mul_comm] using hkIcc.2
  · rintro ⟨k, hk1, hkcop, rfl, hbound⟩
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hk1, ?_⟩, hkcop⟩, rfl⟩
    rw [Nat.le_div_iff_mul_le hD2pos]
    simpa [D2, mul_comm] using hbound

theorem unitCoreCategory_filter_div
    {E R : Finset ℕ} (hE : IsPrimeSupport E) {N t : ℕ}
    (ht : 0 < t) :
    (unitCoreCategory E R N).filter (fun m => t ≤ N / m) =
      unitCoreCategory E R (N / t) := by
  ext m
  rw [Finset.mem_filter, mem_unitCoreCategory_iff hE,
    mem_unitCoreCategory_iff hE]
  constructor
  · rintro ⟨⟨k, hk1, hkcop, hmk, hmN⟩, htq⟩
    have hDpos :
        0 < primeProduct (E \ R) ^ 2 :=
      pow_pos (primeProduct_pos
        (isPrimeSupport_mono hE Finset.sdiff_subset)) 2
    have hmpos : 0 < m := by
      rw [hmk]
      positivity
    refine ⟨k, hk1, hkcop, hmk, ?_⟩
    rw [Nat.le_div_iff_mul_le ht]
    rw [Nat.le_div_iff_mul_le hmpos] at htq
    simpa [mul_comm] using htq
  · rintro ⟨k, hk1, hkcop, hmk, hmNt⟩
    have hDpos :
        0 < primeProduct (E \ R) ^ 2 :=
      pow_pos (primeProduct_pos
        (isPrimeSupport_mono hE Finset.sdiff_subset)) 2
    have hmpos : 0 < m := by
      rw [hmk]
      positivity
    have hmtN : m * t ≤ N :=
      (Nat.le_div_iff_mul_le ht).mp hmNt
    refine ⟨⟨k, hk1, hkcop, hmk, ?_⟩, ?_⟩
    · exact (Nat.le_mul_of_pos_right m ht).trans hmtN
    · rw [Nat.le_div_iff_mul_le hmpos]
      simpa [mul_comm] using hmtN

theorem value_eq_sum_bounded_increments
    (b : ℕ → ℕ) (hb : Monotone b) (hb0 : b 0 = 0)
    {H q : ℕ} (hsat : H ≤ q → b q = b H) :
    b q =
      ∑ t ∈ Finset.Icc 1 H,
        if t ≤ q then b t - b (t - 1) else 0 := by
  by_cases hqH : q ≤ H
  · calc
      b q = ∑ t ∈ Finset.Icc 1 q, (b t - b (t - 1)) :=
        (sum_Icc_nat_increments b hb hb0 q).symm
      _ = ∑ t ∈ Finset.Icc 1 H,
          if t ≤ q then b t - b (t - 1) else 0 := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr
        · ext t
          simp only [Finset.mem_filter, Finset.mem_Icc]
          omega
        · intro t ht
          simp only
  · have hHq : H ≤ q := by omega
    rw [hsat hHq, ← sum_Icc_nat_increments b hb hb0 H]
    apply Finset.sum_congr rfl
    intro t ht
    rw [if_pos ((Finset.mem_Icc.mp ht).2.trans hHq)]

theorem sum_unitCoreCategory_eq_increment_layers
    {E R : Finset ℕ} (hE : IsPrimeSupport E)
    (b : ℕ → ℕ) (hb : Monotone b) (hb0 : b 0 = 0)
    {H N : ℕ} (hsat : ∀ q, H ≤ q → b q = b H) :
    (∑ m ∈ unitCoreCategory E R N, b (N / m)) =
      ∑ t ∈ Finset.Icc 1 H,
        (b t - b (t - 1)) *
          (unitCoreCategory E R (N / t)).card := by
  calc
    (∑ m ∈ unitCoreCategory E R N, b (N / m)) =
        ∑ m ∈ unitCoreCategory E R N,
          ∑ t ∈ Finset.Icc 1 H,
            if t ≤ N / m then b t - b (t - 1) else 0 := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact value_eq_sum_bounded_increments b hb hb0
        (fun h => hsat (N / m) h)
    _ = ∑ t ∈ Finset.Icc 1 H,
        ∑ m ∈ unitCoreCategory E R N,
          if t ≤ N / m then b t - b (t - 1) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ t ∈ Finset.Icc 1 H,
        (b t - b (t - 1)) *
          (unitCoreCategory E R (N / t)).card := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [← Finset.sum_filter]
      rw [unitCoreCategory_filter_div hE
        (show 0 < t from (Finset.mem_Icc.mp ht).1)]
      simp [mul_comm]

theorem sum_unitCoreCategory_squarefreeExtremal_eq
    {E R : Finset ℕ} (hE : IsPrimeSupport E)
    (hR : IsPrimeSupport R) (N : ℕ) :
    (∑ m ∈ unitCoreCategory E R N,
        squarefreeExtremal R (N / m)) =
      ∑ t ∈ Finset.Icc 1 (primeProduct R),
        (squarefreeExtremal R t -
          squarefreeExtremal R (t - 1)) *
            (unitCoreCategory E R (N / t)).card := by
  exact sum_unitCoreCategory_eq_increment_layers hE
    (squarefreeExtremal R) (squarefreeExtremal_mono R)
    (squarefreeExtremal_zero R hR)
    (fun q hq => squarefreeExtremal_eq_total_of_total_le hR hq)

/-! ## Explicit finite density bound -/

/-- Natural density of the arithmetic core category indexed by `R`. -/
noncomputable def unitCoreCategoryDensity
    (E R : Finset ℕ) : ℝ :=
  (primeProduct R).totient /
    ((primeProduct R : ℝ) * (primeProduct (E \ R) : ℝ) ^ 2)

theorem unitCoreCategoryDensity_nonneg (E R : Finset ℕ) :
    0 ≤ unitCoreCategoryDensity E R := by
  rw [unitCoreCategoryDensity]
  positivity

/-- Periodic category counting with an explicit uniform `O(1)` error. -/
theorem cast_card_unitCoreCategory_le
    {E R : Finset ℕ} (hE : IsPrimeSupport E) (hRE : R ⊆ E) (X : ℕ) :
    ((unitCoreCategory E R X).card : ℝ) ≤
      unitCoreCategoryDensity E R * X +
        ((primeProduct R).totient : ℝ) := by
  let d := primeProduct R
  let D2 := primeProduct (E \ R) ^ 2
  have hdpos : 0 < d :=
    primeProduct_pos (isPrimeSupport_mono hE hRE)
  have hD2pos : 0 < D2 := by
    dsimp [D2]
    exact pow_pos (primeProduct_pos
      (isPrimeSupport_mono hE Finset.sdiff_subset)) 2
  have hcount := card_unitCoreCategory_le hE hRE X
  change
    (unitCoreCategory E R X).card ≤
      d.totient * (X / D2 / d + 1) at hcount
  rw [Nat.div_div_eq_div_mul] at hcount
  calc
    ((unitCoreCategory E R X).card : ℝ) ≤
        ((d.totient * (X / (D2 * d) + 1) : ℕ) : ℝ) := by
      exact_mod_cast hcount
    _ = (d.totient : ℝ) *
        (((X / (D2 * d) : ℕ) : ℝ) + 1) := by norm_num
    _ ≤ (d.totient : ℝ) *
        ((X : ℝ) / (D2 * d : ℕ) + 1) := by
      gcongr
      exact Nat.cast_div_le
    _ = unitCoreCategoryDensity E R * X +
        (d.totient : ℝ) := by
      rw [unitCoreCategoryDensity]
      dsimp [d, D2]
      have hd : (primeProduct R : ℝ) ≠ 0 := by positivity
      have hbaseD :
          (primeProduct (E \ R) : ℝ) ≠ 0 := by
        exact_mod_cast primeProduct_ne_zero
          (isPrimeSupport_mono hE Finset.sdiff_subset)
      have hD :
          (primeProduct (E \ R) : ℝ) ^ 2 ≠ 0 :=
        pow_ne_zero 2 hbaseD
      push_cast
      field_simp

/-- One core category contributes its density times the squarefree
capacity, plus an explicit bounded remainder. -/
theorem cast_sum_unitCoreCategory_squarefreeExtremal_le
    {E R : Finset ℕ} (hE : IsPrimeSupport E) (hRE : R ⊆ E)
    (N : ℕ) :
    ((∑ m ∈ unitCoreCategory E R N,
        squarefreeExtremal R (N / m) : ℕ) : ℝ) ≤
      unitCoreCategoryDensity E R * (N : ℝ) * squarefreeI R +
        ((primeProduct R).totient : ℝ) *
          squarefreeExtremal R (primeProduct R) := by
  have hR : IsPrimeSupport R := isPrimeSupport_mono hE hRE
  have hlayers :=
    sum_unitCoreCategory_squarefreeExtremal_eq hE hR N
  rw [hlayers]
  push_cast
  calc
    (∑ t ∈ Finset.Icc 1 (primeProduct R),
        ((squarefreeExtremal R t -
          squarefreeExtremal R (t - 1) : ℕ) : ℝ) *
          ((unitCoreCategory E R (N / t)).card : ℝ)) ≤
      ∑ t ∈ Finset.Icc 1 (primeProduct R),
        ((squarefreeExtremal R t -
          squarefreeExtremal R (t - 1) : ℕ) : ℝ) *
          (unitCoreCategoryDensity E R * ((N : ℝ) / (t : ℝ)) +
            ((primeProduct R).totient : ℝ)) := by
      apply Finset.sum_le_sum
      intro t ht
      apply mul_le_mul_of_nonneg_left
      · calc
          ((unitCoreCategory E R (N / t)).card : ℝ) ≤
              unitCoreCategoryDensity E R * ((N / t : ℕ) : ℝ) +
                ((primeProduct R).totient : ℝ) :=
            cast_card_unitCoreCategory_le hE hRE (N / t)
          _ ≤ unitCoreCategoryDensity E R * ((N : ℝ) / (t : ℝ)) +
                ((primeProduct R).totient : ℝ) := by
            simpa [add_comm] using add_le_add_right
              (mul_le_mul_of_nonneg_left
                (Nat.cast_div_le :
                  ((N / t : ℕ) : ℝ) ≤ (N : ℝ) / (t : ℝ))
                (unitCoreCategoryDensity_nonneg E R))
              ((primeProduct R).totient : ℝ)
      · positivity
    _ = unitCoreCategoryDensity E R * (N : ℝ) *
          (∑ t ∈ Finset.Icc 1 (primeProduct R),
            ((squarefreeExtremal R t -
              squarefreeExtremal R (t - 1) : ℕ) : ℝ) / (t : ℝ)) +
        ((primeProduct R).totient : ℝ) *
          (∑ t ∈ Finset.Icc 1 (primeProduct R),
            ((squarefreeExtremal R t -
              squarefreeExtremal R (t - 1) : ℕ) : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _ht
      ring
    _ = unitCoreCategoryDensity E R * (N : ℝ) * squarefreeI R +
        ((primeProduct R).totient : ℝ) *
          squarefreeExtremal R (primeProduct R) := by
      rw [← squarefreeI_eq_increment_sum R hR]
      have htel :
          (∑ t ∈ Finset.Icc 1 (primeProduct R),
            ((squarefreeExtremal R t -
              squarefreeExtremal R (t - 1) : ℕ) : ℝ)) =
            squarefreeExtremal R (primeProduct R) := by
        exact_mod_cast sum_Icc_nat_increments
          (squarefreeExtremal R) (squarefreeExtremal_mono R)
          (squarefreeExtremal_zero R hR) (primeProduct R)
      rw [htel]

/-- Sum of category-density-weighted squarefree capacities. -/
noncomputable def finitePrimeDensityBound (E : Finset ℕ) : ℝ :=
  ∑ R ∈ E.powerset, unitCoreCategoryDensity E R * squarefreeI R

/-- Explicit bounded error in the finite reduction. -/
noncomputable def finitePrimeDensityError (E : Finset ℕ) : ℝ :=
  ∑ R ∈ E.powerset,
    ((primeProduct R).totient : ℝ) *
      squarefreeExtremal R (primeProduct R)

theorem sum_unitCores_le_sum_categories
    {E : Finset ℕ} (hE : IsPrimeSupport E) (N : ℕ) :
    (∑ m ∈ unitCores E N,
        squarefreeExtremal (E \ m.primeFactors) (N / m)) ≤
      ∑ R ∈ E.powerset,
        ∑ m ∈ unitCoreCategory E R N,
          squarefreeExtremal R (N / m) := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := unitCores E N) (t := E.powerset)
    (g := fun m => E \ m.primeFactors)
    (fun m _hm => Finset.mem_powerset.mpr Finset.sdiff_subset)
    (fun m => squarefreeExtremal (E \ m.primeFactors) (N / m))]
  apply Finset.sum_le_sum
  intro R hR
  calc
    (∑ i ∈ unitCores E N with E \ i.primeFactors = R,
        squarefreeExtremal (E \ i.primeFactors) (N / i)) =
        ∑ i ∈ unitCores E N with E \ i.primeFactors = R,
          squarefreeExtremal R (N / i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ ≤ ∑ m ∈ unitCoreCategory E R N,
        squarefreeExtremal R (N / m) := by
      apply Finset.sum_le_sum_of_subset
      intro m hm
      have hmData := Finset.mem_filter.mp hm
      have hmCategory := unitCore_mem_ownCategory hE hmData.1
      simpa [hmData.2] using hmCategory

/-- Complete finite reduction with its explicit `O_E(1)` remainder. -/
theorem cast_f_le_finitePrimeDensityBound
    {E : Finset ℕ} (hE : IsPrimeSupport E) (N : ℕ) :
    (f N : ℝ) ≤
      (N : ℝ) * finitePrimeDensityBound E +
        finitePrimeDensityError E := by
  calc
    (f N : ℝ) ≤
        ((∑ m ∈ unitCores E N,
          squarefreeExtremal (E \ m.primeFactors) (N / m) : ℕ) : ℝ) := by
      exact_mod_cast f_le_unitExponentDeletion hE N
    _ ≤ ((∑ R ∈ E.powerset,
        ∑ m ∈ unitCoreCategory E R N,
          squarefreeExtremal R (N / m) : ℕ) : ℝ) := by
      exact_mod_cast sum_unitCores_le_sum_categories hE N
    _ = ∑ R ∈ E.powerset,
        ((∑ m ∈ unitCoreCategory E R N,
          squarefreeExtremal R (N / m) : ℕ) : ℝ) := by
      push_cast
      rfl
    _ ≤ ∑ R ∈ E.powerset,
        (unitCoreCategoryDensity E R * (N : ℝ) * squarefreeI R +
          ((primeProduct R).totient : ℝ) *
            squarefreeExtremal R (primeProduct R)) := by
      apply Finset.sum_le_sum
      intro R hR
      exact cast_sum_unitCoreCategory_squarefreeExtremal_le hE
        (Finset.mem_powerset.mp hR) N
    _ = (N : ℝ) * finitePrimeDensityBound E +
        finitePrimeDensityError E := by
      rw [finitePrimeDensityBound, finitePrimeDensityError,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro R _hR
      ring

theorem f_div_le_finitePrimeDensityBound
    {E : Finset ℕ} (hE : IsPrimeSupport E) {N : ℕ} (hN : 0 < N) :
    (f N : ℝ) / (N : ℝ) ≤
      finitePrimeDensityBound E +
        finitePrimeDensityError E / (N : ℝ) := by
  apply (div_le_iff₀ (by exact_mod_cast hN)).mpr
  calc
    (f N : ℝ) ≤
        (N : ℝ) * finitePrimeDensityBound E +
          finitePrimeDensityError E :=
      cast_f_le_finitePrimeDensityBound hE N
    _ = (finitePrimeDensityBound E +
          finitePrimeDensityError E / (N : ℝ)) * (N : ℝ) := by
      field_simp

/-! ## Normalizing the category weights -/

theorem totient_primeProduct_div_eq_prod
    (R : Finset ℕ) (hR : IsPrimeSupport R) :
    ((primeProduct R).totient : ℝ) / (primeProduct R : ℝ) =
      ∏ p ∈ R, (1 - (p : ℝ)⁻¹) := by
  have hq := Nat.totient_eq_mul_prod_factors (primeProduct R)
  rw [primeFactors_primeProduct hR] at hq
  have hqdiv :
      ((primeProduct R).totient : ℚ) / (primeProduct R : ℚ) =
        ∏ p ∈ R, (1 - (p : ℚ)⁻¹) := by
    rw [hq]
    field_simp [primeProduct_ne_zero hR]
  have hr := congrArg (fun x : ℚ => (x : ℝ)) hqdiv
  simpa using hr

/-- The inclusion probability in the normalized deletion law. -/
noncomputable def deletionInclusion (p : ℕ) : ℝ :=
  1 - (p : ℝ)⁻¹ ^ 2

theorem unitCoreCategoryDensity_mul_Z_eq_subsetWeight
    {E R : Finset ℕ} (hE : IsPrimeSupport E) (hRE : R ⊆ E) :
    unitCoreCategoryDensity E R * squarefreeZ R =
      subsetWeight E deletionInclusion R := by
  have hR : IsPrimeSupport R := isPrimeSupport_mono hE hRE
  have htot := totient_primeProduct_div_eq_prod R hR
  rw [unitCoreCategoryDensity, squarefreeZ_eq_prod, subsetWeight]
  have hdR : (primeProduct R : ℝ) ≠ 0 := by
    exact_mod_cast primeProduct_ne_zero hR
  have hcomp : IsPrimeSupport (E \ R) :=
    isPrimeSupport_mono hE Finset.sdiff_subset
  have hdC : (primeProduct (E \ R) : ℝ) ≠ 0 := by
    exact_mod_cast primeProduct_ne_zero hcomp
  rw [show ((primeProduct R).totient : ℝ) /
      ((primeProduct R : ℝ) * (primeProduct (E \ R) : ℝ) ^ 2) =
      (((primeProduct R).totient : ℝ) / (primeProduct R : ℝ)) /
        (primeProduct (E \ R) : ℝ) ^ 2 by field_simp]
  rw [htot, div_eq_mul_inv]
  rw [show (∏ p ∈ R, (1 - (p : ℝ)⁻¹)) *
      ((primeProduct (E \ R) : ℝ) ^ 2)⁻¹ *
      (∏ p ∈ R, (1 + (p : ℝ)⁻¹)) =
      ((∏ p ∈ R, (1 - (p : ℝ)⁻¹)) *
        ∏ p ∈ R, (1 + (p : ℝ)⁻¹)) *
          ((primeProduct (E \ R) : ℝ) ^ 2)⁻¹ by ring]
  rw [← Finset.prod_mul_distrib]
  simp_rw [show ∀ p : ℕ,
      (1 - (p : ℝ)⁻¹) * (1 + (p : ℝ)⁻¹) =
        1 - (p : ℝ)⁻¹ ^ 2 by intro p; ring]
  rw [primeProduct, Nat.cast_prod, ← Finset.prod_pow]
  rw [← Finset.prod_inv_distrib]
  simp only [inv_pow, deletionInclusion]
  congr 1
  apply Finset.prod_congr rfl
  intro p _hp
  ring

theorem deletionInclusion_bounds
    {E : Finset ℕ} (hE : IsPrimeSupport E) {p : ℕ} (hp : p ∈ E) :
    0 ≤ deletionInclusion p ∧ deletionInclusion p ≤ 1 := by
  have hpReal : 1 ≤ (p : ℝ) := by
    exact_mod_cast (hE p hp).one_le
  have hinv : 0 ≤ (p : ℝ)⁻¹ ^ 2 := sq_nonneg _
  have hinvle : (p : ℝ)⁻¹ ^ 2 ≤ 1 := by
    have : (p : ℝ)⁻¹ ≤ 1 := by
      simpa using (inv_le_one₀ (by positivity)).mpr hpReal
    simpa [pow_two] using
      mul_self_le_mul_self (inv_nonneg.mpr (by positivity)) this
  exact ⟨sub_nonneg.mpr hinvle, sub_le_self 1 hinv⟩

theorem one_sub_prod_one_sub_le_sum
    {ι : Type*} [DecidableEq ι] (P : Finset ι) (a : ι → ℝ)
    (ha0 : ∀ p ∈ P, 0 ≤ a p) (ha1 : ∀ p ∈ P, a p ≤ 1) :
    1 - ∏ p ∈ P, (1 - a p) ≤ ∑ p ∈ P, a p := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
      rw [Finset.prod_insert hp, Finset.sum_insert hp]
      have hprod0 : 0 ≤ ∏ q ∈ P, (1 - a q) := by
        apply Finset.prod_nonneg
        intro q hq
        exact sub_nonneg.mpr (ha1 q (Finset.mem_insert_of_mem hq))
      have hprod1 : ∏ q ∈ P, (1 - a q) ≤ 1 := by
        apply Finset.prod_le_one
        · intro q hq
          exact sub_nonneg.mpr (ha1 q (Finset.mem_insert_of_mem hq))
        · intro q hq
          exact sub_le_self 1 (ha0 q (Finset.mem_insert_of_mem hq))
      calc
        1 - (1 - a p) * ∏ q ∈ P, (1 - a q) =
            (1 - ∏ q ∈ P, (1 - a q)) +
              a p * ∏ q ∈ P, (1 - a q) := by ring
        _ ≤ (∑ q ∈ P, a q) + a p := by
          apply _root_.add_le_add
          · exact ih
              (fun q hq => ha0 q (Finset.mem_insert_of_mem hq))
              (fun q hq => ha1 q (Finset.mem_insert_of_mem hq))
          · exact mul_le_of_le_one_right
              (ha0 p (Finset.mem_insert_self p P)) hprod1
        _ = a p + ∑ q ∈ P, a q := by ring

theorem subsetWeight_expectation_le_full_add_missing
    {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r : ι → ℝ) (g : Finset ι → ℝ)
    (hr0 : ∀ p ∈ P, 0 ≤ r p) (hr1 : ∀ p ∈ P, r p ≤ 1)
    (hg0 : ∀ S ∈ P.powerset, 0 ≤ g S)
    (hg1 : ∀ S ∈ P.powerset, g S ≤ 1) :
    ∑ S ∈ P.powerset, subsetWeight P r S * g S ≤
      g P + ∑ p ∈ P, (1 - r p) := by
  let W := fun S => subsetWeight P r S
  have hPmem : P ∈ P.powerset := Finset.mem_powerset.mpr subset_rfl
  have hsplitW :
      (∑ S ∈ P.powerset.erase P, W S) + W P = 1 := by
    rw [Finset.sum_erase_add P.powerset W hPmem]
    exact sum_subsetWeight P r
  have hsplit :
      (∑ S ∈ P.powerset, W S * g S) =
        (∑ S ∈ P.powerset.erase P, W S * g S) + W P * g P := by
    exact (Finset.sum_erase_add P.powerset
      (fun S => W S * g S) hPmem).symm
  rw [hsplit]
  have hoff :
      (∑ S ∈ P.powerset.erase P, W S * g S) ≤
        ∑ S ∈ P.powerset.erase P, W S := by
    apply Finset.sum_le_sum
    intro S hS
    apply mul_le_of_le_one_right
    · exact subsetWeight_nonneg hr0 hr1
        (Finset.mem_powerset.mp (Finset.mem_of_mem_erase hS))
    · exact hg1 S (Finset.mem_of_mem_erase hS)
  calc
    (∑ S ∈ P.powerset.erase P, W S * g S) + W P * g P ≤
        (∑ S ∈ P.powerset.erase P, W S) + W P * g P :=
      by simpa [add_comm] using add_le_add_right hoff (W P * g P)
    _ = 1 - W P + W P * g P := by linarith
    _ ≤ g P + (1 - W P) := by
      have hWle : W P ≤ 1 := by
        have hother : 0 ≤ ∑ S ∈ P.powerset.erase P, W S := by
          apply Finset.sum_nonneg
          intro S hS
          exact subsetWeight_nonneg hr0 hr1
            (Finset.mem_powerset.mp (Finset.mem_of_mem_erase hS))
        linarith
      have hgp := hg0 P hPmem
      nlinarith
    _ ≤ g P + ∑ p ∈ P, (1 - r p) := by
      have hWP :
          W P = ∏ p ∈ P, r p := by
        simp [W, subsetWeight]
      rw [hWP]
      have hunion :=
        one_sub_prod_one_sub_le_sum P (fun p => 1 - r p)
          (fun p hp => sub_nonneg.mpr (hr1 p hp))
          (fun p hp => sub_le_self 1 (hr0 p hp))
      simpa only [sub_sub_cancel, add_comm] using
        add_le_add_right hunion (g P)

theorem unitCoreCategoryDensity_mul_I_eq_weighted_normalized
    {E R : Finset ℕ} (hE : IsPrimeSupport E) (hRE : R ⊆ E) :
    unitCoreCategoryDensity E R * squarefreeI R =
      subsetWeight E deletionInclusion R *
        (squarefreeI R / squarefreeZ R) := by
  have hR : IsPrimeSupport R := isPrimeSupport_mono hE hRE
  have hZ := squarefreeZ_pos R hR
  calc
    unitCoreCategoryDensity E R * squarefreeI R =
        (unitCoreCategoryDensity E R * squarefreeZ R) *
          (squarefreeI R / squarefreeZ R) := by
      field_simp
    _ = subsetWeight E deletionInclusion R *
          (squarefreeI R / squarefreeZ R) := by
      rw [unitCoreCategoryDensity_mul_Z_eq_subsetWeight hE hRE]

/-- The normalized all-unit-deletion inequality from the manuscript,
now as a finite identity/inequality over all support categories. -/
theorem finitePrimeDensityBound_le_normalized
    (E : Finset ℕ) (hE : IsPrimeSupport E) :
    finitePrimeDensityBound E ≤
      squarefreeI E / squarefreeZ E +
        ∑ p ∈ E, (p : ℝ)⁻¹ ^ 2 := by
  have hexpect :
      finitePrimeDensityBound E =
        ∑ R ∈ E.powerset,
          subsetWeight E deletionInclusion R *
            (squarefreeI R / squarefreeZ R) := by
    rw [finitePrimeDensityBound]
    apply Finset.sum_congr rfl
    intro R hR
    exact unitCoreCategoryDensity_mul_I_eq_weighted_normalized hE
      (Finset.mem_powerset.mp hR)
  rw [hexpect]
  have hbound :=
    subsetWeight_expectation_le_full_add_missing E deletionInclusion
      (fun R => squarefreeI R / squarefreeZ R)
      (fun p hp => (deletionInclusion_bounds hE hp).1)
      (fun p hp => (deletionInclusion_bounds hE hp).2)
      (fun R hR => (squarefree_normalized_bounds R
        (isPrimeSupport_mono hE (Finset.mem_powerset.mp hR))).1)
      (fun R hR => (squarefree_normalized_bounds R
        (isPrimeSupport_mono hE (Finset.mem_powerset.mp hR))).2)
  simpa only [deletionInclusion, sub_sub_cancel] using hbound

theorem finitePrimeDensityError_nonneg (E : Finset ℕ) :
    0 ≤ finitePrimeDensityError E := by
  rw [finitePrimeDensityError]
  apply Finset.sum_nonneg
  intro R _hR
  positivity

/-- Epsilon/eventual form of the finite-prime density envelope.  This is
the limsup API needed by the final quantifier argument. -/
theorem eventually_f_div_le_normalized
    (E : Finset ℕ) (hE : IsPrimeSupport E)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (f N : ℝ) / (N : ℝ) ≤
        squarefreeI E / squarefreeZ E +
          (∑ p ∈ E, (p : ℝ)⁻¹ ^ 2) + ε := by
  have hlim :
      Tendsto (fun N : ℕ => finitePrimeDensityError E / (N : ℝ))
        atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop
      (finitePrimeDensityError E)
  have herr :
      ∀ᶠ N : ℕ in atTop,
        finitePrimeDensityError E / (N : ℝ) < ε :=
    (tendsto_order.mp hlim).2 ε hε
  filter_upwards [herr, eventually_gt_atTop 0] with N herror hN
  calc
    (f N : ℝ) / (N : ℝ) ≤
        finitePrimeDensityBound E +
          finitePrimeDensityError E / (N : ℝ) :=
      f_div_le_finitePrimeDensityBound hE hN
    _ ≤ (squarefreeI E / squarefreeZ E +
          ∑ p ∈ E, (p : ℝ)⁻¹ ^ 2) +
          finitePrimeDensityError E / (N : ℝ) :=
      by simpa [add_comm] using
        add_le_add_right (finitePrimeDensityBound_le_normalized E hE)
          (finitePrimeDensityError E / (N : ℝ))
    _ ≤ squarefreeI E / squarefreeZ E +
          (∑ p ∈ E, (p : ℝ)⁻¹ ^ 2) + ε := by
      linarith

/-- The remaining task after the finite-prime reduction: it is enough to
produce finite prime supports with arbitrarily small normalized
squarefree capacity and square-reciprocal tail. -/
theorem mainTheorem_of_finite_squarefree_capacity
    (hcapacity :
      ∀ ε : ℝ, 0 < ε →
        ∃ E : Finset ℕ, IsPrimeSupport E ∧
          squarefreeI E / squarefreeZ E +
            (∑ p ∈ E, (p : ℝ)⁻¹ ^ 2) < ε) :
    MainTheorem := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  obtain ⟨E, hE, hEsmall⟩ := hcapacity (ε / 2) (half_pos hε)
  have hevent :=
    eventually_f_div_le_normalized E hE (ε := ε / 2) (half_pos hε)
  filter_upwards [hevent, eventually_gt_atTop 0] with N hbound hN
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hratio :
      (f N : ℝ) / (N : ℝ) ≤ ε := by
    linarith
  have hf :
      (f N : ℝ) ≤ ε * (N : ℝ) :=
    (div_le_iff₀ hNreal).mp hratio
  have hf0 : (0 : ℝ) ≤ (f N : ℝ) := by positivity
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := hNreal.le
  simpa only [Real.norm_eq_abs, abs_of_nonneg hf0,
    abs_of_nonneg hN0] using hf

end Erdos536
