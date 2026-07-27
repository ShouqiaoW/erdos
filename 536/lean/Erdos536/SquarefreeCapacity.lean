import Erdos536.Squarefree

/-!
# Finite squarefree capacity

This module gives a completely finite form of the squarefree capacity from
the manuscript. Every support product is a natural number. Consequently,
the extremal prefix function changes only at integer cutoffs, and its
integral against `x⁻² dx` is exactly a finite weighted sum plus one tail
term.
-/

open scoped BigOperators
open Finset Nat

namespace Erdos536

/-- The prime supports contained in `R` whose product is at most `n`. -/
def squarefreePrefix (R : Finset ℕ) (n : ℕ) : Finset (Finset ℕ) :=
  R.powerset.filter fun S => primeProduct S ≤ n

/-- All admissible subfamilies of the squarefree prefix at `n`. -/
noncomputable def squarefreeAdmissibleFamilies
    (R : Finset ℕ) (n : ℕ) : Finset (Finset (Finset ℕ)) := by
  classical
  exact (squarefreePrefix R n).powerset.filter Admissible

/-- The maximum size of an admissible family in the prefix at `n`. -/
noncomputable def squarefreeExtremal (R : Finset ℕ) (n : ℕ) : ℕ :=
  (squarefreeAdmissibleFamilies R n).sup card

/-- The squarefree partition function
`Z_R = ∑_{S ⊆ R} 1 / primeProduct S`. -/
noncomputable def squarefreeZ (R : Finset ℕ) : ℝ :=
  ∑ S ∈ R.powerset, (primeProduct S : ℝ)⁻¹

/-- The exact integral weight of the interval `[n, n+1]` for the density
`x ↦ x⁻²`. -/
noncomputable def reciprocalStep (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹

/-- The exact finite form of the manuscript's squarefree capacity.

Put `D = primeProduct R`. Since all possible support products are integers
at most `D`, the real prefix extremum is constant on every interval
`[n, n+1)` and is constant with value `squarefreeExtremal R D` after `D`.
The identities

`∫_[n,n+1] x⁻² dx = 1/n - 1/(n+1)` and
`∫_[D,∞) x⁻² dx = 1/D`

therefore turn the manuscript's interval integral into this finite sum
exactly. The theorem `sum_reciprocalStep_Ico` below proves the corresponding
finite telescoping identity used in the formal argument.
-/
noncomputable def squarefreeI (R : Finset ℕ) : ℝ :=
  (∑ n ∈ Ico 1 (primeProduct R),
      (squarefreeExtremal R n : ℝ) * reciprocalStep n) +
    (squarefreeExtremal R (primeProduct R) : ℝ) /
      (primeProduct R : ℝ)

@[simp]
theorem admissible_empty : Admissible ∅ := by
  simp [Admissible]

theorem mem_squarefreePrefix_iff {R S : Finset ℕ} {n : ℕ} :
    S ∈ squarefreePrefix R n ↔ S ⊆ R ∧ primeProduct S ≤ n := by
  simp [squarefreePrefix]

theorem mem_squarefreeAdmissibleFamilies_iff
    {R : Finset ℕ} {n : ℕ} {𝓕 : Finset (Finset ℕ)} :
    𝓕 ∈ squarefreeAdmissibleFamilies R n ↔
      𝓕 ⊆ squarefreePrefix R n ∧ Admissible 𝓕 := by
  simp [squarefreeAdmissibleFamilies]

theorem squarefreeAdmissibleFamilies_nonempty (R : Finset ℕ) (n : ℕ) :
    (squarefreeAdmissibleFamilies R n).Nonempty := by
  exact ⟨∅, mem_squarefreeAdmissibleFamilies_iff.mpr
    ⟨empty_subset _, admissible_empty⟩⟩

/-- Every admissible family in the prefix has size at most the extremal
quantity. -/
theorem card_le_squarefreeExtremal
    {R : Finset ℕ} {n : ℕ} {𝓕 : Finset (Finset ℕ)}
    (hsub : 𝓕 ⊆ squarefreePrefix R n) (hadm : Admissible 𝓕) :
    𝓕.card ≤ squarefreeExtremal R n := by
  rw [squarefreeExtremal]
  exact Finset.le_sup
    (mem_squarefreeAdmissibleFamilies_iff.mpr ⟨hsub, hadm⟩)

/-- The finite maximum defining `squarefreeExtremal` is attained. -/
theorem exists_squarefreeExtremal (R : Finset ℕ) (n : ℕ) :
    ∃ 𝓕 : Finset (Finset ℕ),
      𝓕 ⊆ squarefreePrefix R n ∧ Admissible 𝓕 ∧
        𝓕.card = squarefreeExtremal R n := by
  obtain ⟨𝓕, h𝓕, hsup⟩ :=
    Finset.exists_mem_eq_sup (squarefreeAdmissibleFamilies R n)
      (squarefreeAdmissibleFamilies_nonempty R n) card
  rw [mem_squarefreeAdmissibleFamilies_iff] at h𝓕
  exact ⟨𝓕, h𝓕.1, h𝓕.2, hsup.symm⟩

theorem squarefreeExtremal_le_prefix_card (R : Finset ℕ) (n : ℕ) :
    squarefreeExtremal R n ≤ (squarefreePrefix R n).card := by
  rw [squarefreeExtremal]
  apply Finset.sup_le
  intro 𝓕 h𝓕
  exact card_le_card (mem_squarefreeAdmissibleFamilies_iff.mp h𝓕).1

/-- The finite sum defining `Z_R` has the expected Euler-product form. -/
theorem squarefreeZ_eq_prod (R : Finset ℕ) :
    squarefreeZ R = ∏ p ∈ R, (1 + (p : ℝ)⁻¹) := by
  rw [squarefreeZ]
  calc
    (∑ S ∈ R.powerset, (primeProduct S : ℝ)⁻¹) =
        ∑ S ∈ R.powerset, ∏ p ∈ S, (p : ℝ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro S _hS
          rw [Finset.prod_inv_distrib]
          simp [primeProduct]
    _ = ∏ p ∈ R, ((p : ℝ)⁻¹ + 1) := by
      rw [Finset.prod_add]
      simp
    _ = ∏ p ∈ R, (1 + (p : ℝ)⁻¹) := by
      apply Finset.prod_congr rfl
      intro p _hp
      rw [add_comm]

theorem reciprocalStep_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ reciprocalStep n := by
  rw [reciprocalStep, sub_nonneg]
  apply inv_anti₀
  · exact_mod_cast (show 0 < n from Nat.zero_lt_of_lt hn)
  · exact_mod_cast Nat.le_add_right n 1

/-- Exact telescoping of the interval weights. This is the finite identity
underlying the conversion from the manuscript's interval integral. -/
theorem sum_reciprocalStep_Ico {d D : ℕ} (hdD : d ≤ D) :
    (∑ n ∈ Ico d D, reciprocalStep n) + (D : ℝ)⁻¹ = (d : ℝ)⁻¹ := by
  rw [Finset.sum_Ico_eq_sum_range]
  have htel := Finset.sum_range_sub'
    (fun k : ℕ => ((d + k : ℕ) : ℝ)⁻¹) (D - d)
  have hadd : d + (D - d) = D := Nat.add_sub_of_le hdD
  rw [hadd] at htel
  simpa [reciprocalStep, Nat.add_assoc, add_comm] using
    (add_eq_of_eq_sub' htel)

theorem cast_squarefreePrefix_card (R : Finset ℕ) (n : ℕ) :
    ((squarefreePrefix R n).card : ℝ) =
      ∑ S ∈ R.powerset, if primeProduct S ≤ n then 1 else 0 := by
  classical
  rw [squarefreePrefix, Finset.card_filter, Nat.cast_sum]
  simp

theorem primeProduct_le_total {R S : Finset ℕ} (hR : IsPrimeSupport R)
    (hSR : S ⊆ R) : primeProduct S ≤ primeProduct R := by
  apply Nat.le_of_dvd (primeProduct_pos hR)
  exact Finset.prod_dvd_prod_of_subset S R (fun p => p) hSR

theorem squarefreePrefix_at_total (R : Finset ℕ) (hR : IsPrimeSupport R) :
    squarefreePrefix R (primeProduct R) = R.powerset := by
  ext S
  simp only [mem_squarefreePrefix_iff, mem_powerset]
  constructor
  · exact fun h => h.1
  · intro hSR
    exact ⟨hSR, primeProduct_le_total hR hSR⟩

/-- If admissibility is discarded, the complete prefix-cardinality step
sum is exactly `Z_R`. Thus the elementary bound
`squarefreeExtremal R n ≤ #(squarefreePrefix R n)` integrates with no
loss to `squarefreeI R ≤ squarefreeZ R`. -/
theorem prefix_card_step_sum_eq_Z (R : Finset ℕ) (hR : IsPrimeSupport R) :
    (∑ n ∈ Ico 1 (primeProduct R),
        ((squarefreePrefix R n).card : ℝ) * reciprocalStep n) +
        ((squarefreePrefix R (primeProduct R)).card : ℝ) /
          (primeProduct R : ℝ) =
      squarefreeZ R := by
  classical
  let D := primeProduct R
  rw [squarefreeZ]
  simp_rw [cast_squarefreePrefix_card]
  change
    (∑ n ∈ Ico 1 D,
        (∑ S ∈ R.powerset, if primeProduct S ≤ n then 1 else 0) *
          reciprocalStep n) +
        (∑ S ∈ R.powerset, if primeProduct S ≤ D then 1 else 0) /
          (D : ℝ) =
      ∑ S ∈ R.powerset, (primeProduct S : ℝ)⁻¹
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.sum_div]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  have hSR : S ⊆ R := mem_powerset.mp hS
  have hdD : primeProduct S ≤ D := primeProduct_le_total hR hSR
  rw [if_pos hdD]
  rw [show
      (∑ x ∈ Ico 1 D, if primeProduct S ≤ x then reciprocalStep x else 0) =
        ∑ x ∈ Ico (primeProduct S) D, reciprocalStep x by
    rw [← Finset.sum_filter]
    congr 1
    ext n
    simp only [mem_filter, mem_Ico]
    have hdpos : 0 < primeProduct S :=
      primeProduct_pos (isPrimeSupport_mono hR hSR)
    omega]
  simpa [div_eq_mul_inv] using sum_reciprocalStep_Ico hdD

theorem squarefreeZ_pos (R : Finset ℕ) (hR : IsPrimeSupport R) :
    0 < squarefreeZ R := by
  rw [squarefreeZ_eq_prod]
  apply Finset.prod_pos
  intro p hp
  have hpReal : 0 < (p : ℝ) := by
    exact_mod_cast (hR p hp).pos
  positivity

theorem squarefreeI_nonneg (R : Finset ℕ) : 0 ≤ squarefreeI R := by
  rw [squarefreeI]
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro n hn
    apply mul_nonneg
    · exact Nat.cast_nonneg _
    · exact reciprocalStep_nonneg (mem_Ico.mp hn).1
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem squarefreeI_le_Z (R : Finset ℕ) (hR : IsPrimeSupport R) :
    squarefreeI R ≤ squarefreeZ R := by
  rw [squarefreeI]
  calc
    (∑ n ∈ Ico 1 (primeProduct R),
        (squarefreeExtremal R n : ℝ) * reciprocalStep n) +
        (squarefreeExtremal R (primeProduct R) : ℝ) /
          (primeProduct R : ℝ) ≤
      (∑ n ∈ Ico 1 (primeProduct R),
        ((squarefreePrefix R n).card : ℝ) * reciprocalStep n) +
        ((squarefreePrefix R (primeProduct R)).card : ℝ) /
          (primeProduct R : ℝ) := by
      apply _root_.add_le_add
      · apply Finset.sum_le_sum
        intro n hn
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast squarefreeExtremal_le_prefix_card R n
        · exact reciprocalStep_nonneg (mem_Ico.mp hn).1
      · apply div_le_div_of_nonneg_right
        · exact_mod_cast
            squarefreeExtremal_le_prefix_card R (primeProduct R)
        · exact Nat.cast_nonneg _
    _ = squarefreeZ R := prefix_card_step_sum_eq_Z R hR

/-- The normalized squarefree capacity lies in the unit interval. -/
theorem squarefree_normalized_bounds (R : Finset ℕ)
    (hR : IsPrimeSupport R) :
    0 ≤ squarefreeI R / squarefreeZ R ∧
      squarefreeI R / squarefreeZ R ≤ 1 := by
  have hZpos := squarefreeZ_pos R hR
  exact ⟨div_nonneg (squarefreeI_nonneg R) hZpos.le,
    (div_le_one₀ hZpos).mpr (squarefreeI_le_Z R hR)⟩

end Erdos536
