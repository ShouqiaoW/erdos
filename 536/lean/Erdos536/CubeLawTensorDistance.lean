import Erdos536.CubeLawTensor

/-!
# Marginal distance for tensor cube laws

On disjoint ambient supports, union identifies a pair of component
supports with a unique support in the union.  Both the tensor marginal
and the reciprocal canonical law factor under this identification.  The
usual product-law `L¹` inequality then bounds the error of an independent
tensor by the sum of its two component errors.
-/

open scoped BigOperators
open Finset

namespace Erdos536

private theorem union_eq_union_iff_of_disjoint
    {A B X Y R S : Finset ℕ}
    (hAR : A ⊆ R) (hBR : B ⊆ S)
    (hXR : X ⊆ R) (hYS : Y ⊆ S)
    (hRS : Disjoint R S) :
    X ∪ Y = A ∪ B ↔ X = A ∧ Y = B := by
  constructor
  · intro h
    have hXA : X = A := by
      apply Finset.Subset.antisymm
      · intro p hpX
        have hp : p ∈ A ∪ B := h ▸ Finset.mem_union_left Y hpX
        rcases Finset.mem_union.mp hp with hpA | hpB
        · exact hpA
        · exact (Finset.disjoint_left.mp hRS (hXR hpX) (hBR hpB)).elim
      · intro p hpA
        have hp : p ∈ X ∪ Y := h.symm ▸ Finset.mem_union_left B hpA
        rcases Finset.mem_union.mp hp with hpX | hpY
        · exact hpX
        · exact (Finset.disjoint_left.mp hRS (hAR hpA) (hYS hpY)).elim
    have hYB : Y = B := by
      apply Finset.Subset.antisymm
      · intro p hpY
        have hp : p ∈ A ∪ B := h ▸ Finset.mem_union_right X hpY
        rcases Finset.mem_union.mp hp with hpA | hpB
        · exact
            (Finset.disjoint_left.mp hRS (hAR hpA) (hYS hpY)).elim
        · exact hpB
      · intro p hpB
        have hp : p ∈ X ∪ Y := h.symm ▸ Finset.mem_union_right A hpB
        rcases Finset.mem_union.mp hp with hpX | hpY
        · exact
            (Finset.disjoint_left.mp hRS (hXR hpX) (hBR hpB)).elim
        · exact hpY
    exact ⟨hXA, hYB⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Summation over the powerset of a disjoint union is iterated
summation over the two component powersets. -/
theorem sum_powerset_union_disjoint
    {R S : Finset ℕ} (hRS : Disjoint R S)
    (F : Finset ℕ → ℝ) :
    (∑ U ∈ (R ∪ S).powerset, F U) =
      ∑ A ∈ R.powerset, ∑ B ∈ S.powerset, F (A ∪ B) := by
  classical
  rw [← Finset.sum_product R.powerset S.powerset
    (fun AB ↦ F (AB.1 ∪ AB.2))]
  symm
  apply Finset.sum_bij
      (fun AB _hAB ↦ AB.1 ∪ AB.2)
  · intro AB hAB
    rw [Finset.mem_product] at hAB
    exact Finset.mem_powerset.mpr
      (Finset.union_subset_union
        (Finset.mem_powerset.mp hAB.1)
        (Finset.mem_powerset.mp hAB.2))
  · intro AB₁ hAB₁ AB₂ hAB₂ heq
    rw [Finset.mem_product] at hAB₁ hAB₂
    have hsplit :=
      (union_eq_union_iff_of_disjoint
        (Finset.mem_powerset.mp hAB₂.1)
        (Finset.mem_powerset.mp hAB₂.2)
        (Finset.mem_powerset.mp hAB₁.1)
        (Finset.mem_powerset.mp hAB₁.2) hRS).mp heq
    exact Prod.ext hsplit.1 hsplit.2
  · intro U hU
    have hUsub := Finset.mem_powerset.mp hU
    let A := U ∩ R
    let B := U ∩ S
    have hA : A ∈ R.powerset :=
      Finset.mem_powerset.mpr Finset.inter_subset_right
    have hB : B ∈ S.powerset :=
      Finset.mem_powerset.mpr Finset.inter_subset_right
    have hdecomp : A ∪ B = U := by
      ext p
      simp only [A, B, Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
      · intro hp
        rcases Finset.mem_union.mp (hUsub hp) with hpR | hpS
        · exact Or.inl ⟨hp, hpR⟩
        · exact Or.inr ⟨hp, hpS⟩
    exact ⟨(A, B), Finset.mem_product.mpr ⟨hA, hB⟩, hdecomp⟩
  · intro AB _hAB
    rfl

theorem primeProduct_union_of_disjoint
    {A B : Finset ℕ} (hAB : Disjoint A B) :
    primeProduct (A ∪ B) = primeProduct A * primeProduct B := by
  exact Finset.prod_union hAB

theorem squarefreeZ_union_of_disjoint
    {R S : Finset ℕ} (hRS : Disjoint R S) :
    squarefreeZ (R ∪ S) = squarefreeZ R * squarefreeZ S := by
  rw [squarefreeZ_eq_prod, squarefreeZ_eq_prod, squarefreeZ_eq_prod]
  exact Finset.prod_union hRS

/-- The reciprocal squarefree probability mass of one support. -/
noncomputable def reciprocalSupportMass
    (R A : Finset ℕ) : ℝ :=
  1 / (squarefreeZ R * (primeProduct A : ℝ))

theorem reciprocalSupportMass_nonneg
    {R A : Finset ℕ} (hR : IsPrimeSupport R) (hAR : A ⊆ R) :
    0 ≤ reciprocalSupportMass R A := by
  rw [reciprocalSupportMass]
  exact div_nonneg zero_le_one
    (mul_nonneg (squarefreeZ_pos R hR).le
      (by exact_mod_cast
        (primeProduct_pos (isPrimeSupport_mono hR hAR)).le))

theorem sum_reciprocalSupportMass
    (R : Finset ℕ) (hR : IsPrimeSupport R) :
    ∑ A ∈ R.powerset, reciprocalSupportMass R A = 1 := by
  have hZne : squarefreeZ R ≠ 0 := (squarefreeZ_pos R hR).ne'
  simp only [reciprocalSupportMass]
  calc
    (∑ A ∈ R.powerset,
        1 / (squarefreeZ R * (primeProduct A : ℝ))) =
        (squarefreeZ R)⁻¹ *
          ∑ A ∈ R.powerset, (primeProduct A : ℝ)⁻¹ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro A _hA
            simp only [one_div, mul_inv_rev]
            rw [mul_comm]
    _ = (squarefreeZ R)⁻¹ * squarefreeZ R := by
          rw [squarefreeZ]
    _ = 1 := inv_mul_cancel₀ hZne

/-- The reciprocal canonical support law factorizes across disjoint
supports. -/
theorem reciprocalSupportMass_union
    {R S A B : Finset ℕ}
    (hRS : Disjoint R S) (hAR : A ⊆ R) (hBS : B ⊆ S) :
    reciprocalSupportMass (R ∪ S) (A ∪ B) =
      reciprocalSupportMass R A * reciprocalSupportMass S B := by
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hpA hpB
    exact Finset.disjoint_left.mp hRS (hAR hpA) (hBS hpB)
  rw [reciprocalSupportMass, reciprocalSupportMass,
    reciprocalSupportMass, squarefreeZ_union_of_disjoint hRS,
    primeProduct_union_of_disjoint hAB]
  push_cast
  simp only [one_div, mul_inv_rev]
  ring

theorem FiniteCubeLaw.wordSupportMass_nonneg
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (ω : Fin H → ZMod 3)
    (A : Finset ℕ) :
    0 ≤ L.wordSupportMass ω A := by
  classical
  rw [FiniteCubeLaw.wordSupportMass]
  apply Finset.sum_nonneg
  intro a ha
  split_ifs
  · exact L.mass_nonneg a ha
  · exact le_rfl

theorem FiniteCubeLaw.sum_wordSupportMass
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (ω : Fin H → ZMod 3) :
    ∑ A ∈ R.powerset, L.wordSupportMass ω A = 1 := by
  classical
  simp only [FiniteCubeLaw.wordSupportMass]
  rw [Finset.sum_comm]
  calc
    (∑ a ∈ L.samples, ∑ A ∈ R.powerset,
        if (L.cube a).wordSupport ω = A then L.mass a else 0) =
        ∑ a ∈ L.samples, L.mass a := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_eq_single ((L.cube a).wordSupport ω)]
          · simp
          · intro A _hA hAne
            simp [hAne.symm]
          · intro hnot
            exact (hnot (Finset.mem_powerset.mpr
              (L.wordSupport_subset a ha ω))).elim
    _ = 1 := L.mass_sum

private theorem FiniteCubeLaw.wordSupportMass_eq_subtype_sum
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (ω : Fin H → ZMod 3)
    (A : Finset ℕ) :
    L.wordSupportMass ω A =
      ∑ a : ↥L.samples,
        if (L.cube a).wordSupport ω = A then L.mass a else 0 := by
  rw [FiniteCubeLaw.wordSupportMass]
  exact (Finset.sum_coe_sort L.samples
    (fun a ↦ if (L.cube a).wordSupport ω = A then L.mass a else 0)).symm

/-- At a union support, the tensor marginal is the product of the two
component marginals. -/
theorem FiniteCubeLaw.tensor_wordSupportMass_union
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {H K : ℕ} {R S A B : Finset ℕ}
    (L : FiniteCubeLaw α H R) (M : FiniteCubeLaw β K S)
    (hRS : Disjoint R S) (hAR : A ⊆ R) (hBS : B ⊆ S)
    (ω : Fin H → ZMod 3) (τ : Fin K → ZMod 3) :
    (L.tensor M hRS).wordSupportMass (Fin.append ω τ) (A ∪ B) =
      L.wordSupportMass ω A * M.wordSupportMass τ B := by
  classical
  rw [L.wordSupportMass_eq_subtype_sum,
    M.wordSupportMass_eq_subtype_sum]
  rw [FiniteCubeLaw.wordSupportMass]
  rw [L.tensor_samples M hRS]
  simp only [L.tensor_mass M hRS]
  simp_rw [L.tensor_wordSupport M hRS]
  simp only [Fin.append_left, Fin.append_right]
  change
    (∑ ab : ↥L.samples × ↥M.samples,
      if ((L.cube ab.1).wordSupport ω ∪
          (M.cube ab.2).wordSupport τ) = A ∪ B then
        L.mass ab.1 * M.mass ab.2
      else 0) =
      (∑ a : ↥L.samples,
        if (L.cube a).wordSupport ω = A then L.mass a else 0) *
      ∑ b : ↥M.samples,
        if (M.cube b).wordSupport τ = B then M.mass b else 0
  rw [Fintype.sum_prod_type]
  calc
    (∑ a : ↥L.samples, ∑ b : ↥M.samples,
        if ((L.cube a).wordSupport ω ∪
            (M.cube b).wordSupport τ) = A ∪ B then
          L.mass a * M.mass b
        else 0) =
        ∑ a : ↥L.samples, ∑ b : ↥M.samples,
          (if (L.cube a).wordSupport ω = A then L.mass a else 0) *
            (if (M.cube b).wordSupport τ = B then M.mass b else 0) := by
          apply Finset.sum_congr rfl
          intro a _ha
          apply Finset.sum_congr rfl
          intro b _hb
          have hsplit :=
            union_eq_union_iff_of_disjoint hAR hBS
              (L.wordSupport_subset a a.property ω)
              (M.wordSupport_subset b b.property τ) hRS
          simp only [hsplit]
          by_cases hLa : (L.cube a).wordSupport ω = A
          · by_cases hMb : (M.cube b).wordSupport τ = B
            · simp [hLa, hMb]
            · simp [hLa, hMb]
          · simp [hLa]
    _ = (∑ a : ↥L.samples,
          if (L.cube a).wordSupport ω = A then L.mass a else 0) *
        ∑ b : ↥M.samples,
          if (M.cube b).wordSupport τ = B then M.mass b else 0 := by
          simp_rw [← Finset.mul_sum]
          rw [← Finset.sum_mul]

/-- `L¹` distance between product laws is at most the sum of the two
component distances. -/
theorem product_l1_distance_le
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (K : Finset κ)
    (μ μ₀ : ι → ℝ) (ν ν₀ : κ → ℝ)
    (hν : ∀ b ∈ K, 0 ≤ ν b)
    (hμ₀ : ∀ a ∈ I, 0 ≤ μ₀ a)
    (hνsum : ∑ b ∈ K, ν b = 1)
    (hμ₀sum : ∑ a ∈ I, μ₀ a = 1) :
    (∑ a ∈ I, ∑ b ∈ K,
        |μ a * ν b - μ₀ a * ν₀ b|) ≤
      (∑ a ∈ I, |μ a - μ₀ a|) +
        ∑ b ∈ K, |ν b - ν₀ b| := by
  calc
    (∑ a ∈ I, ∑ b ∈ K,
        |μ a * ν b - μ₀ a * ν₀ b|) ≤
        ∑ a ∈ I, ∑ b ∈ K,
          (|μ a - μ₀ a| * ν b +
            μ₀ a * |ν b - ν₀ b|) := by
          apply Finset.sum_le_sum
          intro a ha
          apply Finset.sum_le_sum
          intro b hb
          rw [show
              μ a * ν b - μ₀ a * ν₀ b =
                (μ a - μ₀ a) * ν b +
                  μ₀ a * (ν b - ν₀ b) by ring]
          calc
            |(μ a - μ₀ a) * ν b +
                μ₀ a * (ν b - ν₀ b)| ≤
                |(μ a - μ₀ a) * ν b| +
                  |μ₀ a * (ν b - ν₀ b)| := abs_add_le _ _
            _ = |μ a - μ₀ a| * ν b +
                  μ₀ a * |ν b - ν₀ b| := by
                    rw [abs_mul, abs_mul,
                      abs_of_nonneg (hν b hb),
                      abs_of_nonneg (hμ₀ a ha)]
    _ = ∑ a ∈ I,
          (|μ a - μ₀ a| * ∑ b ∈ K, ν b +
            μ₀ a * ∑ b ∈ K, |ν b - ν₀ b|) := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib]
    _ = ∑ a ∈ I,
          (|μ a - μ₀ a| +
            μ₀ a * ∑ b ∈ K, |ν b - ν₀ b|) := by
          rw [hνsum]
          simp
    _ = (∑ a ∈ I, |μ a - μ₀ a|) +
          (∑ a ∈ I, μ₀ a) *
            ∑ b ∈ K, |ν b - ν₀ b| := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = (∑ a ∈ I, |μ a - μ₀ a|) +
          ∑ b ∈ K, |ν b - ν₀ b| := by
          rw [hμ₀sum, one_mul]

/-- Tensoring independent cube laws on disjoint prime supports adds at
most their two reciprocal-support marginal errors. -/
theorem FiniteCubeLaw.tensor_wordSupportDistance_le
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {H K : ℕ} {R S : Finset ℕ}
    (L : FiniteCubeLaw α H R) (M : FiniteCubeLaw β K S)
    (hR : IsPrimeSupport R)
    (hRS : Disjoint R S)
    (ω : Fin H → ZMod 3) (τ : Fin K → ZMod 3) :
    (L.tensor M hRS).wordSupportDistance (Fin.append ω τ) ≤
      L.wordSupportDistance ω + M.wordSupportDistance τ := by
  classical
  rw [FiniteCubeLaw.wordSupportDistance,
    sum_powerset_union_disjoint hRS]
  calc
    (∑ A ∈ R.powerset, ∑ B ∈ S.powerset,
        |(L.tensor M hRS).wordSupportMass
            (Fin.append ω τ) (A ∪ B) -
          1 / (squarefreeZ (R ∪ S) *
            (primeProduct (A ∪ B) : ℝ))|) =
        ∑ A ∈ R.powerset, ∑ B ∈ S.powerset,
          |L.wordSupportMass ω A * M.wordSupportMass τ B -
            reciprocalSupportMass R A *
              reciprocalSupportMass S B| := by
          apply Finset.sum_congr rfl
          intro A hA
          apply Finset.sum_congr rfl
          intro B hB
          rw [L.tensor_wordSupportMass_union M hRS
            (Finset.mem_powerset.mp hA)
            (Finset.mem_powerset.mp hB) ω τ]
          change
            |L.wordSupportMass ω A * M.wordSupportMass τ B -
              reciprocalSupportMass (R ∪ S) (A ∪ B)| =
              |L.wordSupportMass ω A * M.wordSupportMass τ B -
                reciprocalSupportMass R A *
                  reciprocalSupportMass S B|
          rw [reciprocalSupportMass_union hRS
            (Finset.mem_powerset.mp hA)
            (Finset.mem_powerset.mp hB)]
    _ ≤ (∑ A ∈ R.powerset,
          |L.wordSupportMass ω A - reciprocalSupportMass R A|) +
        ∑ B ∈ S.powerset,
          |M.wordSupportMass τ B - reciprocalSupportMass S B| := by
          apply product_l1_distance_le
          · intro B _hB
            exact M.wordSupportMass_nonneg τ B
          · intro A hA
            exact reciprocalSupportMass_nonneg hR
              (Finset.mem_powerset.mp hA)
          · exact M.sum_wordSupportMass τ
          · exact sum_reciprocalSupportMass R hR
    _ = L.wordSupportDistance ω + M.wordSupportDistance τ := by
          rfl

end Erdos536
