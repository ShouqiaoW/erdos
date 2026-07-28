import Erdos390.WholePaper.FloatingRoundingCounts

/-!
# Integer row sums force two fractional coordinates

After integral coordinates are frozen, an active row cannot contain exactly
one fractional coordinate: the whole row sum is an integer and every other
entry is zero or one.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

def rowSet {A R : Type*} [Fintype A]
    (row : A → R) (r : R) : Finset A := by
  classical
  exact Finset.univ.filter fun a ↦ row a = r

@[simp]
theorem mem_rowSet {A R : Type*} [Fintype A]
    {row : A → R} {r : R} {a : A} :
    a ∈ rowSet row r ↔ row a = r := by
  classical
  simp [rowSet]

private theorem eq_zero_or_one_of_not_fractional
    {A : Type*} [Fintype A] {x : A → ℝ} {a : A}
    (ha : a ∉ fractionalSupport x) :
    x a = 0 ∨ x a = 1 := by
  by_contra h
  push_neg at h
  exact ha (mem_fractionalSupport.mpr h)

/-- The exact row-count fact used at every iteration of floating rounding. -/
theorem two_le_card_rowFiber_of_integer_rowSums
    {A R : Type*} [Fintype A] [Fintype R]
    (row : A → R) (x : A → ℝ)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hrowInt : ∀ r, ∃ k : ℤ,
      ∑ a ∈ rowSet row r, x a = (k : ℝ)) :
    ∀ r ∈ activeRows (fractionalSupport x) row,
      2 ≤ (rowFiber (fractionalSupport x) row r).card := by
  classical
  intro r hr
  have hfiberNe : (rowFiber (fractionalSupport x) row r).Nonempty := by
    obtain ⟨a, haF, har⟩ := mem_activeRows.mp hr
    exact ⟨a, mem_rowFiber.mpr ⟨haF, har⟩⟩
  by_contra hnot
  have hcardOne : (rowFiber (fractionalSupport x) row r).card = 1 := by
    have hpos : 0 < (rowFiber (fractionalSupport x) row r).card :=
      Finset.card_pos.mpr hfiberNe
    omega
  obtain ⟨a, haFiber⟩ := Finset.card_eq_one.mp hcardOne
  have haMem : a ∈ rowFiber (fractionalSupport x) row r := by
    rw [haFiber]
    simp
  have haFrac : a ∈ fractionalSupport x := (mem_rowFiber.mp haMem).1
  have harow : row a = r := (mem_rowFiber.mp haMem).2
  have haxpos : 0 < x a :=
    lt_of_le_of_ne (hx a).1 (mem_fractionalSupport.mp haFrac).1.symm
  have haxlt : x a < 1 :=
    lt_of_le_of_ne (hx a).2 (mem_fractionalSupport.mp haFrac).2
  let rest : Finset A := (rowSet row r).erase a
  have hrest01 : ∀ b ∈ rest, x b = 0 ∨ x b = 1 := by
    intro b hb
    have hbrow : row b = r := by
      exact mem_rowSet.mp (Finset.mem_of_mem_erase hb)
    have hbne : b ≠ a := Finset.ne_of_mem_erase hb
    have hbnotFrac : b ∉ fractionalSupport x := by
      intro hbFrac
      have hbFiber : b ∈ rowFiber (fractionalSupport x) row r :=
        mem_rowFiber.mpr ⟨hbFrac, hbrow⟩
      have : b = a := by simpa only [haFiber, Finset.mem_singleton] using hbFiber
      exact hbne this
    exact eq_zero_or_one_of_not_fractional hbnotFrac
  let ones : Finset A := rest.filter fun b ↦ x b = 1
  have hrestSum : ∑ b ∈ rest, x b = (ones.card : ℝ) := by
    calc
      (∑ b ∈ rest, x b) =
          ∑ b ∈ rest, if x b = 1 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        rcases hrest01 b hb with hzero | hone
        · simp [hzero]
        · simp [hone]
      _ = ∑ _b ∈ ones, (1 : ℝ) := by
        dsimp only [ones]
        rw [Finset.sum_filter]
      _ = (ones.card : ℝ) := by simp
  have haRowSet : a ∈ rowSet row r := mem_rowSet.mpr harow
  have hrowSplit :
      ∑ b ∈ rowSet row r, x b = (ones.card : ℝ) + x a := by
    rw [← Finset.sum_erase_add _ _ haRowSet]
    simpa only [rest] using congrArg (fun y : ℝ ↦ y + x a) hrestSum
  obtain ⟨k, hk⟩ := hrowInt r
  have hcast : (((k - (ones.card : ℤ)) : ℤ) : ℝ) = x a := by
    push_cast
    linarith [hk, hrowSplit]
  have hkposR : (0 : ℝ) < ((k - (ones.card : ℤ) : ℤ) : ℝ) := by
    rw [hcast]
    exact haxpos
  have hkltR : ((k - (ones.card : ℤ) : ℤ) : ℝ) < 1 := by
    rw [hcast]
    exact haxlt
  have hkpos : (0 : ℤ) < k - (ones.card : ℤ) := by exact_mod_cast hkposR
  have hklt : k - (ones.card : ℤ) < (1 : ℤ) := by exact_mod_cast hkltR
  omega

end

end Erdos390.WholePaper
