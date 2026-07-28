import Erdos390.WholePaper.FloatingRoundingStep

/-!
# Counting retained equations in floating rounding

The paper retains active row equations and columns meeting more than `4*d`
currently fractional coordinates.  These elementary double-counts show that
their total number is strictly smaller than the number of fractional
coordinates, which is the hypothesis of `exists_floating_step`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

def activeRows {A R : Type*} [Fintype A] [Fintype R]
    (F : Finset A) (row : A → R) : Finset R := by
  classical
  exact F.image row

def rowFiber {A R : Type*} [Fintype A]
    (F : Finset A) (row : A → R) (r : R) : Finset A := by
  classical
  exact F.filter fun a ↦ row a = r

def columnSupportIn {A C : Type*} [Fintype A]
    (F : Finset A) (inc : C → A → Prop) (c : C) : Finset A := by
  classical
  exact F.filter fun a ↦ inc c a

def columnsContaining {A C : Type*} [Fintype C]
    (H : Finset C) (inc : C → A → Prop) (a : A) : Finset C := by
  classical
  exact H.filter fun c ↦ inc c a

def heavyColumns {A C : Type*} [Fintype A] [Fintype C]
    (F : Finset A) (inc : C → A → Prop) (d : ℕ) : Finset C := by
  classical
  exact Finset.univ.filter fun c ↦
    4 * d < (columnSupportIn F inc c).card

@[simp]
theorem mem_activeRows {A R : Type*} [Fintype A] [Fintype R]
    {F : Finset A} {row : A → R} {r : R} :
    r ∈ activeRows F row ↔ ∃ a ∈ F, row a = r := by
  classical
  simp [activeRows]

@[simp]
theorem mem_rowFiber {A R : Type*} [Fintype A]
    {F : Finset A} {row : A → R} {r : R} {a : A} :
    a ∈ rowFiber F row r ↔ a ∈ F ∧ row a = r := by
  classical
  simp [rowFiber]

@[simp]
theorem mem_columnSupportIn {A C : Type*} [Fintype A]
    {F : Finset A} {inc : C → A → Prop} {c : C} {a : A} :
    a ∈ columnSupportIn F inc c ↔ a ∈ F ∧ inc c a := by
  classical
  simp [columnSupportIn]

@[simp]
theorem mem_columnsContaining {A C : Type*} [Fintype C]
    {H : Finset C} {inc : C → A → Prop} {a : A} {c : C} :
    c ∈ columnsContaining H inc a ↔ c ∈ H ∧ inc c a := by
  classical
  simp [columnsContaining]

@[simp]
theorem mem_heavyColumns {A C : Type*} [Fintype A] [Fintype C]
    {F : Finset A} {inc : C → A → Prop} {d : ℕ} {c : C} :
    c ∈ heavyColumns F inc d ↔
      4 * d < (columnSupportIn F inc c).card := by
  classical
  simp [heavyColumns]

/-- If every active row contains at least two fractional coordinates, active
rows consume at most half of the fractional-coordinate count. -/
theorem two_mul_card_activeRows_le
    {A R : Type*} [Fintype A] [Fintype R]
    (F : Finset A) (row : A → R)
    (htwo : ∀ r ∈ activeRows F row,
      2 ≤ (rowFiber F row r).card) :
    2 * (activeRows F row).card ≤ F.card := by
  classical
  have hmaps : (F : Set A).MapsTo row (activeRows F row) := by
    intro a ha
    exact mem_activeRows.mpr ⟨a, ha, rfl⟩
  have hpartition :
      F.card = ∑ r ∈ activeRows F row, (rowFiber F row r).card := by
    simpa only [rowFiber] using
      (Finset.card_eq_sum_card_fiberwise hmaps)
  rw [hpartition]
  calc
    2 * (activeRows F row).card =
        ∑ _r ∈ activeRows F row, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ r ∈ activeRows F row, (rowFiber F row r).card := by
      exact Finset.sum_le_sum fun r hr ↦ htwo r hr

private theorem incidence_sum_swap
    {A C : Type*} [Fintype A] [Fintype C]
    (F : Finset A) (H : Finset C) (inc : C → A → Prop) :
    (∑ c ∈ H, (columnSupportIn F inc c).card) =
      ∑ a ∈ F, (columnsContaining H inc a).card := by
  classical
  simp only [columnSupportIn, columnsContaining, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [Finset.sum_comm]

/-- With column degree at most `d`, fewer than one quarter of the fractional
coordinates can index columns that contain more than `4*d` of them. -/
theorem four_mul_card_heavyColumns_lt
    {A C : Type*} [Fintype A] [Fintype C]
    (F : Finset A) (inc : C → A → Prop) (d : ℕ)
    (hF : F.Nonempty)
    (hsparse : ∀ a,
      (columnsContaining Finset.univ inc a).card ≤ d) :
    4 * (heavyColumns F inc d).card < F.card := by
  classical
  let H : Finset C := heavyColumns F inc d
  let total : ℕ := ∑ c ∈ H, (columnSupportIn F inc c).card
  have hlower : (4 * d + 1) * H.card ≤ total := by
    calc
      (4 * d + 1) * H.card = ∑ _c ∈ H, (4 * d + 1) := by
        simp [Nat.mul_comm]
      _ ≤ ∑ c ∈ H, (columnSupportIn F inc c).card := by
        apply Finset.sum_le_sum
        intro c hc
        have hc' : 4 * d < (columnSupportIn F inc c).card := by
          simpa only [H, mem_heavyColumns] using hc
        omega
      _ = total := rfl
  have hupper : total ≤ d * F.card := by
    dsimp only [total]
    rw [incidence_sum_swap F H inc]
    calc
      (∑ a ∈ F, (columnsContaining H inc a).card) ≤
          ∑ _a ∈ F, d := by
        apply Finset.sum_le_sum
        intro a _
        exact (Finset.card_le_card (by
          intro c hc
          have hcInc : inc c a := (mem_columnsContaining.mp hc).2
          exact mem_columnsContaining.mpr ⟨Finset.mem_univ c, hcInc⟩)).trans
            (hsparse a)
      _ = d * F.card := by simp [Nat.mul_comm]
  have hFpos : 0 < F.card := Finset.card_pos.mpr hF
  by_cases hd : d = 0
  · have hH : H.card = 0 := by
      subst d
      simp only [Nat.mul_zero, zero_add, one_mul] at hlower hupper
      omega
    simpa only [H, hH, mul_zero] using hFpos
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    by_cases hHzero : H.card = 0
    · simpa only [H, hHzero, mul_zero] using hFpos
    · have hHpos : 0 < H.card := Nat.pos_of_ne_zero hHzero
      by_contra hnot
      have hmle : F.card ≤ 4 * H.card := Nat.le_of_not_gt hnot
      have hpoly : (4 * d + 1) * H.card ≤ 4 * d * H.card := by
        calc
          (4 * d + 1) * H.card ≤ total := hlower
          _ ≤ d * F.card := hupper
          _ ≤ d * (4 * H.card) := Nat.mul_le_mul_left d hmle
          _ = 4 * d * H.card := by ring
      nlinarith

/-- The retained active-row and heavy-column equations together have rank
strictly below the number of fractional coordinates. -/
theorem card_activeRows_add_heavyColumns_lt
    {A R C : Type*} [Fintype A] [Fintype R] [Fintype C]
    (F : Finset A) (row : A → R) (inc : C → A → Prop) (d : ℕ)
    (hF : F.Nonempty)
    (htwo : ∀ r ∈ activeRows F row,
      2 ≤ (rowFiber F row r).card)
    (hsparse : ∀ a,
      (columnsContaining Finset.univ inc a).card ≤ d) :
    (activeRows F row).card + (heavyColumns F inc d).card < F.card := by
  have hrow := two_mul_card_activeRows_le F row htwo
  have hcol := four_mul_card_heavyColumns_lt F inc d hF hsparse
  omega

end

end Erdos390.WholePaper
