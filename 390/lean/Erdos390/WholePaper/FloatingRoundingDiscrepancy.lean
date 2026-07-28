import Erdos390.WholePaper.FloatingRoundingCounts

/-!
# Discrepancy after a column becomes light

Once a column has at most `4*d` still-fractional coordinates, every later
change is supported on those coordinates and has magnitude at most one per
coordinate.  This is the final estimate in the paper's floating-rounding
argument.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

def zeroOneColumn {A C : Type*} (inc : C → A → Prop) (c : C) (a : A) : ℝ := by
  classical
  exact if inc c a then 1 else 0

/-- A zero-one column can change by at most the number of its coordinates in
the set on which changes are still permitted. -/
theorem abs_column_discrepancy_le_card
    {A C : Type*} [Fintype A]
    (F : Finset A) (inc : C → A → Prop) (c : C)
    (x X : A → ℝ)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hX : ∀ a, 0 ≤ X a ∧ X a ≤ 1)
    (houtside : ∀ a ∉ F, X a = x a) :
    |∑ a, (X a - x a) * zeroOneColumn inc c a| ≤
      ((columnSupportIn F inc c).card : ℝ) := by
  classical
  let D : Finset A := columnSupportIn F inc c
  have hsum :
      (∑ a, (X a - x a) * zeroOneColumn inc c a) =
        ∑ a ∈ D, (X a - x a) := by
    calc
      (∑ a, (X a - x a) * zeroOneColumn inc c a) =
          ∑ a ∈ (Finset.univ : Finset A),
            ((X a - x a) * zeroOneColumn inc c a) := rfl
      _ = ∑ a ∈ D,
            ((X a - x a) * zeroOneColumn inc c a) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ D)
        intro a _ haD
        by_cases haF : a ∈ F
        · have hnotInc : ¬ inc c a := by
            intro hinc
            exact haD (by
              simpa only [D, mem_columnSupportIn] using And.intro haF hinc)
          simp [zeroOneColumn, hnotInc]
        · simp [zeroOneColumn, houtside a haF]
      _ = ∑ a ∈ D, (X a - x a) := by
        apply Finset.sum_congr rfl
        intro a ha
        have hinc : inc c a := (mem_columnSupportIn.mp (by
          simpa only [D] using ha)).2
        simp [zeroOneColumn, hinc]
  rw [hsum]
  calc
    |∑ a ∈ D, (X a - x a)| ≤ ∑ a ∈ D, |X a - x a| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ D, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_le]
      constructor <;> linarith [hx a, hX a]
    _ = (D.card : ℝ) := by simp
    _ = ((columnSupportIn F inc c).card : ℝ) := by rfl

end

end Erdos390.WholePaper
