import Erdos390.WholePaper.FloatingRounding

open scoped BigOperators

namespace Erdos390.WholePaper

example {A R C : Type*} [Fintype A] [Fintype R] [Fintype C]
    [DecidableEq A] [DecidableEq R] [DecidableEq C]
    (row : A → R) (inc : C → A → Prop)
    [∀ c a, Decidable (inc c a)]
    (d : ℕ) (x : A → ℝ)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hrowInt : ∀ r, ∃ k : ℤ,
      ∑ a ∈ Finset.univ.filter (fun a ↦ row a = r), x a = (k : ℝ))
    (hsparse : ∀ a,
      (Finset.univ.filter fun c ↦ inc c a).card ≤ d) :
    ∃ X : A → ℝ,
      (∀ a, X a = 0 ∨ X a = 1) ∧
      (∀ r,
        ∑ a ∈ Finset.univ.filter (fun a ↦ row a = r), X a =
          ∑ a ∈ Finset.univ.filter (fun a ↦ row a = r), x a) ∧
      ∀ c,
        |∑ a, (X a - x a) * (if inc c a then (1 : ℝ) else 0)| ≤
          (4 * d : ℝ) := by
  have hrowInt' : ∀ r, ∃ k : ℤ,
      ∑ a ∈ rowSet row r, x a = (k : ℝ) := by
    intro r
    have hrs : rowSet row r =
        Finset.univ.filter (fun a ↦ row a = r) := by
      ext a
      simp only [mem_rowSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hrs]
    exact hrowInt r
  have hsparse' : ∀ a,
      (columnsContaining Finset.univ inc a).card ≤ d := by
    intro a
    have hcs : columnsContaining Finset.univ inc a =
        Finset.univ.filter fun c ↦ inc c a := by
      ext c
      simp only [mem_columnsContaining, Finset.mem_filter, Finset.mem_univ,
        true_and]
    rw [hcs]
    exact hsparse a
  obtain ⟨X, hX, hrows, hcols⟩ :=
    floating_rounding row inc d x hx hrowInt' hsparse'
  refine ⟨X, hX, ?_, ?_⟩
  · intro r
    have hrs : rowSet row r =
        Finset.univ.filter (fun a ↦ row a = r) := by
      ext a
      simp only [mem_rowSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hrs]
    exact hrows r
  · intro c
    have hsum :
        (∑ a, (X a - x a) * (if inc c a then (1 : ℝ) else 0)) =
          ∑ a, (X a - x a) * zeroOneColumn inc c a := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases hinc : inc c a <;> simp [zeroOneColumn, hinc]
    rw [hsum]
    exact hcols c

end Erdos390.WholePaper
