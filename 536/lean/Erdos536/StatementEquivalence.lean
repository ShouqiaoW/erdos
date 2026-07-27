import Erdos536.Statement

/-!
# Equivalence of the two exact formulations
-/

open Filter Finset Nat

namespace Erdos536

/-- The little-o statement in the manuscript is equivalent to the
positive-density formulation on the Erdős Problems page. -/
theorem mainTheorem_iff_positiveDensity :
    MainTheorem ↔ PositiveDensityFormulation := by
  constructor
  · intro hmain ε hε
    have hbound := hmain.bound (c := ε / 2) (half_pos hε)
    filter_upwards [hbound, eventually_ge_atTop 1] with N hN hNpos
    intro A hsub hcard
    by_cases hwitness :
        ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, IsLcmTriangle a b c
    · exact hwitness
    · exfalso
      have hfree : LcmTriangleFree A :=
        (lcmTriangleFree_iff_no_witness A).mpr hwitness
      have hcardf : A.card ≤ f N := card_le_f hsub hfree
      have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
      have hfbound : (f N : ℝ) ≤ (ε / 2) * (N : ℝ) := by
        have hf0 : (0 : ℝ) ≤ (f N : ℝ) := by positivity
        have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
        simpa only [Real.norm_eq_abs, abs_of_nonneg hf0, abs_of_nonneg hN0] using hN
      have hsmall : (A.card : ℝ) < ε * (N : ℝ) := by
        calc
          (A.card : ℝ) ≤ (f N : ℝ) := by exact_mod_cast hcardf
          _ ≤ (ε / 2) * (N : ℝ) := hfbound
          _ < ε * (N : ℝ) := by nlinarith
      exact (not_le_of_gt hsmall) hcard
  · intro hdensity
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    filter_upwards [hdensity ε hε] with N hN
    have hf0 : (0 : ℝ) ≤ (f N : ℝ) := by positivity
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
    simp only [Real.norm_eq_abs, abs_of_nonneg hf0, abs_of_nonneg hN0]
    by_cases hbound : (f N : ℝ) ≤ ε * (N : ℝ)
    · exact hbound
    · exfalso
      obtain ⟨A, hsub, hfree, hcard⟩ := exists_extremal N
      have hdense : ε * (N : ℝ) ≤ (A.card : ℝ) := by
        rw [hcard]
        exact le_of_lt (lt_of_not_ge hbound)
      obtain ⟨a, ha, b, hb, c, hc, htriangle⟩ := hN A hsub hdense
      exact (hfree ha hb hc) htriangle

end Erdos536
