import Erdos536.Extremal

/-!
# Erdős Problem 536: exact statement

The main assertion is stated both as `f(N) = o(N)` and in the original
positive-density quantifiers.  The proof manuscript establishes the
little-o formulation.
-/

open Filter Finset Nat Set

namespace Erdos536

/-- The main theorem of the manuscript: `f(N) = o(N)`. -/
def MainTheorem : Prop :=
  (fun N : ℕ => (f N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ))

/-- The equivalent positive-density formulation printed on the Erdős
Problems page, with the answer specialized to “yes”. -/
def PositiveDensityFormulation : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → ε * (N : ℝ) ≤ (A.card : ℝ) →
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, IsLcmTriangle a b c

/-- A finite set is safe exactly when it has no explicit witness to the
forbidden configuration. -/
theorem lcmTriangleFree_iff_no_witness (A : Finset ℕ) :
    LcmTriangleFree A ↔
      ¬∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, IsLcmTriangle a b c := by
  constructor
  · intro hfree ⟨a, ha, b, hb, c, hc, htriangle⟩
    exact (hfree ha hb hc) htriangle
  · intro hnone a b c ha hb hc htriangle
    exact hnone ⟨a, ha, b, hb, c, hc, htriangle⟩

end Erdos536
