import Erdos390.WholePaper.PrimePowerColumns

/-!
# Floating rounding for the complete prime-power column family
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Applying the abstract floating-rounding lemma to every prime-power
divisibility column up to `M`, with the logarithmic degree bound proved
internally. -/
theorem floating_rounding_primePowerColumns
    {A R : Type*} [Fintype A] [Fintype R]
    (row : A → R) (value : A → ℕ) (M : ℕ) (x : A → ℝ)
    (hvaluePos : ∀ a, 0 < value a)
    (hvalueLe : ∀ a, value a ≤ M)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hrowInt : ∀ r, ∃ k : ℤ,
      ∑ a ∈ rowSet row r, x a = (k : ℝ)) :
    ∃ X : A → ℝ,
      (∀ a, X a = 0 ∨ X a = 1) ∧
      (∀ r, ∑ a ∈ rowSet row r, X a =
        ∑ a ∈ rowSet row r, x a) ∧
      ∀ q : ↥(primePowerColumns M),
        |∑ a, (X a - x a) *
          zeroOneColumn
            (fun q' a' ↦ primePowerInc M q' (value a')) q a| ≤
          (4 * Nat.log 2 M : ℝ) := by
  let inc : ↥(primePowerColumns M) → A → Prop :=
    fun q a ↦ primePowerInc M q (value a)
  have hsparse : ∀ a,
      (columnsContaining Finset.univ inc a).card ≤ Nat.log 2 M := by
    intro a
    simpa only [inc] using
      primePowerColumns_degree_le_log (hvaluePos a) (hvalueLe a)
  simpa only [inc] using
    floating_rounding row inc (Nat.log 2 M) x hx hrowInt hsparse

end

end Erdos390.WholePaper
