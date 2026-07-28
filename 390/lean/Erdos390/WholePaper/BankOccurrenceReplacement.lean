import Erdos390.WholePaper.Definitions

/-!
# Occurrence-level integral cofactor replacement

Selected occurrences are indexed before their values are inspected, so equal
cofactor values remain distinct occurrences.  The replacement identity is
cross-multiplied in `ℕ`; no individual quotient `new/old` is formed.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Replace precisely the selected cofactor occurrences. -/
def replaceCofactorOccurrences
    {I : Type*} [DecidableEq I]
    (selected : Finset I) (old replacement : I → ℕ) (i : I) : ℕ :=
  if i ∈ selected then replacement i else old i

theorem replaceCofactorOccurrences_of_mem
    {I : Type*} [DecidableEq I]
    {selected : Finset I} {old replacement : I → ℕ}
    {i : I} (hi : i ∈ selected) :
    replaceCofactorOccurrences selected old replacement i = replacement i := by
  simp [replaceCofactorOccurrences, hi]

theorem replaceCofactorOccurrences_of_not_mem
    {I : Type*} [DecidableEq I]
    {selected : Finset I} {old replacement : I → ℕ}
    {i : I} (hi : i ∉ selected) :
    replaceCofactorOccurrences selected old replacement i = old i := by
  simp [replaceCofactorOccurrences, hi]

/-- Exact occurrence-level product identity.  The selected old factors on
the left are the denominators that would occur in informal ratio notation,
but here they cancel by an equality entirely inside `ℕ`. -/
theorem replaceCofactorOccurrences_product_identity
    {I : Type*} [Fintype I] [DecidableEq I]
    (selected : Finset I) (old replacement : I → ℕ) :
    (∏ i : I, replaceCofactorOccurrences selected old replacement i) *
        (∏ i ∈ selected, old i) =
      (∏ i : I, old i) * (∏ i ∈ selected, replacement i) := by
  classical
  calc
    (∏ i : I, replaceCofactorOccurrences selected old replacement i) *
          (∏ i ∈ selected, old i) =
        ∏ i : I, replaceCofactorOccurrences selected old replacement i *
          (if i ∈ selected then old i else 1) := by
            rw [Finset.prod_mul_distrib]
            simp [Finset.prod_ite_mem]
    _ = ∏ i : I, old i *
          (if i ∈ selected then replacement i else 1) := by
            apply Finset.prod_congr rfl
            intro i _hi
            by_cases hi : i ∈ selected <;>
              simp [replaceCofactorOccurrences, hi, Nat.mul_comm]
    _ = (∏ i : I, old i) * (∏ i ∈ selected, replacement i) := by
          rw [Finset.prod_mul_distrib]
          simp [Finset.prod_ite_mem]

/-- The modified cofactor product is an explicit natural number satisfying
the cross-multiplied ratio identity. -/
theorem exists_integral_occurrenceReplacement
    {I : Type*} [Fintype I] [DecidableEq I]
    (selected : Finset I) (old replacement : I → ℕ) :
    ∃ D' : ℕ,
      D' = ∏ i : I, replaceCofactorOccurrences selected old replacement i ∧
      D' * (∏ i ∈ selected, old i) =
        (∏ i : I, old i) * (∏ i ∈ selected, replacement i) := by
  exact ⟨∏ i : I, replaceCofactorOccurrences selected old replacement i,
    rfl, replaceCofactorOccurrences_product_identity selected old replacement⟩

/-- Product of marker--cofactor anchors at the occurrence level. -/
def occurrenceAnchorProduct
    {I : Type*} [Fintype I]
    (marker cofactor : I → ℕ) : ℕ :=
  ∏ i : I, marker i * cofactor i

theorem occurrenceAnchorProduct_eq_marker_mul_cofactorProduct
    {I : Type*} [Fintype I] (marker cofactor : I → ℕ) :
    occurrenceAnchorProduct marker cofactor =
      (∏ i : I, marker i) * (∏ i : I, cofactor i) := by
  exact Finset.prod_mul_distrib

/-- Replacing the selected cofactors changes the anchor product by exactly
the same occurrence-level cross-product. -/
theorem occurrenceAnchorProduct_replacement_identity
    {I : Type*} [Fintype I] [DecidableEq I]
    (selected : Finset I) (marker old replacement : I → ℕ) :
    occurrenceAnchorProduct marker
        (replaceCofactorOccurrences selected old replacement) *
        (∏ i ∈ selected, old i) =
      occurrenceAnchorProduct marker old *
        (∏ i ∈ selected, replacement i) := by
  rw [occurrenceAnchorProduct_eq_marker_mul_cofactorProduct,
    occurrenceAnchorProduct_eq_marker_mul_cofactorProduct]
  have hproduct :=
    replaceCofactorOccurrences_product_identity selected old replacement
  calc
    ((∏ i : I, marker i) *
        ∏ i : I, replaceCofactorOccurrences selected old replacement i) *
          (∏ i ∈ selected, old i) =
        (∏ i : I, marker i) *
          ((∏ i : I, replaceCofactorOccurrences selected old replacement i) *
            (∏ i ∈ selected, old i)) := by ac_rfl
    _ = (∏ i : I, marker i) *
          ((∏ i : I, old i) *
            (∏ i ∈ selected, replacement i)) := by rw [hproduct]
    _ = ((∏ i : I, marker i) * (∏ i : I, old i)) *
          (∏ i ∈ selected, replacement i) := by ac_rfl

end

end Erdos390.WholePaper
