import Erdos390.WholePaper.BankOccurrenceReplacement

/-!
# Expanded statement audit for occurrence-level integral replacement

The selected objects are occurrences indexed by `I`, not distinct numerical
values.  Every identity is an equality of natural-number products; no
per-factor quotient occurs.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example {I : Type*} [DecidableEq I]
    (selected : Finset I) (old replacement : I → ℕ) (i : I) :
    replaceCofactorOccurrences selected old replacement i =
      if i ∈ selected then replacement i else old i := rfl

example {I : Type*} [Fintype I] [DecidableEq I]
    (selected : Finset I) (old replacement : I → ℕ) :
    (∏ i : I, if i ∈ selected then replacement i else old i) *
        (∏ i ∈ selected, old i) =
      (∏ i : I, old i) * (∏ i ∈ selected, replacement i) := by
  simpa only [replaceCofactorOccurrences] using
    replaceCofactorOccurrences_product_identity selected old replacement

example {I : Type*} [Fintype I] [DecidableEq I]
    (selected : Finset I) (old replacement : I → ℕ) :
    ∃ D' : ℕ,
      D' = (∏ i : I, if i ∈ selected then replacement i else old i) ∧
      D' * (∏ i ∈ selected, old i) =
        (∏ i : I, old i) * (∏ i ∈ selected, replacement i) := by
  simpa only [replaceCofactorOccurrences] using
    exists_integral_occurrenceReplacement selected old replacement

example {I : Type*} [Fintype I] (marker cofactor : I → ℕ) :
    (∏ i : I, marker i * cofactor i) =
      (∏ i : I, marker i) * (∏ i : I, cofactor i) := by
  simpa only [occurrenceAnchorProduct] using
    occurrenceAnchorProduct_eq_marker_mul_cofactorProduct marker cofactor

example {I : Type*} [Fintype I] [DecidableEq I]
    (selected : Finset I) (marker old replacement : I → ℕ) :
    (∏ i : I,
        marker i * (if i ∈ selected then replacement i else old i)) *
        (∏ i ∈ selected, old i) =
      (∏ i : I, marker i * old i) *
        (∏ i ∈ selected, replacement i) := by
  simpa only [occurrenceAnchorProduct, replaceCofactorOccurrences] using
    occurrenceAnchorProduct_replacement_identity
      selected marker old replacement

end

end Erdos390.WholePaper
