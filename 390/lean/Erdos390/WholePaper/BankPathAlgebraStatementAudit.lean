import Erdos390.WholePaper.BankPathAlgebra

/-!
# Expanded statement audit for the finite bank-path algebra

This audit exposes the actual factorization-coordinate telescope, the four
displayed bottom moves, both orientations of a unit path, and the exact
finite selection realizing every vector in the `β`-box.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example (cores : ℕ → ℕ) (steps : ℕ) :
    (∑ i ∈ Finset.range steps,
      (fun p : ℕ ↦
        ((cores (i + 1)).factorization p : ℤ) -
          ((cores i).factorization p : ℤ))) =
      (fun p : ℕ ↦
        ((cores steps).factorization p : ℤ) -
          ((cores 0).factorization p : ℤ)) := by
  simpa only [ordinaryPathChange, factorMoveChange,
    integerValuationVector, Pi.sub_apply] using
      ordinaryPathChange_telescope cores steps

example (p : ℕ) :
    (coordinateUnit 5 - coordinateUnit p) +
        ((2 : ℤ) • coordinateUnit 2 - coordinateUnit 5) +
        (coordinateUnit 3 - (2 : ℤ) • coordinateUnit 2) +
        (coordinateUnit 2 - coordinateUnit 3) - coordinateUnit 2 =
      -coordinateUnit p := by
  simpa only [bottomFiveToFourChange, bottomFourToThreeChange,
    bottomThreeToTwoChange, bottomTwoToOneChange, add_neg] using
      ordinary_and_four_bottom_moves_eq_neg_unit p

example :
    factorMoveChange 5 4 + factorMoveChange 4 3 +
        factorMoveChange 3 2 + factorMoveChange 2 1 =
      -coordinateUnit 5 := by
  rw [factorMoveChange_five_to_four, factorMoveChange_four_to_three,
    factorMoveChange_three_to_two, factorMoveChange_two_to_one]
  exact fourBottomMovesChange_eq_neg_unit_five

example {p steps : ℕ} (hp : p.Prime) (cores : ℕ → ℕ)
    (hstart : cores 0 = p) (hfinish : cores steps = 5) :
    (∑ i ∈ Finset.range steps,
        factorMoveChange (cores i) (cores (i + 1))) +
          (factorMoveChange 5 4 + factorMoveChange 4 3 +
            factorMoveChange 3 2 + factorMoveChange 2 1) =
      -coordinateUnit p := by
  rw [← ordinaryPathChange, factorMoveChange_five_to_four,
    factorMoveChange_four_to_three, factorMoveChange_three_to_two,
    factorMoveChange_two_to_one, ← fourBottomMovesChange]
  exact fullDownwardPathChange_eq_neg_unit hp cores hstart hfinish

example {p steps : ℕ} (hp : p.Prime) (cores : ℕ → ℕ)
    (hstart : cores 0 = p) (hfinish : cores steps = 5) :
    -(ordinaryPathChange cores steps + fourBottomMovesChange) =
      coordinateUnit p :=
  reverse_fullDownwardPathChange_eq_unit hp cores hstart hfinish

example {I : Type*} [Fintype I] [DecidableEq I]
    (β : I → ℕ) (z : I → ℤ)
    (hz : ∀ p, |z p| ≤ (β p : ℤ)) :
    ∃ positive negative : I → ℕ,
      (∀ p, positive p ≤ β p) ∧
      (∀ p, negative p ≤ β p) ∧
      (∀ p, positive p + negative p ≤ β p) ∧
      (∑ p : I, (
        (positive p : ℤ) • (fun q ↦ if p = q then 1 else 0) +
          (negative p : ℤ) • (-(fun q ↦ if p = q then 1 else 0)))) = z := by
  simpa only [signedUnitPathChange, coordinateUnit] using
    twoSidedUnitPaths_boxUniversal β z hz

end

end Erdos390.WholePaper
