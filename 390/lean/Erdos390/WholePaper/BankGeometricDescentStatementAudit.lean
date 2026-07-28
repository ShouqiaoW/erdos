import Erdos390.WholePaper.BankGeometricDescentCore

/-!
# Expanded statement audit for the literal geometric descent

The examples expose the ceiling branch, exact integer cross-products, literal
rational cell inequalities, the two-step cell exit, and all fifteen small
table pairs.
-/

namespace Erdos390.WholePaper

noncomputable section

example (q : ℕ) :
    largeCoreCeil q = (4 * q) ⌈/⌉ 5 := rfl

example (q : ℕ) :
    largeCoreStep q =
      if IsPowerOfTwo ((4 * q) ⌈/⌉ 5) then
        (4 * q) ⌈/⌉ 5 - 1
      else (4 * q) ⌈/⌉ 5 := rfl

example {Q : ℚ} {q : ℕ}
    (hQ : 20 < Q) (hq : 6 ≤ q) (hqNonpower : ¬ IsPowerOfTwo q)
    (hcell : Q < (q : ℚ) ∧ (q : ℚ) ≤ 4 * Q / 3) :
    let b₀ := (4 * q) ⌈/⌉ 5
    let b := if IsPowerOfTwo b₀ then b₀ - 1 else b₀
    ¬ IsPowerOfTwo q ∧
      ¬ IsPowerOfTwo b ∧
      5 ≤ b ∧ b < q ∧
      ((Q < (q : ℚ) ∧ (q : ℚ) ≤ 4 * Q / 3) ∧
        3 * Q / 4 < (b : ℚ)) ∧
      4 * q ≤ 5 * b + 5 ∧
      5 * b < 4 * q + 5 ∧
      20 * b < 17 * q := by
  have hcell' : CoreInGeometricCell Q q := hcell
  simpa only [largeCoreCeil, largeCoreStep, CoreInGeometricCell,
    InGeometricDescentCell] using
      largeCoreStep_spec hQ hq hqNonpower hcell'

example (q : ℕ) :
    let b₀ := (4 * q) ⌈/⌉ 5
    let b := if IsPowerOfTwo b₀ then b₀ - 1 else b₀
    (b : ℚ) ≤ 4 * (q : ℚ) / 5 + 1 := by
  simpa only [largeCoreCeil, largeCoreStep] using
    largeCoreStep_le_four_fifths_add_one q

example {q : ℕ} (hq : 21 ≤ q) :
    let b₀ := (4 * q) ⌈/⌉ 5
    let b := if IsPowerOfTwo b₀ then b₀ - 1 else b₀
    (b : ℚ) < 17 * (q : ℚ) / 20 := by
  simpa only [largeCoreCeil, largeCoreStep] using
    largeCoreStep_lt_seventeen_twentieths hq

example {Q : ℚ} {q : ℕ} (hQ : 20 < Q)
    (hsource : Q < (q : ℚ) ∧ (q : ℚ) ≤ 4 * Q / 3)
    (hfirst : Q < (largeCoreStep q : ℚ) ∧
      (largeCoreStep q : ℚ) ≤ 4 * Q / 3) :
    ((largeCoreStep (largeCoreStep q) : ℕ) : ℚ) < Q := by
  exact two_consecutive_largeCoreSteps_leave_cell hQ hsource hfirst

end

end Erdos390.WholePaper
