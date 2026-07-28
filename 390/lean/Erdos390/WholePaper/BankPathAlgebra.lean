import Erdos390.WholePaper.Definitions

/-!
# Exact finite algebra of the universal bank paths

This module isolates the algebraic part of the paper's precharged bank.  It
contains no prime-supply, donor, congestion, or asymptotic hypothesis:
ordinary component changes telescope, the four displayed bottom changes
complete a prime-to-five descent to a signed unit vector, reversing a path
reverses that sign, and finitely many copies of both orientations realize
every integral vector in the prescribed box.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Integer-valued prime-coordinate vectors. -/
abbrev BankVector (I : Type*) := I → ℤ

/-- The coordinate unit vector at `p`. -/
def coordinateUnit {I : Type*} [DecidableEq I] (p : I) : BankVector I :=
  fun q ↦ if p = q then 1 else 0

/-- The complete integer valuation vector of a natural number. -/
def integerValuationVector (a : ℕ) : BankVector ℕ :=
  fun p ↦ (a.factorization p : ℤ)

/-- A prime has its coordinate unit valuation vector. -/
theorem integerValuationVector_prime {p : ℕ} (hp : p.Prime) :
    integerValuationVector p = coordinateUnit p := by
  funext q
  rw [integerValuationVector, hp.factorization]
  by_cases hpq : p = q
  · subst q
    simp [coordinateUnit]
  · simp [coordinateUnit, hpq]

/-- A prime power has the expected integer valuation vector. -/
theorem integerValuationVector_prime_pow {p k : ℕ} (hp : p.Prime) :
    integerValuationVector (p ^ k) =
      (k : ℤ) • coordinateUnit p := by
  funext q
  rw [integerValuationVector, hp.factorization_pow]
  by_cases hpq : p = q
  · subst q
    simp [coordinateUnit]
  · simp [coordinateUnit, hpq]

/-- One has zero valuation vector. -/
theorem integerValuationVector_one :
    integerValuationVector 1 = 0 := by
  funext p
  simp [integerValuationVector]

/-- Signed valuation change of a component whose source core is replaced by
its target core. -/
def factorMoveChange (source target : ℕ) : BankVector ℕ :=
  integerValuationVector target - integerValuationVector source

/-- Total signed change along the first `steps` component edges of a core
path. -/
def ordinaryPathChange (cores : ℕ → ℕ) (steps : ℕ) : BankVector ℕ :=
  ∑ i ∈ Finset.range steps, factorMoveChange (cores i) (cores (i + 1))

/-- Ordinary component changes telescope exactly to the endpoint change. -/
theorem ordinaryPathChange_telescope (cores : ℕ → ℕ) (steps : ℕ) :
    ordinaryPathChange cores steps =
      integerValuationVector (cores steps) -
        integerValuationVector (cores 0) := by
  simpa only [ordinaryPathChange, factorMoveChange] using
    Finset.sum_range_sub (fun i ↦ integerValuationVector (cores i)) steps

/-- A prime-to-five ordinary descent changes valuation by `e_5-e_p`. -/
theorem ordinaryPathChange_prime_to_five
    {p steps : ℕ} (hp : p.Prime) (cores : ℕ → ℕ)
    (hstart : cores 0 = p) (hfinish : cores steps = 5) :
    ordinaryPathChange cores steps =
      coordinateUnit 5 - coordinateUnit p := by
  rw [ordinaryPathChange_telescope, hstart, hfinish,
    integerValuationVector_prime hp]
  have hfive : Nat.Prime 5 := by norm_num
  rw [integerValuationVector_prime hfive]

/-- The four literal bottom changes from the paper. -/
def bottomFiveToFourChange : BankVector ℕ :=
  (2 : ℤ) • coordinateUnit 2 - coordinateUnit 5

def bottomFourToThreeChange : BankVector ℕ :=
  coordinateUnit 3 - (2 : ℤ) • coordinateUnit 2

def bottomThreeToTwoChange : BankVector ℕ :=
  coordinateUnit 2 - coordinateUnit 3

def bottomTwoToOneChange : BankVector ℕ :=
  -coordinateUnit 2

/-- Each displayed bottom vector is the valuation change of its literal
integer-core move. -/
theorem factorMoveChange_five_to_four :
    factorMoveChange 5 4 = bottomFiveToFourChange := by
  have htwo : Nat.Prime 2 := by norm_num
  have hfive : Nat.Prime 5 := by norm_num
  rw [factorMoveChange, show 4 = 2 ^ 2 by norm_num,
    integerValuationVector_prime_pow htwo,
    integerValuationVector_prime hfive]
  rfl

theorem factorMoveChange_four_to_three :
    factorMoveChange 4 3 = bottomFourToThreeChange := by
  have htwo : Nat.Prime 2 := by norm_num
  have hthree : Nat.Prime 3 := by norm_num
  rw [factorMoveChange, show 4 = 2 ^ 2 by norm_num,
    integerValuationVector_prime_pow htwo,
    integerValuationVector_prime hthree]
  rfl

theorem factorMoveChange_three_to_two :
    factorMoveChange 3 2 = bottomThreeToTwoChange := by
  have htwo : Nat.Prime 2 := by norm_num
  have hthree : Nat.Prime 3 := by norm_num
  rw [factorMoveChange, integerValuationVector_prime htwo,
    integerValuationVector_prime hthree]
  rfl

theorem factorMoveChange_two_to_one :
    factorMoveChange 2 1 = bottomTwoToOneChange := by
  have htwo : Nat.Prime 2 := by norm_num
  rw [factorMoveChange, integerValuationVector_prime htwo,
    integerValuationVector_one, zero_sub]
  rfl

/-- Total change of the four bottom moves `5→4→3→2→1`. -/
def fourBottomMovesChange : BankVector ℕ :=
  bottomFiveToFourChange + bottomFourToThreeChange +
    bottomThreeToTwoChange + bottomTwoToOneChange

/-- The four bottom moves telescope from `5` to `1`. -/
theorem fourBottomMovesChange_eq_neg_unit_five :
    fourBottomMovesChange = -coordinateUnit 5 := by
  rw [fourBottomMovesChange, bottomFiveToFourChange,
    bottomFourToThreeChange, bottomThreeToTwoChange,
    bottomTwoToOneChange]
  abel

/-- The paper's displayed unit-vector calculation: an ordinary `p→5`
change followed by all four bottom moves is exactly `-e_p`. -/
theorem ordinary_and_four_bottom_moves_eq_neg_unit (p : ℕ) :
    (coordinateUnit 5 - coordinateUnit p) +
        bottomFiveToFourChange + bottomFourToThreeChange +
          bottomThreeToTwoChange + bottomTwoToOneChange =
      -coordinateUnit p := by
  rw [bottomFiveToFourChange, bottomFourToThreeChange,
    bottomThreeToTwoChange, bottomTwoToOneChange]
  abel

/-- A literal ordinary core path ending at five, followed by the bottom
path, has change `-e_p`. -/
theorem fullDownwardPathChange_eq_neg_unit
    {p steps : ℕ} (hp : p.Prime) (cores : ℕ → ℕ)
    (hstart : cores 0 = p) (hfinish : cores steps = 5) :
    ordinaryPathChange cores steps + fourBottomMovesChange =
      -coordinateUnit p := by
  rw [ordinaryPathChange_prime_to_five hp cores hstart hfinish,
    fourBottomMovesChange_eq_neg_unit_five]
  abel

/-- Reversing every component orientation negates the path change and hence
produces the positive unit vector. -/
theorem reverse_fullDownwardPathChange_eq_unit
    {p steps : ℕ} (hp : p.Prime) (cores : ℕ → ℕ)
    (hstart : cores 0 = p) (hfinish : cores steps = 5) :
    -(ordinaryPathChange cores steps + fourBottomMovesChange) =
      coordinateUnit p := by
  rw [fullDownwardPathChange_eq_neg_unit hp cores hstart hfinish]
  simp

/-- The short bottom paths for the exceptional source primes. -/
theorem three_to_one_change_eq_neg_unit_three :
    bottomThreeToTwoChange + bottomTwoToOneChange =
      -coordinateUnit 3 := by
  rw [bottomThreeToTwoChange, bottomTwoToOneChange]
  abel

theorem two_to_one_change_eq_neg_unit_two :
    bottomTwoToOneChange = -coordinateUnit 2 := rfl

/-- Net vector change obtained by using `positive p` positive-unit paths and
`negative p` negative-unit paths at every coordinate. -/
def signedUnitPathChange {I : Type*} [Fintype I] [DecidableEq I]
    (positive negative : I → ℕ) : BankVector I :=
  ∑ p : I, (
    (positive p : ℤ) • coordinateUnit p +
      (negative p : ℤ) • (-coordinateUnit p))

/-- Coordinate evaluation of a finite collection of signed unit paths. -/
theorem signedUnitPathChange_apply {I : Type*} [Fintype I] [DecidableEq I]
    (positive negative : I → ℕ) (q : I) :
    signedUnitPathChange positive negative q =
      (positive q : ℤ) - (negative q : ℤ) := by
  classical
  simp only [signedUnitPathChange, Finset.sum_apply]
  rw [Finset.sum_eq_single q]
  · simp [coordinateUnit, sub_eq_add_neg]
  · intro p _hp hpq
    simp [coordinateUnit, hpq]
  · simp

/-- Positive and negative counts canonically associated with an integral
target coordinate. -/
def positiveUnitPathCount {I : Type*} (z : BankVector I) (p : I) : ℕ :=
  (z p).toNat

def negativeUnitPathCount {I : Type*} (z : BankVector I) (p : I) : ℕ :=
  (-z p).toNat

/-- `β` copies of each signed unit path realize every integral vector in
the coordinate box `|z_p| ≤ β_p`.  The constructed selection in fact uses
only one orientation at each coordinate. -/
theorem twoSidedUnitPaths_boxUniversal
    {I : Type*} [Fintype I] [DecidableEq I]
    (β : I → ℕ) (z : BankVector I)
    (hz : ∀ p, |z p| ≤ (β p : ℤ)) :
    ∃ positive negative : I → ℕ,
      (∀ p, positive p ≤ β p) ∧
      (∀ p, negative p ≤ β p) ∧
      (∀ p, positive p + negative p ≤ β p) ∧
      signedUnitPathChange positive negative = z := by
  refine ⟨positiveUnitPathCount z, negativeUnitPathCount z, ?_, ?_, ?_, ?_⟩
  · intro p
    have hupper : z p ≤ (β p : ℤ) :=
      (le_abs_self (z p)).trans (hz p)
    dsimp only [positiveUnitPathCount]
    omega
  · intro p
    have hupper : -z p ≤ (β p : ℤ) :=
      (neg_le_abs (z p)).trans (hz p)
    dsimp only [negativeUnitPathCount]
    omega
  · intro p
    dsimp only [positiveUnitPathCount, negativeUnitPathCount]
    have habs : (z p).natAbs ≤ β p := by
      have hcast : ((z p).natAbs : ℤ) ≤ (β p : ℤ) := by
        simpa only [Int.natCast_natAbs] using hz p
      exact_mod_cast hcast
    rw [Int.toNat_add_toNat_neg_eq_natAbs]
    exact habs
  · funext p
    rw [signedUnitPathChange_apply]
    dsimp only [positiveUnitPathCount, negativeUnitPathCount]
    exact Int.toNat_sub_toNat_neg (z p)

end

end Erdos390.WholePaper
