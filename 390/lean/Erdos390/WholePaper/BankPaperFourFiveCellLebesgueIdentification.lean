import Erdos390.WholePaper.BankPaperFourFiveMovingFaceBV
import Erdos390.WholePaper.BankPaperFourFiveFixedSimplexKernel

/-!
# Log-log cells as literal Lebesgue cells

The continuum atom used by the reciprocal-prime BV transfer is not a
formal surrogate: on every integer cell `(m-1,m]` it is exactly the
Lebesgue integral of `dx / (x log x)`.  This file proves that identity and
rewrites the one-, two-, and three-coordinate cell products as products of
literal Lebesgue cell integrals.

The endpoint convention is immaterial for these absolutely continuous
cell measures.  No limiting argument is used in this identification.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-- Density of logarithmic-coordinate Lebesgue measure in the physical
prime variable. -/
def fourFiveLogLogLebesgueDensity (x : Real) : Real :=
  1 / (x * Real.log x)

theorem hasDerivAt_fourFiveLogLogPrimitiveReal
    {x : Real} (hx : 1 < x) :
    HasDerivAt (fun t : Real => Real.log (Real.log t))
      (fourFiveLogLogLebesgueDensity x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hd := (Real.hasDerivAt_log hx0).log hlog0
  convert hd using 1
  unfold fourFiveLogLogLebesgueDensity
  field_simp [hx0, hlog0]

theorem continuousOn_fourFiveLogLogLebesgueDensity
    {a b : Real} (ha : 1 < a) :
    ContinuousOn fourFiveLogLogLebesgueDensity (Set.Icc a b) := by
  intro x hx
  have hx1 : 1 < x := ha.trans_le hx.1
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  unfold fourFiveLogLogLebesgueDensity
  exact ContinuousAt.continuousWithinAt
    (continuousAt_const.div
      (continuousAt_id.mul (Real.continuousAt_log hx0))
      (mul_ne_zero hx0 hlog0))

/-- Exact fundamental-theorem identity on an arbitrary interval above one. -/
theorem integral_fourFiveLogLogLebesgueDensity
    {a b : Real} (ha : 1 < a) (hab : a <= b) :
    (∫ x in a..b, fourFiveLogLogLebesgueDensity x) =
      Real.log (Real.log b) - Real.log (Real.log a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact hasDerivAt_fourFiveLogLogPrimitiveReal (ha.trans_le hx.1)
  · exact (continuousOn_fourFiveLogLogLebesgueDensity ha)
      |>.intervalIntegrable_of_Icc hab

/-- Literal Lebesgue mass of one integer cell. -/
def fourFiveLogLogLebesgueCellAtom (m : Nat) : Real :=
  ∫ x in ((m - 1 : Nat) : Real)..(m : Real),
    fourFiveLogLogLebesgueDensity x

/-- Every log-log difference cell beyond `2` is its exact Lebesgue cell
integral. -/
theorem fourFiveLogLogCell_eq_lebesgueCell
    {m : Nat} (hm : 3 <= m) :
    fourFiveLogLogPrimitive m - fourFiveLogLogPrimitive (m - 1) =
      fourFiveLogLogLebesgueCellAtom m := by
  have hleft : (1 : Real) < ((m - 1 : Nat) : Real) := by
    exact_mod_cast (show 1 < m - 1 by omega)
  have horder : ((m - 1 : Nat) : Real) <= (m : Real) := by
    exact_mod_cast Nat.sub_le m 1
  rw [fourFiveLogLogLebesgueCellAtom,
    integral_fourFiveLogLogLebesgueDensity hleft horder]
  rfl

/-- Anchored continuum atoms are the same literal cell integrals on their
support. -/
theorem fourFiveAnchoredLogLogCellAtom_eq_lebesgueCell
    {A m : Nat} (hA : 2 <= A) :
    fourFiveAnchoredLogLogCellAtom A m =
      if A < m then fourFiveLogLogLebesgueCellAtom m else 0 := by
  unfold fourFiveAnchoredLogLogCellAtom
  by_cases hAm : A < m
  · rw [if_pos hAm, if_pos hAm]
    exact fourFiveLogLogCell_eq_lebesgueCell (by omega)
  · rw [if_neg hAm, if_neg hAm]

/-- One-coordinate weighted cell sum written with literal Lebesgue cells. -/
theorem fourFiveWeightedLogLogCellSum_eq_lebesgueCells
    (f : Nat -> Real) {A Y : Nat} (hA : 2 <= A) :
    fourFiveWeightedLogLogCellSum f A Y =
      ∑ m ∈ Finset.Ioc A Y,
        f m * fourFiveLogLogLebesgueCellAtom m := by
  unfold fourFiveWeightedLogLogCellSum
  apply Finset.sum_congr rfl
  intro m hm
  have hAm := (Finset.mem_Ioc.mp hm).1
  rw [← fourFiveLogLogCell_eq_lebesgueCell (by omega)]

/-- Product of one literal Lebesgue cell measure. -/
def fourFiveLebesgueCellProductOne
    (K : Nat -> Real) (A Y : Nat) : Real :=
  fourFiveFiniteProductOne (Finset.Ioc A Y)
    fourFiveLogLogLebesgueCellAtom K

/-- Product of two literal Lebesgue cell measures. -/
def fourFiveLebesgueCellProductTwo
    (K : Nat -> Nat -> Real) (A Y : Nat) : Real :=
  fourFiveFiniteProductTwo (Finset.Ioc A Y)
    fourFiveLogLogLebesgueCellAtom K

/-- Product of three literal Lebesgue cell measures. -/
def fourFiveLebesgueCellProductThree
    (K : Nat -> Nat -> Nat -> Real) (A Y : Nat) : Real :=
  fourFiveFiniteProductThree (Finset.Ioc A Y)
    fourFiveLogLogLebesgueCellAtom K

/-- Exact one-coordinate cell-to-Lebesgue identification. -/
theorem fourFiveContinuumLogLogProductOne_eq_lebesgueCells
    (K : Nat -> Real) {A Y : Nat} (hA : 2 <= A) :
    fourFiveContinuumLogLogProductOne K A Y =
      fourFiveLebesgueCellProductOne K A Y := by
  unfold fourFiveContinuumLogLogProductOne
    fourFiveLebesgueCellProductOne fourFiveFiniteProductOne
  apply Finset.sum_congr rfl
  intro m hm
  have hAm := (Finset.mem_Ioc.mp hm).1
  rw [fourFiveAnchoredLogLogCellAtom_eq_lebesgueCell hA, if_pos hAm]

/-- Exact two-coordinate cell-to-Lebesgue identification. -/
theorem fourFiveContinuumLogLogProductTwo_eq_lebesgueCells
    (K : Nat -> Nat -> Real) {A Y : Nat} (hA : 2 <= A) :
    fourFiveContinuumLogLogProductTwo K A Y =
      fourFiveLebesgueCellProductTwo K A Y := by
  unfold fourFiveContinuumLogLogProductTwo
    fourFiveLebesgueCellProductTwo fourFiveFiniteProductTwo
  apply Finset.sum_congr rfl
  intro i hi
  have hAi := (Finset.mem_Ioc.mp hi).1
  rw [fourFiveAnchoredLogLogCellAtom_eq_lebesgueCell hA, if_pos hAi]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hAj := (Finset.mem_Ioc.mp hj).1
  rw [fourFiveAnchoredLogLogCellAtom_eq_lebesgueCell hA, if_pos hAj]

/-- Exact three-coordinate cell-to-Lebesgue identification. -/
theorem fourFiveContinuumLogLogProductThree_eq_lebesgueCells
    (K : Nat -> Nat -> Nat -> Real) {A Y : Nat} (hA : 2 <= A) :
    fourFiveContinuumLogLogProductThree K A Y =
      fourFiveLebesgueCellProductThree K A Y := by
  unfold fourFiveContinuumLogLogProductThree
    fourFiveLebesgueCellProductThree fourFiveFiniteProductThree
  apply Finset.sum_congr rfl
  intro i hi
  have hAi := (Finset.mem_Ioc.mp hi).1
  rw [fourFiveAnchoredLogLogCellAtom_eq_lebesgueCell hA, if_pos hAi]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hAj := (Finset.mem_Ioc.mp hj).1
  rw [fourFiveAnchoredLogLogCellAtom_eq_lebesgueCell hA, if_pos hAj]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hAk := (Finset.mem_Ioc.mp hk).1
  rw [fourFiveAnchoredLogLogCellAtom_eq_lebesgueCell hA, if_pos hAk]

end Erdos390.WholePaper.BankPaperRealization
