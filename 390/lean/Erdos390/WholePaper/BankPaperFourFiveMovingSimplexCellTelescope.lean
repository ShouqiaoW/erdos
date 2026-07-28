import Erdos390.WholePaper.BankPaperFourFiveMovingFaceCellOscillation

/-!
# Product telescope for moving-simplex log-log cells

The one-dimensional cell defect has two exact pieces: an interior
telescoping defect and the defect of the unique crossed strict-face cell.
This file carries each piece separately through the two- and
three-coordinate product telescope.

For an arbitrary conditional defect `D(c)` bounded by `R`, the two
replacement positions cost `2 M R` and the three replacement positions
cost `3 M^2 R`, where `M` bounds the total log-log cell mass.  Applying this
once with the interior defect (`R = delta_A`) and once with the strict-face
defect (`R = delta_A`) gives

* one coordinate: `delta_A + delta_A = 2 delta_A`;
* two coordinates: `2 delta_A M + 2 delta_A M = 4 delta_A M`;
* three coordinates: `3 delta_A M^2 + 3 delta_A M^2 = 6 delta_A M^2`.

Every expression is a finite sum of the paper's literal cells.  In
particular, no convergence or abstract mesh hypothesis is used.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-! ## The existing compact mass budget, in literal-cell form -/

theorem sum_abs_fourFiveLogLogLebesgueCellAtom_eq_logLogIncrement
    {A Y : Nat} (hA : 2 <= A) (hAY : A <= Y) :
    (∑ n ∈ Finset.Ioc A Y,
      |fourFiveLogLogLebesgueCellAtom n|) =
      fourFiveLogLogPrimitive Y - fourFiveLogLogPrimitive A := by
  calc
    (∑ n ∈ Finset.Ioc A Y,
        |fourFiveLogLogLebesgueCellAtom n|) =
        ∑ n ∈ Finset.Ioc A Y,
          |fourFiveAnchoredLogLogCellAtom A n| := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnA := (Finset.mem_Ioc.mp hn).1
      rw [fourFiveAnchoredLogLogCellAtom_eq_lebesgueCell hA,
        if_pos hnA]
    _ = fourFiveLogLogPrimitive Y - fourFiveLogLogPrimitive A :=
      sum_abs_fourFiveAnchoredLogLogCellAtom hA hAY

/-- The untouched literal cell coordinates fit the same compact mass cap
as the reciprocal-prime/product-measure telescope. -/
theorem sum_abs_fourFiveLogLogLebesgueCellAtom_le_compact
    {A Y : Nat} (hA : 2 <= A) (hAY : A <= Y)
    (hspan : fourFiveLogLogPrimitive Y - fourFiveLogLogPrimitive A <=
      Real.log ((24 : Real) / 5)) :
    (∑ n ∈ Finset.Ioc A Y,
      |fourFiveLogLogLebesgueCellAtom n|) <=
      fourFiveCompactReciprocalMass := by
  rw [sum_abs_fourFiveLogLogLebesgueCellAtom_eq_logLogIncrement hA hAY]
  unfold fourFiveCompactReciprocalMass
  linarith

/-! ## Generic finite cell-product ledgers -/

/-- Two positions at which a one-dimensional conditional cell defect can
occur.  The first untouched coordinate is sampled at its right endpoint;
the second is already integrated through its literal cell. -/
def fourFiveLogLogCellTelescopeTwo
    (D : Real -> Real) (A Y y : Nat) : Real :=
  (∑ q ∈ Finset.Ioc A Y,
      fourFiveLogLogLebesgueCellAtom q *
        D (fourFiveLogCoordinate y q)) +
    ∑ p ∈ Finset.Ioc A Y,
      ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
        fourFiveLogLogLebesgueDensity x *
          D (fourFiveRealLogCoordinate y x)

/-- Three positions at which a one-dimensional conditional cell defect can
occur.  Untouched coordinates to the left are integrated, and those to the
right remain right-endpoint samples. -/
def fourFiveLogLogCellTelescopeThree
    (D : Real -> Real) (A Y y : Nat) : Real :=
  (∑ q ∈ Finset.Ioc A Y,
      fourFiveLogLogLebesgueCellAtom q *
        (∑ r ∈ Finset.Ioc A Y,
          fourFiveLogLogLebesgueCellAtom r *
            D (fourFiveLogCoordinate y q +
              fourFiveLogCoordinate y r))) +
    (∑ p ∈ Finset.Ioc A Y,
      ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
        fourFiveLogLogLebesgueDensity x *
          (∑ r ∈ Finset.Ioc A Y,
            fourFiveLogLogLebesgueCellAtom r *
              D (fourFiveRealLogCoordinate y x +
                fourFiveLogCoordinate y r))) +
    ∑ p ∈ Finset.Ioc A Y,
      ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
        fourFiveLogLogLebesgueDensity x *
          (∑ q ∈ Finset.Ioc A Y,
            ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
              fourFiveLogLogLebesgueDensity z *
                D (fourFiveRealLogCoordinate y x +
                  fourFiveRealLogCoordinate y z))

/-- The same three-position ledger ordered from the last sampled coordinate.
Keeping that finite coordinate outer avoids an unnecessary Fubini swap in
the exact three-coordinate hybrid identity. -/
def fourFiveLogLogCellTelescopeThreeRightOrdered
    (D : Real -> Real) (A Y y : Nat) : Real :=
  (∑ r ∈ Finset.Ioc A Y,
      fourFiveLogLogLebesgueCellAtom r *
        fourFiveLogLogCellTelescopeTwo
          (fun c => D (c + fourFiveLogCoordinate y r)) A Y y) +
    ∑ p ∈ Finset.Ioc A Y,
      ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
        fourFiveLogLogLebesgueDensity x *
          (∑ q ∈ Finset.Ioc A Y,
            ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
              fourFiveLogLogLebesgueDensity z *
                D (fourFiveRealLogCoordinate y x +
                  fourFiveRealLogCoordinate y z))

theorem abs_fourFiveLogLogCellTelescopeTwo_le
    {D : Real -> Real} {A Y y : Nat} {M R : Real}
    (hA : 2 <= A) (hAY : A <= Y) (hR : 0 <= R)
    (hmass : (∑ n ∈ Finset.Ioc A Y,
      |fourFiveLogLogLebesgueCellAtom n|) <= M)
    (hD : ∀ c : Real, |D c| <= R) :
    |fourFiveLogLogCellTelescopeTwo D A Y y| <= 2 * M * R := by
  have hmass' : (∑ n ∈ Finset.Ioc A Y,
      fourFiveLogLogLebesgueCellAtom n) <= M := by
    rw [← sum_abs_fourFiveLogLogLebesgueCellAtom_eq_sum hA]
    exact hmass
  have hM : 0 <= M := by
    exact (Finset.sum_nonneg fun n _hn =>
      abs_nonneg (fourFiveLogLogLebesgueCellAtom n)).trans hmass
  have hsample :
      |∑ q ∈ Finset.Ioc A Y,
          fourFiveLogLogLebesgueCellAtom q *
            D (fourFiveLogCoordinate y q)| <= M * R := by
    exact abs_fourFiveFiniteWeightedSum_le_mass_mul
      (Finset.Ioc A Y) fourFiveLogLogLebesgueCellAtom
      (fun q => D (fourFiveLogCoordinate y q))
      hmass (fun q _hq => hD _) hR
  have hintegrated :
      |∑ p ∈ Finset.Ioc A Y,
          ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
            fourFiveLogLogLebesgueDensity x *
              D (fourFiveRealLogCoordinate y x)| <= M * R := by
    exact abs_sum_fourFiveLogLogWeightedCellIntegrals_le_mass_mul
      hA hAY hR hmass' (fun _p _hp x _hx => hD _)
  unfold fourFiveLogLogCellTelescopeTwo
  calc
    |(∑ q ∈ Finset.Ioc A Y,
          fourFiveLogLogLebesgueCellAtom q *
            D (fourFiveLogCoordinate y q)) +
        ∑ p ∈ Finset.Ioc A Y,
          ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
            fourFiveLogLogLebesgueDensity x *
              D (fourFiveRealLogCoordinate y x)| <=
      |∑ q ∈ Finset.Ioc A Y,
          fourFiveLogLogLebesgueCellAtom q *
            D (fourFiveLogCoordinate y q)| +
        |∑ p ∈ Finset.Ioc A Y,
          ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
            fourFiveLogLogLebesgueDensity x *
              D (fourFiveRealLogCoordinate y x)| := abs_add_le _ _
    _ <= M * R + M * R := add_le_add hsample hintegrated
    _ = 2 * M * R := by ring

theorem abs_fourFiveLogLogCellTelescopeThree_le
    {D : Real -> Real} {A Y y : Nat} {M R : Real}
    (hA : 2 <= A) (hAY : A <= Y) (hR : 0 <= R)
    (hmass : (∑ n ∈ Finset.Ioc A Y,
      |fourFiveLogLogLebesgueCellAtom n|) <= M)
    (hD : ∀ c : Real, |D c| <= R) :
    |fourFiveLogLogCellTelescopeThree D A Y y| <= 3 * M ^ 2 * R := by
  have hmass' : (∑ n ∈ Finset.Ioc A Y,
      fourFiveLogLogLebesgueCellAtom n) <= M := by
    rw [← sum_abs_fourFiveLogLogLebesgueCellAtom_eq_sum hA]
    exact hmass
  have hM : 0 <= M := by
    exact (Finset.sum_nonneg fun n _hn =>
      abs_nonneg (fourFiveLogLogLebesgueCellAtom n)).trans hmass
  have hMR : 0 <= M * R := mul_nonneg hM hR
  let T1 : Real :=
    ∑ q ∈ Finset.Ioc A Y,
      fourFiveLogLogLebesgueCellAtom q *
        (∑ r ∈ Finset.Ioc A Y,
          fourFiveLogLogLebesgueCellAtom r *
            D (fourFiveLogCoordinate y q + fourFiveLogCoordinate y r))
  let T2 : Real :=
    ∑ p ∈ Finset.Ioc A Y,
      ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
        fourFiveLogLogLebesgueDensity x *
          (∑ r ∈ Finset.Ioc A Y,
            fourFiveLogLogLebesgueCellAtom r *
              D (fourFiveRealLogCoordinate y x +
                fourFiveLogCoordinate y r))
  let T3 : Real :=
    ∑ p ∈ Finset.Ioc A Y,
      ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
        fourFiveLogLogLebesgueDensity x *
          (∑ q ∈ Finset.Ioc A Y,
            ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
              fourFiveLogLogLebesgueDensity z *
                D (fourFiveRealLogCoordinate y x +
                  fourFiveRealLogCoordinate y z))
  have hsampleInner (q : Nat) :
      |∑ r ∈ Finset.Ioc A Y,
          fourFiveLogLogLebesgueCellAtom r *
            D (fourFiveLogCoordinate y q +
              fourFiveLogCoordinate y r)| <= M * R := by
    exact abs_fourFiveFiniteWeightedSum_le_mass_mul
      (Finset.Ioc A Y) fourFiveLogLogLebesgueCellAtom
      (fun r => D (fourFiveLogCoordinate y q +
        fourFiveLogCoordinate y r))
      hmass (fun r _hr => hD _) hR
  have hfirst : |T1| <= M * (M * R) := by
    dsimp [T1]
    exact abs_fourFiveFiniteWeightedSum_le_mass_mul
      (Finset.Ioc A Y) fourFiveLogLogLebesgueCellAtom
      (fun q => ∑ r ∈ Finset.Ioc A Y,
        fourFiveLogLogLebesgueCellAtom r *
          D (fourFiveLogCoordinate y q + fourFiveLogCoordinate y r))
      hmass (fun q _hq => hsampleInner q) hMR
  have hsecondInner (x : Real) :
      |∑ r ∈ Finset.Ioc A Y,
          fourFiveLogLogLebesgueCellAtom r *
            D (fourFiveRealLogCoordinate y x +
              fourFiveLogCoordinate y r)| <= M * R := by
    exact abs_fourFiveFiniteWeightedSum_le_mass_mul
      (Finset.Ioc A Y) fourFiveLogLogLebesgueCellAtom
      (fun r => D (fourFiveRealLogCoordinate y x +
        fourFiveLogCoordinate y r))
      hmass (fun r _hr => hD _) hR
  have hsecond : |T2| <= M * (M * R) := by
    dsimp [T2]
    exact abs_sum_fourFiveLogLogWeightedCellIntegrals_le_mass_mul
      hA hAY hMR hmass'
        (fun _p _hp x _hx => hsecondInner x)
  have hthirdInner (x : Real) :
      |∑ q ∈ Finset.Ioc A Y,
          ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              D (fourFiveRealLogCoordinate y x +
                fourFiveRealLogCoordinate y z)| <= M * R := by
    exact abs_sum_fourFiveLogLogWeightedCellIntegrals_le_mass_mul
      hA hAY hR hmass'
        (fun _q _hq z _hz => hD _)
  have hthird : |T3| <= M * (M * R) := by
    dsimp [T3]
    exact abs_sum_fourFiveLogLogWeightedCellIntegrals_le_mass_mul
      hA hAY hMR hmass'
        (fun _p _hp x _hx => hthirdInner x)
  unfold fourFiveLogLogCellTelescopeThree
  change |T1 + T2 + T3| <= 3 * M ^ 2 * R
  calc
    |T1 + T2 + T3| <= |T1| + |T2| + |T3| := by
      exact (abs_add_le _ _).trans
        (add_le_add_left (abs_add_le _ _) _)
    _ <= M * (M * R) + M * (M * R) + M * (M * R) := by
      exact add_le_add (add_le_add hfirst hsecond) hthird
    _ = 3 * M ^ 2 * R := by ring

theorem abs_fourFiveLogLogCellTelescopeThreeRightOrdered_le
    {D : Real -> Real} {A Y y : Nat} {M R : Real}
    (hA : 2 <= A) (hAY : A <= Y) (hR : 0 <= R)
    (hmass : (∑ n ∈ Finset.Ioc A Y,
      |fourFiveLogLogLebesgueCellAtom n|) <= M)
    (hD : ∀ c : Real, |D c| <= R) :
    |fourFiveLogLogCellTelescopeThreeRightOrdered D A Y y| <=
      3 * M ^ 2 * R := by
  have hmass' : (∑ n ∈ Finset.Ioc A Y,
      fourFiveLogLogLebesgueCellAtom n) <= M := by
    rw [← sum_abs_fourFiveLogLogLebesgueCellAtom_eq_sum hA]
    exact hmass
  have hM : 0 <= M := by
    exact (Finset.sum_nonneg fun n _hn =>
      abs_nonneg (fourFiveLogLogLebesgueCellAtom n)).trans hmass
  have hMR : 0 <= M * R := mul_nonneg hM hR
  have htwo (r : Nat) :
      |fourFiveLogLogCellTelescopeTwo
        (fun c => D (c + fourFiveLogCoordinate y r)) A Y y| <=
          2 * M * R := by
    exact abs_fourFiveLogLogCellTelescopeTwo_le hA hAY hR hmass
      (fun c => hD _)
  have hfirst :
      |∑ r ∈ Finset.Ioc A Y,
          fourFiveLogLogLebesgueCellAtom r *
            fourFiveLogLogCellTelescopeTwo
              (fun c => D (c + fourFiveLogCoordinate y r)) A Y y| <=
        M * (2 * M * R) := by
    exact abs_fourFiveFiniteWeightedSum_le_mass_mul
      (Finset.Ioc A Y) fourFiveLogLogLebesgueCellAtom
      (fun r => fourFiveLogLogCellTelescopeTwo
        (fun c => D (c + fourFiveLogCoordinate y r)) A Y y)
      hmass (fun r _hr => htwo r)
      (by positivity)
  have hinner (x : Real) :
      |∑ q ∈ Finset.Ioc A Y,
          ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              D (fourFiveRealLogCoordinate y x +
                fourFiveRealLogCoordinate y z)| <= M * R := by
    exact abs_sum_fourFiveLogLogWeightedCellIntegrals_le_mass_mul
      hA hAY hR hmass' (fun _q _hq z _hz => hD _)
  have hthird :
      |∑ p ∈ Finset.Ioc A Y,
          ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
            fourFiveLogLogLebesgueDensity x *
              (∑ q ∈ Finset.Ioc A Y,
                ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                  fourFiveLogLogLebesgueDensity z *
                    D (fourFiveRealLogCoordinate y x +
                      fourFiveRealLogCoordinate y z))| <= M * (M * R) := by
    exact abs_sum_fourFiveLogLogWeightedCellIntegrals_le_mass_mul
      hA hAY hMR hmass' (fun _p _hp x _hx => hinner x)
  unfold fourFiveLogLogCellTelescopeThreeRightOrdered
  calc
    |(∑ r ∈ Finset.Ioc A Y,
          fourFiveLogLogLebesgueCellAtom r *
            fourFiveLogLogCellTelescopeTwo
              (fun c => D (c + fourFiveLogCoordinate y r)) A Y y) +
        ∑ p ∈ Finset.Ioc A Y,
          ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
            fourFiveLogLogLebesgueDensity x *
              (∑ q ∈ Finset.Ioc A Y,
                ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                  fourFiveLogLogLebesgueDensity z *
                    D (fourFiveRealLogCoordinate y x +
                      fourFiveRealLogCoordinate y z))| <=
      |∑ r ∈ Finset.Ioc A Y,
          fourFiveLogLogLebesgueCellAtom r *
            fourFiveLogLogCellTelescopeTwo
              (fun c => D (c + fourFiveLogCoordinate y r)) A Y y| +
        |∑ p ∈ Finset.Ioc A Y,
          ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
            fourFiveLogLogLebesgueDensity x *
              (∑ q ∈ Finset.Ioc A Y,
                ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                  fourFiveLogLogLebesgueDensity z *
                    D (fourFiveRealLogCoordinate y x +
                      fourFiveRealLogCoordinate y z))| := abs_add_le _ _
    _ <= M * (2 * M * R) + M * (M * R) := add_le_add hfirst hthird
    _ = 3 * M ^ 2 * R := by ring

/-! ## Interior and strict-face specializations -/

/-- Interior one-coordinate conditional defect as a function of the sum of
the already fixed logarithmic coordinates. -/
def fourFiveMovingFaceInteriorConditionalDefect
    (A Y y : Nat) (u : Real) (c : Real) : Real :=
  fourFiveMovingFaceInteriorLebesgueCellDefectSum A Y y u c

/-- Unique strict-face conditional defect as a function of the sum of the
already fixed logarithmic coordinates. -/
def fourFiveMovingFaceStrictConditionalDefect
    (A Y y : Nat) (u : Real) (c : Real) : Real :=
  fourFiveMovingFaceStrictLebesgueCellDefect A Y y u c

def fourFiveMovingSimplexCellInteriorTelescopeTwo
    (A Y y : Nat) (u : Real) : Real :=
  fourFiveLogLogCellTelescopeTwo
    (fourFiveMovingFaceInteriorConditionalDefect A Y y u) A Y y

def fourFiveMovingSimplexCellStrictTelescopeTwo
    (A Y y : Nat) (u : Real) : Real :=
  fourFiveLogLogCellTelescopeTwo
    (fourFiveMovingFaceStrictConditionalDefect A Y y u) A Y y

def fourFiveMovingSimplexCellTelescopeTwo
    (A Y y : Nat) (u : Real) : Real :=
  fourFiveMovingSimplexCellInteriorTelescopeTwo A Y y u +
    fourFiveMovingSimplexCellStrictTelescopeTwo A Y y u

def fourFiveMovingSimplexCellInteriorTelescopeThree
    (A Y y : Nat) (u : Real) : Real :=
  fourFiveLogLogCellTelescopeThree
    (fourFiveMovingFaceInteriorConditionalDefect A Y y u) A Y y

def fourFiveMovingSimplexCellStrictTelescopeThree
    (A Y y : Nat) (u : Real) : Real :=
  fourFiveLogLogCellTelescopeThree
    (fourFiveMovingFaceStrictConditionalDefect A Y y u) A Y y

def fourFiveMovingSimplexCellTelescopeThree
    (A Y y : Nat) (u : Real) : Real :=
  fourFiveMovingSimplexCellInteriorTelescopeThree A Y y u +
    fourFiveMovingSimplexCellStrictTelescopeThree A Y y u

theorem abs_fourFiveMovingSimplexCellInteriorTelescopeTwo_le
    {A Y y : Nat} {u M : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hmass : (∑ n ∈ Finset.Ioc A Y,
      |fourFiveLogLogLebesgueCellAtom n|) <= M) :
    |fourFiveMovingSimplexCellInteriorTelescopeTwo A Y y u| <=
      2 * M * fourFiveLogLogCellMeshBound A := by
  unfold fourFiveMovingSimplexCellInteriorTelescopeTwo
    fourFiveMovingFaceInteriorConditionalDefect
  exact abs_fourFiveLogLogCellTelescopeTwo_le (hy.trans hyA) hAY
    (fourFiveLogLogCellMeshBound_pos (hy.trans hyA)).le hmass
    (fun c => abs_fourFiveMovingFaceInteriorLebesgueCellDefectSum_le
      hy hyA hAY)

theorem abs_fourFiveMovingSimplexCellStrictTelescopeTwo_le
    {A Y y : Nat} {u M : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hmass : (∑ n ∈ Finset.Ioc A Y,
      |fourFiveLogLogLebesgueCellAtom n|) <= M) :
    |fourFiveMovingSimplexCellStrictTelescopeTwo A Y y u| <=
      2 * M * fourFiveLogLogCellMeshBound A := by
  unfold fourFiveMovingSimplexCellStrictTelescopeTwo
    fourFiveMovingFaceStrictConditionalDefect
  exact abs_fourFiveLogLogCellTelescopeTwo_le (hy.trans hyA) hAY
    (fourFiveLogLogCellMeshBound_pos (hy.trans hyA)).le hmass
    (fun c => abs_fourFiveMovingFaceStrictLebesgueCellDefect_le hy hyA)

theorem abs_fourFiveMovingSimplexCellTelescopeTwo_le
    {A Y y : Nat} {u M : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hmass : (∑ n ∈ Finset.Ioc A Y,
      |fourFiveLogLogLebesgueCellAtom n|) <= M) :
    |fourFiveMovingSimplexCellTelescopeTwo A Y y u| <=
      4 * fourFiveLogLogCellMeshBound A * M := by
  unfold fourFiveMovingSimplexCellTelescopeTwo
  calc
    |fourFiveMovingSimplexCellInteriorTelescopeTwo A Y y u +
        fourFiveMovingSimplexCellStrictTelescopeTwo A Y y u| <=
      |fourFiveMovingSimplexCellInteriorTelescopeTwo A Y y u| +
        |fourFiveMovingSimplexCellStrictTelescopeTwo A Y y u| := abs_add_le _ _
    _ <= 2 * M * fourFiveLogLogCellMeshBound A +
        2 * M * fourFiveLogLogCellMeshBound A :=
      add_le_add
        (abs_fourFiveMovingSimplexCellInteriorTelescopeTwo_le
          hy hyA hAY hmass)
        (abs_fourFiveMovingSimplexCellStrictTelescopeTwo_le
          hy hyA hAY hmass)
    _ = 4 * fourFiveLogLogCellMeshBound A * M := by ring

theorem abs_fourFiveMovingSimplexCellInteriorTelescopeThree_le
    {A Y y : Nat} {u M : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hmass : (∑ n ∈ Finset.Ioc A Y,
      |fourFiveLogLogLebesgueCellAtom n|) <= M) :
    |fourFiveMovingSimplexCellInteriorTelescopeThree A Y y u| <=
      3 * M ^ 2 * fourFiveLogLogCellMeshBound A := by
  unfold fourFiveMovingSimplexCellInteriorTelescopeThree
    fourFiveMovingFaceInteriorConditionalDefect
  exact abs_fourFiveLogLogCellTelescopeThree_le (hy.trans hyA) hAY
    (fourFiveLogLogCellMeshBound_pos (hy.trans hyA)).le hmass
    (fun c => abs_fourFiveMovingFaceInteriorLebesgueCellDefectSum_le
      hy hyA hAY)

theorem abs_fourFiveMovingSimplexCellStrictTelescopeThree_le
    {A Y y : Nat} {u M : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hmass : (∑ n ∈ Finset.Ioc A Y,
      |fourFiveLogLogLebesgueCellAtom n|) <= M) :
    |fourFiveMovingSimplexCellStrictTelescopeThree A Y y u| <=
      3 * M ^ 2 * fourFiveLogLogCellMeshBound A := by
  unfold fourFiveMovingSimplexCellStrictTelescopeThree
    fourFiveMovingFaceStrictConditionalDefect
  exact abs_fourFiveLogLogCellTelescopeThree_le (hy.trans hyA) hAY
    (fourFiveLogLogCellMeshBound_pos (hy.trans hyA)).le hmass
    (fun c => abs_fourFiveMovingFaceStrictLebesgueCellDefect_le hy hyA)

theorem abs_fourFiveMovingSimplexCellTelescopeThree_le
    {A Y y : Nat} {u M : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hmass : (∑ n ∈ Finset.Ioc A Y,
      |fourFiveLogLogLebesgueCellAtom n|) <= M) :
    |fourFiveMovingSimplexCellTelescopeThree A Y y u| <=
      6 * fourFiveLogLogCellMeshBound A * M ^ 2 := by
  unfold fourFiveMovingSimplexCellTelescopeThree
  calc
    |fourFiveMovingSimplexCellInteriorTelescopeThree A Y y u +
        fourFiveMovingSimplexCellStrictTelescopeThree A Y y u| <=
      |fourFiveMovingSimplexCellInteriorTelescopeThree A Y y u| +
        |fourFiveMovingSimplexCellStrictTelescopeThree A Y y u| :=
      abs_add_le _ _
    _ <= 3 * M ^ 2 * fourFiveLogLogCellMeshBound A +
        3 * M ^ 2 * fourFiveLogLogCellMeshBound A :=
      add_le_add
        (abs_fourFiveMovingSimplexCellInteriorTelescopeThree_le
          hy hyA hAY hmass)
        (abs_fourFiveMovingSimplexCellStrictTelescopeThree_le
          hy hyA hAY hmass)
    _ = 6 * fourFiveLogLogCellMeshBound A * M ^ 2 := by ring

/-! ## Corollaries with the paper's common compact mass cap -/

theorem abs_fourFiveMovingSimplexCellTelescopeTwo_le_compact
    {A Y y : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hspan : fourFiveLogLogPrimitive Y - fourFiveLogLogPrimitive A <=
      Real.log ((24 : Real) / 5)) :
    |fourFiveMovingSimplexCellTelescopeTwo A Y y u| <=
      4 * fourFiveLogLogCellMeshBound A *
        fourFiveCompactReciprocalMass := by
  exact abs_fourFiveMovingSimplexCellTelescopeTwo_le hy hyA hAY
    (sum_abs_fourFiveLogLogLebesgueCellAtom_le_compact
      (hy.trans hyA) hAY hspan)

theorem abs_fourFiveMovingSimplexCellTelescopeThree_le_compact
    {A Y y : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hspan : fourFiveLogLogPrimitive Y - fourFiveLogLogPrimitive A <=
      Real.log ((24 : Real) / 5)) :
    |fourFiveMovingSimplexCellTelescopeThree A Y y u| <=
      6 * fourFiveLogLogCellMeshBound A *
        fourFiveCompactReciprocalMass ^ 2 := by
  exact abs_fourFiveMovingSimplexCellTelescopeThree_le hy hyA hAY
    (sum_abs_fourFiveLogLogLebesgueCellAtom_le_compact
      (hy.trans hyA) hAY hspan)

end Erdos390.WholePaper.BankPaperRealization
