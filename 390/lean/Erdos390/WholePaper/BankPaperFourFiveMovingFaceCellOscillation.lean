import Erdos390.WholePaper.BankPaperFourFiveMovingFixedSimplexIdentification
import Erdos390.Full.FriableAsymptotic

/-!
# Log-log cells at the strict moving face

The continuum replacement in the four/five chamber is a finite collection
of the paper's literal cells `(n-1,n]`, with measure `dx/(x log x)`.  This
file proves the right-endpoint quadrature estimate for the one-dimensional
conditional moving-face kernel.

There are two contributions.  On cells whose right endpoint is active, the
reciprocal kernel is increasing and the cell oscillations telescope to at
most one.  There is at most one further cell whose interior is active while
its right endpoint is inactive; that unique strict-face cell costs at most
one.  Thus the total oscillation envelope is at most two.  Since every
paper cell has mass at most

`delta_A = 1 / (A log A)`,

the finite cell quadrature defect is at most `2 delta_A`.  No limiting mesh
or convergence hypothesis occurs.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-! ## The real conditional moving face -/

/-- The reciprocal part of a conditional moving-face kernel, before the
anchor and strict-face cutoffs are imposed. -/
def fourFiveRealMovingFaceReciprocal
    (y : Nat) (u c x : Real) : Real :=
  (u - c - fourFiveRealLogCoordinate y x)⁻¹

/-- The conditional moving-face kernel on the real physical coordinate.
At a natural right endpoint it is the kernel already used by the discrete
BV argument. -/
def fourFiveRealMovingFaceKernel
    (A y : Nat) (u c x : Real) : Real :=
  if (A : Real) < x ∧
      fourFiveRealLogCoordinate y x < u - c - 1 then
    fourFiveRealMovingFaceReciprocal y u c x
  else 0

@[simp] theorem fourFiveRealLogCoordinate_natCast
    (y n : Nat) :
    fourFiveRealLogCoordinate y (n : Real) =
      fourFiveLogCoordinate y n := by
  rfl

theorem fourFiveRealLogCoordinate_mono
    {y : Nat} (hy : 2 <= y) {a b : Real}
    (ha : 0 < a) (hab : a <= b) :
    fourFiveRealLogCoordinate y a <=
      fourFiveRealLogCoordinate y b := by
  have hylog : 0 < Real.log (y : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlog : Real.log a <= Real.log b :=
    Real.log_le_log ha hab
  unfold fourFiveRealLogCoordinate
  exact (div_le_div_iff_of_pos_right hylog).mpr hlog

theorem fourFiveRealMovingFaceReciprocal_mono
    {y : Nat} (hy : 2 <= y) {u c a b : Real}
    (ha : 0 < a) (hab : a <= b)
    (hbface : fourFiveRealLogCoordinate y b < u - c - 1) :
    fourFiveRealMovingFaceReciprocal y u c a <=
      fourFiveRealMovingFaceReciprocal y u c b := by
  have hcoord := fourFiveRealLogCoordinate_mono hy ha hab
  have hdenB : 0 < u - c - fourFiveRealLogCoordinate y b := by
    linarith
  have hdenA : 0 < u - c - fourFiveRealLogCoordinate y a := by
    linarith
  unfold fourFiveRealMovingFaceReciprocal
  exact (inv_le_inv₀ hdenA hdenB).mpr (by linarith)

theorem fourFiveRealMovingFaceReciprocal_nonneg_le_one
    {y : Nat} {u c x : Real}
    (hface : fourFiveRealLogCoordinate y x < u - c - 1) :
    0 <= fourFiveRealMovingFaceReciprocal y u c x ∧
      fourFiveRealMovingFaceReciprocal y u c x <= 1 := by
  have hden : 1 < u - c - fourFiveRealLogCoordinate y x := by
    linarith
  constructor
  · unfold fourFiveRealMovingFaceReciprocal
    exact inv_nonneg.mpr (zero_le_one.trans hden.le)
  · unfold fourFiveRealMovingFaceReciprocal
    simpa only [inv_one] using
      (inv_le_inv₀ (zero_lt_one.trans hden) zero_lt_one).mpr hden.le

theorem fourFiveRealMovingFaceKernel_nonneg_le_one
    {A y : Nat} {u c x : Real} :
    0 <= fourFiveRealMovingFaceKernel A y u c x ∧
      fourFiveRealMovingFaceKernel A y u c x <= 1 := by
  unfold fourFiveRealMovingFaceKernel
  split_ifs with h
  · exact fourFiveRealMovingFaceReciprocal_nonneg_le_one h.2
  · exact ⟨le_rfl, zero_le_one⟩

theorem measurable_fourFiveRealLogCoordinate (y : Nat) :
    Measurable (fourFiveRealLogCoordinate y) := by
  unfold fourFiveRealLogCoordinate
  exact Real.measurable_log.div measurable_const

theorem measurable_fourFiveRealMovingFaceKernel
    (A y : Nat) (u c : Real) :
    Measurable (fourFiveRealMovingFaceKernel A y u c) := by
  have hcoord := measurable_fourFiveRealLogCoordinate y
  have hactive : MeasurableSet
      {x : Real | (A : Real) < x ∧
        fourFiveRealLogCoordinate y x < u - c - 1} :=
    measurableSet_Ioi.inter (hcoord measurableSet_Iio)
  have hrecip : Measurable
      (fourFiveRealMovingFaceReciprocal y u c) := by
    unfold fourFiveRealMovingFaceReciprocal
    exact ((measurable_const.sub measurable_const).sub hcoord).inv
  unfold fourFiveRealMovingFaceKernel
  exact Measurable.ite hactive hrecip measurable_const

theorem measurable_fourFiveLogLogLebesgueDensity :
    Measurable fourFiveLogLogLebesgueDensity := by
  unfold fourFiveLogLogLebesgueDensity
  exact measurable_const.div
    (measurable_id.mul Real.measurable_log)

theorem fourFiveRealMovingFaceKernel_natCast
    {A y n : Nat} {u c : Real} :
    fourFiveRealMovingFaceKernel A y u c (n : Real) =
      fourFiveMovingFaceKernel A y u c n := by
  unfold fourFiveRealMovingFaceKernel fourFiveMovingFaceKernel
    fourFiveRealMovingFaceReciprocal
  by_cases hAn : A < n
  · have hcast : (A : Real) < (n : Real) := by exact_mod_cast hAn
    simp [hAn, hcast]
  · have hcast : ¬(A : Real) < (n : Real) := by exact_mod_cast hAn
    simp [hAn, hcast]

/-! ## The unique cell crossed by the strict face -/

/-- The strict face crosses cell `(n-1,n]` when its lower endpoint is on
the active side and its right endpoint is on the inactive side. -/
def fourFiveMovingFaceStrictCell
    (y n : Nat) (u c : Real) : Prop :=
  fourFiveLogCoordinate y (n - 1) < u - c - 1 ∧
    u - c - 1 <= fourFiveLogCoordinate y n

/-- The only natural index at which a strict-face cell can occur.  If the
integer cutoff lies below the anchor this is the first cell; otherwise it
is the cell immediately following the greatest active integer. -/
def fourFiveMovingFaceStrictCellIndex
    (A Y y : Nat) (u c : Real) : Nat :=
  max (A + 1) (fourFiveMovingFaceCutoff A Y y u c + 1)

theorem fourFiveMovingFaceStrictCell_subsingleton
    {A Y y n m : Nat} {u c : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hn : n ∈ Finset.Ioc A Y) (hm : m ∈ Finset.Ioc A Y)
    (hnface : fourFiveMovingFaceStrictCell y n u c)
    (hmface : fourFiveMovingFaceStrictCell y m u c) :
    n = m := by
  by_contra hne
  wlog hnm : n < m generalizing n m
  · exact this (n := m) (m := n) hm hn hmface hnface
      (fun hmn => hne hmn.symm) (by omega)
  have hnle : n <= m - 1 := by omega
  have hnpos : 0 < (n : Real) := by
    exact_mod_cast (show 0 < n by
      have := (Finset.mem_Ioc.mp hn).1
      omega)
  have hcoord := fourFiveRealLogCoordinate_mono hy hnpos
    (by exact_mod_cast hnle : (n : Real) <= ((m - 1 : Nat) : Real))
  simp only [fourFiveRealLogCoordinate_natCast] at hcoord
  linarith [hnface.2, hmface.1]

/-- A crossed strict-face cell is the displayed distinguished cell.  This
is the explicit form used in the oscillation envelope below. -/
theorem fourFiveMovingFaceStrictCell_eq_index
    {A Y y n : Nat} {u c : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hn : n ∈ Finset.Ioc A Y)
    (hnface : fourFiveMovingFaceStrictCell y n u c) :
    n = fourFiveMovingFaceStrictCellIndex A Y y u c := by
  let R := fourFiveMovingFaceCutoff A Y y u c
  have hnData := Finset.mem_Ioc.mp hn
  have hnInactive : ¬ n <= R := by
    intro hnR
    have hactive :=
      (fourFiveMovingFace_active_iff_le_cutoff hy hyA hn).mpr hnR
    linarith [hactive, hnface.2]
  by_cases hRA : R <= A
  · have hnPred : n - 1 <= A := by
      by_contra hnot
      have hAleft : A < n - 1 := by omega
      have hn1mem : n - 1 ∈ Finset.Ioc A Y :=
        Finset.mem_Ioc.mpr ⟨hAleft, by omega⟩
      have hn1R :=
        (fourFiveMovingFace_active_iff_le_cutoff hy hyA hn1mem).mp
          hnface.1
      omega
    have hnEq : n = A + 1 := by omega
    unfold fourFiveMovingFaceStrictCellIndex
    dsimp [R] at hRA ⊢
    rw [max_eq_left]
    · exact hnEq
    · omega
  · have hAR : A < R := by omega
    have hRn : R < n := by omega
    have hAleft : A < n - 1 := by omega
    have hn1mem : n - 1 ∈ Finset.Ioc A Y :=
      Finset.mem_Ioc.mpr ⟨hAleft, by omega⟩
    have hn1R :=
      (fourFiveMovingFace_active_iff_le_cutoff hy hyA hn1mem).mp
        hnface.1
    have hnEq : n = R + 1 := by omega
    unfold fourFiveMovingFaceStrictCellIndex
    dsimp [R] at hAR hnEq ⊢
    rw [max_eq_right]
    · exact hnEq
    · omega

/-! ## A two-unit finite oscillation envelope -/

/-- Cellwise oscillation envelope.  The first summand is the telescoping
increase on active right endpoints.  The second reserves one unit for the
unique strict-face cell. -/
def fourFiveMovingFaceCellOscillationEnvelope
    (A Y y : Nat) (u c : Real) (n : Nat) : Real :=
  let R := fourFiveMovingFaceCutoff A Y y u c
  let g := fun k : Nat =>
    fourFiveRealMovingFaceReciprocal y u c (k : Real)
  (if A < n ∧ n <= R then g n - g (n - 1) else 0) +
    if n = fourFiveMovingFaceStrictCellIndex A Y y u c then 1 else 0

/-- The telescoping, non-boundary part of the cell envelope. -/
def fourFiveMovingFaceInteriorCellOscillation
    (A Y y : Nat) (u c : Real) (n : Nat) : Real :=
  let R := fourFiveMovingFaceCutoff A Y y u c
  let g := fun k : Nat =>
    fourFiveRealMovingFaceReciprocal y u c (k : Real)
  if A < n ∧ n <= R then g n - g (n - 1) else 0

/-- The isolated one-cell charge at the crossed strict face. -/
def fourFiveMovingFaceStrictCellCharge
    (A Y y : Nat) (u c : Real) (n : Nat) : Real :=
  if n = fourFiveMovingFaceStrictCellIndex A Y y u c then 1 else 0

theorem fourFiveMovingFaceCellOscillationEnvelope_eq_interior_add_strict
    (A Y y : Nat) (u c : Real) (n : Nat) :
    fourFiveMovingFaceCellOscillationEnvelope A Y y u c n =
      fourFiveMovingFaceInteriorCellOscillation A Y y u c n +
        fourFiveMovingFaceStrictCellCharge A Y y u c n := by
  rfl

theorem fourFiveMovingFaceCellOscillationEnvelope_nonneg
    {A Y y n : Nat} {u c : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hn : n ∈ Finset.Ioc A Y) :
    0 <= fourFiveMovingFaceCellOscillationEnvelope A Y y u c n := by
  let R := fourFiveMovingFaceCutoff A Y y u c
  let g := fun k : Nat =>
    fourFiveRealMovingFaceReciprocal y u c (k : Real)
  have hnData := Finset.mem_Ioc.mp hn
  by_cases hnR : n <= R
  · have hface :=
      (fourFiveMovingFace_active_iff_le_cutoff hy hyA hn).mpr hnR
    have hn1pos : 0 < ((n - 1 : Nat) : Real) := by
      exact_mod_cast (show 0 < n - 1 by omega)
    have hmono : g (n - 1) <= g n := by
      exact fourFiveRealMovingFaceReciprocal_mono hy hn1pos
        (by exact_mod_cast Nat.sub_le n 1) (by simpa [g] using hface)
    unfold fourFiveMovingFaceCellOscillationEnvelope
    dsimp [R, g]
    rw [if_pos ⟨hnData.1, hnR⟩]
    split_ifs <;> linarith
  · unfold fourFiveMovingFaceCellOscillationEnvelope
    dsimp [R, g]
    rw [if_neg (fun h => hnR h.2)]
    split_ifs <;> norm_num

theorem sum_fourFiveMovingFaceCellOscillationEnvelope_le_two
    {A Y y : Nat} {u c : Real}
    (hy : 2 <= y) (hyA : y <= A) (_hAY : A <= Y) :
    (∑ n ∈ Finset.Ioc A Y,
      fourFiveMovingFaceCellOscillationEnvelope A Y y u c n) <= 2 := by
  classical
  let R := fourFiveMovingFaceCutoff A Y y u c
  let g := fun k : Nat =>
    fourFiveRealMovingFaceReciprocal y u c (k : Real)
  let J := fourFiveMovingFaceStrictCellIndex A Y y u c
  have hRY : R <= Y := by
    dsimp [R]
    exact Nat.findGreatest_le Y
  have hinteriorRewrite :
      (∑ n ∈ Finset.Ioc A Y,
          if A < n ∧ n <= R then g n - g (n - 1) else 0) =
        ∑ n ∈ Finset.Ioc A R, (g n - g (n - 1)) := by
    rw [← Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    omega
  have hboundary :
      (∑ n ∈ Finset.Ioc A Y, if n = J then (1 : Real) else 0) <= 1 := by
    rw [Finset.sum_ite_eq']
    split_ifs <;> norm_num
  have hinterior :
      (∑ n ∈ Finset.Ioc A R, (g n - g (n - 1))) <= 1 := by
    by_cases hAR : A < R
    · have hRpos : 0 < R := by omega
      have hPR : A < R ∧
          fourFiveLogCoordinate y R < u - c - 1 :=
        Nat.findGreatest_of_ne_zero rfl hRpos.ne'
      have hApos : 0 < (A : Real) := by
        exact_mod_cast (show 0 < A by omega)
      have hcoordAR : fourFiveLogCoordinate y A <=
          fourFiveLogCoordinate y R :=
        fourFiveLogCoordinate_mono hy (by omega) hAR.le
      have hgA : 0 <= g A := by
        apply (fourFiveRealMovingFaceReciprocal_nonneg_le_one
          (y := y) (u := u) (c := c) (x := (A : Real)) ?_).1
        simpa only [fourFiveRealLogCoordinate_natCast] using
          hcoordAR.trans_lt hPR.2
      have hgR : g R <= 1 := by
        apply (fourFiveRealMovingFaceReciprocal_nonneg_le_one
          (y := y) (u := u) (c := c) (x := (R : Real)) ?_).2
        simpa only [fourFiveRealLogCoordinate_natCast] using hPR.2
      calc
        (∑ n ∈ Finset.Ioc A R, (g n - g (n - 1))) =
            ∑ k ∈ Finset.Ico A R, (g (k + 1) - g k) := by
          simpa [Nat.add_sub_cancel] using
            (Erdos390.Full.FriableAsymptotic.sum_Ioc_shift
              (fun n => g n - g (n - 1)) (z := A) (y := R))
        _ = g R - g A := Finset.sum_Ico_sub g hAR.le
        _ <= 1 := by linarith
    · have hRA : R <= A := by omega
      have hempty : Finset.Ioc A R = ∅ := Finset.Ioc_eq_empty_of_le hRA
      rw [hempty]
      norm_num
  unfold fourFiveMovingFaceCellOscillationEnvelope
  dsimp [R, g, J]
  rw [Finset.sum_add_distrib, hinteriorRewrite]
  linarith

theorem sum_fourFiveMovingFaceInteriorCellOscillation_le_one
    {A Y y : Nat} {u c : Real}
    (hy : 2 <= y) (hyA : y <= A) (_hAY : A <= Y) :
    (∑ n ∈ Finset.Ioc A Y,
      fourFiveMovingFaceInteriorCellOscillation A Y y u c n) <= 1 := by
  let R := fourFiveMovingFaceCutoff A Y y u c
  let g := fun k : Nat =>
    fourFiveRealMovingFaceReciprocal y u c (k : Real)
  have hRY : R <= Y := by
    dsimp [R]
    exact Nat.findGreatest_le Y
  have hreindex :
      (∑ n ∈ Finset.Ioc A Y,
          if A < n ∧ n <= R then g n - g (n - 1) else 0) =
        ∑ n ∈ Finset.Ioc A R, (g n - g (n - 1)) := by
    rw [← Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    omega
  unfold fourFiveMovingFaceInteriorCellOscillation
  dsimp [R, g]
  rw [hreindex]
  by_cases hAR : A < R
  · have hRpos : 0 < R := by omega
    have hPR : A < R ∧
        fourFiveLogCoordinate y R < u - c - 1 :=
      Nat.findGreatest_of_ne_zero rfl hRpos.ne'
    have hcoordAR : fourFiveLogCoordinate y A <=
        fourFiveLogCoordinate y R :=
      fourFiveLogCoordinate_mono hy (by omega) hAR.le
    have hgA : 0 <= g A := by
      apply (fourFiveRealMovingFaceReciprocal_nonneg_le_one
        (y := y) (u := u) (c := c) (x := (A : Real)) ?_).1
      simpa only [fourFiveRealLogCoordinate_natCast] using
        hcoordAR.trans_lt hPR.2
    have hgR : g R <= 1 := by
      apply (fourFiveRealMovingFaceReciprocal_nonneg_le_one
        (y := y) (u := u) (c := c) (x := (R : Real)) ?_).2
      simpa only [fourFiveRealLogCoordinate_natCast] using hPR.2
    calc
      (∑ n ∈ Finset.Ioc A R, (g n - g (n - 1))) =
          ∑ k ∈ Finset.Ico A R, (g (k + 1) - g k) := by
        simpa [Nat.add_sub_cancel] using
          (Erdos390.Full.FriableAsymptotic.sum_Ioc_shift
            (fun n => g n - g (n - 1)) (z := A) (y := R))
      _ = g R - g A := Finset.sum_Ico_sub g hAR.le
      _ <= 1 := by linarith
  · have hRA : R <= A := by omega
    have hempty : Finset.Ioc A R = ∅ := Finset.Ioc_eq_empty_of_le hRA
    rw [hempty]
    norm_num

theorem sum_fourFiveMovingFaceStrictCellCharge_le_one
    {A Y y : Nat} {u c : Real} :
    (∑ n ∈ Finset.Ioc A Y,
      fourFiveMovingFaceStrictCellCharge A Y y u c n) <= 1 := by
  classical
  unfold fourFiveMovingFaceStrictCellCharge
  rw [Finset.sum_ite_eq']
  split_ifs <;> norm_num

/-! ## Pointwise right-endpoint control -/

theorem abs_fourFiveMovingFaceKernel_nat_sub_real_le_envelope
    {A Y y n : Nat} {u c x : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hn : n ∈ Finset.Ioc A Y)
    (hx : x ∈ Set.Ioc (((n - 1 : Nat) : Real)) (n : Real)) :
    |fourFiveMovingFaceKernel A y u c n -
        fourFiveRealMovingFaceKernel A y u c x| <=
      fourFiveMovingFaceCellOscillationEnvelope A Y y u c n := by
  let R := fourFiveMovingFaceCutoff A Y y u c
  let g := fun z : Real => fourFiveRealMovingFaceReciprocal y u c z
  have hnData := Finset.mem_Ioc.mp hn
  have hAnReal : (A : Real) < (n : Real) := by
    exact_mod_cast hnData.1
  have hxA : (A : Real) < x := by
    have hAle : A <= n - 1 := by omega
    exact (by exact_mod_cast hAle : (A : Real) <= ((n - 1 : Nat) : Real))
      |>.trans_lt hx.1
  have hn1pos : 0 < ((n - 1 : Nat) : Real) := by
    exact_mod_cast (show 0 < n - 1 by omega)
  have hxpos : 0 < x := hn1pos.trans hx.1
  have hcoordLeft : fourFiveLogCoordinate y (n - 1) <=
      fourFiveRealLogCoordinate y x := by
    have h := fourFiveRealLogCoordinate_mono hy hn1pos hx.1.le
    simpa only [fourFiveRealLogCoordinate_natCast] using h
  have hcoordRight : fourFiveRealLogCoordinate y x <=
      fourFiveLogCoordinate y n := by
    have h := fourFiveRealLogCoordinate_mono hy hxpos hx.2
    simpa only [fourFiveRealLogCoordinate_natCast] using h
  by_cases hnface : fourFiveLogCoordinate y n < u - c - 1
  · have hnR :=
      (fourFiveMovingFace_active_iff_le_cutoff hy hyA hn).mp hnface
    have hxface : fourFiveRealLogCoordinate y x < u - c - 1 :=
      hcoordRight.trans_lt hnface
    have hleftFace : fourFiveLogCoordinate y (n - 1) < u - c - 1 :=
      hcoordLeft.trans_lt hxface
    have hgLeftX : g ((n - 1 : Nat) : Real) <= g x :=
      fourFiveRealMovingFaceReciprocal_mono hy hn1pos hx.1.le hxface
    have hgXRight : g x <= g (n : Real) :=
      fourFiveRealMovingFaceReciprocal_mono hy hxpos hx.2
        (by simpa only [fourFiveRealLogCoordinate_natCast] using hnface)
    have hdiffNonneg : 0 <= g (n : Real) - g x := sub_nonneg.mpr hgXRight
    have hbound :
        |g (n : Real) - g x| <=
          g (n : Real) - g ((n - 1 : Nat) : Real) := by
      rw [abs_of_nonneg hdiffNonneg]
      linarith
    have hnfaceReal :
        fourFiveRealLogCoordinate y (n : Real) < u - c - 1 := by
      simpa only [fourFiveRealLogCoordinate_natCast] using hnface
    rw [← fourFiveRealMovingFaceKernel_natCast
      (A := A) (y := y) (n := n) (u := u) (c := c)]
    simp only [fourFiveRealMovingFaceKernel,
      if_pos (show (A : Real) < (n : Real) ∧
        fourFiveRealLogCoordinate y (n : Real) < u - c - 1 from
          ⟨hAnReal, hnfaceReal⟩),
      if_pos (show (A : Real) < x ∧
        fourFiveRealLogCoordinate y x < u - c - 1 from
          ⟨hxA, hxface⟩)]
    unfold fourFiveMovingFaceCellOscillationEnvelope
    dsimp [R]
    rw [if_pos ⟨hnData.1, hnR⟩]
    have hcharge :
        0 <=
          (if n = fourFiveMovingFaceStrictCellIndex A Y y u c then
            (1 : Real) else 0) := by
      split_ifs <;> norm_num
    exact hbound.trans (le_add_of_nonneg_right hcharge)
  · have hnR : ¬ n <= R :=
      mt (fourFiveMovingFace_active_iff_le_cutoff hy hyA hn).mpr hnface
    by_cases hxface : fourFiveRealLogCoordinate y x < u - c - 1
    · have hstrict : fourFiveMovingFaceStrictCell y n u c := by
        constructor
        · exact hcoordLeft.trans_lt hxface
        · exact le_of_not_gt hnface
      have hnJ := fourFiveMovingFaceStrictCell_eq_index hy hyA hn hstrict
      have hkbound := fourFiveRealMovingFaceReciprocal_nonneg_le_one
        (y := y) (u := u) (c := c) (x := x) hxface
      rw [← fourFiveRealMovingFaceKernel_natCast
        (A := A) (y := y) (n := n) (u := u) (c := c)]
      simp only [fourFiveRealMovingFaceKernel,
        if_neg (fun h : (A : Real) < (n : Real) ∧
            fourFiveRealLogCoordinate y (n : Real) < u - c - 1 =>
          hnface (by
          simpa only [fourFiveRealLogCoordinate_natCast] using h.2)),
        if_pos (show (A : Real) < x ∧
          fourFiveRealLogCoordinate y x < u - c - 1 from
            ⟨hxA, hxface⟩),
        zero_sub, abs_neg]
      unfold fourFiveMovingFaceCellOscillationEnvelope
      dsimp [R]
      rw [if_neg (fun h => hnR h.2), if_pos hnJ]
      simpa [abs_of_nonneg hkbound.1] using hkbound.2
    · rw [← fourFiveRealMovingFaceKernel_natCast
        (A := A) (y := y) (n := n) (u := u) (c := c)]
      simp only [fourFiveRealMovingFaceKernel,
        if_neg (fun h : (A : Real) < (n : Real) ∧
            fourFiveRealLogCoordinate y (n : Real) < u - c - 1 =>
          hnface (by
          simpa only [fourFiveRealLogCoordinate_natCast] using h.2)),
        if_neg (fun h : (A : Real) < x ∧
            fourFiveRealLogCoordinate y x < u - c - 1 =>
          hxface h.2),
        sub_zero, abs_zero]
      exact fourFiveMovingFaceCellOscillationEnvelope_nonneg
        (u := u) (c := c) hy hyA hn

/-! ## The mesh is derived from the literal paper cells -/

/-- Explicit upper bound for every log-log cell beginning at or above `A`. -/
def fourFiveLogLogCellMeshBound (A : Nat) : Real :=
  1 / ((A : Real) * Real.log (A : Real))

theorem fourFiveLogLogCellMeshBound_pos
    {A : Nat} (hA : 2 <= A) :
    0 < fourFiveLogLogCellMeshBound A := by
  have hAreal : 0 < (A : Real) := by positivity
  have hlog : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  unfold fourFiveLogLogCellMeshBound
  positivity

theorem fourFiveLogLogLebesgueDensity_le_meshBound
    {A n : Nat} {x : Real} (hA : 2 <= A) (hAn : A < n)
    (hx : x ∈ Set.Icc (((n - 1 : Nat) : Real)) (n : Real)) :
    0 <= fourFiveLogLogLebesgueDensity x ∧
      fourFiveLogLogLebesgueDensity x <= fourFiveLogLogCellMeshBound A := by
  have hAn1 : A <= n - 1 := by omega
  have hAx : (A : Real) <= x :=
    (by exact_mod_cast hAn1 : (A : Real) <= ((n - 1 : Nat) : Real))
      |>.trans hx.1
  have hApos : 0 < (A : Real) := by positivity
  have hxpos : 0 < x := hApos.trans_le hAx
  have hlogA : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hlogmono : Real.log (A : Real) <= Real.log x :=
    Real.log_le_log hApos hAx
  have hlogx : 0 < Real.log x := hlogA.trans_le hlogmono
  have hdenle :
      (A : Real) * Real.log (A : Real) <= x * Real.log x := by
    exact mul_le_mul hAx hlogmono hlogA.le hxpos.le
  unfold fourFiveLogLogLebesgueDensity fourFiveLogLogCellMeshBound
  constructor
  · positivity
  · exact one_div_le_one_div_of_le (mul_pos hApos hlogA) hdenle

theorem fourFiveLogLogLebesgueCellAtom_le_meshBound
    {A n : Nat} (hA : 2 <= A) (hAn : A < n) :
    fourFiveLogLogLebesgueCellAtom n <= fourFiveLogLogCellMeshBound A := by
  have hab : (((n - 1 : Nat) : Real)) <= (n : Real) := by
    exact_mod_cast Nat.sub_le n 1
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fourFiveLogLogLebesgueDensity)
    (C := fourFiveLogLogCellMeshBound A)
    (a := ((n - 1 : Nat) : Real)) (b := (n : Real)) (fun x hx => by
      rw [Real.norm_eq_abs]
      have hxIcc : x ∈ Set.Icc (((n - 1 : Nat) : Real)) (n : Real) := by
        simpa only [Set.uIcc_of_le hab] using Set.uIoc_subset_uIcc hx
      have hb := fourFiveLogLogLebesgueDensity_le_meshBound hA hAn
        hxIcc
      simpa [abs_of_nonneg hb.1] using hb.2)
  have hcellNonneg : 0 <= fourFiveLogLogLebesgueCellAtom n := by
    rw [← fourFiveLogLogCell_eq_lebesgueCell (by omega)]
    have hanchored := fourFiveAnchoredLogLogCellAtom_nonneg
      (A := A) (n := n) hA
    simpa [fourFiveAnchoredLogLogCellAtom, hAn] using hanchored
  change ‖fourFiveLogLogLebesgueCellAtom n‖ <= _ at hnorm
  rw [Real.norm_eq_abs, abs_of_nonneg hcellNonneg] at hnorm
  simpa [Nat.cast_sub (by omega : 1 <= n), Nat.cast_one,
    abs_of_nonneg (fourFiveLogLogCellMeshBound_pos hA).le] using hnorm

theorem fourFiveLogLogLebesgueCellAtom_nonneg
    {A n : Nat} (hA : 2 <= A) (hAn : A < n) :
    0 <= fourFiveLogLogLebesgueCellAtom n := by
  rw [← fourFiveLogLogCell_eq_lebesgueCell (by omega)]
  have hanchored := fourFiveAnchoredLogLogCellAtom_nonneg
    (A := A) (n := n) hA
  simpa [fourFiveAnchoredLogLogCellAtom, hAn] using hanchored

theorem sum_abs_fourFiveLogLogLebesgueCellAtom_eq_sum
    {A Y : Nat} (hA : 2 <= A) :
    (∑ n ∈ Finset.Ioc A Y, |fourFiveLogLogLebesgueCellAtom n|) =
      ∑ n ∈ Finset.Ioc A Y, fourFiveLogLogLebesgueCellAtom n := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [abs_of_nonneg (fourFiveLogLogLebesgueCellAtom_nonneg hA
    (Finset.mem_Ioc.mp hn).1)]

theorem intervalIntegrable_fourFiveDensity_mul_realMovingFace_cell
    {A Y y n : Nat} {u c : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hn : n ∈ Finset.Ioc A Y) :
    IntervalIntegrable
      (fun x : Real => fourFiveLogLogLebesgueDensity x *
        fourFiveRealMovingFaceKernel A y u c x)
      volume (((n - 1 : Nat) : Real)) (n : Real) := by
  have hA : 2 <= A := hy.trans hyA
  have hab : (((n - 1 : Nat) : Real)) <= (n : Real) := by
    exact_mod_cast Nat.sub_le n 1
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  let mu : Measure Real :=
    volume.restrict
      (Set.Icc (((n - 1 : Nat) : Real)) (n : Real))
  have hdelta0 : 0 <= fourFiveLogLogCellMeshBound A :=
    (fourFiveLogLogCellMeshBound_pos hA).le
  have hconst : Integrable
      (fun _ : Real => fourFiveLogLogCellMeshBound A) mu := by
    exact integrable_const _
  have hmeas : Measurable
      (fun x : Real => fourFiveLogLogLebesgueDensity x *
        fourFiveRealMovingFaceKernel A y u c x) :=
    measurable_fourFiveLogLogLebesgueDensity.mul
      (measurable_fourFiveRealMovingFaceKernel A y u c)
  apply hconst.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Real.norm_eq_abs, abs_mul]
  have hdensity := fourFiveLogLogLebesgueDensity_le_meshBound hA
    (Finset.mem_Ioc.mp hn).1 hx
  have hkernel := fourFiveRealMovingFaceKernel_nonneg_le_one
    (A := A) (y := y) (u := u) (c := c) (x := x)
  rw [abs_of_nonneg hdensity.1, abs_of_nonneg hkernel.1]
  calc
    fourFiveLogLogLebesgueDensity x *
        fourFiveRealMovingFaceKernel A y u c x <=
      fourFiveLogLogCellMeshBound A *
        fourFiveRealMovingFaceKernel A y u c x :=
      mul_le_mul_of_nonneg_right hdensity.2 hkernel.1
    _ <= fourFiveLogLogCellMeshBound A * 1 :=
      mul_le_mul_of_nonneg_left hkernel.2 hdelta0
    _ = fourFiveLogLogCellMeshBound A := mul_one _

/-- A uniformly bounded function can be integrated against one literal
log-log cell at the exact cost `cellMass * bound`.  The function itself need
not be supplied with a separate integrability hypothesis. -/
theorem abs_fourFiveLogLogWeightedCellIntegral_le_atom_mul
    {A n : Nat} {g : Real -> Real} {R : Real}
    (hA : 2 <= A) (hAn : A < n) (_hR : 0 <= R)
    (hg : ∀ x ∈ Set.Ioc (((n - 1 : Nat) : Real)) (n : Real),
      |g x| <= R) :
    |∫ x in (((n - 1 : Nat) : Real))..(n : Real),
        fourFiveLogLogLebesgueDensity x * g x| <=
      fourFiveLogLogLebesgueCellAtom n * R := by
  have hab : (((n - 1 : Nat) : Real)) <= (n : Real) := by
    exact_mod_cast Nat.sub_le n 1
  have hleft : (1 : Real) < ((n - 1 : Nat) : Real) := by
    exact_mod_cast (show 1 < n - 1 by omega)
  have hdensity : IntervalIntegrable fourFiveLogLogLebesgueDensity
      volume (((n - 1 : Nat) : Real)) (n : Real) :=
    (continuousOn_fourFiveLogLogLebesgueDensity hleft)
      |>.intervalIntegrable_of_Icc hab
  have hmajor : IntervalIntegrable
      (fun x : Real => fourFiveLogLogLebesgueDensity x * R)
      volume (((n - 1 : Nat) : Real)) (n : Real) :=
    hdensity.mul_const R
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun x : Real => fourFiveLogLogLebesgueDensity x * g x)
    (g := fun x : Real => fourFiveLogLogLebesgueDensity x * R)
    hab (by
      filter_upwards with x
      intro hx
      rw [Real.norm_eq_abs, abs_mul]
      have hdensityNonneg :=
        (fourFiveLogLogLebesgueDensity_le_meshBound hA hAn
          (Set.Ioc_subset_Icc_self hx)).1
      rw [abs_of_nonneg hdensityNonneg]
      exact mul_le_mul_of_nonneg_left (hg x hx) hdensityNonneg) hmajor
  rw [intervalIntegral.integral_mul_const] at hnorm
  simpa only [fourFiveLogLogLebesgueCellAtom, Real.norm_eq_abs] using hnorm

/-- Finite union of paper cells: an `R`-bounded function costs the total
log-log cell mass times `R`. -/
theorem abs_sum_fourFiveLogLogWeightedCellIntegrals_le_mass_mul
    {A Y : Nat} {g : Real -> Real} {M R : Real}
    (hA : 2 <= A) (_hAY : A <= Y) (hR : 0 <= R)
    (hmass : (∑ n ∈ Finset.Ioc A Y,
      fourFiveLogLogLebesgueCellAtom n) <= M)
    (hg : ∀ n ∈ Finset.Ioc A Y,
      ∀ x ∈ Set.Ioc (((n - 1 : Nat) : Real)) (n : Real),
        |g x| <= R) :
    |∑ n ∈ Finset.Ioc A Y,
        ∫ x in (((n - 1 : Nat) : Real))..(n : Real),
          fourFiveLogLogLebesgueDensity x * g x| <= M * R := by
  have hM : 0 <= M := by
    have hsum0 : 0 <= (∑ n ∈ Finset.Ioc A Y,
        fourFiveLogLogLebesgueCellAtom n) := by
      apply Finset.sum_nonneg
      intro n hn
      rw [← fourFiveLogLogCell_eq_lebesgueCell (by
        have hnA := (Finset.mem_Ioc.mp hn).1
        omega)]
      have hnA := (Finset.mem_Ioc.mp hn).1
      simpa [fourFiveAnchoredLogLogCellAtom, hnA] using
        (fourFiveAnchoredLogLogCellAtom_nonneg
          (A := A) (n := n) hA)
    exact hsum0.trans hmass
  calc
    |∑ n ∈ Finset.Ioc A Y,
        ∫ x in (((n - 1 : Nat) : Real))..(n : Real),
          fourFiveLogLogLebesgueDensity x * g x| <=
      ∑ n ∈ Finset.Ioc A Y,
        |∫ x in (((n - 1 : Nat) : Real))..(n : Real),
          fourFiveLogLogLebesgueDensity x * g x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ n ∈ Finset.Ioc A Y,
        fourFiveLogLogLebesgueCellAtom n * R := by
      apply Finset.sum_le_sum
      intro n hn
      exact abs_fourFiveLogLogWeightedCellIntegral_le_atom_mul hA
        (Finset.mem_Ioc.mp hn).1 hR (hg n hn)
    _ = (∑ n ∈ Finset.Ioc A Y,
        fourFiveLogLogLebesgueCellAtom n) * R := by
      rw [Finset.sum_mul]
    _ <= M * R := mul_le_mul_of_nonneg_right hmass hR

/-! ## The finite one-dimensional quadrature defect -/

/-- The literal signed defect on one paper cell. -/
def fourFiveMovingFaceLebesgueCellDefect
    (A _Y y : Nat) (u c : Real) (n : Nat) : Real :=
  ∫ x in (((n - 1 : Nat) : Real))..(n : Real),
    fourFiveLogLogLebesgueDensity x *
      (fourFiveMovingFaceKernel A y u c n -
        fourFiveRealMovingFaceKernel A y u c x)

/-- On every paper cell, the signed integral above is exactly the
right-endpoint mass times the sampled kernel minus the varying real-kernel
integral. -/
theorem fourFiveLebesgueCell_sample_sub_real_eq_defect
    {A Y y n : Nat} {u c : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hn : n ∈ Finset.Ioc A Y) :
    fourFiveLogLogLebesgueCellAtom n *
          fourFiveMovingFaceKernel A y u c n -
        (∫ x in (((n - 1 : Nat) : Real))..(n : Real),
          fourFiveLogLogLebesgueDensity x *
            fourFiveRealMovingFaceKernel A y u c x) =
      fourFiveMovingFaceLebesgueCellDefect A Y y u c n := by
  have hleft : (1 : Real) < ((n - 1 : Nat) : Real) := by
    exact_mod_cast (show 1 < n - 1 by
      have hnA := (Finset.mem_Ioc.mp hn).1
      omega)
  have hab : (((n - 1 : Nat) : Real)) <= (n : Real) := by
    exact_mod_cast Nat.sub_le n 1
  have hdensity : IntervalIntegrable fourFiveLogLogLebesgueDensity
      volume (((n - 1 : Nat) : Real)) (n : Real) :=
    (continuousOn_fourFiveLogLogLebesgueDensity hleft)
      |>.intervalIntegrable_of_Icc hab
  have hsample : IntervalIntegrable
      (fun x : Real => fourFiveLogLogLebesgueDensity x *
        fourFiveMovingFaceKernel A y u c n)
      volume (((n - 1 : Nat) : Real)) (n : Real) :=
    hdensity.mul_const _
  have hreal :=
    intervalIntegrable_fourFiveDensity_mul_realMovingFace_cell
      (u := u) (c := c) hy hyA hn
  unfold fourFiveLogLogLebesgueCellAtom
    fourFiveMovingFaceLebesgueCellDefect
  rw [← intervalIntegral.integral_mul_const,
    ← intervalIntegral.integral_sub hsample hreal]
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

theorem abs_fourFiveMovingFaceLebesgueCellDefect_le
    {A Y y n : Nat} {u c : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hn : n ∈ Finset.Ioc A Y) :
    |fourFiveMovingFaceLebesgueCellDefect A Y y u c n| <=
      fourFiveLogLogCellMeshBound A *
        fourFiveMovingFaceCellOscillationEnvelope A Y y u c n := by
  have hA : 2 <= A := hy.trans hyA
  have henv0 := fourFiveMovingFaceCellOscillationEnvelope_nonneg
    (u := u) (c := c) hy hyA hn
  have hab : (((n - 1 : Nat) : Real)) <= (n : Real) := by
    exact_mod_cast Nat.sub_le n 1
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : Real => fourFiveLogLogLebesgueDensity x *
      (fourFiveMovingFaceKernel A y u c n -
        fourFiveRealMovingFaceKernel A y u c x))
    (C := fourFiveLogLogCellMeshBound A *
      fourFiveMovingFaceCellOscillationEnvelope A Y y u c n)
    (a := ((n - 1 : Nat) : Real)) (b := (n : Real)) (fun x hx => by
      rw [Real.norm_eq_abs, abs_mul]
      have hxIoc : x ∈ Set.Ioc (((n - 1 : Nat) : Real)) (n : Real) := by
        simpa only [Set.uIoc_of_le hab] using hx
      have hxIcc : x ∈ Set.Icc (((n - 1 : Nat) : Real)) (n : Real) := by
        simpa only [Set.uIcc_of_le hab] using Set.uIoc_subset_uIcc hx
      have hdensity := fourFiveLogLogLebesgueDensity_le_meshBound hA
        (Finset.mem_Ioc.mp hn).1 hxIcc
      have hkernel := abs_fourFiveMovingFaceKernel_nat_sub_real_le_envelope
        (u := u) (c := c) hy hyA hn hxIoc
      rw [abs_of_nonneg hdensity.1]
      exact mul_le_mul hdensity.2 hkernel (abs_nonneg _)
        (fourFiveLogLogCellMeshBound_pos hA).le)
  have hnOne : 1 <= n := by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  have hcellLength :
      |(n : Real) - ((n - 1 : Nat) : Real)| = 1 := by
    rw [Nat.cast_sub hnOne, Nat.cast_one]
    have hnCast : (1 : Real) <= (n : Real) := by
      exact_mod_cast hnOne
    rw [abs_of_nonneg (by linarith)]
    ring
  simpa only [fourFiveMovingFaceLebesgueCellDefect,
    Real.norm_eq_abs, hcellLength, mul_one] using hnorm

/-- Sum of all literal signed cell defects for a conditional face. -/
def fourFiveMovingFaceLebesgueCellDefectSum
    (A Y y : Nat) (u c : Real) : Real :=
  ∑ n ∈ Finset.Ioc A Y,
    fourFiveMovingFaceLebesgueCellDefect A Y y u c n

/-- Signed sum over every cell except the distinguished crossed-face cell. -/
def fourFiveMovingFaceInteriorLebesgueCellDefectSum
    (A Y y : Nat) (u c : Real) : Real :=
  ∑ n ∈ Finset.Ioc A Y,
    if n = fourFiveMovingFaceStrictCellIndex A Y y u c then 0
    else fourFiveMovingFaceLebesgueCellDefect A Y y u c n

/-- Signed defect carried by the single distinguished strict-face cell. -/
def fourFiveMovingFaceStrictLebesgueCellDefect
    (A Y y : Nat) (u c : Real) : Real :=
  ∑ n ∈ Finset.Ioc A Y,
    if n = fourFiveMovingFaceStrictCellIndex A Y y u c then
      fourFiveMovingFaceLebesgueCellDefect A Y y u c n
    else 0

theorem fourFiveMovingFaceLebesgueCellDefectSum_eq_interior_add_strict
    (A Y y : Nat) (u c : Real) :
    fourFiveMovingFaceLebesgueCellDefectSum A Y y u c =
      fourFiveMovingFaceInteriorLebesgueCellDefectSum A Y y u c +
        fourFiveMovingFaceStrictLebesgueCellDefect A Y y u c := by
  unfold fourFiveMovingFaceLebesgueCellDefectSum
    fourFiveMovingFaceInteriorLebesgueCellDefectSum
    fourFiveMovingFaceStrictLebesgueCellDefect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  split_ifs <;> ring

theorem abs_fourFiveMovingFaceInteriorLebesgueCellDefectSum_le
    {A Y y : Nat} {u c : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y) :
    |fourFiveMovingFaceInteriorLebesgueCellDefectSum A Y y u c| <=
      fourFiveLogLogCellMeshBound A := by
  have hdelta0 : 0 <= fourFiveLogLogCellMeshBound A :=
    (fourFiveLogLogCellMeshBound_pos (hy.trans hyA)).le
  calc
    |fourFiveMovingFaceInteriorLebesgueCellDefectSum A Y y u c| <=
        ∑ n ∈ Finset.Ioc A Y,
          |if n = fourFiveMovingFaceStrictCellIndex A Y y u c then 0
            else fourFiveMovingFaceLebesgueCellDefect A Y y u c n| := by
      unfold fourFiveMovingFaceInteriorLebesgueCellDefectSum
      exact Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ n ∈ Finset.Ioc A Y,
        fourFiveLogLogCellMeshBound A *
          fourFiveMovingFaceInteriorCellOscillation A Y y u c n := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hnJ : n = fourFiveMovingFaceStrictCellIndex A Y y u c
      · rw [if_pos hnJ, abs_zero]
        have hinterior0 :
            0 <=
              fourFiveMovingFaceInteriorCellOscillation
                A Y y u c n := by
          let R := fourFiveMovingFaceCutoff A Y y u c
          let g := fun k : Nat =>
            fourFiveRealMovingFaceReciprocal y u c (k : Real)
          have hnData := Finset.mem_Ioc.mp hn
          by_cases hnR : n <= R
          · have hface :=
              (fourFiveMovingFace_active_iff_le_cutoff
                hy hyA hn).mpr hnR
            have hn1pos : 0 < ((n - 1 : Nat) : Real) := by
              exact_mod_cast (show 0 < n - 1 by omega)
            have hmono : g (n - 1) <= g n := by
              exact fourFiveRealMovingFaceReciprocal_mono
                hy hn1pos
                (by exact_mod_cast Nat.sub_le n 1)
                (by simpa [g] using hface)
            unfold fourFiveMovingFaceInteriorCellOscillation
            dsimp [R, g]
            rw [if_pos ⟨hnData.1, hnR⟩]
            exact sub_nonneg.mpr hmono
          · unfold fourFiveMovingFaceInteriorCellOscillation
            dsimp [R, g]
            rw [if_neg (fun h => hnR h.2)]
        exact mul_nonneg hdelta0 hinterior0
      · rw [if_neg hnJ]
        have hcell := abs_fourFiveMovingFaceLebesgueCellDefect_le
          (u := u) (c := c) hy hyA hn
        rw [fourFiveMovingFaceCellOscillationEnvelope_eq_interior_add_strict,
          show fourFiveMovingFaceStrictCellCharge A Y y u c n = 0 by
            simp [fourFiveMovingFaceStrictCellCharge, hnJ], add_zero] at hcell
        exact hcell
    _ = fourFiveLogLogCellMeshBound A *
        (∑ n ∈ Finset.Ioc A Y,
          fourFiveMovingFaceInteriorCellOscillation A Y y u c n) := by
      rw [Finset.mul_sum]
    _ <= fourFiveLogLogCellMeshBound A * 1 :=
      mul_le_mul_of_nonneg_left
        (sum_fourFiveMovingFaceInteriorCellOscillation_le_one
          hy hyA hAY) hdelta0
    _ = fourFiveLogLogCellMeshBound A := mul_one _

theorem abs_fourFiveMovingFaceStrictLebesgueCellDefect_le
    {A Y y : Nat} {u c : Real}
    (hy : 2 <= y) (hyA : y <= A) :
    |fourFiveMovingFaceStrictLebesgueCellDefect A Y y u c| <=
      fourFiveLogLogCellMeshBound A := by
  classical
  have hdelta0 : 0 <= fourFiveLogLogCellMeshBound A :=
    (fourFiveLogLogCellMeshBound_pos (hy.trans hyA)).le
  calc
    |fourFiveMovingFaceStrictLebesgueCellDefect A Y y u c| <=
        ∑ n ∈ Finset.Ioc A Y,
          |if n = fourFiveMovingFaceStrictCellIndex A Y y u c then
              fourFiveMovingFaceLebesgueCellDefect A Y y u c n else 0| := by
      unfold fourFiveMovingFaceStrictLebesgueCellDefect
      exact Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ n ∈ Finset.Ioc A Y,
        fourFiveLogLogCellMeshBound A *
          fourFiveMovingFaceStrictCellCharge A Y y u c n := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hnJ : n = fourFiveMovingFaceStrictCellIndex A Y y u c
      · rw [if_pos hnJ]
        have hcell := abs_fourFiveMovingFaceLebesgueCellDefect_le
          (u := u) (c := c) hy hyA hn
        have hfirstFalseIndex :
            ¬ (A < fourFiveMovingFaceStrictCellIndex A Y y u c ∧
              fourFiveMovingFaceStrictCellIndex A Y y u c <=
                fourFiveMovingFaceCutoff A Y y u c) := by
          unfold fourFiveMovingFaceStrictCellIndex
          omega
        simpa [fourFiveMovingFaceStrictCellCharge, hnJ,
          fourFiveMovingFaceCellOscillationEnvelope,
          hfirstFalseIndex] using hcell
      · simp [hnJ, fourFiveMovingFaceStrictCellCharge]
    _ = fourFiveLogLogCellMeshBound A *
        (∑ n ∈ Finset.Ioc A Y,
          fourFiveMovingFaceStrictCellCharge A Y y u c n) := by
      rw [Finset.mul_sum]
    _ <= fourFiveLogLogCellMeshBound A * 1 :=
      mul_le_mul_of_nonneg_left
        (sum_fourFiveMovingFaceStrictCellCharge_le_one
          (A := A) (Y := Y) (y := y) (u := u) (c := c)) hdelta0
    _ = fourFiveLogLogCellMeshBound A := mul_one _

/-- The finite right-endpoint log-log-cell sum. -/
def fourFiveMovingFaceRightEndpointCellSum
    (A Y y : Nat) (u c : Real) : Real :=
  ∑ n ∈ Finset.Ioc A Y,
    fourFiveLogLogLebesgueCellAtom n *
      fourFiveMovingFaceKernel A y u c n

/-- The same finite union of cells with the moving-face kernel allowed to
vary inside each literal cell. -/
def fourFiveMovingFaceRealCellIntegralSum
    (A Y y : Nat) (u c : Real) : Real :=
  ∑ n ∈ Finset.Ioc A Y,
    ∫ x in (((n - 1 : Nat) : Real))..(n : Real),
      fourFiveLogLogLebesgueDensity x *
        fourFiveRealMovingFaceKernel A y u c x

theorem fourFiveMovingFaceRightEndpointCellSum_sub_real_eq_defectSum
    {A Y y : Nat} {u c : Real}
    (hy : 2 <= y) (hyA : y <= A) :
    fourFiveMovingFaceRightEndpointCellSum A Y y u c -
        fourFiveMovingFaceRealCellIntegralSum A Y y u c =
      fourFiveMovingFaceLebesgueCellDefectSum A Y y u c := by
  unfold fourFiveMovingFaceRightEndpointCellSum
    fourFiveMovingFaceRealCellIntegralSum
    fourFiveMovingFaceLebesgueCellDefectSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact fourFiveLebesgueCell_sample_sub_real_eq_defect hy hyA hn

/-- Finite one-dimensional log-log-cell quadrature.  The factor `2` is the
one unit of telescoping interior variation plus the one possible strict-face
cell. -/
theorem abs_fourFiveMovingFaceLebesgueCellDefectSum_le
    {A Y y : Nat} {u c : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y) :
    |fourFiveMovingFaceLebesgueCellDefectSum A Y y u c| <=
      2 * fourFiveLogLogCellMeshBound A := by
  have hdelta0 : 0 <= fourFiveLogLogCellMeshBound A :=
    (fourFiveLogLogCellMeshBound_pos (hy.trans hyA)).le
  calc
    |fourFiveMovingFaceLebesgueCellDefectSum A Y y u c| <=
        ∑ n ∈ Finset.Ioc A Y,
          |fourFiveMovingFaceLebesgueCellDefect A Y y u c n| := by
      unfold fourFiveMovingFaceLebesgueCellDefectSum
      exact Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ n ∈ Finset.Ioc A Y,
        fourFiveLogLogCellMeshBound A *
          fourFiveMovingFaceCellOscillationEnvelope A Y y u c n := by
      apply Finset.sum_le_sum
      intro n hn
      exact abs_fourFiveMovingFaceLebesgueCellDefect_le
        (u := u) (c := c) hy hyA hn
    _ = fourFiveLogLogCellMeshBound A *
        (∑ n ∈ Finset.Ioc A Y,
          fourFiveMovingFaceCellOscillationEnvelope A Y y u c n) := by
      rw [Finset.mul_sum]
    _ <= fourFiveLogLogCellMeshBound A * 2 := by
      exact mul_le_mul_of_nonneg_left
        (sum_fourFiveMovingFaceCellOscillationEnvelope_le_two
          hy hyA hAY) hdelta0
    _ = 2 * fourFiveLogLogCellMeshBound A := by ring

/-- Final one-dimensional Riemann estimate on the paper's actual cells. -/
theorem abs_fourFiveMovingFaceRightEndpointCellSum_sub_real_le
    {A Y y : Nat} {u c : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y) :
    |fourFiveMovingFaceRightEndpointCellSum A Y y u c -
        fourFiveMovingFaceRealCellIntegralSum A Y y u c| <=
      2 * fourFiveLogLogCellMeshBound A := by
  rw [fourFiveMovingFaceRightEndpointCellSum_sub_real_eq_defectSum hy hyA]
  exact abs_fourFiveMovingFaceLebesgueCellDefectSum_le hy hyA hAY

end Erdos390.WholePaper.BankPaperRealization
