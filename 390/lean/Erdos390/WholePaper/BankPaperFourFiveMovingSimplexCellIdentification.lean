import Erdos390.WholePaper.BankPaperFourFiveMovingSimplexCellTelescope
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Exact finite-cell identification for the moving simplex

This file identifies the two-coordinate cell telescope with the literal
difference between the right-corner sampled product and the iterated real
cell integral.  The proof inserts one hybrid product.  All rearrangements
are finite-sum identities or Fubini on one compact cell rectangle; the
joint kernel is measurable and bounded there.

The same real kernel is also prepared in three coordinates.  It is the
literal physical-variable form of the logarithmic moving-simplex density.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-! ## Real moving-simplex kernels -/

def fourFiveRealMovingSimplexKernelOne
    (A y : Nat) (u x : Real) : Real :=
  fourFiveRealMovingFaceKernel A y u 0 x

def fourFiveRealMovingSimplexKernelTwo
    (A y : Nat) (u x z : Real) : Real :=
  if (A : Real) < x ∧ (A : Real) < z ∧
      fourFiveRealLogCoordinate y x +
        fourFiveRealLogCoordinate y z < u - 1 then
    (u - fourFiveRealLogCoordinate y x -
      fourFiveRealLogCoordinate y z)⁻¹
  else 0

def fourFiveRealMovingSimplexKernelThree
    (A y : Nat) (u x z w : Real) : Real :=
  if (A : Real) < x ∧ (A : Real) < z ∧ (A : Real) < w ∧
      fourFiveRealLogCoordinate y x +
        fourFiveRealLogCoordinate y z +
          fourFiveRealLogCoordinate y w < u - 1 then
    (u - fourFiveRealLogCoordinate y x -
      fourFiveRealLogCoordinate y z -
        fourFiveRealLogCoordinate y w)⁻¹
  else 0

theorem fourFiveRealMovingSimplexKernelTwo_eq_face_first
    {A y : Nat} {u x z : Real} (hzA : (A : Real) < z) :
    fourFiveRealMovingSimplexKernelTwo A y u x z =
      fourFiveRealMovingFaceKernel A y u
        (fourFiveRealLogCoordinate y z) x := by
  unfold fourFiveRealMovingSimplexKernelTwo
    fourFiveRealMovingFaceKernel fourFiveRealMovingFaceReciprocal
  split_ifs <;> simp_all <;> ring_nf at * <;> linarith

theorem fourFiveRealMovingSimplexKernelTwo_eq_face_second
    {A y : Nat} {u x z : Real} (hxA : (A : Real) < x) :
    fourFiveRealMovingSimplexKernelTwo A y u x z =
      fourFiveRealMovingFaceKernel A y u
        (fourFiveRealLogCoordinate y x) z := by
  unfold fourFiveRealMovingSimplexKernelTwo
    fourFiveRealMovingFaceKernel fourFiveRealMovingFaceReciprocal
  split_ifs <;> simp_all <;> ring_nf at * <;> linarith

theorem fourFiveRealMovingSimplexKernelTwo_natCast
    {A Y y p q : Nat} {u : Real}
    (_hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y) :
    fourFiveRealMovingSimplexKernelTwo A y u (p : Real) (q : Real) =
      fourFiveMovingSimplexKernelTwo A y u p q := by
  have hqA : (A : Real) < (q : Real) := by
    exact_mod_cast (Finset.mem_Ioc.mp hq).1
  rw [fourFiveRealMovingSimplexKernelTwo_eq_face_first hqA,
    fourFiveRealLogCoordinate_natCast,
    fourFiveRealMovingFaceKernel_natCast,
    ← fourFiveMovingSimplexKernelTwo_eq_face_first hq]

theorem fourFiveRealMovingSimplexKernelTwo_nonneg_le_one
    {A y : Nat} {u x z : Real} :
    0 <= fourFiveRealMovingSimplexKernelTwo A y u x z ∧
      fourFiveRealMovingSimplexKernelTwo A y u x z <= 1 := by
  unfold fourFiveRealMovingSimplexKernelTwo
  split_ifs with h
  · have hden : 1 < u - fourFiveRealLogCoordinate y x -
        fourFiveRealLogCoordinate y z := by
      linarith [h.2.2]
    constructor
    · exact inv_nonneg.mpr (zero_le_one.trans hden.le)
    · simpa only [inv_one] using
        (inv_le_inv₀ (zero_lt_one.trans hden) zero_lt_one).mpr hden.le
  · exact ⟨le_rfl, zero_le_one⟩

theorem measurable_fourFiveRealMovingSimplexKernelTwo
    (A y : Nat) (u : Real) :
    Measurable (Function.uncurry
      (fourFiveRealMovingSimplexKernelTwo A y u)) := by
  have hcoordX : Measurable
      (fun p : Real × Real => fourFiveRealLogCoordinate y p.1) :=
    (measurable_fourFiveRealLogCoordinate y).comp measurable_fst
  have hcoordZ : Measurable
      (fun p : Real × Real => fourFiveRealLogCoordinate y p.2) :=
    (measurable_fourFiveRealLogCoordinate y).comp measurable_snd
  have hactive : MeasurableSet {p : Real × Real |
      (A : Real) < p.1 ∧ (A : Real) < p.2 ∧
        fourFiveRealLogCoordinate y p.1 +
          fourFiveRealLogCoordinate y p.2 < u - 1} :=
    (measurable_fst measurableSet_Ioi).inter
      ((measurable_snd measurableSet_Ioi).inter
        ((hcoordX.add hcoordZ) measurableSet_Iio))
  have hrecip : Measurable (fun p : Real × Real =>
      (u - fourFiveRealLogCoordinate y p.1 -
        fourFiveRealLogCoordinate y p.2)⁻¹) :=
    ((measurable_const.sub hcoordX).sub hcoordZ).inv
  unfold Function.uncurry fourFiveRealMovingSimplexKernelTwo
  exact Measurable.ite hactive hrecip measurable_const

theorem fourFiveRealMovingSimplexKernelThree_eq_face_third
    {A y : Nat} {u x z w : Real}
    (hxA : (A : Real) < x) (hzA : (A : Real) < z) :
    fourFiveRealMovingSimplexKernelThree A y u x z w =
      fourFiveRealMovingFaceKernel A y u
        (fourFiveRealLogCoordinate y x +
          fourFiveRealLogCoordinate y z) w := by
  unfold fourFiveRealMovingSimplexKernelThree
    fourFiveRealMovingFaceKernel fourFiveRealMovingFaceReciprocal
  split_ifs <;> simp_all <;> ring_nf at * <;> linarith

theorem fourFiveRealMovingSimplexKernelThree_eq_two_shift
    {A y : Nat} {u x z w : Real} (hwA : (A : Real) < w) :
    fourFiveRealMovingSimplexKernelThree A y u x z w =
      fourFiveRealMovingSimplexKernelTwo A y
        (u - fourFiveRealLogCoordinate y w) x z := by
  unfold fourFiveRealMovingSimplexKernelThree
    fourFiveRealMovingSimplexKernelTwo
  split_ifs <;> simp_all <;> ring_nf at * <;> linarith

/-- The analogous two-coordinate reduction with the first coordinate held
fixed.  This orientation is the one used for the inner `z,w` cell block in
the exact three-dimensional Fubini argument. -/
theorem fourFiveRealMovingSimplexKernelThree_eq_two_shift_first
    {A y : Nat} {u x z w : Real} (hxA : (A : Real) < x) :
    fourFiveRealMovingSimplexKernelThree A y u x z w =
      fourFiveRealMovingSimplexKernelTwo A y
        (u - fourFiveRealLogCoordinate y x) z w := by
  unfold fourFiveRealMovingSimplexKernelThree
    fourFiveRealMovingSimplexKernelTwo
  split_ifs <;> simp_all <;> ring_nf at * <;> linarith

theorem fourFiveMovingSimplexKernelThree_eq_two_shift
    {A Y y p q r : Nat} {u : Real}
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y)
    (hr : r ∈ Finset.Ioc A Y) :
    fourFiveMovingSimplexKernelThree A y u p q r =
      fourFiveMovingSimplexKernelTwo A y
        (u - fourFiveLogCoordinate y r) p q := by
  unfold fourFiveMovingSimplexKernelThree
    fourFiveMovingSimplexKernelTwo
  have hpA := (Finset.mem_Ioc.mp hp).1
  have hqA := (Finset.mem_Ioc.mp hq).1
  have hrA := (Finset.mem_Ioc.mp hr).1
  split_ifs <;> simp_all <;> ring_nf at * <;> linarith

theorem fourFiveRealMovingSimplexKernelThree_natCast
    {A Y y p q r : Nat} {u : Real}
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y)
    (hr : r ∈ Finset.Ioc A Y) :
    fourFiveRealMovingSimplexKernelThree A y u
        (p : Real) (q : Real) (r : Real) =
      fourFiveMovingSimplexKernelThree A y u p q r := by
  have hrA : (A : Real) < (r : Real) := by
    exact_mod_cast (Finset.mem_Ioc.mp hr).1
  rw [fourFiveRealMovingSimplexKernelThree_eq_two_shift hrA,
    fourFiveRealLogCoordinate_natCast,
    fourFiveRealMovingSimplexKernelTwo_natCast hp hq,
    ← fourFiveMovingSimplexKernelThree_eq_two_shift hp hq hr]

theorem fourFiveMovingFaceKernel_shift
    (A y n : Nat) (u c d : Real) :
    fourFiveMovingFaceKernel A y (u - d) c n =
      fourFiveMovingFaceKernel A y u (c + d) n := by
  unfold fourFiveMovingFaceKernel
  split_ifs <;> simp_all <;> ring_nf at * <;> linarith

theorem fourFiveRealMovingFaceKernel_shift
    (A y : Nat) (u c d x : Real) :
    fourFiveRealMovingFaceKernel A y (u - d) c x =
      fourFiveRealMovingFaceKernel A y u (c + d) x := by
  unfold fourFiveRealMovingFaceKernel fourFiveRealMovingFaceReciprocal
  split_ifs <;> simp_all <;> ring_nf at * <;> linarith

theorem fourFiveMovingFaceLebesgueCellDefectSum_shift
    (A Y y : Nat) (u c d : Real) :
    fourFiveMovingFaceLebesgueCellDefectSum A Y y (u - d) c =
      fourFiveMovingFaceLebesgueCellDefectSum A Y y u (c + d) := by
  unfold fourFiveMovingFaceLebesgueCellDefectSum
    fourFiveMovingFaceLebesgueCellDefect
  apply Finset.sum_congr rfl
  intro n _hn
  apply intervalIntegral.integral_congr
  intro x _hx
  exact congrArg
    (fun z : Real => fourFiveLogLogLebesgueDensity x * z)
    (congrArg₂ (fun a b : Real => a - b)
      (fourFiveMovingFaceKernel_shift A y n u c d)
      (fourFiveRealMovingFaceKernel_shift A y u c d x))

/-! ## Integrability on one literal cell rectangle -/

private def fourFiveRealMovingSimplexDensityTwo
    (A y : Nat) (u : Real) (p : Real × Real) : Real :=
  fourFiveLogLogLebesgueDensity p.1 *
    fourFiveLogLogLebesgueDensity p.2 *
      fourFiveRealMovingSimplexKernelTwo A y u p.1 p.2

private theorem integrable_fourFiveRealMovingSimplexDensityTwo_cell
    {A Y y p q : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y) :
    let mu := volume.restrict
      (Set.Ioc (((p - 1 : Nat) : Real)) (p : Real))
    let nu := volume.restrict
      (Set.Ioc (((q - 1 : Nat) : Real)) (q : Real))
    Integrable (fourFiveRealMovingSimplexDensityTwo A y u) (mu.prod nu) := by
  dsimp only
  let mu : Measure Real := volume.restrict
    (Set.Ioc (((p - 1 : Nat) : Real)) (p : Real))
  let nu : Measure Real := volume.restrict
    (Set.Ioc (((q - 1 : Nat) : Real)) (q : Real))
  let delta := fourFiveLogLogCellMeshBound A
  have hA : 2 <= A := hy.trans hyA
  have hdelta : 0 <= delta := (fourFiveLogLogCellMeshBound_pos hA).le
  have hmeas : Measurable
      (fourFiveRealMovingSimplexDensityTwo A y u) := by
    unfold fourFiveRealMovingSimplexDensityTwo
    exact ((measurable_fourFiveLogLogLebesgueDensity.comp measurable_fst).mul
      (measurable_fourFiveLogLogLebesgueDensity.comp measurable_snd)).mul
        (measurable_fourFiveRealMovingSimplexKernelTwo A y u)
  have hconst : Integrable (fun _ : Real × Real => delta ^ 2)
      (mu.prod nu) := integrable_const _
  have hbound : ∀ᵐ r ∂(mu.prod nu),
      ‖fourFiveRealMovingSimplexDensityTwo A y u r‖ <= delta ^ 2 := by
    rw [Measure.ae_prod_iff_ae_ae
      (measurableSet_le hmeas.norm measurable_const)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    have hdx := fourFiveLogLogLebesgueDensity_le_meshBound hA
      (Finset.mem_Ioc.mp hp).1 (Set.Ioc_subset_Icc_self hx)
    have hdz := fourFiveLogLogLebesgueDensity_le_meshBound hA
      (Finset.mem_Ioc.mp hq).1 (Set.Ioc_subset_Icc_self hz)
    have hK := fourFiveRealMovingSimplexKernelTwo_nonneg_le_one
      (A := A) (y := y) (u := u) (x := x) (z := z)
    rw [fourFiveRealMovingSimplexDensityTwo, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_of_nonneg hdx.1, abs_of_nonneg hdz.1,
      abs_of_nonneg hK.1, pow_two]
    exact calc
      fourFiveLogLogLebesgueDensity x *
          fourFiveLogLogLebesgueDensity z *
            fourFiveRealMovingSimplexKernelTwo A y u x z <=
        delta * delta * 1 := by
          exact mul_le_mul
            (mul_le_mul hdx.2 hdz.2 hdz.1 hdelta)
            hK.2 hK.1 (mul_nonneg hdelta hdelta)
      _ = delta * delta := mul_one _
  exact hconst.mono' hmeas.aestronglyMeasurable hbound

private theorem intervalIntegrable_fourFiveRealMovingSimplexTwo_partial_cell
    {A Y y p q : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y) :
    IntervalIntegrable
      (fun x : Real => fourFiveLogLogLebesgueDensity x *
        (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            fourFiveRealMovingSimplexKernelTwo A y u x z))
      volume (((p - 1 : Nat) : Real)) (p : Real) := by
  have hporder : (((p - 1 : Nat) : Real)) <= (p : Real) := by
    exact_mod_cast Nat.sub_le p 1
  have hqorder : (((q - 1 : Nat) : Real)) <= (q : Real) := by
    exact_mod_cast Nat.sub_le q 1
  let mu : Measure Real := volume.restrict
    (Set.Ioc (((p - 1 : Nat) : Real)) (p : Real))
  let nu : Measure Real := volume.restrict
    (Set.Ioc (((q - 1 : Nat) : Real)) (q : Real))
  have hjoint := integrable_fourFiveRealMovingSimplexDensityTwo_cell
    (u := u) hy hyA hp hq
  have hpartial := hjoint.integral_prod_left
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hporder]
  simpa [mu, nu, intervalIntegral.integral_of_le hqorder,
    fourFiveRealMovingSimplexDensityTwo,
    MeasureTheory.integral_const_mul, mul_assoc] using hpartial

/-! ## Sample, hybrid, and fully integrated two-coordinate products -/

def fourFiveMovingSimplexRightEndpointProductTwo
    (A Y y : Nat) (u : Real) : Real :=
  fourFiveLebesgueCellProductTwo
    (fourFiveMovingSimplexKernelTwo A y u) A Y

def fourFiveMovingSimplexHybridCellProductTwo
    (A Y y : Nat) (u : Real) : Real :=
  ∑ p ∈ Finset.Ioc A Y,
    ∑ q ∈ Finset.Ioc A Y,
      fourFiveLogLogLebesgueCellAtom q *
        (∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          fourFiveLogLogLebesgueDensity x *
            fourFiveRealMovingSimplexKernelTwo A y u x (q : Real))

def fourFiveMovingSimplexIteratedRealCellProductTwo
    (A Y y : Nat) (u : Real) : Real :=
  ∑ p ∈ Finset.Ioc A Y,
    ∑ q ∈ Finset.Ioc A Y,
      ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
        fourFiveLogLogLebesgueDensity x *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              fourFiveRealMovingSimplexKernelTwo A y u x z)

theorem fourFiveMovingSimplexRightEndpointProductTwo_sub_hybrid
    {A Y y : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A) :
    fourFiveMovingSimplexRightEndpointProductTwo A Y y u -
        fourFiveMovingSimplexHybridCellProductTwo A Y y u =
      ∑ q ∈ Finset.Ioc A Y,
        fourFiveLogLogLebesgueCellAtom q *
          fourFiveMovingFaceLebesgueCellDefectSum A Y y u
            (fourFiveLogCoordinate y q) := by
  unfold fourFiveMovingSimplexRightEndpointProductTwo
    fourFiveLebesgueCellProductTwo fourFiveFiniteProductTwo
    fourFiveMovingSimplexHybridCellProductTwo
  calc
    (∑ p ∈ Finset.Ioc A Y,
        fourFiveLogLogLebesgueCellAtom p *
          (∑ q ∈ Finset.Ioc A Y,
            fourFiveLogLogLebesgueCellAtom q *
              fourFiveMovingSimplexKernelTwo A y u p q)) -
        ∑ p ∈ Finset.Ioc A Y,
          ∑ q ∈ Finset.Ioc A Y,
            fourFiveLogLogLebesgueCellAtom q *
              (∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                fourFiveLogLogLebesgueDensity x *
                  fourFiveRealMovingSimplexKernelTwo A y u x (q : Real)) =
      ∑ p ∈ Finset.Ioc A Y,
        ∑ q ∈ Finset.Ioc A Y,
          fourFiveLogLogLebesgueCellAtom q *
            (fourFiveLogLogLebesgueCellAtom p *
                fourFiveMovingSimplexKernelTwo A y u p q -
              ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                fourFiveLogLogLebesgueDensity x *
                  fourFiveRealMovingSimplexKernelTwo A y u x (q : Real)) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro p _hp
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro q _hq
        ring
    _ = ∑ q ∈ Finset.Ioc A Y,
        fourFiveLogLogLebesgueCellAtom q *
          (∑ p ∈ Finset.Ioc A Y,
            (fourFiveLogLogLebesgueCellAtom p *
                fourFiveMovingSimplexKernelTwo A y u p q -
              ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                fourFiveLogLogLebesgueDensity x *
                  fourFiveRealMovingSimplexKernelTwo A y u x (q : Real))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _hq
      rw [Finset.mul_sum]
    _ = ∑ q ∈ Finset.Ioc A Y,
        fourFiveLogLogLebesgueCellAtom q *
          fourFiveMovingFaceLebesgueCellDefectSum A Y y u
            (fourFiveLogCoordinate y q) := by
      apply Finset.sum_congr rfl
      intro q hq
      apply congrArg (fun z : Real => fourFiveLogLogLebesgueCellAtom q * z)
      unfold fourFiveMovingFaceLebesgueCellDefectSum
      apply Finset.sum_congr rfl
      intro p hp
      rw [fourFiveMovingSimplexKernelTwo_eq_face_first hq]
      have hqA : (A : Real) < (q : Real) := by
        exact_mod_cast (Finset.mem_Ioc.mp hq).1
      have hreal (x : Real) :
          fourFiveRealMovingSimplexKernelTwo A y u x (q : Real) =
            fourFiveRealMovingFaceKernel A y u
              (fourFiveLogCoordinate y q) x := by
        simpa only [fourFiveRealLogCoordinate_natCast] using
          (fourFiveRealMovingSimplexKernelTwo_eq_face_first
            (A := A) (y := y) (u := u) (x := x)
            (z := (q : Real)) hqA)
      have hintegral :
          (∫ x in (((p - 1 : Nat) : Real))..(p : Real),
              fourFiveLogLogLebesgueDensity x *
                fourFiveRealMovingSimplexKernelTwo A y u x (q : Real)) =
            ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
              fourFiveLogLogLebesgueDensity x *
                fourFiveRealMovingFaceKernel A y u
                  (fourFiveLogCoordinate y q) x := by
        apply intervalIntegral.integral_congr
        intro x _hx
        exact congrArg (fun t : Real =>
          fourFiveLogLogLebesgueDensity x * t) (hreal x)
      rw [hintegral]
      exact fourFiveLebesgueCell_sample_sub_real_eq_defect hy hyA hp

theorem fourFiveMovingSimplexHybridCellProductTwo_sub_iterated
    {A Y y : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A) :
    fourFiveMovingSimplexHybridCellProductTwo A Y y u -
        fourFiveMovingSimplexIteratedRealCellProductTwo A Y y u =
      ∑ p ∈ Finset.Ioc A Y,
        ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          fourFiveLogLogLebesgueDensity x *
            fourFiveMovingFaceLebesgueCellDefectSum A Y y u
              (fourFiveRealLogCoordinate y x) := by
  unfold fourFiveMovingSimplexHybridCellProductTwo
    fourFiveMovingSimplexIteratedRealCellProductTwo
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hpA : ∀ x ∈ Set.uIoc (((p - 1 : Nat) : Real)) (p : Real),
      (A : Real) < x := by
    intro x hx
    have hporder : (((p - 1 : Nat) : Real)) <= (p : Real) := by
      exact_mod_cast Nat.sub_le p 1
    have hxIoc :
        x ∈ Set.Ioc (((p - 1 : Nat) : Real)) (p : Real) := by
      simpa only [Set.uIoc_of_le hporder] using hx
    have hApred : A <= p - 1 := by
      have := (Finset.mem_Ioc.mp hp).1
      omega
    exact (by exact_mod_cast hApred :
      (A : Real) <= ((p - 1 : Nat) : Real)).trans_lt hxIoc.1
  have hleftIntegrable (q : Nat) (hq : q ∈ Finset.Ioc A Y) :
      IntervalIntegrable
        (fun x : Real => fourFiveLogLogLebesgueDensity x *
          (fourFiveLogLogLebesgueCellAtom q *
            fourFiveRealMovingSimplexKernelTwo A y u x (q : Real)))
        volume (((p - 1 : Nat) : Real)) (p : Real) := by
    have hqA : (A : Real) < (q : Real) := by
      exact_mod_cast (Finset.mem_Ioc.mp hq).1
    have hbase := intervalIntegrable_fourFiveDensity_mul_realMovingFace_cell
      (u := u) (c := fourFiveLogCoordinate y q) hy hyA hp
    apply (hbase.const_mul
      (fourFiveLogLogLebesgueCellAtom q)).congr
    intro x hx
    have hreal :
        fourFiveRealMovingSimplexKernelTwo A y u x (q : Real) =
          fourFiveRealMovingFaceKernel A y u
            (fourFiveLogCoordinate y q) x := by
      simpa only [fourFiveRealLogCoordinate_natCast] using
        (fourFiveRealMovingSimplexKernelTwo_eq_face_first
          (A := A) (y := y) (u := u) (x := x)
          (z := (q : Real)) hqA)
    calc
      fourFiveLogLogLebesgueCellAtom q *
            (fourFiveLogLogLebesgueDensity x *
              fourFiveRealMovingFaceKernel A y u
                (fourFiveLogCoordinate y q) x) =
          fourFiveLogLogLebesgueDensity x *
            (fourFiveLogLogLebesgueCellAtom q *
              fourFiveRealMovingFaceKernel A y u
                (fourFiveLogCoordinate y q) x) := by
        ring
      _ = fourFiveLogLogLebesgueDensity x *
            (fourFiveLogLogLebesgueCellAtom q *
              fourFiveRealMovingSimplexKernelTwo A y u
                x (q : Real)) :=
        congrArg
          (fun k : Real => fourFiveLogLogLebesgueDensity x *
            (fourFiveLogLogLebesgueCellAtom q * k))
          hreal.symm
  have hrightIntegrable (q : Nat) (hq : q ∈ Finset.Ioc A Y) :=
    intervalIntegrable_fourFiveRealMovingSimplexTwo_partial_cell
      (u := u) hy hyA hp hq
  have hdiffIntegrable (q : Nat) (hq : q ∈ Finset.Ioc A Y) :
      IntervalIntegrable
        (fun x : Real =>
          fourFiveLogLogLebesgueDensity x *
              (fourFiveLogLogLebesgueCellAtom q *
                fourFiveRealMovingSimplexKernelTwo A y u x (q : Real)) -
            fourFiveLogLogLebesgueDensity x *
              (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  fourFiveRealMovingSimplexKernelTwo A y u x z))
        volume (((p - 1 : Nat) : Real)) (p : Real) :=
    (hleftIntegrable q hq).sub (hrightIntegrable q hq)
  calc
    (∑ q ∈ Finset.Ioc A Y,
          fourFiveLogLogLebesgueCellAtom q *
            (∫ x in (((p - 1 : Nat) : Real))..(p : Real),
              fourFiveLogLogLebesgueDensity x *
                fourFiveRealMovingSimplexKernelTwo A y u x (q : Real))) -
        ∑ q ∈ Finset.Ioc A Y,
          ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
            fourFiveLogLogLebesgueDensity x *
              (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  fourFiveRealMovingSimplexKernelTwo A y u x z) =
      ∑ q ∈ Finset.Ioc A Y,
        ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          (fourFiveLogLogLebesgueDensity x *
              (fourFiveLogLogLebesgueCellAtom q *
                fourFiveRealMovingSimplexKernelTwo A y u x (q : Real)) -
            fourFiveLogLogLebesgueDensity x *
              (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  fourFiveRealMovingSimplexKernelTwo A y u x z)) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro q hq
        calc
          fourFiveLogLogLebesgueCellAtom q *
                (∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                  fourFiveLogLogLebesgueDensity x *
                    fourFiveRealMovingSimplexKernelTwo A y u x (q : Real)) -
              ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                fourFiveLogLogLebesgueDensity x *
                  (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                    fourFiveLogLogLebesgueDensity z *
                      fourFiveRealMovingSimplexKernelTwo A y u x z) =
            (∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                fourFiveLogLogLebesgueDensity x *
                  (fourFiveLogLogLebesgueCellAtom q *
                    fourFiveRealMovingSimplexKernelTwo A y u x (q : Real))) -
              ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                fourFiveLogLogLebesgueDensity x *
                  (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                    fourFiveLogLogLebesgueDensity z *
                      fourFiveRealMovingSimplexKernelTwo A y u x z) := by
              congr 1
              rw [← intervalIntegral.integral_const_mul]
              apply intervalIntegral.integral_congr
              intro x _hx
              ring
          _ = ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
              (fourFiveLogLogLebesgueDensity x *
                  (fourFiveLogLogLebesgueCellAtom q *
                    fourFiveRealMovingSimplexKernelTwo A y u x (q : Real)) -
                fourFiveLogLogLebesgueDensity x *
                  (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                    fourFiveLogLogLebesgueDensity z *
                      fourFiveRealMovingSimplexKernelTwo A y u x z)) :=
            (intervalIntegral.integral_sub
              (hleftIntegrable q hq) (hrightIntegrable q hq)).symm
    _ = ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
        ∑ q ∈ Finset.Ioc A Y,
          (fourFiveLogLogLebesgueDensity x *
              (fourFiveLogLogLebesgueCellAtom q *
                fourFiveRealMovingSimplexKernelTwo A y u x (q : Real)) -
            fourFiveLogLogLebesgueDensity x *
              (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  fourFiveRealMovingSimplexKernelTwo A y u x z)) := by
      symm
      exact intervalIntegral.integral_finset_sum hdiffIntegrable
    _ = ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
        fourFiveLogLogLebesgueDensity x *
          fourFiveMovingFaceLebesgueCellDefectSum A Y y u
            (fourFiveRealLogCoordinate y x) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x
      intro hx
      unfold fourFiveMovingFaceLebesgueCellDefectSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [← mul_sub]
      apply congrArg
        (fun z : Real => fourFiveLogLogLebesgueDensity x * z)
      have hface (z : Real) :
          fourFiveRealMovingSimplexKernelTwo A y u x z =
            fourFiveRealMovingFaceKernel A y u
              (fourFiveRealLogCoordinate y x) z :=
        fourFiveRealMovingSimplexKernelTwo_eq_face_second (hpA x hx)
      have hsample :
          fourFiveRealMovingSimplexKernelTwo A y u x (q : Real) =
            fourFiveMovingFaceKernel A y u
              (fourFiveRealLogCoordinate y x) q := by
        calc
          fourFiveRealMovingSimplexKernelTwo A y u x (q : Real) =
              fourFiveRealMovingFaceKernel A y u
                (fourFiveRealLogCoordinate y x) (q : Real) :=
            hface (q : Real)
          _ = fourFiveMovingFaceKernel A y u
                (fourFiveRealLogCoordinate y x) q :=
            fourFiveRealMovingFaceKernel_natCast
      have hintegral :
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
              fourFiveLogLogLebesgueDensity z *
                fourFiveRealMovingSimplexKernelTwo A y u x z) =
            ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
              fourFiveLogLogLebesgueDensity z *
                fourFiveRealMovingFaceKernel A y u
                  (fourFiveRealLogCoordinate y x) z := by
        apply intervalIntegral.integral_congr
        intro z _hz
        exact congrArg (fun t : Real =>
          fourFiveLogLogLebesgueDensity z * t) (hface z)
      rw [hsample, hintegral]
      exact fourFiveLebesgueCell_sample_sub_real_eq_defect hy hyA hq

/-- Exact two-coordinate finite-cell telescope. -/
theorem fourFiveMovingSimplexRightEndpointProductTwo_sub_iterated_eq_telescope
    {A Y y : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A) :
    fourFiveMovingSimplexRightEndpointProductTwo A Y y u -
        fourFiveMovingSimplexIteratedRealCellProductTwo A Y y u =
      fourFiveLogLogCellTelescopeTwo
        (fourFiveMovingFaceLebesgueCellDefectSum A Y y u) A Y y := by
  rw [show fourFiveMovingSimplexRightEndpointProductTwo A Y y u -
      fourFiveMovingSimplexIteratedRealCellProductTwo A Y y u =
      (fourFiveMovingSimplexRightEndpointProductTwo A Y y u -
        fourFiveMovingSimplexHybridCellProductTwo A Y y u) +
      (fourFiveMovingSimplexHybridCellProductTwo A Y y u -
        fourFiveMovingSimplexIteratedRealCellProductTwo A Y y u) by ring,
    fourFiveMovingSimplexRightEndpointProductTwo_sub_hybrid hy hyA,
    fourFiveMovingSimplexHybridCellProductTwo_sub_iterated hy hyA]
  rfl

/-- Quantitative two-coordinate consequence of the exact telescope.  Its
`4 delta_A M` is the sum of the separately established interior and
strict-face budgets `2 delta_A M + 2 delta_A M`. -/
theorem abs_fourFiveMovingSimplexRightEndpointProductTwo_sub_iterated_le
    {A Y y : Nat} {u M : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hmass : (∑ n ∈ Finset.Ioc A Y,
      |fourFiveLogLogLebesgueCellAtom n|) <= M) :
    |fourFiveMovingSimplexRightEndpointProductTwo A Y y u -
        fourFiveMovingSimplexIteratedRealCellProductTwo A Y y u| <=
      4 * fourFiveLogLogCellMeshBound A * M := by
  rw [fourFiveMovingSimplexRightEndpointProductTwo_sub_iterated_eq_telescope
    hy hyA]
  have h := abs_fourFiveLogLogCellTelescopeTwo_le
    (D := fourFiveMovingFaceLebesgueCellDefectSum A Y y u)
    (A := A) (Y := Y) (y := y)
    (M := M) (R := 2 * fourFiveLogLogCellMeshBound A)
    (hy.trans hyA) hAY
    (mul_nonneg (by norm_num)
      (fourFiveLogLogCellMeshBound_pos (hy.trans hyA)).le)
    hmass (fun c =>
      abs_fourFiveMovingFaceLebesgueCellDefectSum_le hy hyA hAY)
  convert h using 1; ring

/-! ## Three coordinates, using the exact two-coordinate block -/

def fourFiveMovingSimplexRightEndpointProductThree
    (A Y y : Nat) (u : Real) : Real :=
  fourFiveLebesgueCellProductThree
    (fourFiveMovingSimplexKernelThree A y u) A Y

/-- Hybrid in which the first two coordinates are integrated and the last
coordinate is still sampled at its cell endpoint. -/
def fourFiveMovingSimplexTwoIntegratedHybridThree
    (A Y y : Nat) (u : Real) : Real :=
  ∑ r ∈ Finset.Ioc A Y,
    fourFiveLogLogLebesgueCellAtom r *
      fourFiveMovingSimplexIteratedRealCellProductTwo A Y y
        (u - fourFiveLogCoordinate y r)

def fourFiveMovingSimplexIteratedRealCellProductThree
    (A Y y : Nat) (u : Real) : Real :=
  ∑ p ∈ Finset.Ioc A Y,
    ∑ q ∈ Finset.Ioc A Y,
      ∑ r ∈ Finset.Ioc A Y,
        ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          fourFiveLogLogLebesgueDensity x *
            (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
              fourFiveLogLogLebesgueDensity z *
                (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                  fourFiveLogLogLebesgueDensity w *
                    fourFiveRealMovingSimplexKernelThree A y u x z w))

theorem fourFiveMovingSimplexRightEndpointProductThree_eq_sum_two
    {A Y y : Nat} {u : Real} :
    fourFiveMovingSimplexRightEndpointProductThree A Y y u =
      ∑ r ∈ Finset.Ioc A Y,
        fourFiveLogLogLebesgueCellAtom r *
          fourFiveMovingSimplexRightEndpointProductTwo A Y y
            (u - fourFiveLogCoordinate y r) := by
  unfold fourFiveMovingSimplexRightEndpointProductThree
    fourFiveLebesgueCellProductThree fourFiveFiniteProductThree
    fourFiveMovingSimplexRightEndpointProductTwo
    fourFiveLebesgueCellProductTwo fourFiveFiniteProductTwo
  simp_rw [Finset.mul_sum]
  calc
    (∑ p ∈ Finset.Ioc A Y,
      ∑ q ∈ Finset.Ioc A Y,
        ∑ r ∈ Finset.Ioc A Y,
          fourFiveLogLogLebesgueCellAtom p *
            (fourFiveLogLogLebesgueCellAtom q *
              (fourFiveLogLogLebesgueCellAtom r *
                fourFiveMovingSimplexKernelThree A y u p q r))) =
      ∑ p ∈ Finset.Ioc A Y,
        ∑ r ∈ Finset.Ioc A Y,
          ∑ q ∈ Finset.Ioc A Y,
            fourFiveLogLogLebesgueCellAtom p *
              (fourFiveLogLogLebesgueCellAtom q *
                (fourFiveLogLogLebesgueCellAtom r *
                  fourFiveMovingSimplexKernelThree A y u p q r)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.sum_comm]
    _ = ∑ r ∈ Finset.Ioc A Y,
        ∑ p ∈ Finset.Ioc A Y,
          ∑ q ∈ Finset.Ioc A Y,
            fourFiveLogLogLebesgueCellAtom p *
              (fourFiveLogLogLebesgueCellAtom q *
                (fourFiveLogLogLebesgueCellAtom r *
                  fourFiveMovingSimplexKernelThree A y u p q r)) := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ Finset.Ioc A Y,
        ∑ p ∈ Finset.Ioc A Y,
          ∑ q ∈ Finset.Ioc A Y,
            fourFiveLogLogLebesgueCellAtom r *
              (fourFiveLogLogLebesgueCellAtom p *
                (fourFiveLogLogLebesgueCellAtom q *
                  fourFiveMovingSimplexKernelTwo A y
                    (u - fourFiveLogCoordinate y r) p q)) := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      rw [fourFiveMovingSimplexKernelThree_eq_two_shift hp hq hr]
      ring

theorem fourFiveMovingSimplexRightEndpointProductThree_sub_twoIntegrated
    {A Y y : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A) :
    fourFiveMovingSimplexRightEndpointProductThree A Y y u -
        fourFiveMovingSimplexTwoIntegratedHybridThree A Y y u =
      ∑ r ∈ Finset.Ioc A Y,
        fourFiveLogLogLebesgueCellAtom r *
          fourFiveLogLogCellTelescopeTwo
            (fun c => fourFiveMovingFaceLebesgueCellDefectSum A Y y u
              (c + fourFiveLogCoordinate y r)) A Y y := by
  rw [fourFiveMovingSimplexRightEndpointProductThree_eq_sum_two]
  unfold fourFiveMovingSimplexTwoIntegratedHybridThree
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← mul_sub]
  rw [fourFiveMovingSimplexRightEndpointProductTwo_sub_iterated_eq_telescope
    hy hyA]
  apply congrArg (fun z : Real => fourFiveLogLogLebesgueCellAtom r * z)
  apply congrArg
    (fun D : Real -> Real => fourFiveLogLogCellTelescopeTwo D A Y y)
  funext c
  exact fourFiveMovingFaceLebesgueCellDefectSum_shift A Y y u c
    (fourFiveLogCoordinate y r)

theorem fourFiveRealMovingSimplexKernelThree_nonneg_le_one
    {A y : Nat} {u x z w : Real} :
    0 <= fourFiveRealMovingSimplexKernelThree A y u x z w ∧
      fourFiveRealMovingSimplexKernelThree A y u x z w <= 1 := by
  unfold fourFiveRealMovingSimplexKernelThree
  split_ifs with h
  · have hden : 1 < u - fourFiveRealLogCoordinate y x -
        fourFiveRealLogCoordinate y z - fourFiveRealLogCoordinate y w := by
      linarith [h.2.2.2]
    constructor
    · exact inv_nonneg.mpr (zero_le_one.trans hden.le)
    · simpa only [inv_one] using
        (inv_le_inv₀ (zero_lt_one.trans hden) zero_lt_one).mpr hden.le
  · exact ⟨le_rfl, zero_le_one⟩

theorem measurable_fourFiveRealMovingSimplexKernelThree
    (A y : Nat) (u : Real) :
    Measurable (fun p : (Real × Real) × Real =>
      fourFiveRealMovingSimplexKernelThree A y u p.1.1 p.1.2 p.2) := by
  have hx : Measurable (fun p : (Real × Real) × Real =>
      fourFiveRealLogCoordinate y p.1.1) :=
    (measurable_fourFiveRealLogCoordinate y).comp
      (measurable_fst.comp measurable_fst)
  have hz : Measurable (fun p : (Real × Real) × Real =>
      fourFiveRealLogCoordinate y p.1.2) :=
    (measurable_fourFiveRealLogCoordinate y).comp
      (measurable_snd.comp measurable_fst)
  have hw : Measurable (fun p : (Real × Real) × Real =>
      fourFiveRealLogCoordinate y p.2) :=
    (measurable_fourFiveRealLogCoordinate y).comp measurable_snd
  have hactive : MeasurableSet {p : (Real × Real) × Real |
      (A : Real) < p.1.1 ∧ (A : Real) < p.1.2 ∧
        (A : Real) < p.2 ∧
        fourFiveRealLogCoordinate y p.1.1 +
          fourFiveRealLogCoordinate y p.1.2 +
            fourFiveRealLogCoordinate y p.2 < u - 1} :=
    ((measurable_fst.comp measurable_fst) measurableSet_Ioi).inter
      (((measurable_snd.comp measurable_fst) measurableSet_Ioi).inter
        ((measurable_snd measurableSet_Ioi).inter
          (((hx.add hz).add hw) measurableSet_Iio)))
  have hrecip : Measurable (fun p : (Real × Real) × Real =>
      (u - fourFiveRealLogCoordinate y p.1.1 -
        fourFiveRealLogCoordinate y p.1.2 -
          fourFiveRealLogCoordinate y p.2)⁻¹) :=
    (((measurable_const.sub hx).sub hz).sub hw).inv
  unfold fourFiveRealMovingSimplexKernelThree
  exact Measurable.ite hactive hrecip measurable_const

private def fourFiveRealMovingSimplexDensityThree
    (A y : Nat) (u : Real) (p : (Real × Real) × Real) : Real :=
  fourFiveLogLogLebesgueDensity p.1.1 *
    fourFiveLogLogLebesgueDensity p.1.2 *
      fourFiveLogLogLebesgueDensity p.2 *
        fourFiveRealMovingSimplexKernelThree A y u p.1.1 p.1.2 p.2

private theorem integrable_fourFiveRealMovingSimplexDensityThree_cell
    {A Y y p q r : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y)
    (hr : r ∈ Finset.Ioc A Y) :
    let mu := volume.restrict
      (Set.Ioc (((p - 1 : Nat) : Real)) (p : Real))
    let nu := volume.restrict
      (Set.Ioc (((q - 1 : Nat) : Real)) (q : Real))
    let xi := volume.restrict
      (Set.Ioc (((r - 1 : Nat) : Real)) (r : Real))
    Integrable (fourFiveRealMovingSimplexDensityThree A y u)
      ((mu.prod nu).prod xi) := by
  dsimp only
  let mu : Measure Real := volume.restrict
    (Set.Ioc (((p - 1 : Nat) : Real)) (p : Real))
  let nu : Measure Real := volume.restrict
    (Set.Ioc (((q - 1 : Nat) : Real)) (q : Real))
  let xi : Measure Real := volume.restrict
    (Set.Ioc (((r - 1 : Nat) : Real)) (r : Real))
  let delta := fourFiveLogLogCellMeshBound A
  have hA : 2 <= A := hy.trans hyA
  have hdelta : 0 <= delta := (fourFiveLogLogCellMeshBound_pos hA).le
  have hmeas : Measurable
      (fourFiveRealMovingSimplexDensityThree A y u) := by
    unfold fourFiveRealMovingSimplexDensityThree
    exact (((measurable_fourFiveLogLogLebesgueDensity.comp
      (measurable_fst.comp measurable_fst)).mul
        (measurable_fourFiveLogLogLebesgueDensity.comp
          (measurable_snd.comp measurable_fst))).mul
            (measurable_fourFiveLogLogLebesgueDensity.comp measurable_snd)).mul
      (measurable_fourFiveRealMovingSimplexKernelThree A y u)
  have hconst : Integrable
      (fun _ : (Real × Real) × Real => delta ^ 3)
      ((mu.prod nu).prod xi) := integrable_const _
  have hbound : ∀ᵐ s ∂((mu.prod nu).prod xi),
      ‖fourFiveRealMovingSimplexDensityThree A y u s‖ <= delta ^ 3 := by
    simp only [mu, nu, xi, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem
      ((measurableSet_Ioc.prod measurableSet_Ioc).prod measurableSet_Ioc)]
      with s hs
    rcases s with ⟨⟨x, z⟩, w⟩
    rcases hs with ⟨⟨hx, hz⟩, hw⟩
    have hdx := fourFiveLogLogLebesgueDensity_le_meshBound hA
      (Finset.mem_Ioc.mp hp).1 (Set.Ioc_subset_Icc_self hx)
    have hdz := fourFiveLogLogLebesgueDensity_le_meshBound hA
      (Finset.mem_Ioc.mp hq).1 (Set.Ioc_subset_Icc_self hz)
    have hdw := fourFiveLogLogLebesgueDensity_le_meshBound hA
      (Finset.mem_Ioc.mp hr).1 (Set.Ioc_subset_Icc_self hw)
    have hK := fourFiveRealMovingSimplexKernelThree_nonneg_le_one
      (A := A) (y := y) (u := u) (x := x) (z := z) (w := w)
    rw [fourFiveRealMovingSimplexDensityThree, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_mul, abs_of_nonneg hdx.1,
      abs_of_nonneg hdz.1, abs_of_nonneg hdw.1,
      abs_of_nonneg hK.1, pow_succ, pow_two]
    have hxyz :
        fourFiveLogLogLebesgueDensity x *
            fourFiveLogLogLebesgueDensity z *
              fourFiveLogLogLebesgueDensity w <=
          delta * delta * delta :=
      mul_le_mul
        (mul_le_mul hdx.2 hdz.2 hdz.1 hdelta)
        hdw.2 hdw.1 (mul_nonneg hdelta hdelta)
    have hall :
        fourFiveLogLogLebesgueDensity x *
              fourFiveLogLogLebesgueDensity z *
                fourFiveLogLogLebesgueDensity w *
            fourFiveRealMovingSimplexKernelThree A y u x z w <=
          (delta * delta * delta) * 1 :=
      mul_le_mul hxyz hK.2 hK.1
        (mul_nonneg (mul_nonneg hdelta hdelta) hdelta)
    simpa only [mul_one] using hall
  exact hconst.mono' hmeas.aestronglyMeasurable hbound

private theorem intervalIntegrable_fourFiveRealMovingSimplexThree_partial_cell
    {A Y y p q r : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y)
    (hr : r ∈ Finset.Ioc A Y) :
    IntervalIntegrable
      (fun x : Real => fourFiveLogLogLebesgueDensity x *
        (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w)))
      volume (((p - 1 : Nat) : Real)) (p : Real) := by
  have hporder : (((p - 1 : Nat) : Real)) <= (p : Real) := by
    exact_mod_cast Nat.sub_le p 1
  have hqorder : (((q - 1 : Nat) : Real)) <= (q : Real) := by
    exact_mod_cast Nat.sub_le q 1
  have hrorder : (((r - 1 : Nat) : Real)) <= (r : Real) := by
    exact_mod_cast Nat.sub_le r 1
  let mu : Measure Real := volume.restrict
    (Set.Ioc (((p - 1 : Nat) : Real)) (p : Real))
  let nu : Measure Real := volume.restrict
    (Set.Ioc (((q - 1 : Nat) : Real)) (q : Real))
  let xi : Measure Real := volume.restrict
    (Set.Ioc (((r - 1 : Nat) : Real)) (r : Real))
  have hjoint := integrable_fourFiveRealMovingSimplexDensityThree_cell
    (u := u) hy hyA hp hq hr
  have hpartialXZ := hjoint.integral_prod_left
  have hpartialX := hpartialXZ.integral_prod_left
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hporder]
  simpa [mu, nu, xi, intervalIntegral.integral_of_le hqorder,
    intervalIntegral.integral_of_le hrorder,
    fourFiveRealMovingSimplexDensityThree,
    MeasureTheory.integral_const_mul, mul_assoc] using hpartialX

theorem fourFiveMovingSimplexTwoIntegratedHybridThree_eq_explicit
    {A Y y : Nat} {u : Real} :
    fourFiveMovingSimplexTwoIntegratedHybridThree A Y y u =
      ∑ r ∈ Finset.Ioc A Y,
        fourFiveLogLogLebesgueCellAtom r *
          (∑ p ∈ Finset.Ioc A Y,
            ∑ q ∈ Finset.Ioc A Y,
              ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                fourFiveLogLogLebesgueDensity x *
                  (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                    fourFiveLogLogLebesgueDensity z *
                      fourFiveRealMovingSimplexKernelThree A y u
                        x z (r : Real))) := by
  unfold fourFiveMovingSimplexTwoIntegratedHybridThree
    fourFiveMovingSimplexIteratedRealCellProductTwo
  apply Finset.sum_congr rfl
  intro r hr
  apply congrArg (fun v : Real => fourFiveLogLogLebesgueCellAtom r * v)
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro q _hq
  apply intervalIntegral.integral_congr
  intro x _hx
  apply congrArg (fun v : Real => fourFiveLogLogLebesgueDensity x * v)
  apply intervalIntegral.integral_congr
  intro z _hz
  have hrA : (A : Real) < (r : Real) := by
    exact_mod_cast (Finset.mem_Ioc.mp hr).1
  apply congrArg (fun v : Real => fourFiveLogLogLebesgueDensity z * v)
  simpa only [fourFiveRealLogCoordinate_natCast] using
    (fourFiveRealMovingSimplexKernelThree_eq_two_shift
      (A := A) (y := y) (u := u) (x := x) (z := z)
      (w := (r : Real)) hrA).symm

private theorem fourFiveThree_lastCellDefect_pointwise
    {A Y y p q r : Nat} {u x z : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y)
    (hr : r ∈ Finset.Ioc A Y)
    (hx : x ∈ Set.uIoc (((p - 1 : Nat) : Real)) (p : Real))
    (hz : z ∈ Set.uIoc (((q - 1 : Nat) : Real)) (q : Real)) :
    fourFiveLogLogLebesgueCellAtom r *
          fourFiveRealMovingSimplexKernelThree A y u x z (r : Real) -
        (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
          fourFiveLogLogLebesgueDensity w *
            fourFiveRealMovingSimplexKernelThree A y u x z w) =
      fourFiveMovingFaceLebesgueCellDefect A Y y u
        (fourFiveRealLogCoordinate y x +
          fourFiveRealLogCoordinate y z) r := by
  have hporder : (((p - 1 : Nat) : Real)) <= (p : Real) := by
    exact_mod_cast Nat.sub_le p 1
  have hqorder : (((q - 1 : Nat) : Real)) <= (q : Real) := by
    exact_mod_cast Nat.sub_le q 1
  have hxIoc : x ∈ Set.Ioc (((p - 1 : Nat) : Real)) (p : Real) := by
    simpa [Set.uIoc_of_le hporder] using hx
  have hzIoc : z ∈ Set.Ioc (((q - 1 : Nat) : Real)) (q : Real) := by
    simpa [Set.uIoc_of_le hqorder] using hz
  have hApred : A <= p - 1 := by
    have := (Finset.mem_Ioc.mp hp).1
    omega
  have hAqpred : A <= q - 1 := by
    have := (Finset.mem_Ioc.mp hq).1
    omega
  have hxA : (A : Real) < x :=
    (by exact_mod_cast hApred :
      (A : Real) <= ((p - 1 : Nat) : Real)).trans_lt hxIoc.1
  have hzA : (A : Real) < z :=
    (by exact_mod_cast hAqpred :
      (A : Real) <= ((q - 1 : Nat) : Real)).trans_lt hzIoc.1
  have hsample :
      fourFiveRealMovingSimplexKernelThree A y u x z (r : Real) =
        fourFiveMovingFaceKernel A y u
          (fourFiveRealLogCoordinate y x +
            fourFiveRealLogCoordinate y z) r := by
    calc
      fourFiveRealMovingSimplexKernelThree A y u x z (r : Real) =
          fourFiveRealMovingFaceKernel A y u
            (fourFiveRealLogCoordinate y x +
              fourFiveRealLogCoordinate y z) (r : Real) :=
        fourFiveRealMovingSimplexKernelThree_eq_face_third hxA hzA
      _ = fourFiveMovingFaceKernel A y u
            (fourFiveRealLogCoordinate y x +
              fourFiveRealLogCoordinate y z) r :=
        fourFiveRealMovingFaceKernel_natCast
  have hintegral :
      (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
        fourFiveLogLogLebesgueDensity w *
          fourFiveRealMovingSimplexKernelThree A y u x z w) =
        ∫ w in (((r - 1 : Nat) : Real))..(r : Real),
          fourFiveLogLogLebesgueDensity w *
            fourFiveRealMovingFaceKernel A y u
              (fourFiveRealLogCoordinate y x +
                fourFiveRealLogCoordinate y z) w := by
    apply intervalIntegral.integral_congr
    intro w _hw
    apply congrArg (fun v : Real => fourFiveLogLogLebesgueDensity w * v)
    exact fourFiveRealMovingSimplexKernelThree_eq_face_third hxA hzA
  rw [hsample, hintegral]
  exact fourFiveLebesgueCell_sample_sub_real_eq_defect hy hyA hr

private theorem intervalIntegrable_fourFiveThree_lastCellSample_inner
    {A Y y p q r : Nat} {u x : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y)
    (hr : r ∈ Finset.Ioc A Y)
    (hx : x ∈ Set.uIoc (((p - 1 : Nat) : Real)) (p : Real)) :
    IntervalIntegrable
      (fun z : Real => fourFiveLogLogLebesgueDensity z *
        (fourFiveLogLogLebesgueCellAtom r *
          fourFiveRealMovingSimplexKernelThree A y u x z (r : Real)))
      volume (((q - 1 : Nat) : Real)) (q : Real) := by
  have hporder : (((p - 1 : Nat) : Real)) <= (p : Real) := by
    exact_mod_cast Nat.sub_le p 1
  have hxIoc : x ∈ Set.Ioc (((p - 1 : Nat) : Real)) (p : Real) := by
    simpa [Set.uIoc_of_le hporder] using hx
  have hApred : A <= p - 1 := by
    have := (Finset.mem_Ioc.mp hp).1
    omega
  have hxA : (A : Real) < x :=
    (by exact_mod_cast hApred :
      (A : Real) <= ((p - 1 : Nat) : Real)).trans_lt hxIoc.1
  have hrA : (A : Real) < (r : Real) := by
    exact_mod_cast (Finset.mem_Ioc.mp hr).1
  have hleftBase := intervalIntegrable_fourFiveDensity_mul_realMovingFace_cell
    (u := u) (c := fourFiveRealLogCoordinate y x +
      fourFiveLogCoordinate y r) hy hyA hq
  apply (hleftBase.const_mul
    (fourFiveLogLogLebesgueCellAtom r)).congr
  intro z hz
  have hzIoc : z ∈ Set.Ioc (((q - 1 : Nat) : Real)) (q : Real) := by
    simpa [Set.uIoc_of_le
      (by exact_mod_cast Nat.sub_le q 1)] using hz
  have hAqpred : A <= q - 1 := by
    have := (Finset.mem_Ioc.mp hq).1
    omega
  have hzA : (A : Real) < z :=
    (by exact_mod_cast hAqpred :
      (A : Real) <= ((q - 1 : Nat) : Real)).trans_lt hzIoc.1
  have hkernel :
      fourFiveRealMovingSimplexKernelThree A y u x z (r : Real) =
        fourFiveRealMovingFaceKernel A y u
          (fourFiveRealLogCoordinate y x +
            fourFiveLogCoordinate y r) z := by
    calc
      fourFiveRealMovingSimplexKernelThree A y u x z (r : Real) =
          fourFiveRealMovingSimplexKernelTwo A y
            (u - fourFiveRealLogCoordinate y (r : Real)) x z :=
        fourFiveRealMovingSimplexKernelThree_eq_two_shift hrA
      _ = fourFiveRealMovingSimplexKernelTwo A y
            (u - fourFiveLogCoordinate y r) x z := by
        rw [fourFiveRealLogCoordinate_natCast]
      _ = fourFiveRealMovingFaceKernel A y
            (u - fourFiveLogCoordinate y r)
            (fourFiveRealLogCoordinate y x) z :=
        fourFiveRealMovingSimplexKernelTwo_eq_face_second hxA
      _ = fourFiveRealMovingFaceKernel A y u
            (fourFiveRealLogCoordinate y x +
              fourFiveLogCoordinate y r) z :=
        fourFiveRealMovingFaceKernel_shift A y u
          (fourFiveRealLogCoordinate y x)
          (fourFiveLogCoordinate y r) z
  calc
    _ = fourFiveLogLogLebesgueDensity z *
        (fourFiveLogLogLebesgueCellAtom r *
          fourFiveRealMovingFaceKernel A y u
            (fourFiveRealLogCoordinate y x +
              fourFiveLogCoordinate y r) z) := by
      ring
    _ = _ := congrArg
      (fun v : Real => fourFiveLogLogLebesgueDensity z *
        (fourFiveLogLogLebesgueCellAtom r * v)) hkernel.symm

private theorem intervalIntegrable_fourFiveThree_lastCellReal_inner
    {A Y y p q r : Nat} {u x : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y)
    (hr : r ∈ Finset.Ioc A Y)
    (hx : x ∈ Set.uIoc (((p - 1 : Nat) : Real)) (p : Real)) :
    IntervalIntegrable
      (fun z : Real => fourFiveLogLogLebesgueDensity z *
        (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
          fourFiveLogLogLebesgueDensity w *
            fourFiveRealMovingSimplexKernelThree A y u x z w))
      volume (((q - 1 : Nat) : Real)) (q : Real) := by
  have hporder : (((p - 1 : Nat) : Real)) <= (p : Real) := by
    exact_mod_cast Nat.sub_le p 1
  have hxIoc : x ∈ Set.Ioc (((p - 1 : Nat) : Real)) (p : Real) := by
    simpa [Set.uIoc_of_le hporder] using hx
  have hApred : A <= p - 1 := by
    have := (Finset.mem_Ioc.mp hp).1
    omega
  have hxA : (A : Real) < x :=
    (by exact_mod_cast hApred :
      (A : Real) <= ((p - 1 : Nat) : Real)).trans_lt hxIoc.1
  have hright :=
    intervalIntegrable_fourFiveRealMovingSimplexTwo_partial_cell
      (u := u - fourFiveRealLogCoordinate y x) hy hyA hq hr
  apply hright.congr
  intro z _hz
  apply congrArg (fun v : Real => fourFiveLogLogLebesgueDensity z * v)
  apply intervalIntegral.integral_congr
  intro w _hw
  apply congrArg (fun v : Real => fourFiveLogLogLebesgueDensity w * v)
  exact
    (fourFiveRealMovingSimplexKernelThree_eq_two_shift_first
      (A := A) (y := y) (u := u) (x := x) (z := z) (w := w) hxA).symm

private theorem intervalIntegrable_fourFiveThree_lastCellDefect_inner
    {A Y y p q r : Nat} {u x : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y)
    (hr : r ∈ Finset.Ioc A Y)
    (hx : x ∈ Set.uIoc (((p - 1 : Nat) : Real)) (p : Real)) :
    IntervalIntegrable
      (fun z : Real => fourFiveLogLogLebesgueDensity z *
        fourFiveMovingFaceLebesgueCellDefect A Y y u
          (fourFiveRealLogCoordinate y x +
            fourFiveRealLogCoordinate y z) r)
      volume (((q - 1 : Nat) : Real)) (q : Real) := by
  have hsample := intervalIntegrable_fourFiveThree_lastCellSample_inner
    (u := u) hy hyA hp hq hr hx
  have hreal := intervalIntegrable_fourFiveThree_lastCellReal_inner
    (u := u) hy hyA hp hq hr hx
  apply (hsample.sub hreal).congr
  intro z hz
  calc
    _ = fourFiveLogLogLebesgueDensity z *
        (fourFiveLogLogLebesgueCellAtom r *
            fourFiveRealMovingSimplexKernelThree A y u x z (r : Real) -
          (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree A y u x z w)) := by
      ring
    _ = _ := congrArg
      (fun v : Real => fourFiveLogLogLebesgueDensity z * v)
      (fourFiveThree_lastCellDefect_pointwise
        (u := u) hy hyA hp hq hr hx hz)

private theorem fourFiveThree_lastCellDefect_inner_identity
    {A Y y p q r : Nat} {u x : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y)
    (hr : r ∈ Finset.Ioc A Y)
    (hx : x ∈ Set.uIoc (((p - 1 : Nat) : Real)) (p : Real)) :
    fourFiveLogLogLebesgueCellAtom r *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              fourFiveRealMovingSimplexKernelThree A y u x z (r : Real)) -
        (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w)) =
      ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
        fourFiveLogLogLebesgueDensity z *
          fourFiveMovingFaceLebesgueCellDefect A Y y u
            (fourFiveRealLogCoordinate y x +
              fourFiveRealLogCoordinate y z) r := by
  have hsample := intervalIntegrable_fourFiveThree_lastCellSample_inner
    (u := u) hy hyA hp hq hr hx
  have hreal := intervalIntegrable_fourFiveThree_lastCellReal_inner
    (u := u) hy hyA hp hq hr hx
  calc
    fourFiveLogLogLebesgueCellAtom r *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              fourFiveRealMovingSimplexKernelThree A y u x z (r : Real)) -
        (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w)) =
      (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            (fourFiveLogLogLebesgueCellAtom r *
              fourFiveRealMovingSimplexKernelThree A y u x z (r : Real))) -
        (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w)) := by
          congr 1
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro z _hz
          ring
    _ = ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          (fourFiveLogLogLebesgueDensity z *
              (fourFiveLogLogLebesgueCellAtom r *
                fourFiveRealMovingSimplexKernelThree A y u x z (r : Real)) -
            fourFiveLogLogLebesgueDensity z *
              (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                fourFiveLogLogLebesgueDensity w *
                  fourFiveRealMovingSimplexKernelThree A y u x z w)) :=
      (intervalIntegral.integral_sub hsample hreal).symm
    _ = ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
        fourFiveLogLogLebesgueDensity z *
          fourFiveMovingFaceLebesgueCellDefect A Y y u
            (fourFiveRealLogCoordinate y x +
              fourFiveRealLogCoordinate y z) r := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with z
      intro hz
      rw [← mul_sub]
      apply congrArg (fun v : Real => fourFiveLogLogLebesgueDensity z * v)
      exact fourFiveThree_lastCellDefect_pointwise
        (u := u) hy hyA hp hq hr hx hz

private theorem intervalIntegrable_fourFiveThree_lastCellSample_outer
    {A Y y p q r : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y)
    (hr : r ∈ Finset.Ioc A Y) :
    IntervalIntegrable
      (fun x : Real => fourFiveLogLogLebesgueDensity x *
        (fourFiveLogLogLebesgueCellAtom r *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              fourFiveRealMovingSimplexKernelThree A y u x z (r : Real))))
      volume (((p - 1 : Nat) : Real)) (p : Real) := by
  have hrA : (A : Real) < (r : Real) := by
    exact_mod_cast (Finset.mem_Ioc.mp hr).1
  have hbase :=
    intervalIntegrable_fourFiveRealMovingSimplexTwo_partial_cell
      (u := u - fourFiveLogCoordinate y r) hy hyA hp hq
  apply (hbase.const_mul
    (fourFiveLogLogLebesgueCellAtom r)).congr
  intro x _hx
  have hinner :
      (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
        fourFiveLogLogLebesgueDensity z *
          fourFiveRealMovingSimplexKernelTwo A y
            (u - fourFiveLogCoordinate y r) x z) =
        ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            fourFiveRealMovingSimplexKernelThree A y u x z (r : Real) := by
    apply intervalIntegral.integral_congr
    intro z _hz
    apply congrArg (fun v : Real =>
      fourFiveLogLogLebesgueDensity z * v)
    symm
    simpa only [fourFiveRealLogCoordinate_natCast] using
      (fourFiveRealMovingSimplexKernelThree_eq_two_shift
        (A := A) (y := y) (u := u) (x := x) (z := z)
        (w := (r : Real)) hrA)
  calc
    _ = fourFiveLogLogLebesgueDensity x *
        (fourFiveLogLogLebesgueCellAtom r *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              fourFiveRealMovingSimplexKernelTwo A y
                (u - fourFiveLogCoordinate y r) x z)) := by
      ring
    _ = _ := congrArg
      (fun v : Real => fourFiveLogLogLebesgueDensity x *
        (fourFiveLogLogLebesgueCellAtom r * v)) hinner

private theorem intervalIntegrable_fourFiveThree_lastCellDefect_outer
    {A Y y p q r : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y)
    (hr : r ∈ Finset.Ioc A Y) :
    IntervalIntegrable
      (fun x : Real => fourFiveLogLogLebesgueDensity x *
        (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            fourFiveMovingFaceLebesgueCellDefect A Y y u
              (fourFiveRealLogCoordinate y x +
                fourFiveRealLogCoordinate y z) r))
      volume (((p - 1 : Nat) : Real)) (p : Real) := by
  have hleft := intervalIntegrable_fourFiveThree_lastCellSample_outer
    (u := u) hy hyA hp hq hr
  have hright := intervalIntegrable_fourFiveRealMovingSimplexThree_partial_cell
    (u := u) hy hyA hp hq hr
  apply (hleft.sub hright).congr
  intro x hx
  calc
    _ = fourFiveLogLogLebesgueDensity x *
        (fourFiveLogLogLebesgueCellAtom r *
            (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
              fourFiveLogLogLebesgueDensity z *
                fourFiveRealMovingSimplexKernelThree A y u
                  x z (r : Real)) -
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                fourFiveLogLogLebesgueDensity w *
                  fourFiveRealMovingSimplexKernelThree A y u x z w))) := by
      ring
    _ = _ := congrArg
      (fun v : Real => fourFiveLogLogLebesgueDensity x * v)
      (fourFiveThree_lastCellDefect_inner_identity
        (u := u) hy hyA hp hq hr hx)

/-- Exact last-coordinate replacement on one literal three-dimensional
cell.  The right-endpoint sample and the triple integral differ by the
integrated one-dimensional conditional defect. -/
theorem fourFiveMovingSimplex_lastCellDefect_identity
    {A Y y p q r : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y)
    (hr : r ∈ Finset.Ioc A Y) :
    fourFiveLogLogLebesgueCellAtom r *
          (∫ x in (((p - 1 : Nat) : Real))..(p : Real),
            fourFiveLogLogLebesgueDensity x *
              (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  fourFiveRealMovingSimplexKernelThree A y u
                    x z (r : Real))) -
        (∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          fourFiveLogLogLebesgueDensity x *
            (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
              fourFiveLogLogLebesgueDensity z *
                (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                  fourFiveLogLogLebesgueDensity w *
                    fourFiveRealMovingSimplexKernelThree A y u x z w))) =
      ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
        fourFiveLogLogLebesgueDensity x *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              fourFiveMovingFaceLebesgueCellDefect A Y y u
                (fourFiveRealLogCoordinate y x +
                  fourFiveRealLogCoordinate y z) r) := by
  have hsample := intervalIntegrable_fourFiveThree_lastCellSample_outer
    (u := u) hy hyA hp hq hr
  have hreal := intervalIntegrable_fourFiveRealMovingSimplexThree_partial_cell
    (u := u) hy hyA hp hq hr
  calc
    fourFiveLogLogLebesgueCellAtom r *
          (∫ x in (((p - 1 : Nat) : Real))..(p : Real),
            fourFiveLogLogLebesgueDensity x *
              (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  fourFiveRealMovingSimplexKernelThree A y u
                    x z (r : Real))) -
        (∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          fourFiveLogLogLebesgueDensity x *
            (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
              fourFiveLogLogLebesgueDensity z *
                (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                  fourFiveLogLogLebesgueDensity w *
                    fourFiveRealMovingSimplexKernelThree A y u x z w))) =
      (∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          fourFiveLogLogLebesgueDensity x *
            (fourFiveLogLogLebesgueCellAtom r *
              (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  fourFiveRealMovingSimplexKernelThree A y u
                    x z (r : Real)))) -
        (∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          fourFiveLogLogLebesgueDensity x *
            (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
              fourFiveLogLogLebesgueDensity z *
                (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                  fourFiveLogLogLebesgueDensity w *
                    fourFiveRealMovingSimplexKernelThree A y u x z w))) := by
          congr 1
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro x _hx
          ring
    _ = ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          (fourFiveLogLogLebesgueDensity x *
              (fourFiveLogLogLebesgueCellAtom r *
                (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                  fourFiveLogLogLebesgueDensity z *
                    fourFiveRealMovingSimplexKernelThree A y u
                      x z (r : Real))) -
            fourFiveLogLogLebesgueDensity x *
              (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                    fourFiveLogLogLebesgueDensity w *
                      fourFiveRealMovingSimplexKernelThree A y u x z w))) :=
      (intervalIntegral.integral_sub hsample hreal).symm
    _ = ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
        fourFiveLogLogLebesgueDensity x *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              fourFiveMovingFaceLebesgueCellDefect A Y y u
                (fourFiveRealLogCoordinate y x +
                  fourFiveRealLogCoordinate y z) r) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x
      intro hx
      rw [← mul_sub]
      apply congrArg (fun v : Real => fourFiveLogLogLebesgueDensity x * v)
      exact fourFiveThree_lastCellDefect_inner_identity
        (u := u) hy hyA hp hq hr hx

private theorem fourFiveThree_sum_lastCellDefect_inner
    {A Y y p q : Nat} {u x : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y)
    (hx : x ∈ Set.uIoc (((p - 1 : Nat) : Real)) (p : Real)) :
    (∑ r ∈ Finset.Ioc A Y,
        ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            fourFiveMovingFaceLebesgueCellDefect A Y y u
              (fourFiveRealLogCoordinate y x +
                fourFiveRealLogCoordinate y z) r) =
      ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
        fourFiveLogLogLebesgueDensity z *
          fourFiveMovingFaceLebesgueCellDefectSum A Y y u
            (fourFiveRealLogCoordinate y x +
              fourFiveRealLogCoordinate y z) := by
  calc
    (∑ r ∈ Finset.Ioc A Y,
        ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            fourFiveMovingFaceLebesgueCellDefect A Y y u
              (fourFiveRealLogCoordinate y x +
                fourFiveRealLogCoordinate y z) r) =
      ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
        ∑ r ∈ Finset.Ioc A Y,
          fourFiveLogLogLebesgueDensity z *
            fourFiveMovingFaceLebesgueCellDefect A Y y u
              (fourFiveRealLogCoordinate y x +
                fourFiveRealLogCoordinate y z) r := by
          symm
          exact intervalIntegral.integral_finset_sum
            (fun r hr => intervalIntegrable_fourFiveThree_lastCellDefect_inner
              (u := u) hy hyA hp hq hr hx)
    _ = ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
        fourFiveLogLogLebesgueDensity z *
          fourFiveMovingFaceLebesgueCellDefectSum A Y y u
            (fourFiveRealLogCoordinate y x +
              fourFiveRealLogCoordinate y z) := by
      apply intervalIntegral.integral_congr
      intro z _hz
      unfold fourFiveMovingFaceLebesgueCellDefectSum
      exact
        (Finset.mul_sum (Finset.Ioc A Y)
          (fun r =>
            fourFiveMovingFaceLebesgueCellDefect A Y y u
              (fourFiveRealLogCoordinate y x +
                fourFiveRealLogCoordinate y z) r)
          (fourFiveLogLogLebesgueDensity z)).symm

private theorem fourFiveThree_sum_lastCellDefect_outer
    {A Y y p q : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y) :
    (∑ r ∈ Finset.Ioc A Y,
        ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          fourFiveLogLogLebesgueDensity x *
            (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
              fourFiveLogLogLebesgueDensity z *
                fourFiveMovingFaceLebesgueCellDefect A Y y u
                  (fourFiveRealLogCoordinate y x +
                    fourFiveRealLogCoordinate y z) r)) =
      ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
        fourFiveLogLogLebesgueDensity x *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              fourFiveMovingFaceLebesgueCellDefectSum A Y y u
                (fourFiveRealLogCoordinate y x +
                  fourFiveRealLogCoordinate y z)) := by
  calc
    (∑ r ∈ Finset.Ioc A Y,
        ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          fourFiveLogLogLebesgueDensity x *
            (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
              fourFiveLogLogLebesgueDensity z *
                fourFiveMovingFaceLebesgueCellDefect A Y y u
                  (fourFiveRealLogCoordinate y x +
                    fourFiveRealLogCoordinate y z) r)) =
      ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
        ∑ r ∈ Finset.Ioc A Y,
          fourFiveLogLogLebesgueDensity x *
            (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
              fourFiveLogLogLebesgueDensity z *
                fourFiveMovingFaceLebesgueCellDefect A Y y u
                  (fourFiveRealLogCoordinate y x +
                    fourFiveRealLogCoordinate y z) r) := by
          symm
          exact intervalIntegral.integral_finset_sum
            (fun r hr => intervalIntegrable_fourFiveThree_lastCellDefect_outer
              (u := u) hy hyA hp hq hr)
    _ = ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
        fourFiveLogLogLebesgueDensity x *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              fourFiveMovingFaceLebesgueCellDefectSum A Y y u
                (fourFiveRealLogCoordinate y x +
                  fourFiveRealLogCoordinate y z)) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x
      intro hx
      calc
        (∑ r ∈ Finset.Ioc A Y,
            fourFiveLogLogLebesgueDensity x *
              (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  fourFiveMovingFaceLebesgueCellDefect A Y y u
                    (fourFiveRealLogCoordinate y x +
                      fourFiveRealLogCoordinate y z) r)) =
          fourFiveLogLogLebesgueDensity x *
            (∑ r ∈ Finset.Ioc A Y,
              ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  fourFiveMovingFaceLebesgueCellDefect A Y y u
                    (fourFiveRealLogCoordinate y x +
                      fourFiveRealLogCoordinate y z) r) := by
            exact
              (Finset.mul_sum (Finset.Ioc A Y)
                (fun r =>
                  ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                    fourFiveLogLogLebesgueDensity z *
                      fourFiveMovingFaceLebesgueCellDefect A Y y u
                        (fourFiveRealLogCoordinate y x +
                          fourFiveRealLogCoordinate y z) r)
                (fourFiveLogLogLebesgueDensity x)).symm
        _ = fourFiveLogLogLebesgueDensity x *
            (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
              fourFiveLogLogLebesgueDensity z *
                fourFiveMovingFaceLebesgueCellDefectSum A Y y u
                  (fourFiveRealLogCoordinate y x +
                    fourFiveRealLogCoordinate y z)) := by
          apply congrArg
            (fun v : Real => fourFiveLogLogLebesgueDensity x * v)
          exact fourFiveThree_sum_lastCellDefect_inner
            (u := u) hy hyA hp hq hx

private theorem intervalIntegrable_fourFiveThree_lastCellDefectSum_outer
    {A Y y p q : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y) :
    IntervalIntegrable
      (fun x : Real => fourFiveLogLogLebesgueDensity x *
        (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            fourFiveMovingFaceLebesgueCellDefectSum A Y y u
              (fourFiveRealLogCoordinate y x +
                fourFiveRealLogCoordinate y z)))
      volume (((p - 1 : Nat) : Real)) (p : Real) := by
  have hsum : IntervalIntegrable
      (∑ r ∈ Finset.Ioc A Y,
        fun x : Real => fourFiveLogLogLebesgueDensity x *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              fourFiveMovingFaceLebesgueCellDefect A Y y u
                (fourFiveRealLogCoordinate y x +
                  fourFiveRealLogCoordinate y z) r))
      volume (((p - 1 : Nat) : Real)) (p : Real) :=
    IntervalIntegrable.sum (Finset.Ioc A Y)
      (fun r hr => intervalIntegrable_fourFiveThree_lastCellDefect_outer
        (u := u) hy hyA hp hq hr)
  apply hsum.congr
  intro x hx
  simp only [Finset.sum_apply]
  calc
    (∑ r ∈ Finset.Ioc A Y,
        fourFiveLogLogLebesgueDensity x *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              fourFiveMovingFaceLebesgueCellDefect A Y y u
                (fourFiveRealLogCoordinate y x +
                  fourFiveRealLogCoordinate y z) r)) =
      fourFiveLogLogLebesgueDensity x *
        (∑ r ∈ Finset.Ioc A Y,
          ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              fourFiveMovingFaceLebesgueCellDefect A Y y u
                (fourFiveRealLogCoordinate y x +
                  fourFiveRealLogCoordinate y z) r) := by
        exact
          (Finset.mul_sum (Finset.Ioc A Y)
            (fun r =>
              ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  fourFiveMovingFaceLebesgueCellDefect A Y y u
                    (fourFiveRealLogCoordinate y x +
                      fourFiveRealLogCoordinate y z) r)
            (fourFiveLogLogLebesgueDensity x)).symm
    _ = fourFiveLogLogLebesgueDensity x *
        (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            fourFiveMovingFaceLebesgueCellDefectSum A Y y u
              (fourFiveRealLogCoordinate y x +
                fourFiveRealLogCoordinate y z)) := by
      apply congrArg
        (fun v : Real => fourFiveLogLogLebesgueDensity x * v)
      exact fourFiveThree_sum_lastCellDefect_inner
        (u := u) hy hyA hp hq hx

/-- Exact last-coordinate part of the three-dimensional hybrid.  All
sum/integral interchanges are finite and are justified cell by cell. -/
theorem fourFiveMovingSimplexTwoIntegratedHybridThree_sub_iterated
    {A Y y : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A) :
    fourFiveMovingSimplexTwoIntegratedHybridThree A Y y u -
        fourFiveMovingSimplexIteratedRealCellProductThree A Y y u =
      ∑ p ∈ Finset.Ioc A Y,
        ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          fourFiveLogLogLebesgueDensity x *
            (∑ q ∈ Finset.Ioc A Y,
              ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  fourFiveMovingFaceLebesgueCellDefectSum A Y y u
                    (fourFiveRealLogCoordinate y x +
                      fourFiveRealLogCoordinate y z)) := by
  rw [fourFiveMovingSimplexTwoIntegratedHybridThree_eq_explicit]
  unfold fourFiveMovingSimplexIteratedRealCellProductThree
  calc
    (∑ r ∈ Finset.Ioc A Y,
          fourFiveLogLogLebesgueCellAtom r *
            (∑ p ∈ Finset.Ioc A Y,
              ∑ q ∈ Finset.Ioc A Y,
                ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                  fourFiveLogLogLebesgueDensity x *
                    (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                      fourFiveLogLogLebesgueDensity z *
                        fourFiveRealMovingSimplexKernelThree A y u
                          x z (r : Real)))) -
        ∑ p ∈ Finset.Ioc A Y,
          ∑ q ∈ Finset.Ioc A Y,
            ∑ r ∈ Finset.Ioc A Y,
              ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                fourFiveLogLogLebesgueDensity x *
                  (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                    fourFiveLogLogLebesgueDensity z *
                      (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                        fourFiveLogLogLebesgueDensity w *
                          fourFiveRealMovingSimplexKernelThree A y u x z w)) =
      (∑ p ∈ Finset.Ioc A Y,
        ∑ q ∈ Finset.Ioc A Y,
          ∑ r ∈ Finset.Ioc A Y,
            fourFiveLogLogLebesgueCellAtom r *
              (∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                fourFiveLogLogLebesgueDensity x *
                  (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                    fourFiveLogLogLebesgueDensity z *
                      fourFiveRealMovingSimplexKernelThree A y u
                        x z (r : Real)))) -
        ∑ p ∈ Finset.Ioc A Y,
          ∑ q ∈ Finset.Ioc A Y,
            ∑ r ∈ Finset.Ioc A Y,
              ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                fourFiveLogLogLebesgueDensity x *
                  (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                    fourFiveLogLogLebesgueDensity z *
                      (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                        fourFiveLogLogLebesgueDensity w *
                          fourFiveRealMovingSimplexKernelThree A y u x z w)) := by
          congr 1
          calc
            (∑ r ∈ Finset.Ioc A Y,
                fourFiveLogLogLebesgueCellAtom r *
                  (∑ p ∈ Finset.Ioc A Y,
                    ∑ q ∈ Finset.Ioc A Y,
                      ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                        fourFiveLogLogLebesgueDensity x *
                          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                            fourFiveLogLogLebesgueDensity z *
                              fourFiveRealMovingSimplexKernelThree A y u
                                x z (r : Real)))) =
              ∑ r ∈ Finset.Ioc A Y,
                ∑ p ∈ Finset.Ioc A Y,
                  ∑ q ∈ Finset.Ioc A Y,
                    fourFiveLogLogLebesgueCellAtom r *
                      (∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                        fourFiveLogLogLebesgueDensity x *
                          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                            fourFiveLogLogLebesgueDensity z *
                              fourFiveRealMovingSimplexKernelThree A y u
                                x z (r : Real))) := by
                  apply Finset.sum_congr rfl
                  intro r _hr
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro p _hp
                  rw [Finset.mul_sum]
            _ = ∑ p ∈ Finset.Ioc A Y,
                ∑ q ∈ Finset.Ioc A Y,
                  ∑ r ∈ Finset.Ioc A Y,
                    fourFiveLogLogLebesgueCellAtom r *
                      (∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                        fourFiveLogLogLebesgueDensity x *
                          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                            fourFiveLogLogLebesgueDensity z *
                              fourFiveRealMovingSimplexKernelThree A y u
                                x z (r : Real))) := by
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro p _hp
                  rw [Finset.sum_comm]
    _ = ∑ p ∈ Finset.Ioc A Y,
        ∑ q ∈ Finset.Ioc A Y,
          ∑ r ∈ Finset.Ioc A Y,
            (fourFiveLogLogLebesgueCellAtom r *
                (∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                  fourFiveLogLogLebesgueDensity x *
                    (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                      fourFiveLogLogLebesgueDensity z *
                        fourFiveRealMovingSimplexKernelThree A y u
                          x z (r : Real))) -
              ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                fourFiveLogLogLebesgueDensity x *
                  (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                    fourFiveLogLogLebesgueDensity z *
                      (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                        fourFiveLogLogLebesgueDensity w *
                          fourFiveRealMovingSimplexKernelThree A y u x z w))) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro p _hp
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro q _hq
          rw [← Finset.sum_sub_distrib]
    _ = ∑ p ∈ Finset.Ioc A Y,
        ∑ q ∈ Finset.Ioc A Y,
          ∑ r ∈ Finset.Ioc A Y,
            ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
              fourFiveLogLogLebesgueDensity x *
                (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                  fourFiveLogLogLebesgueDensity z *
                    fourFiveMovingFaceLebesgueCellDefect A Y y u
                      (fourFiveRealLogCoordinate y x +
                        fourFiveRealLogCoordinate y z) r) := by
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro q hq
          apply Finset.sum_congr rfl
          intro r hr
          exact fourFiveMovingSimplex_lastCellDefect_identity
            hy hyA hp hq hr
    _ = ∑ p ∈ Finset.Ioc A Y,
        ∑ q ∈ Finset.Ioc A Y,
          ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
            fourFiveLogLogLebesgueDensity x *
              (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  fourFiveMovingFaceLebesgueCellDefectSum A Y y u
                    (fourFiveRealLogCoordinate y x +
                      fourFiveRealLogCoordinate y z)) := by
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro q hq
          exact fourFiveThree_sum_lastCellDefect_outer hy hyA hp hq
    _ = ∑ p ∈ Finset.Ioc A Y,
        ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          fourFiveLogLogLebesgueDensity x *
            (∑ q ∈ Finset.Ioc A Y,
              ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  fourFiveMovingFaceLebesgueCellDefectSum A Y y u
                    (fourFiveRealLogCoordinate y x +
                      fourFiveRealLogCoordinate y z)) := by
          apply Finset.sum_congr rfl
          intro p hp
          calc
            (∑ q ∈ Finset.Ioc A Y,
                ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                  fourFiveLogLogLebesgueDensity x *
                    (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                      fourFiveLogLogLebesgueDensity z *
                        fourFiveMovingFaceLebesgueCellDefectSum A Y y u
                          (fourFiveRealLogCoordinate y x +
                            fourFiveRealLogCoordinate y z))) =
              ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                ∑ q ∈ Finset.Ioc A Y,
                  fourFiveLogLogLebesgueDensity x *
                    (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                      fourFiveLogLogLebesgueDensity z *
                        fourFiveMovingFaceLebesgueCellDefectSum A Y y u
                          (fourFiveRealLogCoordinate y x +
                            fourFiveRealLogCoordinate y z)) := by
                  symm
                  exact intervalIntegral.integral_finset_sum
                    (fun q hq =>
                      intervalIntegrable_fourFiveThree_lastCellDefectSum_outer
                        hy hyA hp hq)
            _ = ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
                fourFiveLogLogLebesgueDensity x *
                  (∑ q ∈ Finset.Ioc A Y,
                    ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                      fourFiveLogLogLebesgueDensity z *
                        fourFiveMovingFaceLebesgueCellDefectSum A Y y u
                          (fourFiveRealLogCoordinate y x +
                            fourFiveRealLogCoordinate y z)) := by
                  apply intervalIntegral.integral_congr
                  intro x _hx
                  simp only [Finset.mul_sum]

/-- Exact three-coordinate finite-cell telescope in the order naturally
produced by the final-coordinate hybrid. -/
theorem fourFiveMovingSimplexRightEndpointProductThree_sub_iterated_eq_telescope
    {A Y y : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A) :
    fourFiveMovingSimplexRightEndpointProductThree A Y y u -
        fourFiveMovingSimplexIteratedRealCellProductThree A Y y u =
      fourFiveLogLogCellTelescopeThreeRightOrdered
        (fourFiveMovingFaceLebesgueCellDefectSum A Y y u) A Y y := by
  rw [show fourFiveMovingSimplexRightEndpointProductThree A Y y u -
      fourFiveMovingSimplexIteratedRealCellProductThree A Y y u =
      (fourFiveMovingSimplexRightEndpointProductThree A Y y u -
        fourFiveMovingSimplexTwoIntegratedHybridThree A Y y u) +
      (fourFiveMovingSimplexTwoIntegratedHybridThree A Y y u -
        fourFiveMovingSimplexIteratedRealCellProductThree A Y y u) by ring,
    fourFiveMovingSimplexRightEndpointProductThree_sub_twoIntegrated hy hyA,
    fourFiveMovingSimplexTwoIntegratedHybridThree_sub_iterated hy hyA]
  rfl

/-- Quantitative three-coordinate consequence of the exact hybrid identity.
The constant is the preserved split budget
`3 delta_A M^2 + 3 delta_A M^2 = 6 delta_A M^2`. -/
theorem abs_fourFiveMovingSimplexRightEndpointProductThree_sub_iterated_le
    {A Y y : Nat} {u M : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hmass : (∑ n ∈ Finset.Ioc A Y,
      |fourFiveLogLogLebesgueCellAtom n|) <= M) :
    |fourFiveMovingSimplexRightEndpointProductThree A Y y u -
        fourFiveMovingSimplexIteratedRealCellProductThree A Y y u| <=
      6 * fourFiveLogLogCellMeshBound A * M ^ 2 := by
  rw [fourFiveMovingSimplexRightEndpointProductThree_sub_iterated_eq_telescope
    hy hyA]
  have h := abs_fourFiveLogLogCellTelescopeThreeRightOrdered_le
    (D := fourFiveMovingFaceLebesgueCellDefectSum A Y y u)
    (A := A) (Y := Y) (y := y)
    (M := M) (R := 2 * fourFiveLogLogCellMeshBound A)
    (hy.trans hyA) hAY
    (mul_nonneg (by norm_num)
      (fourFiveLogLogCellMeshBound_pos (hy.trans hyA)).le)
    hmass (fun c =>
      abs_fourFiveMovingFaceLebesgueCellDefectSum_le hy hyA hAY)
  exact h.trans_eq (by ring)

/-! ## Exact union of the active physical cells -/

private theorem sum_fourFiveUnitCellIntegrals_eq_interval
    {A Y : Nat} {f : Real -> Real} (hAY : A <= Y)
    (hint : ∀ n ∈ Finset.Ioc A Y,
      IntervalIntegrable f volume
        (((n - 1 : Nat) : Real)) (n : Real)) :
    (∑ n ∈ Finset.Ioc A Y,
        ∫ x in (((n - 1 : Nat) : Real))..(n : Real), f x) =
      ∫ x in (A : Real)..(Y : Real), f x := by
  rw [Erdos390.Full.FriableAsymptotic.sum_Ioc_shift]
  have h := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (f := f) (μ := volume) (a := fun k : Nat => (k : Real)) hAY
    (fun k hk => by
      have hn : k + 1 ∈ Finset.Ioc A Y := by
        simpa [Finset.mem_Ico, Finset.mem_Ioc] using hk
      simpa [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using
        hint (k + 1) hn)
  simpa [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using h

/-- The finite union of one-dimensional paper cells is the single physical
interval `(A,Y]`; this is an exact adjacent-interval identity. -/
theorem fourFiveMovingFaceRealCellIntegralSum_eq_interval
    {A Y y : Nat} {u c : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y) :
    fourFiveMovingFaceRealCellIntegralSum A Y y u c =
      ∫ x in (A : Real)..(Y : Real),
        fourFiveLogLogLebesgueDensity x *
          fourFiveRealMovingFaceKernel A y u c x := by
  unfold fourFiveMovingFaceRealCellIntegralSum
  exact sum_fourFiveUnitCellIntegrals_eq_interval hAY
    (fun n hn => intervalIntegrable_fourFiveDensity_mul_realMovingFace_cell
      hy hyA hn)

def fourFiveMovingSimplexActivePhysicalIntegralTwo
    (A Y y : Nat) (u : Real) : Real :=
  ∫ x in (A : Real)..(Y : Real),
    fourFiveLogLogLebesgueDensity x *
      (∫ z in (A : Real)..(Y : Real),
        fourFiveLogLogLebesgueDensity z *
          fourFiveRealMovingSimplexKernelTwo A y u x z)

def fourFiveMovingSimplexActivePhysicalIntegralThree
    (A Y y : Nat) (u : Real) : Real :=
  ∫ x in (A : Real)..(Y : Real),
    fourFiveLogLogLebesgueDensity x *
      (∫ z in (A : Real)..(Y : Real),
        fourFiveLogLogLebesgueDensity z *
          (∫ w in (A : Real)..(Y : Real),
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree A y u x z w))

private theorem fourFiveTwo_inner_cell_union
    {A Y y p : Nat} {u x : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hp : p ∈ Finset.Ioc A Y)
    (hx : x ∈ Set.uIoc (((p - 1 : Nat) : Real)) (p : Real)) :
    (∑ q ∈ Finset.Ioc A Y,
        ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            fourFiveRealMovingSimplexKernelTwo A y u x z) =
      ∫ z in (A : Real)..(Y : Real),
        fourFiveLogLogLebesgueDensity z *
          fourFiveRealMovingSimplexKernelTwo A y u x z := by
  have hporder : (((p - 1 : Nat) : Real)) <= (p : Real) := by
    exact_mod_cast Nat.sub_le p 1
  have hxIoc : x ∈ Set.Ioc (((p - 1 : Nat) : Real)) (p : Real) := by
    simpa [Set.uIoc_of_le hporder] using hx
  have hApred : A <= p - 1 := by
    have := (Finset.mem_Ioc.mp hp).1
    omega
  have hxA : (A : Real) < x :=
    (by exact_mod_cast hApred :
      (A : Real) <= ((p - 1 : Nat) : Real)).trans_lt hxIoc.1
  apply sum_fourFiveUnitCellIntegrals_eq_interval hAY
  intro q hq
  have hface := intervalIntegrable_fourFiveDensity_mul_realMovingFace_cell
    (u := u) (c := fourFiveRealLogCoordinate y x) hy hyA hq
  apply hface.congr
  intro z _hz
  exact congrArg (fun v : Real => fourFiveLogLogLebesgueDensity z * v)
    (fourFiveRealMovingSimplexKernelTwo_eq_face_second
      (A := A) (y := y) (u := u) (x := x) (z := z) hxA).symm

private theorem intervalIntegrable_fourFiveTwo_active_union_cell
    {A Y y p : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hp : p ∈ Finset.Ioc A Y) :
    IntervalIntegrable
      (fun x : Real => fourFiveLogLogLebesgueDensity x *
        (∫ z in (A : Real)..(Y : Real),
          fourFiveLogLogLebesgueDensity z *
            fourFiveRealMovingSimplexKernelTwo A y u x z))
      volume (((p - 1 : Nat) : Real)) (p : Real) := by
  have hsum : IntervalIntegrable
      (∑ q ∈ Finset.Ioc A Y,
        fun x : Real => fourFiveLogLogLebesgueDensity x *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              fourFiveRealMovingSimplexKernelTwo A y u x z))
      volume (((p - 1 : Nat) : Real)) (p : Real) :=
    IntervalIntegrable.sum (Finset.Ioc A Y)
      (fun q hq =>
        intervalIntegrable_fourFiveRealMovingSimplexTwo_partial_cell
          (u := u) hy hyA hp hq)
  apply hsum.congr
  intro x hx
  rw [Finset.sum_apply]
  calc
    (∑ q ∈ Finset.Ioc A Y,
        fourFiveLogLogLebesgueDensity x *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              fourFiveRealMovingSimplexKernelTwo A y u x z)) =
      fourFiveLogLogLebesgueDensity x *
        (∑ q ∈ Finset.Ioc A Y,
          ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              fourFiveRealMovingSimplexKernelTwo A y u x z) := by
        rw [Finset.mul_sum]
    _ = fourFiveLogLogLebesgueDensity x *
        (∫ z in (A : Real)..(Y : Real),
          fourFiveLogLogLebesgueDensity z *
            fourFiveRealMovingSimplexKernelTwo A y u x z) :=
      congrArg (fun v : Real => fourFiveLogLogLebesgueDensity x * v)
        (fourFiveTwo_inner_cell_union (u := u) hy hyA hAY hp hx)

/-- Exact two-dimensional adjacent-cell union. -/
theorem fourFiveMovingSimplexIteratedRealCellProductTwo_eq_activePhysical
    {A Y y : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y) :
    fourFiveMovingSimplexIteratedRealCellProductTwo A Y y u =
      fourFiveMovingSimplexActivePhysicalIntegralTwo A Y y u := by
  unfold fourFiveMovingSimplexIteratedRealCellProductTwo
    fourFiveMovingSimplexActivePhysicalIntegralTwo
  calc
    (∑ p ∈ Finset.Ioc A Y,
        ∑ q ∈ Finset.Ioc A Y,
          ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
            fourFiveLogLogLebesgueDensity x *
              (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  fourFiveRealMovingSimplexKernelTwo A y u x z)) =
      ∑ p ∈ Finset.Ioc A Y,
        ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          ∑ q ∈ Finset.Ioc A Y,
            fourFiveLogLogLebesgueDensity x *
              (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  fourFiveRealMovingSimplexKernelTwo A y u x z) := by
          apply Finset.sum_congr rfl
          intro p hp
          symm
          exact intervalIntegral.integral_finset_sum
            (fun q hq =>
              intervalIntegrable_fourFiveRealMovingSimplexTwo_partial_cell
                (u := u) hy hyA hp hq)
    _ = ∑ p ∈ Finset.Ioc A Y,
        ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          fourFiveLogLogLebesgueDensity x *
            (∫ z in (A : Real)..(Y : Real),
              fourFiveLogLogLebesgueDensity z *
                fourFiveRealMovingSimplexKernelTwo A y u x z) := by
          apply Finset.sum_congr rfl
          intro p hp
          apply intervalIntegral.integral_congr_ae
          filter_upwards with x
          intro hx
          rw [← Finset.mul_sum]
          apply congrArg
            (fun v : Real => fourFiveLogLogLebesgueDensity x * v)
          exact fourFiveTwo_inner_cell_union hy hyA hAY hp hx
    _ = ∫ x in (A : Real)..(Y : Real),
        fourFiveLogLogLebesgueDensity x *
          (∫ z in (A : Real)..(Y : Real),
            fourFiveLogLogLebesgueDensity z *
              fourFiveRealMovingSimplexKernelTwo A y u x z) :=
      sum_fourFiveUnitCellIntegrals_eq_interval hAY
        (fun p hp => intervalIntegrable_fourFiveTwo_active_union_cell
          hy hyA hAY hp)

private theorem fourFiveThree_inner_cell_union
    {A Y y p q : Nat} {u x z : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y)
    (hx : x ∈ Set.uIoc (((p - 1 : Nat) : Real)) (p : Real))
    (hz : z ∈ Set.uIoc (((q - 1 : Nat) : Real)) (q : Real)) :
    (∑ r ∈ Finset.Ioc A Y,
        ∫ w in (((r - 1 : Nat) : Real))..(r : Real),
          fourFiveLogLogLebesgueDensity w *
            fourFiveRealMovingSimplexKernelThree A y u x z w) =
      ∫ w in (A : Real)..(Y : Real),
        fourFiveLogLogLebesgueDensity w *
          fourFiveRealMovingSimplexKernelThree A y u x z w := by
  have hxIoc : x ∈ Set.Ioc (((p - 1 : Nat) : Real)) (p : Real) := by
    simpa [Set.uIoc_of_le
      (by exact_mod_cast Nat.sub_le p 1)] using hx
  have hzIoc : z ∈ Set.Ioc (((q - 1 : Nat) : Real)) (q : Real) := by
    simpa [Set.uIoc_of_le
      (by exact_mod_cast Nat.sub_le q 1)] using hz
  have hxA : (A : Real) < x := by
    have hAp : A <= p - 1 := by
      have := (Finset.mem_Ioc.mp hp).1
      omega
    exact (by exact_mod_cast hAp :
      (A : Real) <= ((p - 1 : Nat) : Real)).trans_lt hxIoc.1
  have hzA : (A : Real) < z := by
    have hAq : A <= q - 1 := by
      have := (Finset.mem_Ioc.mp hq).1
      omega
    exact (by exact_mod_cast hAq :
      (A : Real) <= ((q - 1 : Nat) : Real)).trans_lt hzIoc.1
  apply sum_fourFiveUnitCellIntegrals_eq_interval hAY
  intro r hr
  have hface := intervalIntegrable_fourFiveDensity_mul_realMovingFace_cell
    (u := u) (c := fourFiveRealLogCoordinate y x +
      fourFiveRealLogCoordinate y z) hy hyA hr
  apply hface.congr
  intro w _hw
  exact congrArg (fun v : Real => fourFiveLogLogLebesgueDensity w * v)
    (fourFiveRealMovingSimplexKernelThree_eq_face_third
      (A := A) (y := y) (u := u) (x := x) (z := z) (w := w)
        hxA hzA).symm

private theorem fourFiveThree_sum_lastRealCells_inside_middle
    {A Y y p q : Nat} {u x : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y)
    (hx : x ∈ Set.uIoc (((p - 1 : Nat) : Real)) (p : Real)) :
    (∑ r ∈ Finset.Ioc A Y,
        ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w)) =
      ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
        fourFiveLogLogLebesgueDensity z *
          (∫ w in (A : Real)..(Y : Real),
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree A y u x z w) := by
  calc
    (∑ r ∈ Finset.Ioc A Y,
        ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w)) =
      ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
        ∑ r ∈ Finset.Ioc A Y,
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w) := by
          symm
          exact intervalIntegral.integral_finset_sum
            (fun r hr => intervalIntegrable_fourFiveThree_lastCellReal_inner
              hy hyA hp hq hr hx)
    _ = ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
        fourFiveLogLogLebesgueDensity z *
          (∫ w in (A : Real)..(Y : Real),
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree A y u x z w) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with z
      intro hz
      rw [← Finset.mul_sum]
      apply congrArg (fun v : Real => fourFiveLogLogLebesgueDensity z * v)
      exact fourFiveThree_inner_cell_union hy hyA hAY hp hq hx hz

private theorem intervalIntegrable_fourFiveThree_middle_with_activeLast
    {A Y y p q : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y) :
    IntervalIntegrable
      (fun x : Real => fourFiveLogLogLebesgueDensity x *
        (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (A : Real)..(Y : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w)))
      volume (((p - 1 : Nat) : Real)) (p : Real) := by
  have hsum : IntervalIntegrable
      (∑ r ∈ Finset.Ioc A Y,
        fun x : Real => fourFiveLogLogLebesgueDensity x *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                fourFiveLogLogLebesgueDensity w *
                  fourFiveRealMovingSimplexKernelThree A y u x z w)))
      volume (((p - 1 : Nat) : Real)) (p : Real) :=
    IntervalIntegrable.sum (Finset.Ioc A Y)
      (fun r hr =>
        intervalIntegrable_fourFiveRealMovingSimplexThree_partial_cell
          (u := u) hy hyA hp hq hr)
  apply hsum.congr
  intro x hx
  rw [Finset.sum_apply]
  calc
    (∑ r ∈ Finset.Ioc A Y,
        fourFiveLogLogLebesgueDensity x *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                fourFiveLogLogLebesgueDensity w *
                  fourFiveRealMovingSimplexKernelThree A y u x z w))) =
      fourFiveLogLogLebesgueDensity x *
        (∑ r ∈ Finset.Ioc A Y,
          ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                fourFiveLogLogLebesgueDensity w *
                  fourFiveRealMovingSimplexKernelThree A y u x z w)) := by
        rw [Finset.mul_sum]
    _ = fourFiveLogLogLebesgueDensity x *
        (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (A : Real)..(Y : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w)) :=
      congrArg (fun v : Real => fourFiveLogLogLebesgueDensity x * v)
        (fourFiveThree_sum_lastRealCells_inside_middle
          (u := u) hy hyA hAY hp hq hx)

private theorem fourFiveThree_middle_cell_union
    {A Y y p : Nat} {u x : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hp : p ∈ Finset.Ioc A Y)
    (hx : x ∈ Set.uIoc (((p - 1 : Nat) : Real)) (p : Real)) :
    (∑ q ∈ Finset.Ioc A Y,
        ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (A : Real)..(Y : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w)) =
      ∫ z in (A : Real)..(Y : Real),
        fourFiveLogLogLebesgueDensity z *
          (∫ w in (A : Real)..(Y : Real),
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree A y u x z w) := by
  apply sum_fourFiveUnitCellIntegrals_eq_interval hAY
  intro q hq
  have hsum : IntervalIntegrable
      (∑ r ∈ Finset.Ioc A Y,
        fun z : Real => fourFiveLogLogLebesgueDensity z *
          (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree A y u x z w))
      volume (((q - 1 : Nat) : Real)) (q : Real) :=
    IntervalIntegrable.sum (Finset.Ioc A Y)
      (fun r hr => intervalIntegrable_fourFiveThree_lastCellReal_inner
        hy hyA hp hq hr hx)
  apply hsum.congr
  intro z hz
  rw [Finset.sum_apply]
  calc
    (∑ r ∈ Finset.Ioc A Y,
        fourFiveLogLogLebesgueDensity z *
          (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree A y u x z w)) =
      fourFiveLogLogLebesgueDensity z *
        (∑ r ∈ Finset.Ioc A Y,
          ∫ w in (((r - 1 : Nat) : Real))..(r : Real),
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree A y u x z w) := by
        rw [Finset.mul_sum]
    _ = fourFiveLogLogLebesgueDensity z *
        (∫ w in (A : Real)..(Y : Real),
          fourFiveLogLogLebesgueDensity w *
            fourFiveRealMovingSimplexKernelThree A y u x z w) :=
      congrArg (fun v : Real => fourFiveLogLogLebesgueDensity z * v)
        (fourFiveThree_inner_cell_union (u := u)
          hy hyA hAY hp hq hx hz)

private theorem intervalIntegrable_fourFiveThree_active_union_cell
    {A Y y p : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y)
    (hp : p ∈ Finset.Ioc A Y) :
    IntervalIntegrable
      (fun x : Real => fourFiveLogLogLebesgueDensity x *
        (∫ z in (A : Real)..(Y : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (A : Real)..(Y : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w)))
      volume (((p - 1 : Nat) : Real)) (p : Real) := by
  have hsum : IntervalIntegrable
      (∑ q ∈ Finset.Ioc A Y,
        fun x : Real => fourFiveLogLogLebesgueDensity x *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              (∫ w in (A : Real)..(Y : Real),
                fourFiveLogLogLebesgueDensity w *
                  fourFiveRealMovingSimplexKernelThree A y u x z w)))
      volume (((p - 1 : Nat) : Real)) (p : Real) :=
    IntervalIntegrable.sum (Finset.Ioc A Y)
      (fun q hq => intervalIntegrable_fourFiveThree_middle_with_activeLast
        hy hyA hAY hp hq)
  apply hsum.congr
  intro x hx
  rw [Finset.sum_apply]
  calc
    (∑ q ∈ Finset.Ioc A Y,
        fourFiveLogLogLebesgueDensity x *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              (∫ w in (A : Real)..(Y : Real),
                fourFiveLogLogLebesgueDensity w *
                  fourFiveRealMovingSimplexKernelThree A y u x z w))) =
      fourFiveLogLogLebesgueDensity x *
        (∑ q ∈ Finset.Ioc A Y,
          ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              (∫ w in (A : Real)..(Y : Real),
                fourFiveLogLogLebesgueDensity w *
                  fourFiveRealMovingSimplexKernelThree A y u x z w)) := by
        rw [Finset.mul_sum]
    _ = fourFiveLogLogLebesgueDensity x *
        (∫ z in (A : Real)..(Y : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (A : Real)..(Y : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree A y u x z w)) :=
      congrArg (fun v : Real => fourFiveLogLogLebesgueDensity x * v)
        (fourFiveThree_middle_cell_union (u := u) hy hyA hAY hp hx)

/-- Exact three-dimensional adjacent-cell union. -/
theorem fourFiveMovingSimplexIteratedRealCellProductThree_eq_activePhysical
    {A Y y : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAY : A <= Y) :
    fourFiveMovingSimplexIteratedRealCellProductThree A Y y u =
      fourFiveMovingSimplexActivePhysicalIntegralThree A Y y u := by
  unfold fourFiveMovingSimplexIteratedRealCellProductThree
    fourFiveMovingSimplexActivePhysicalIntegralThree
  calc
    (∑ p ∈ Finset.Ioc A Y,
        ∑ q ∈ Finset.Ioc A Y,
          ∑ r ∈ Finset.Ioc A Y,
            ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
              fourFiveLogLogLebesgueDensity x *
                (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                  fourFiveLogLogLebesgueDensity z *
                    (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                      fourFiveLogLogLebesgueDensity w *
                        fourFiveRealMovingSimplexKernelThree A y u x z w))) =
      ∑ p ∈ Finset.Ioc A Y,
        ∑ q ∈ Finset.Ioc A Y,
          ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
            ∑ r ∈ Finset.Ioc A Y,
              fourFiveLogLogLebesgueDensity x *
                (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                  fourFiveLogLogLebesgueDensity z *
                    (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                      fourFiveLogLogLebesgueDensity w *
                        fourFiveRealMovingSimplexKernelThree A y u x z w)) := by
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro q hq
          symm
          exact intervalIntegral.integral_finset_sum
            (fun r hr =>
              intervalIntegrable_fourFiveRealMovingSimplexThree_partial_cell
                (u := u) hy hyA hp hq hr)
    _ = ∑ p ∈ Finset.Ioc A Y,
        ∑ q ∈ Finset.Ioc A Y,
          ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
            fourFiveLogLogLebesgueDensity x *
              (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  (∫ w in (A : Real)..(Y : Real),
                    fourFiveLogLogLebesgueDensity w *
                      fourFiveRealMovingSimplexKernelThree A y u x z w)) := by
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro q hq
          apply intervalIntegral.integral_congr_ae
          filter_upwards with x
          intro hx
          rw [← Finset.mul_sum]
          apply congrArg
            (fun v : Real => fourFiveLogLogLebesgueDensity x * v)
          exact fourFiveThree_sum_lastRealCells_inside_middle
            hy hyA hAY hp hq hx
    _ = ∑ p ∈ Finset.Ioc A Y,
        ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          ∑ q ∈ Finset.Ioc A Y,
            fourFiveLogLogLebesgueDensity x *
              (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
                fourFiveLogLogLebesgueDensity z *
                  (∫ w in (A : Real)..(Y : Real),
                    fourFiveLogLogLebesgueDensity w *
                      fourFiveRealMovingSimplexKernelThree A y u x z w)) := by
          apply Finset.sum_congr rfl
          intro p hp
          symm
          exact intervalIntegral.integral_finset_sum
            (fun q hq => intervalIntegrable_fourFiveThree_middle_with_activeLast
              hy hyA hAY hp hq)
    _ = ∑ p ∈ Finset.Ioc A Y,
        ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          fourFiveLogLogLebesgueDensity x *
            (∫ z in (A : Real)..(Y : Real),
              fourFiveLogLogLebesgueDensity z *
                (∫ w in (A : Real)..(Y : Real),
                  fourFiveLogLogLebesgueDensity w *
                    fourFiveRealMovingSimplexKernelThree A y u x z w)) := by
          apply Finset.sum_congr rfl
          intro p hp
          apply intervalIntegral.integral_congr_ae
          filter_upwards with x
          intro hx
          rw [← Finset.mul_sum]
          apply congrArg
            (fun v : Real => fourFiveLogLogLebesgueDensity x * v)
          exact fourFiveThree_middle_cell_union hy hyA hAY hp hx
    _ = ∫ x in (A : Real)..(Y : Real),
        fourFiveLogLogLebesgueDensity x *
          (∫ z in (A : Real)..(Y : Real),
            fourFiveLogLogLebesgueDensity z *
              (∫ w in (A : Real)..(Y : Real),
                fourFiveLogLogLebesgueDensity w *
                  fourFiveRealMovingSimplexKernelThree A y u x z w)) :=
      sum_fourFiveUnitCellIntegrals_eq_interval hAY
        (fun p hp => intervalIntegrable_fourFiveThree_active_union_cell
          hy hyA hAY hp)

/-! ## Joint integrability on the finite active box -/

private theorem iUnion_fourFiveUnitCells_eq_Ioc
    (A Y : Nat) :
    (⋃ k ∈ Set.Ico A Y,
        Set.Ioc (k : Real) ((k + 1 : Nat) : Real)) =
      Set.Ioc (A : Real) (Y : Real) := by
  have hmono : Monotone (fun k : Nat => (k : Real)) := by
    intro a b hab
    exact Nat.cast_le.mpr hab
  simpa [Nat.cast_succ] using
    hmono.biUnion_Ico_Ioc_map_succ A Y

/-- The two-coordinate real density is integrable on the whole finite box.
The proof is a finite union of the literal unit-cell integrability results
used above; no global domination or limiting argument is introduced. -/
theorem integrableOn_fourFiveRealMovingSimplexDensityTwo_activeBox
    {A Y y : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A) :
    IntegrableOn
      (fun p : Real × Real =>
        fourFiveLogLogLebesgueDensity p.1 *
          fourFiveLogLogLebesgueDensity p.2 *
            fourFiveRealMovingSimplexKernelTwo A y u p.1 p.2)
      (Set.Ioc (A : Real) (Y : Real) ×ˢ
        Set.Ioc (A : Real) (Y : Real)) volume := by
  let C : Nat -> Set Real := fun k =>
    Set.Ioc (k : Real) ((k + 1 : Nat) : Real)
  let f : Real × Real -> Real := fun p =>
    fourFiveLogLogLebesgueDensity p.1 *
      fourFiveLogLogLebesgueDensity p.2 *
        fourFiveRealMovingSimplexKernelTwo A y u p.1 p.2
  change IntegrableOn f
    (Set.Ioc (A : Real) (Y : Real) ×ˢ
      Set.Ioc (A : Real) (Y : Real)) volume
  have hunion : (⋃ k ∈ Set.Ico A Y, C k) =
      Set.Ioc (A : Real) (Y : Real) := by
    simpa [C] using iUnion_fourFiveUnitCells_eq_Ioc A Y
  have hbox :
      (Set.Ioc (A : Real) (Y : Real) ×ˢ
        Set.Ioc (A : Real) (Y : Real)) =
        ⋃ p ∈ Set.Ico A Y, ⋃ q ∈ Set.Ico A Y, C p ×ˢ C q := by
    rw [← hunion]
    ext z
    simp only [Set.mem_prod, Set.mem_iUnion, exists_prop]
    tauto
  rw [hbox, integrableOn_finite_biUnion (Set.finite_Ico A Y)]
  intro p hp
  rw [integrableOn_finite_biUnion (Set.finite_Ico A Y)]
  intro q hq
  have hp' : p + 1 ∈ Finset.Ioc A Y := by
    rw [Finset.mem_Ioc]
    exact ⟨Nat.lt_succ_of_le hp.1, Nat.succ_le_iff.mpr hp.2⟩
  have hq' : q + 1 ∈ Finset.Ioc A Y := by
    rw [Finset.mem_Ioc]
    exact ⟨Nat.lt_succ_of_le hq.1, Nat.succ_le_iff.mpr hq.2⟩
  have hcell := integrable_fourFiveRealMovingSimplexDensityTwo_cell
    (u := u) hy hyA hp' hq'
  rw [Measure.volume_eq_prod, IntegrableOn, ← Measure.prod_restrict]
  simpa [C, f, fourFiveRealMovingSimplexDensityTwo,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using hcell

/-- The analogous finite-box integrability statement in three coordinates. -/
theorem integrableOn_fourFiveRealMovingSimplexDensityThree_activeBox
    {A Y y : Nat} {u : Real}
    (hy : 2 <= y) (hyA : y <= A) :
    IntegrableOn
      (fun p : (Real × Real) × Real =>
        fourFiveLogLogLebesgueDensity p.1.1 *
          fourFiveLogLogLebesgueDensity p.1.2 *
            fourFiveLogLogLebesgueDensity p.2 *
              fourFiveRealMovingSimplexKernelThree A y u
                p.1.1 p.1.2 p.2)
      ((Set.Ioc (A : Real) (Y : Real) ×ˢ
          Set.Ioc (A : Real) (Y : Real)) ×ˢ
        Set.Ioc (A : Real) (Y : Real)) volume := by
  let C : Nat -> Set Real := fun k =>
    Set.Ioc (k : Real) ((k + 1 : Nat) : Real)
  let f : (Real × Real) × Real -> Real := fun p =>
    fourFiveLogLogLebesgueDensity p.1.1 *
      fourFiveLogLogLebesgueDensity p.1.2 *
        fourFiveLogLogLebesgueDensity p.2 *
          fourFiveRealMovingSimplexKernelThree A y u p.1.1 p.1.2 p.2
  change IntegrableOn f
    ((Set.Ioc (A : Real) (Y : Real) ×ˢ
        Set.Ioc (A : Real) (Y : Real)) ×ˢ
      Set.Ioc (A : Real) (Y : Real)) volume
  have hunion : (⋃ k ∈ Set.Ico A Y, C k) =
      Set.Ioc (A : Real) (Y : Real) := by
    simpa [C] using iUnion_fourFiveUnitCells_eq_Ioc A Y
  have hbox :
      ((Set.Ioc (A : Real) (Y : Real) ×ˢ
          Set.Ioc (A : Real) (Y : Real)) ×ˢ
        Set.Ioc (A : Real) (Y : Real)) =
        ⋃ p ∈ Set.Ico A Y, ⋃ q ∈ Set.Ico A Y,
          ⋃ r ∈ Set.Ico A Y, (C p ×ˢ C q) ×ˢ C r := by
    rw [← hunion]
    ext z
    simp only [Set.mem_prod, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨⟨⟨p, hp, hzp⟩, ⟨q, hq, hzq⟩⟩,
        ⟨r, hr, hzr⟩⟩
      exact ⟨p, hp, q, hq, r, hr, ⟨⟨hzp, hzq⟩, hzr⟩⟩
    · rintro ⟨p, hp, q, hq, r, hr, ⟨⟨hzp, hzq⟩, hzr⟩⟩
      exact ⟨⟨⟨p, hp, hzp⟩, ⟨q, hq, hzq⟩⟩,
        ⟨r, hr, hzr⟩⟩
  rw [hbox, integrableOn_finite_biUnion (Set.finite_Ico A Y)]
  intro p hp
  rw [integrableOn_finite_biUnion (Set.finite_Ico A Y)]
  intro q hq
  rw [integrableOn_finite_biUnion (Set.finite_Ico A Y)]
  intro r hr
  have hp' : p + 1 ∈ Finset.Ioc A Y := by
    rw [Finset.mem_Ioc]
    exact ⟨Nat.lt_succ_of_le hp.1, Nat.succ_le_iff.mpr hp.2⟩
  have hq' : q + 1 ∈ Finset.Ioc A Y := by
    rw [Finset.mem_Ioc]
    exact ⟨Nat.lt_succ_of_le hq.1, Nat.succ_le_iff.mpr hq.2⟩
  have hr' : r + 1 ∈ Finset.Ioc A Y := by
    rw [Finset.mem_Ioc]
    exact ⟨Nat.lt_succ_of_le hr.1, Nat.succ_le_iff.mpr hr.2⟩
  have hcell := integrable_fourFiveRealMovingSimplexDensityThree_cell
    (u := u) hy hyA hp' hq' hr'
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod,
    IntegrableOn, ← Measure.prod_restrict, ← Measure.prod_restrict]
  simpa [C, f, fourFiveRealMovingSimplexDensityThree,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using hcell

end Erdos390.WholePaper.BankPaperRealization
