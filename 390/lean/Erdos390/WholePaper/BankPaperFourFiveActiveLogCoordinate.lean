import Erdos390.WholePaper.BankPaperFourFiveMovingSimplexCellIdentification
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Active physical cells and logarithmic coordinates

This file isolates the exact change of variables used after the finite
right-endpoint cell telescope.  For every positive number of preceding
coordinates, the coordinatewise map

`s_i ↦ exp (log y * s_i)`

sends the strict logarithmic moving simplex onto the physical active
region.  Its Jacobian cancels the factors `dx_i / (x_i log x_i)` exactly.
The strict and closed logarithmic simplexes differ only on the frontier of
a convex set, hence have the same Lebesgue integral.  No limiting mesh or
convergence statement is used.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-! ## Strict and physical moving simplexes -/

def fourFiveStrictLogarithmicMovingSimplex
    (m : Nat) (u : Real) : Set (Fin m -> Real) :=
  {s | (∀ i, 1 < s i) ∧ (∑ i, s i) < u - 1}

def fourFivePhysicalActiveMovingSimplex
    (m : Nat) (y : Nat) (u : Real) : Set (Fin m -> Real) :=
  {x | (∀ i, (y : Real) < x i) ∧
    (∑ i, fourFiveRealLogCoordinate y (x i)) < u - 1}

def fourFivePhysicalActiveMovingSimplexIntegrand
    (m : Nat) (y : Nat) (u : Real) (x : Fin m -> Real) : Real :=
  (∏ i, fourFiveLogLogLebesgueDensity (x i)) *
    (u - ∑ i, fourFiveRealLogCoordinate y (x i))⁻¹

def fourFivePhysicalActiveMovingSimplexKernel
    (m : Nat) (y : Nat) (u : Real) : Real :=
  ∫ x in fourFivePhysicalActiveMovingSimplex m y u,
    fourFivePhysicalActiveMovingSimplexIntegrand m y u x

theorem measurableSet_fourFivePhysicalActiveMovingSimplex
    (m y : Nat) (u : Real) :
    MeasurableSet (fourFivePhysicalActiveMovingSimplex m y u) := by
  have hcoord : MeasurableSet
      {x : Fin m -> Real | ∀ i, (y : Real) < x i} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun i =>
      (measurable_pi_apply i) measurableSet_Ioi
  have hsum : Measurable
      (fun x : Fin m -> Real =>
        ∑ i, fourFiveRealLogCoordinate y (x i)) :=
    Finset.measurable_sum _ fun i _hi =>
      (measurable_fourFiveRealLogCoordinate y).comp
        (measurable_pi_apply i)
  convert hcoord.inter (hsum measurableSet_Iio) using 1

def fourFivePhysicalActiveMovingSimplexOne
    (y : Nat) (u : Real) : Set Real :=
  {x | (y : Real) < x ∧ fourFiveRealLogCoordinate y x < u - 1}

def fourFivePhysicalActiveMovingSimplexTwo
    (y : Nat) (u : Real) : Set (Real × Real) :=
  {p | (y : Real) < p.1 ∧ (y : Real) < p.2 ∧
    fourFiveRealLogCoordinate y p.1 +
      fourFiveRealLogCoordinate y p.2 < u - 1}

def fourFivePhysicalActiveMovingSimplexThree
    (y : Nat) (u : Real) : Set ((Real × Real) × Real) :=
  {p | (y : Real) < p.1.1 ∧ (y : Real) < p.1.2 ∧
    (y : Real) < p.2 ∧
    fourFiveRealLogCoordinate y p.1.1 +
      fourFiveRealLogCoordinate y p.1.2 +
        fourFiveRealLogCoordinate y p.2 < u - 1}

def fourFivePhysicalActiveIntegrandOne
    (y : Nat) (u x : Real) : Real :=
  fourFiveLogLogLebesgueDensity x *
    (u - fourFiveRealLogCoordinate y x)⁻¹

def fourFivePhysicalActiveIntegrandTwo
    (y : Nat) (u : Real) (p : Real × Real) : Real :=
  fourFiveLogLogLebesgueDensity p.1 *
    fourFiveLogLogLebesgueDensity p.2 *
      (u - fourFiveRealLogCoordinate y p.1 -
        fourFiveRealLogCoordinate y p.2)⁻¹

def fourFivePhysicalActiveIntegrandThree
    (y : Nat) (u : Real) (p : (Real × Real) × Real) : Real :=
  fourFiveLogLogLebesgueDensity p.1.1 *
    fourFiveLogLogLebesgueDensity p.1.2 *
      fourFiveLogLogLebesgueDensity p.2 *
        (u - fourFiveRealLogCoordinate y p.1.1 -
          fourFiveRealLogCoordinate y p.1.2 -
            fourFiveRealLogCoordinate y p.2)⁻¹

theorem measurableSet_fourFivePhysicalActiveMovingSimplexOne
    (y : Nat) (u : Real) :
    MeasurableSet (fourFivePhysicalActiveMovingSimplexOne y u) := by
  exact (measurableSet_lt measurable_const measurable_id).inter
    (measurableSet_lt
      (measurable_fourFiveRealLogCoordinate y) measurable_const)

theorem measurableSet_fourFivePhysicalActiveMovingSimplexTwo
    (y : Nat) (u : Real) :
    MeasurableSet (fourFivePhysicalActiveMovingSimplexTwo y u) := by
  have hx : Measurable (fun p : Real × Real =>
      fourFiveRealLogCoordinate y p.1) :=
    (measurable_fourFiveRealLogCoordinate y).comp measurable_fst
  have hz : Measurable (fun p : Real × Real =>
      fourFiveRealLogCoordinate y p.2) :=
    (measurable_fourFiveRealLogCoordinate y).comp measurable_snd
  exact (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt (hx.add hz) measurable_const))

theorem measurableSet_fourFivePhysicalActiveMovingSimplexThree
    (y : Nat) (u : Real) :
    MeasurableSet (fourFivePhysicalActiveMovingSimplexThree y u) := by
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
  exact (measurableSet_lt measurable_const
      (measurable_fst.comp measurable_fst)).inter
    ((measurableSet_lt measurable_const
      (measurable_snd.comp measurable_fst)).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt ((hx.add hz).add hw) measurable_const)))

/-- The concrete coordinate equivalence used to express the three-variable
Pi integral in the paper's nested `((x,z),w)` order. -/
def fourFiveFinThreeArrow :
    (Fin 3 -> Real) ≃ᵐ ((Real × Real) × Real) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Real) 0).trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl Real)
      (MeasurableEquiv.finTwoArrow (α := Real))).trans
        MeasurableEquiv.prodAssoc.symm)

@[simp] theorem fourFiveFinThreeArrow_apply
    (s : Fin 3 -> Real) :
    fourFiveFinThreeArrow s = ((s 0, s 1), s 2) := by
  change ((s 0, (Fin.tail s) 0), (Fin.tail s) 1) =
    ((s 0, s 1), s 2)
  rfl

theorem fourFiveFinThreeArrow_measurePreserving :
    MeasurePreserving fourFiveFinThreeArrow volume volume := by
  have h0 := volume_preserving_piFinSuccAbove
    (fun _ : Fin 3 => Real) (0 : Fin 3)
  have h1 := (MeasurePreserving.id (volume : Measure Real)).prod
    (volume_preserving_finTwoArrow Real)
  have h2 :=
    (volume_preserving_prodAssoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc :
        (Real × Real) × Real ≃ᵐ Real × (Real × Real))).symm
  simpa [fourFiveFinThreeArrow] using h2.comp (h1.comp h0)

private theorem lt_of_fourFiveRealLogCoordinate_lt
    {y : Nat} (hy : 2 <= y) {x b : Real}
    (hx : 0 < x) (hb : 0 < b)
    (h : fourFiveRealLogCoordinate y x <
      fourFiveRealLogCoordinate y b) :
    x < b := by
  have hlogy : 0 < Real.log (y : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlog : Real.log x < Real.log b := by
    exact (div_lt_div_iff_of_pos_right hlogy).mp h
  calc
    x = Real.exp (Real.log x) := (Real.exp_log hx).symm
    _ < Real.exp (Real.log b) := Real.exp_lt_exp.mpr hlog
    _ = b := Real.exp_log hb

private theorem one_lt_fourFiveRealLogCoordinate_of_lt
    {y : Nat} (hy : 2 <= y) {x : Real}
    (hx : (y : Real) < x) :
    1 < fourFiveRealLogCoordinate y x := by
  have hypos : 0 < (y : Real) := by
    exact_mod_cast (show 0 < y by omega)
  have hlogpos : 0 < Real.log (y : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hloglt : Real.log (y : Real) < Real.log x :=
    Real.strictMonoOn_log hypos (hypos.trans hx) hx
  unfold fourFiveRealLogCoordinate
  exact (lt_div_iff₀ hlogpos).mpr (by simpa only [one_mul] using hloglt)

@[simp] theorem fourFiveFinThreeArrow_symm_apply_zero
    (p : (Real × Real) × Real) :
    (fourFiveFinThreeArrow.symm p) 0 = p.1.1 := by
  have h := congrArg (fun q : (Real × Real) × Real => q.1.1)
    (fourFiveFinThreeArrow.apply_symm_apply p)
  simpa only [fourFiveFinThreeArrow_apply] using h

@[simp] theorem fourFiveFinThreeArrow_symm_apply_one
    (p : (Real × Real) × Real) :
    (fourFiveFinThreeArrow.symm p) 1 = p.1.2 := by
  have h := congrArg (fun q : (Real × Real) × Real => q.1.2)
    (fourFiveFinThreeArrow.apply_symm_apply p)
  simpa only [fourFiveFinThreeArrow_apply] using h

@[simp] theorem fourFiveFinThreeArrow_symm_apply_two
    (p : (Real × Real) × Real) :
    (fourFiveFinThreeArrow.symm p) 2 = p.2 := by
  have h := congrArg (fun q : (Real × Real) × Real => q.2)
    (fourFiveFinThreeArrow.apply_symm_apply p)
  simpa only [fourFiveFinThreeArrow_apply] using h

theorem image_fourFivePhysicalActiveMovingSimplex_finOne
    (y : Nat) (u : Real) :
    MeasurableEquiv.funUnique (Fin 1) Real ''
        fourFivePhysicalActiveMovingSimplex 1 y u =
      fourFivePhysicalActiveMovingSimplexOne y u := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa [fourFivePhysicalActiveMovingSimplex,
      fourFivePhysicalActiveMovingSimplexOne,
      Fin.sum_univ_one] using hs
  · intro hx
    refine ⟨(MeasurableEquiv.funUnique (Fin 1) Real).symm x, ?_,
      (MeasurableEquiv.funUnique (Fin 1) Real).apply_symm_apply x⟩
    simpa [fourFivePhysicalActiveMovingSimplex,
      fourFivePhysicalActiveMovingSimplexOne,
      Fin.sum_univ_one] using hx

theorem image_fourFivePhysicalActiveMovingSimplex_finTwo
    (y : Nat) (u : Real) :
    MeasurableEquiv.finTwoArrow ''
        fourFivePhysicalActiveMovingSimplex 2 y u =
      fourFivePhysicalActiveMovingSimplexTwo y u := by
  ext p
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa [fourFivePhysicalActiveMovingSimplex,
      fourFivePhysicalActiveMovingSimplexTwo,
      Fin.forall_fin_two, Fin.sum_univ_two, and_assoc] using hs
  · intro hp
    refine ⟨MeasurableEquiv.finTwoArrow.symm p, ?_,
      MeasurableEquiv.finTwoArrow.apply_symm_apply p⟩
    simpa [fourFivePhysicalActiveMovingSimplex,
      fourFivePhysicalActiveMovingSimplexTwo,
      Fin.forall_fin_two, Fin.sum_univ_two, and_assoc] using hp

theorem image_fourFivePhysicalActiveMovingSimplex_finThree
    (y : Nat) (u : Real) :
    fourFiveFinThreeArrow ''
        fourFivePhysicalActiveMovingSimplex 3 y u =
      fourFivePhysicalActiveMovingSimplexThree y u := by
  ext p
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa [fourFivePhysicalActiveMovingSimplex,
      fourFivePhysicalActiveMovingSimplexThree,
      Fin.forall_fin_succ, Fin.sum_univ_three, and_assoc] using hs
  · intro hp
    refine ⟨fourFiveFinThreeArrow.symm p, ?_,
      fourFiveFinThreeArrow.apply_symm_apply p⟩
    simpa [fourFivePhysicalActiveMovingSimplex,
      fourFivePhysicalActiveMovingSimplexThree,
      Fin.forall_fin_succ, Fin.sum_univ_three, and_assoc] using hp

theorem fourFivePhysicalActiveMovingSimplexKernel_one_eq_setIntegral
    (y : Nat) (u : Real) :
    fourFivePhysicalActiveMovingSimplexKernel 1 y u =
      ∫ x in fourFivePhysicalActiveMovingSimplexOne y u,
        fourFivePhysicalActiveIntegrandOne y u x := by
  let e := MeasurableEquiv.funUnique (Fin 1) Real
  let g := fourFivePhysicalActiveIntegrandOne y u
  have hmap := (volume_preserving_funUnique (Fin 1) Real).setIntegral_image_emb
    e.measurableEmbedding g (fourFivePhysicalActiveMovingSimplex 1 y u)
  unfold fourFivePhysicalActiveMovingSimplexKernel
  calc
    (∫ s in fourFivePhysicalActiveMovingSimplex 1 y u,
        fourFivePhysicalActiveMovingSimplexIntegrand 1 y u s) =
        ∫ s in fourFivePhysicalActiveMovingSimplex 1 y u, g (e s) := by
          apply setIntegral_congr_fun
            (measurableSet_fourFivePhysicalActiveMovingSimplex 1 y u)
          intro s _hs
          simp [g, e, fourFivePhysicalActiveMovingSimplexIntegrand,
            fourFivePhysicalActiveIntegrandOne]
    _ = ∫ x in e '' fourFivePhysicalActiveMovingSimplex 1 y u, g x :=
      hmap.symm
    _ = ∫ x in fourFivePhysicalActiveMovingSimplexOne y u,
        fourFivePhysicalActiveIntegrandOne y u x := by
      rw [image_fourFivePhysicalActiveMovingSimplex_finOne]

theorem fourFivePhysicalActiveMovingSimplexKernel_two_eq_setIntegral
    (y : Nat) (u : Real) :
    fourFivePhysicalActiveMovingSimplexKernel 2 y u =
      ∫ p in fourFivePhysicalActiveMovingSimplexTwo y u,
        fourFivePhysicalActiveIntegrandTwo y u p := by
  let e := MeasurableEquiv.finTwoArrow (α := Real)
  let g := fourFivePhysicalActiveIntegrandTwo y u
  have hmap := (volume_preserving_finTwoArrow Real).setIntegral_image_emb
    e.measurableEmbedding g (fourFivePhysicalActiveMovingSimplex 2 y u)
  unfold fourFivePhysicalActiveMovingSimplexKernel
  calc
    (∫ s in fourFivePhysicalActiveMovingSimplex 2 y u,
        fourFivePhysicalActiveMovingSimplexIntegrand 2 y u s) =
        ∫ s in fourFivePhysicalActiveMovingSimplex 2 y u, g (e s) := by
          apply setIntegral_congr_fun
            (measurableSet_fourFivePhysicalActiveMovingSimplex 2 y u)
          intro s _hs
          have hden :
              u - (fourFiveRealLogCoordinate y (s 0) +
                fourFiveRealLogCoordinate y (s 1)) =
                u - fourFiveRealLogCoordinate y (s 0) -
                  fourFiveRealLogCoordinate y (s 1) := by
            ring
          simp [g, e, fourFivePhysicalActiveMovingSimplexIntegrand,
            fourFivePhysicalActiveIntegrandTwo, Fin.prod_univ_two,
            Fin.sum_univ_two, hden]
    _ = ∫ p in e '' fourFivePhysicalActiveMovingSimplex 2 y u, g p :=
      hmap.symm
    _ = ∫ p in fourFivePhysicalActiveMovingSimplexTwo y u,
        fourFivePhysicalActiveIntegrandTwo y u p := by
      rw [image_fourFivePhysicalActiveMovingSimplex_finTwo]

theorem fourFivePhysicalActiveMovingSimplexKernel_three_eq_setIntegral
    (y : Nat) (u : Real) :
    fourFivePhysicalActiveMovingSimplexKernel 3 y u =
      ∫ p in fourFivePhysicalActiveMovingSimplexThree y u,
        fourFivePhysicalActiveIntegrandThree y u p := by
  let e := fourFiveFinThreeArrow
  let g := fourFivePhysicalActiveIntegrandThree y u
  have hmap := fourFiveFinThreeArrow_measurePreserving.setIntegral_image_emb
    e.measurableEmbedding g (fourFivePhysicalActiveMovingSimplex 3 y u)
  unfold fourFivePhysicalActiveMovingSimplexKernel
  calc
    (∫ s in fourFivePhysicalActiveMovingSimplex 3 y u,
        fourFivePhysicalActiveMovingSimplexIntegrand 3 y u s) =
        ∫ s in fourFivePhysicalActiveMovingSimplex 3 y u, g (e s) := by
          apply setIntegral_congr_fun
            (measurableSet_fourFivePhysicalActiveMovingSimplex 3 y u)
          intro s _hs
          have hden :
              u - (fourFiveRealLogCoordinate y (s 0) +
                fourFiveRealLogCoordinate y (s 1) +
                  fourFiveRealLogCoordinate y (s 2)) =
                u - fourFiveRealLogCoordinate y (s 0) -
                  fourFiveRealLogCoordinate y (s 1) -
                    fourFiveRealLogCoordinate y (s 2) := by
            ring
          simp [g, e, fourFivePhysicalActiveMovingSimplexIntegrand,
            fourFivePhysicalActiveIntegrandThree, Fin.prod_univ_three,
            Fin.sum_univ_three, hden]
    _ = ∫ p in e '' fourFivePhysicalActiveMovingSimplex 3 y u, g p :=
      hmap.symm
    _ = ∫ p in fourFivePhysicalActiveMovingSimplexThree y u,
        fourFivePhysicalActiveIntegrandThree y u p := by
      rw [image_fourFivePhysicalActiveMovingSimplex_finThree]

theorem fourFivePhysicalActiveMovingSimplexOne_subset_Ioc
    {y B : Nat} {u : Real}
    (hy : 2 <= y) (hyB : y <= B)
    (huB : u <= fourFiveRealLogCoordinate y (B : Real)) :
    fourFivePhysicalActiveMovingSimplexOne y u ⊆
      Set.Ioc (y : Real) (B : Real) := by
  intro x hx
  have hxpos : 0 < x := by
    exact (by exact_mod_cast (show 0 < y by omega) :
      (0 : Real) < y).trans hx.1
  have hBpos : 0 < (B : Real) := by
    exact_mod_cast (show 0 < B by omega)
  have hcoord : fourFiveRealLogCoordinate y x <
      fourFiveRealLogCoordinate y (B : Real) := by
    linarith [hx.2, huB]
  exact ⟨hx.1,
    (lt_of_fourFiveRealLogCoordinate_lt
      (y := y) (x := x) (b := (B : Real))
      hy hxpos hBpos hcoord).le⟩

theorem fourFivePhysicalActiveMovingSimplexTwo_subset_box
    {y B : Nat} {u : Real}
    (hy : 2 <= y) (hyB : y <= B)
    (huB : u <= fourFiveRealLogCoordinate y (B : Real)) :
    fourFivePhysicalActiveMovingSimplexTwo y u ⊆
      Set.Ioc (y : Real) (B : Real) ×ˢ Set.Ioc (y : Real) (B : Real) := by
  intro p hp
  have hBpos : 0 < (B : Real) := by
    exact_mod_cast (show 0 < B by omega)
  have hp1coord : 1 < fourFiveRealLogCoordinate y p.1 :=
    one_lt_fourFiveRealLogCoordinate_of_lt hy hp.1
  have hp2coord : 1 < fourFiveRealLogCoordinate y p.2 :=
    one_lt_fourFiveRealLogCoordinate_of_lt hy hp.2.1
  constructor
  · refine ⟨hp.1,
      (lt_of_fourFiveRealLogCoordinate_lt
        (y := y) (x := p.1) (b := (B : Real))
        hy ?_ hBpos ?_).le⟩
    · exact (by exact_mod_cast (show 0 < y by omega) :
        (0 : Real) < y).trans hp.1
    · linarith [hp.2.2, huB, hp2coord]
  · refine ⟨hp.2.1,
      (lt_of_fourFiveRealLogCoordinate_lt
        (y := y) (x := p.2) (b := (B : Real))
        hy ?_ hBpos ?_).le⟩
    · exact (by exact_mod_cast (show 0 < y by omega) :
        (0 : Real) < y).trans hp.2.1
    · linarith [hp.2.2, huB, hp1coord]

theorem fourFivePhysicalActiveMovingSimplexThree_subset_box
    {y B : Nat} {u : Real}
    (hy : 2 <= y) (hyB : y <= B)
    (huB : u <= fourFiveRealLogCoordinate y (B : Real)) :
    fourFivePhysicalActiveMovingSimplexThree y u ⊆
      (Set.Ioc (y : Real) (B : Real) ×ˢ
        Set.Ioc (y : Real) (B : Real)) ×ˢ
          Set.Ioc (y : Real) (B : Real) := by
  intro p hp
  have hBpos : 0 < (B : Real) := by
    exact_mod_cast (show 0 < B by omega)
  have hp1coord : 1 < fourFiveRealLogCoordinate y p.1.1 :=
    one_lt_fourFiveRealLogCoordinate_of_lt hy hp.1
  have hp2coord : 1 < fourFiveRealLogCoordinate y p.1.2 :=
    one_lt_fourFiveRealLogCoordinate_of_lt hy hp.2.1
  have hp3coord : 1 < fourFiveRealLogCoordinate y p.2 :=
    one_lt_fourFiveRealLogCoordinate_of_lt hy hp.2.2.1
  constructor
  · constructor
    · refine ⟨hp.1,
        (lt_of_fourFiveRealLogCoordinate_lt
          (y := y) (x := p.1.1) (b := (B : Real))
          hy ?_ hBpos ?_).le⟩
      · exact (by exact_mod_cast (show 0 < y by omega) :
          (0 : Real) < y).trans hp.1
      · linarith [hp.2.2.2, huB, hp2coord, hp3coord]
    · refine ⟨hp.2.1,
        (lt_of_fourFiveRealLogCoordinate_lt
          (y := y) (x := p.1.2) (b := (B : Real))
          hy ?_ hBpos ?_).le⟩
      · exact (by exact_mod_cast (show 0 < y by omega) :
          (0 : Real) < y).trans hp.2.1
      · linarith [hp.2.2.2, huB, hp1coord, hp3coord]
  · refine ⟨hp.2.2.1,
      (lt_of_fourFiveRealLogCoordinate_lt
        (y := y) (x := p.2) (b := (B : Real))
        hy ?_ hBpos ?_).le⟩
    · exact (by exact_mod_cast (show 0 < y by omega) :
        (0 : Real) < y).trans hp.2.2.1
    · linarith [hp.2.2.2, huB, hp1coord, hp2coord]

theorem fourFiveStrictLogarithmicMovingSimplex_subset_closed
    (m : Nat) (u : Real) :
    fourFiveStrictLogarithmicMovingSimplex m u ⊆
      fourFiveLogarithmicMovingSimplex m u := by
  intro s hs
  exact ⟨fun i => (hs.1 i).le, hs.2.le⟩

theorem isOpen_fourFiveStrictLogarithmicMovingSimplex
    (m : Nat) (u : Real) :
    IsOpen (fourFiveStrictLogarithmicMovingSimplex m u) := by
  have hcoord : IsOpen {s : Fin m -> Real | ∀ i, 1 < s i} := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_apply i)
  have hsum : IsOpen {s : Fin m -> Real | (∑ i, s i) < u - 1} :=
    isOpen_lt
      (continuous_finset_sum Finset.univ fun i _hi => continuous_apply i)
      continuous_const
  convert hcoord.inter hsum using 1

theorem isClosed_fourFiveLogarithmicMovingSimplex
    (m : Nat) (u : Real) :
    IsClosed (fourFiveLogarithmicMovingSimplex m u) := by
  have hcoord : IsClosed {s : Fin m -> Real | ∀ i, 1 <= s i} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun i =>
      isClosed_le continuous_const (continuous_apply i)
  have hsum : IsClosed {s : Fin m -> Real | (∑ i, s i) <= u - 1} :=
    isClosed_le
      (continuous_finset_sum Finset.univ fun i _hi => continuous_apply i)
      continuous_const
  convert hcoord.inter hsum using 1

theorem convex_fourFiveLogarithmicMovingSimplex
    (m : Nat) (u : Real) :
    Convex Real (fourFiveLogarithmicMovingSimplex m u) := by
  rw [convex_iff_add_mem]
  intro a ha b hb c d hc hd hcd
  constructor
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      1 = c * 1 + d * 1 := by rw [← add_mul, hcd, one_mul]
      _ <= c * a i + d * b i :=
        add_le_add
          (mul_le_mul_of_nonneg_left (ha.1 i) hc)
          (mul_le_mul_of_nonneg_left (hb.1 i) hd)
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    calc
      c * (∑ i, a i) + d * (∑ i, b i) <=
          c * (u - 1) + d * (u - 1) :=
        add_le_add
          (mul_le_mul_of_nonneg_left ha.2 hc)
          (mul_le_mul_of_nonneg_left hb.2 hd)
      _ = u - 1 := by rw [← add_mul, hcd, one_mul]

def fourFiveCoordinateSumCLM (m : Nat) :
    (Fin m -> Real) →L[Real] Real :=
  ∑ i, (ContinuousLinearMap.proj i :
    (Fin m -> Real) →L[Real] Real)

@[simp] theorem fourFiveCoordinateSumCLM_apply
    (m : Nat) (s : Fin m -> Real) :
    fourFiveCoordinateSumCLM m s = ∑ i, s i := by
  simp [fourFiveCoordinateSumCLM]

theorem fourFiveCoordinateSumCLM_surjective
    {m : Nat} (hm : 1 <= m) :
    Function.Surjective (fourFiveCoordinateSumCLM m) := by
  classical
  haveI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  intro r
  let s : Fin m -> Real := Pi.single (0 : Fin m) r
  refine ⟨s, ?_⟩
  simp [s]

/-- Every interior point of the closed moving simplex has all inequalities
strict.  Only this inclusion is needed: the reverse inclusion is not used
in the null-frontier argument. -/
theorem interior_fourFiveLogarithmicMovingSimplex_subset_strict
    {m : Nat} (hm : 1 <= m) (u : Real) :
    interior (fourFiveLogarithmicMovingSimplex m u) ⊆
      fourFiveStrictLogarithmicMovingSimplex m u := by
  intro s hs
  constructor
  · intro i
    let p : (Fin m -> Real) →L[Real] Real :=
      ContinuousLinearMap.proj i
    have hsub : fourFiveLogarithmicMovingSimplex m u ⊆
        p ⁻¹' Set.Ici 1 := by
      intro z hz
      exact hz.1 i
    have hi : s ∈ interior (p ⁻¹' Set.Ici 1) :=
      interior_mono hsub hs
    have hopen : IsOpenMap p :=
      p.isOpenMap (LinearMap.proj_surjective i)
    rw [← hopen.preimage_interior_eq_interior_preimage p.continuous,
      interior_Ici] at hi
    exact hi
  · let S := fourFiveCoordinateSumCLM m
    have hsub : fourFiveLogarithmicMovingSimplex m u ⊆
        S ⁻¹' Set.Iic (u - 1) := by
      intro z hz
      simpa [S] using hz.2
    have hi : s ∈ interior (S ⁻¹' Set.Iic (u - 1)) :=
      interior_mono hsub hs
    have hopen : IsOpenMap S :=
      S.isOpenMap (fourFiveCoordinateSumCLM_surjective hm)
    rw [← hopen.preimage_interior_eq_interior_preimage S.continuous,
      interior_Iic] at hi
    simpa [S] using hi

theorem fourFiveStrictLogarithmicMovingSimplex_ae_eq_closed
    {m : Nat} (hm : 1 <= m) (u : Real) :
    fourFiveStrictLogarithmicMovingSimplex m u =ᵐ[volume]
      fourFiveLogarithmicMovingSimplex m u := by
  have hclosed := isClosed_fourFiveLogarithmicMovingSimplex m u
  have hfrontier : volume
      (frontier (fourFiveLogarithmicMovingSimplex m u)) = 0 :=
    (convex_fourFiveLogarithmicMovingSimplex m u).addHaar_frontier volume
  have hdiff : volume
      (fourFiveLogarithmicMovingSimplex m u \
        fourFiveStrictLogarithmicMovingSimplex m u) = 0 := by
    refine measure_mono_null ?_ hfrontier
    intro s hs
    rw [frontier, hclosed.closure_eq]
    exact ⟨hs.1, fun his => hs.2
      (interior_fourFiveLogarithmicMovingSimplex_subset_strict hm u his)⟩
  apply ae_eq_set.mpr
  constructor
  · rw [diff_eq_empty.mpr
      (fourFiveStrictLogarithmicMovingSimplex_subset_closed m u),
      measure_empty]
  · exact hdiff

theorem fourFiveStrictLogarithmicMovingSimplexKernel_eq_closed
    {m : Nat} (hm : 1 <= m) (u : Real) :
    (∫ s in fourFiveStrictLogarithmicMovingSimplex m u,
      fourFiveLogarithmicMovingSimplexIntegrand m u s) =
      fourFiveLogarithmicMovingSimplexKernel m u := by
  unfold fourFiveLogarithmicMovingSimplexKernel
  exact setIntegral_congr_set
    (fourFiveStrictLogarithmicMovingSimplex_ae_eq_closed hm u)

/-! ## The coordinatewise exponential map and its Jacobian -/

def fourFiveLogCoordinateExpMap
    (m : Nat) (y : Nat) (s : Fin m -> Real) : Fin m -> Real :=
  fun i => Real.exp (Real.log (y : Real) * s i)

def fourFiveLogCoordinateExpDerivative
    (m : Nat) (y : Nat) (s : Fin m -> Real) :
    (Fin m -> Real) →L[Real] (Fin m -> Real) :=
  ContinuousLinearMap.pi fun i =>
    (ContinuousLinearMap.smulRight (1 : Real →L[Real] Real)
      (Real.log (y : Real) *
        Real.exp (Real.log (y : Real) * s i))).comp
      (ContinuousLinearMap.proj i)

theorem hasFDerivAt_fourFiveLogCoordinateExpMap
    (m : Nat) (y : Nat) (s : Fin m -> Real) :
    HasFDerivAt (fourFiveLogCoordinateExpMap m y)
      (fourFiveLogCoordinateExpDerivative m y s) s := by
  rw [fourFiveLogCoordinateExpDerivative, hasFDerivAt_pi]
  intro i
  convert (Real.hasDerivAt_exp _).hasFDerivAt.comp s
    ((hasFDerivAt_apply i s).const_smul (Real.log (y : Real))) using 1
  ext v
  simp
  ring

theorem det_fourFiveLogCoordinateExpDerivative
    (m : Nat) (y : Nat) (s : Fin m -> Real) :
    (fourFiveLogCoordinateExpDerivative m y s).det =
      ∏ i, (Real.log (y : Real) *
        Real.exp (Real.log (y : Real) * s i)) := by
  simp [fourFiveLogCoordinateExpDerivative, ContinuousLinearMap.det_pi]

theorem fourFiveLogCoordinateExpMap_injective
    {m y : Nat} (hy : 2 <= y) :
    Function.Injective (fourFiveLogCoordinateExpMap m y) := by
  have hlog : Real.log (y : Real) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < y by omega)))
  intro s t hst
  funext i
  have hi := congrFun hst i
  have hexp : Real.log (y : Real) * s i =
      Real.log (y : Real) * t i := Real.exp_injective hi
  exact (mul_left_cancel₀ hlog hexp)

@[simp] theorem fourFiveRealLogCoordinate_expMap
    {m y : Nat} (hy : 2 <= y) (s : Fin m -> Real) (i : Fin m) :
    fourFiveRealLogCoordinate y
        (fourFiveLogCoordinateExpMap m y s i) = s i := by
  have hlog : Real.log (y : Real) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < y by omega)))
  unfold fourFiveRealLogCoordinate fourFiveLogCoordinateExpMap
  rw [Real.log_exp]
  field_simp [hlog]

theorem image_fourFiveStrictLogarithmicSimplex_exp_eq_physical
    {m y : Nat} (hy : 2 <= y) (u : Real) :
    fourFiveLogCoordinateExpMap m y ''
        fourFiveStrictLogarithmicMovingSimplex m u =
      fourFivePhysicalActiveMovingSimplex m y u := by
  have hypos : 0 < (y : Real) := by exact_mod_cast (show 0 < y by omega)
  have hlogpos : 0 < Real.log (y : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    constructor
    · intro i
      calc
        (y : Real) = Real.exp (Real.log (y : Real)) :=
          (Real.exp_log hypos).symm
        _ < Real.exp (Real.log (y : Real) * s i) :=
          Real.exp_lt_exp.mpr (by nlinarith [hs.1 i])
    · simpa [fourFiveRealLogCoordinate_expMap hy] using hs.2
  · intro hx
    let s : Fin m -> Real := fun i => fourFiveRealLogCoordinate y (x i)
    refine ⟨s, ?_, ?_⟩
    · constructor
      · intro i
        have hloglt : Real.log (y : Real) < Real.log (x i) :=
          Real.strictMonoOn_log
            (by simpa only [Set.mem_Ioi] using hypos)
            (hypos.trans (hx.1 i)) (hx.1 i)
        unfold s fourFiveRealLogCoordinate
        exact (lt_div_iff₀ hlogpos).mpr (by simpa [one_mul] using hloglt)
      · exact hx.2
    · funext i
      unfold fourFiveLogCoordinateExpMap s fourFiveRealLogCoordinate
      have hxi : 0 < x i := hypos.trans (hx.1 i)
      rw [mul_div_cancel₀ _ hlogpos.ne', Real.exp_log hxi]

theorem abs_det_fourFiveLogCoordinateExpDerivative
    {m y : Nat} (hy : 2 <= y) (s : Fin m -> Real) :
    abs (fourFiveLogCoordinateExpDerivative m y s).det =
      ∏ i, (Real.log (y : Real) *
        Real.exp (Real.log (y : Real) * s i)) := by
  rw [det_fourFiveLogCoordinateExpDerivative,
    abs_of_pos (Finset.prod_pos fun i _hi =>
      mul_pos
        (Real.log_pos (by exact_mod_cast (show 1 < y by omega)))
        (Real.exp_pos _))]

theorem fourFive_expJacobian_mul_physicalIntegrand
    {m y : Nat} (hy : 2 <= y) {u : Real}
    {s : Fin m -> Real}
    (hs : s ∈ fourFiveStrictLogarithmicMovingSimplex m u) :
    abs (fourFiveLogCoordinateExpDerivative m y s).det *
        fourFivePhysicalActiveMovingSimplexIntegrand m y u
          (fourFiveLogCoordinateExpMap m y s) =
      fourFiveLogarithmicMovingSimplexIntegrand m u s := by
  have hlogpos : 0 < Real.log (y : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hfactor (i : Fin m) :
      (Real.log (y : Real) *
          Real.exp (Real.log (y : Real) * s i)) *
        fourFiveLogLogLebesgueDensity
          (fourFiveLogCoordinateExpMap m y s i) = (s i)⁻¹ := by
    have hsi : s i ≠ 0 := ne_of_gt (zero_lt_one.trans (hs.1 i))
    unfold fourFiveLogLogLebesgueDensity fourFiveLogCoordinateExpMap
    rw [Real.log_exp]
    field_simp [hlogpos.ne', hsi]
  rw [abs_det_fourFiveLogCoordinateExpDerivative hy]
  unfold fourFivePhysicalActiveMovingSimplexIntegrand
    fourFiveLogarithmicMovingSimplexIntegrand
  simp_rw [fourFiveRealLogCoordinate_expMap hy]
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  simp_rw [hfactor]

/-- Exact physical-to-logarithmic identification on the active region.
The final equality includes the strict-face boundary: it is null because it
lies in the frontier of the closed convex moving simplex. -/
theorem fourFivePhysicalActiveMovingSimplexKernel_eq_logarithmic
    {m y : Nat} (hm : 1 <= m) (hy : 2 <= y) (u : Real) :
    fourFivePhysicalActiveMovingSimplexKernel m y u =
      fourFiveLogarithmicMovingSimplexKernel m u := by
  have himage := image_fourFiveStrictLogarithmicSimplex_exp_eq_physical
    (m := m) hy u
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul
    volume (isOpen_fourFiveStrictLogarithmicMovingSimplex m u).measurableSet
    (fun s _hs =>
      (hasFDerivAt_fourFiveLogCoordinateExpMap m y s).hasFDerivWithinAt)
    (fourFiveLogCoordinateExpMap_injective (m := m) hy).injOn
    (fourFivePhysicalActiveMovingSimplexIntegrand m y u)
  unfold fourFivePhysicalActiveMovingSimplexKernel
  rw [← himage, hchange]
  rw [← fourFiveStrictLogarithmicMovingSimplexKernel_eq_closed hm u]
  apply setIntegral_congr_fun
    (isOpen_fourFiveStrictLogarithmicMovingSimplex m u).measurableSet
  intro s hs
  simpa only [smul_eq_mul] using
    fourFive_expJacobian_mul_physicalIntegrand hy hs

/-! ## The literal finite cells equal the logarithmic kernel -/

/-- In one coordinate, the finite union `(y,B]` contains the entire strict
active support as soon as `u <= log_y B`. -/
theorem fourFiveMovingFaceRealCellIntegralSum_eq_physicalActiveKernel
    {y B : Nat} {u : Real}
    (hy : 2 <= y) (hyB : y <= B)
    (huB : u <= fourFiveRealLogCoordinate y (B : Real)) :
    fourFiveMovingFaceRealCellIntegralSum y B y u 0 =
      fourFivePhysicalActiveMovingSimplexKernel 1 y u := by
  let S := fourFivePhysicalActiveMovingSimplexOne y u
  let box := Set.Ioc (y : Real) (B : Real)
  let f : Real -> Real := fun x =>
    fourFiveLogLogLebesgueDensity x *
      fourFiveRealMovingSimplexKernelOne y y u x
  let g := fourFivePhysicalActiveIntegrandOne y u
  have hyB' : (y : Real) <= (B : Real) := by exact_mod_cast hyB
  have hSbox : S ⊆ box :=
    fourFivePhysicalActiveMovingSimplexOne_subset_Ioc hy hyB huB
  have hzero : ∀ x ∈ box \ S, f x = 0 := by
    intro x hx
    unfold f fourFiveRealMovingSimplexKernelOne
      fourFiveRealMovingFaceKernel
    rw [if_neg]
    · ring
    · intro hactive
      apply hx.2
      exact ⟨hactive.1, by linarith [hactive.2]⟩
  have hrestrict : (∫ x in box, f x) = ∫ x in S, f x :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero
      measurableSet_Ioc hSbox hzero
  rw [fourFiveMovingFaceRealCellIntegralSum_eq_interval hy le_rfl hyB,
    intervalIntegral.integral_of_le hyB']
  change (∫ x in box, f x) = _
  calc
    (∫ x in box, f x) = ∫ x in S, f x := hrestrict
    _ = ∫ x in S, g x := by
      apply setIntegral_congr_fun
        (measurableSet_fourFivePhysicalActiveMovingSimplexOne y u)
      intro x hx
      unfold f g fourFivePhysicalActiveIntegrandOne
        fourFiveRealMovingSimplexKernelOne fourFiveRealMovingFaceKernel
        fourFiveRealMovingFaceReciprocal
      rw [if_pos ⟨hx.1, by linarith [hx.2]⟩]
      ring
    _ = fourFivePhysicalActiveMovingSimplexKernel 1 y u :=
      (fourFivePhysicalActiveMovingSimplexKernel_one_eq_setIntegral y u).symm

theorem fourFiveMovingSimplexActivePhysicalIntegralTwo_eq_physicalActiveKernel
    {y B : Nat} {u : Real}
    (hy : 2 <= y) (hyB : y <= B)
    (huB : u <= fourFiveRealLogCoordinate y (B : Real)) :
    fourFiveMovingSimplexActivePhysicalIntegralTwo y B y u =
      fourFivePhysicalActiveMovingSimplexKernel 2 y u := by
  let S := fourFivePhysicalActiveMovingSimplexTwo y u
  let box := Set.Ioc (y : Real) (B : Real)
  let f : Real × Real -> Real := fun p =>
    fourFiveLogLogLebesgueDensity p.1 *
      fourFiveLogLogLebesgueDensity p.2 *
        fourFiveRealMovingSimplexKernelTwo y y u p.1 p.2
  let g := fourFivePhysicalActiveIntegrandTwo y u
  have hyB' : (y : Real) <= (B : Real) := by exact_mod_cast hyB
  have hSbox : S ⊆ box ×ˢ box :=
    fourFivePhysicalActiveMovingSimplexTwo_subset_box hy hyB huB
  have hzero : ∀ p ∈ (box ×ˢ box) \ S, f p = 0 := by
    intro p hp
    unfold f fourFiveRealMovingSimplexKernelTwo
    rw [if_neg]
    · ring
    · intro hactive
      exact hp.2 hactive
  have hjointVolume :=
    integrableOn_fourFiveRealMovingSimplexDensityTwo_activeBox
      (A := y) (Y := B) (y := y) (u := u) hy le_rfl
  have hjoint : IntegrableOn f (box ×ˢ box)
      ((volume : Measure Real).prod volume) := by
    rw [← Measure.volume_eq_prod]
    simpa [f, box] using hjointVolume
  have hfub := setIntegral_prod f hjoint
  have hrestrict : (∫ p in box ×ˢ box, f p) = ∫ p in S, f p :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero
      (measurableSet_Ioc.prod measurableSet_Ioc) hSbox hzero
  unfold fourFiveMovingSimplexActivePhysicalIntegralTwo
  rw [intervalIntegral.integral_of_le hyB']
  simp_rw [intervalIntegral.integral_of_le hyB']
  change (∫ x in box,
    fourFiveLogLogLebesgueDensity x *
      ∫ z in box, fourFiveLogLogLebesgueDensity z *
        fourFiveRealMovingSimplexKernelTwo y y u x z) = _
  calc
    (∫ x in box,
        fourFiveLogLogLebesgueDensity x *
          ∫ z in box, fourFiveLogLogLebesgueDensity z *
            fourFiveRealMovingSimplexKernelTwo y y u x z) =
        ∫ p in box ×ˢ box, f p := by
          simpa [f, MeasureTheory.integral_const_mul, mul_assoc] using hfub.symm
    _ = ∫ p in S, f p := hrestrict
    _ = ∫ p in S, g p := by
      apply setIntegral_congr_fun
        (measurableSet_fourFivePhysicalActiveMovingSimplexTwo y u)
      intro p hp
      unfold f g fourFivePhysicalActiveIntegrandTwo
        fourFiveRealMovingSimplexKernelTwo
      have hactive :
          (y : Real) < p.1 ∧ (y : Real) < p.2 ∧
            fourFiveRealLogCoordinate y p.1 +
              fourFiveRealLogCoordinate y p.2 < u - 1 := by
        simpa [S, fourFivePhysicalActiveMovingSimplexTwo] using hp
      rw [if_pos hactive]
    _ = fourFivePhysicalActiveMovingSimplexKernel 2 y u :=
      (fourFivePhysicalActiveMovingSimplexKernel_two_eq_setIntegral y u).symm

theorem fourFiveMovingSimplexActivePhysicalIntegralThree_eq_physicalActiveKernel
    {y B : Nat} {u : Real}
    (hy : 2 <= y) (hyB : y <= B)
    (huB : u <= fourFiveRealLogCoordinate y (B : Real)) :
    fourFiveMovingSimplexActivePhysicalIntegralThree y B y u =
      fourFivePhysicalActiveMovingSimplexKernel 3 y u := by
  let S := fourFivePhysicalActiveMovingSimplexThree y u
  let box := Set.Ioc (y : Real) (B : Real)
  let boxTwo := box ×ˢ box
  let f : (Real × Real) × Real -> Real := fun p =>
    fourFiveLogLogLebesgueDensity p.1.1 *
      fourFiveLogLogLebesgueDensity p.1.2 *
        fourFiveLogLogLebesgueDensity p.2 *
          fourFiveRealMovingSimplexKernelThree y y u p.1.1 p.1.2 p.2
  let g := fourFivePhysicalActiveIntegrandThree y u
  have hyB' : (y : Real) <= (B : Real) := by exact_mod_cast hyB
  have hSbox : S ⊆ boxTwo ×ˢ box :=
    fourFivePhysicalActiveMovingSimplexThree_subset_box hy hyB huB
  have hzero : ∀ p ∈ (boxTwo ×ˢ box) \ S, f p = 0 := by
    intro p hp
    unfold f fourFiveRealMovingSimplexKernelThree
    rw [if_neg]
    · ring
    · intro hactive
      exact hp.2 hactive
  have hjointVolume :=
    integrableOn_fourFiveRealMovingSimplexDensityThree_activeBox
      (A := y) (Y := B) (y := y) (u := u) hy le_rfl
  have hjoint : IntegrableOn f (boxTwo ×ˢ box)
      ((volume : Measure (Real × Real)).prod volume) := by
    rw [← Measure.volume_eq_prod]
    simpa [f, box, boxTwo] using hjointVolume
  have hfubLast := setIntegral_prod f hjoint
  have hjointRestrict : Integrable f
      ((volume.restrict boxTwo).prod (volume.restrict box)) := by
    simpa only [IntegrableOn, ← Measure.prod_restrict] using hjoint
  have hpartialRestrict := hjointRestrict.integral_prod_left
  have hpartialVolume : IntegrableOn
      (fun p : Real × Real => ∫ w in box, f (p, w)) boxTwo volume := by
    simpa only [IntegrableOn] using hpartialRestrict
  have hpartial : IntegrableOn
      (fun p : Real × Real => ∫ w in box, f (p, w)) boxTwo
        ((volume : Measure Real).prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hpartialVolume
  have hfubFirst := setIntegral_prod
    (fun p : Real × Real => ∫ w in box, f (p, w)) hpartial
  have hfub : (∫ p in boxTwo ×ˢ box, f p) =
      ∫ x in box, ∫ z in box, ∫ w in box, f ((x, z), w) := by
    calc
      (∫ p in boxTwo ×ˢ box, f p) =
          ∫ p in boxTwo, ∫ w in box, f (p, w) := hfubLast
      _ = ∫ x in box, ∫ z in box, ∫ w in box, f ((x, z), w) :=
        hfubFirst
  have hrestrict : (∫ p in boxTwo ×ˢ box, f p) = ∫ p in S, f p :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero
      ((measurableSet_Ioc.prod measurableSet_Ioc).prod measurableSet_Ioc)
      hSbox hzero
  unfold fourFiveMovingSimplexActivePhysicalIntegralThree
  rw [intervalIntegral.integral_of_le hyB']
  simp_rw [intervalIntegral.integral_of_le hyB']
  change (∫ x in box,
    fourFiveLogLogLebesgueDensity x *
      ∫ z in box, fourFiveLogLogLebesgueDensity z *
        ∫ w in box, fourFiveLogLogLebesgueDensity w *
          fourFiveRealMovingSimplexKernelThree y y u x z w) = _
  calc
    (∫ x in box,
        fourFiveLogLogLebesgueDensity x *
          ∫ z in box, fourFiveLogLogLebesgueDensity z *
            ∫ w in box, fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree y y u x z w) =
        ∫ p in boxTwo ×ˢ box, f p := by
          simpa [f, MeasureTheory.integral_const_mul, mul_assoc] using hfub.symm
    _ = ∫ p in S, f p := hrestrict
    _ = ∫ p in S, g p := by
      apply setIntegral_congr_fun
        (measurableSet_fourFivePhysicalActiveMovingSimplexThree y u)
      intro p hp
      unfold f g fourFivePhysicalActiveIntegrandThree
        fourFiveRealMovingSimplexKernelThree
      have hactive :
          (y : Real) < p.1.1 ∧ (y : Real) < p.1.2 ∧
            (y : Real) < p.2 ∧
            fourFiveRealLogCoordinate y p.1.1 +
                fourFiveRealLogCoordinate y p.1.2 +
              fourFiveRealLogCoordinate y p.2 < u - 1 := by
        simpa [S, fourFivePhysicalActiveMovingSimplexThree] using hp
      rw [if_pos hactive]
    _ = fourFivePhysicalActiveMovingSimplexKernel 3 y u :=
      (fourFivePhysicalActiveMovingSimplexKernel_three_eq_setIntegral y u).symm

theorem fourFiveMovingFaceRealCellIntegralSum_eq_logarithmicKernel
    {y B : Nat} {u : Real}
    (hy : 2 <= y) (hyB : y <= B)
    (huB : u <= fourFiveRealLogCoordinate y (B : Real)) :
    fourFiveMovingFaceRealCellIntegralSum y B y u 0 =
      fourFiveLogarithmicMovingSimplexKernel 1 u := by
  rw [fourFiveMovingFaceRealCellIntegralSum_eq_physicalActiveKernel hy hyB huB,
    fourFivePhysicalActiveMovingSimplexKernel_eq_logarithmic
      (m := 1) (y := y) (u := u) (by omega) hy]

theorem fourFiveMovingSimplexIteratedRealCellProductTwo_eq_logarithmicKernel
    {y B : Nat} {u : Real}
    (hy : 2 <= y) (hyB : y <= B)
    (huB : u <= fourFiveRealLogCoordinate y (B : Real)) :
    fourFiveMovingSimplexIteratedRealCellProductTwo y B y u =
      fourFiveLogarithmicMovingSimplexKernel 2 u := by
  rw [fourFiveMovingSimplexIteratedRealCellProductTwo_eq_activePhysical
      hy le_rfl hyB,
    fourFiveMovingSimplexActivePhysicalIntegralTwo_eq_physicalActiveKernel
      hy hyB huB,
    fourFivePhysicalActiveMovingSimplexKernel_eq_logarithmic
      (m := 2) (y := y) (u := u) (by omega) hy]

theorem fourFiveMovingSimplexIteratedRealCellProductThree_eq_logarithmicKernel
    {y B : Nat} {u : Real}
    (hy : 2 <= y) (hyB : y <= B)
    (huB : u <= fourFiveRealLogCoordinate y (B : Real)) :
    fourFiveMovingSimplexIteratedRealCellProductThree y B y u =
      fourFiveLogarithmicMovingSimplexKernel 3 u := by
  rw [fourFiveMovingSimplexIteratedRealCellProductThree_eq_activePhysical
      hy le_rfl hyB,
    fourFiveMovingSimplexActivePhysicalIntegralThree_eq_physicalActiveKernel
      hy hyB huB,
    fourFivePhysicalActiveMovingSimplexKernel_eq_logarithmic
      (m := 3) (y := y) (u := u) (by omega) hy]

end Erdos390.WholePaper.BankPaperRealization
