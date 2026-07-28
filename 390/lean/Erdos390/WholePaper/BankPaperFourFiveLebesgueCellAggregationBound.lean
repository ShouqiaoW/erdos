import Erdos390.WholePaper.BankPaperFourFiveActiveLogCoordinate

/-!
# Explicit bound for the Lebesgue-cell aggregation residual

The fixed physical box `(y,B]` is used as a measurable proxy under the
outer `t` integral.  The exact active-cell/log-coordinate results identify
that proxy with the logarithmic moving simplex whenever `t <= B`.  This
file then integrates the pointwise cell bounds, preserving the constants
`2`, `4`, and `6` in dimensions one, two, and three.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-! ## Joint measurability in the outer parameter -/

private theorem measurable_fourFiveMovingFaceKernel_parameter
    (A y n : Nat) (c : Real) :
    Measurable (fun u : Real => fourFiveMovingFaceKernel A y u c n) := by
  by_cases hAn : A < n
  · have hactive : MeasurableSet
        {u : Real | fourFiveLogCoordinate y n < u - c - 1} :=
      measurableSet_lt measurable_const
        ((measurable_id.sub measurable_const).sub measurable_const)
    have hrecip : Measurable (fun u : Real =>
        (u - c - fourFiveLogCoordinate y n)⁻¹) :=
      ((measurable_id.sub measurable_const).sub measurable_const).inv
    simp only [fourFiveMovingFaceKernel, hAn, true_and]
    exact Measurable.ite hactive hrecip measurable_const
  · simp [fourFiveMovingFaceKernel, hAn]

private theorem measurable_fourFiveMovingSimplexKernelTwo_parameter
    (A y p q : Nat) :
    Measurable (fun u : Real =>
      fourFiveMovingSimplexKernelTwo A y u p q) := by
  by_cases hp : A < p
  · by_cases hq : A < q
    · have hactive : MeasurableSet {u : Real |
        fourFiveLogCoordinate y p + fourFiveLogCoordinate y q < u - 1} :=
        measurableSet_lt measurable_const
          (measurable_id.sub measurable_const)
      have hrecip : Measurable (fun u : Real =>
        (u - fourFiveLogCoordinate y p - fourFiveLogCoordinate y q)⁻¹) :=
        ((measurable_id.sub measurable_const).sub measurable_const).inv
      simp only [fourFiveMovingSimplexKernelTwo, hp, hq, true_and]
      exact Measurable.ite hactive hrecip measurable_const
    · simp [fourFiveMovingSimplexKernelTwo, hq]
  · simp [fourFiveMovingSimplexKernelTwo, hp]

private theorem measurable_fourFiveMovingSimplexKernelThree_parameter
    (A y p q r : Nat) :
    Measurable (fun u : Real =>
      fourFiveMovingSimplexKernelThree A y u p q r) := by
  by_cases hp : A < p
  · by_cases hq : A < q
    · by_cases hr : A < r
      · have hactive : MeasurableSet {u : Real |
            fourFiveLogCoordinate y p + fourFiveLogCoordinate y q +
              fourFiveLogCoordinate y r < u - 1} :=
          measurableSet_lt measurable_const
            (measurable_id.sub measurable_const)
        have hrecip : Measurable (fun u : Real =>
            (u - fourFiveLogCoordinate y p - fourFiveLogCoordinate y q -
              fourFiveLogCoordinate y r)⁻¹) :=
          (((measurable_id.sub measurable_const).sub measurable_const).sub
            measurable_const).inv
        simp only [fourFiveMovingSimplexKernelThree, hp, hq, hr, true_and]
        exact Measurable.ite hactive hrecip measurable_const
      · simp [fourFiveMovingSimplexKernelThree, hr]
    · simp [fourFiveMovingSimplexKernelThree, hq]
  · simp [fourFiveMovingSimplexKernelThree, hp]

private theorem measurable_fourFiveRealMovingSimplexKernelOne_joint
    (A y : Nat) :
    Measurable (fun p : Real × Real =>
      fourFiveRealMovingSimplexKernelOne A y p.1 p.2) := by
  unfold fourFiveRealMovingSimplexKernelOne fourFiveRealMovingFaceKernel
    fourFiveRealMovingFaceReciprocal
  have hcoord : Measurable (fun p : Real × Real =>
      fourFiveRealLogCoordinate y p.2) :=
    (measurable_fourFiveRealLogCoordinate y).comp measurable_snd
  have hactive : MeasurableSet {p : Real × Real |
      (A : Real) < p.2 ∧
        fourFiveRealLogCoordinate y p.2 < p.1 - 0 - 1} :=
    (measurable_snd measurableSet_Ioi).inter
      (measurableSet_lt hcoord
        ((measurable_fst.sub measurable_const).sub measurable_const))
  have hrecip : Measurable (fun p : Real × Real =>
      (p.1 - 0 - fourFiveRealLogCoordinate y p.2)⁻¹) :=
    ((measurable_fst.sub measurable_const).sub hcoord).inv
  exact Measurable.ite hactive hrecip measurable_const

private theorem measurable_fourFiveRealMovingSimplexKernelTwo_joint
    (A y : Nat) :
    Measurable (fun p : Real × (Real × Real) =>
      fourFiveRealMovingSimplexKernelTwo A y p.1 p.2.1 p.2.2) := by
  have hx : Measurable (fun p : Real × (Real × Real) =>
      fourFiveRealLogCoordinate y p.2.1) :=
    (measurable_fourFiveRealLogCoordinate y).comp
      (measurable_fst.comp measurable_snd)
  have hz : Measurable (fun p : Real × (Real × Real) =>
      fourFiveRealLogCoordinate y p.2.2) :=
    (measurable_fourFiveRealLogCoordinate y).comp
      (measurable_snd.comp measurable_snd)
  have hactive : MeasurableSet {p : Real × (Real × Real) |
      (A : Real) < p.2.1 ∧ (A : Real) < p.2.2 ∧
        fourFiveRealLogCoordinate y p.2.1 +
          fourFiveRealLogCoordinate y p.2.2 < p.1 - 1} :=
    ((measurable_fst.comp measurable_snd) measurableSet_Ioi).inter
      (((measurable_snd.comp measurable_snd) measurableSet_Ioi).inter
        (measurableSet_lt (hx.add hz)
          (measurable_fst.sub measurable_const)))
  have hrecip : Measurable (fun p : Real × (Real × Real) =>
      (p.1 - fourFiveRealLogCoordinate y p.2.1 -
        fourFiveRealLogCoordinate y p.2.2)⁻¹) :=
    ((measurable_fst.sub hx).sub hz).inv
  unfold fourFiveRealMovingSimplexKernelTwo
  exact Measurable.ite hactive hrecip measurable_const

private theorem measurable_fourFiveRealMovingSimplexKernelThree_joint
    (A y : Nat) :
    Measurable (fun p : Real × ((Real × Real) × Real) =>
      fourFiveRealMovingSimplexKernelThree A y p.1
        p.2.1.1 p.2.1.2 p.2.2) := by
  have hx : Measurable (fun p : Real × ((Real × Real) × Real) =>
      fourFiveRealLogCoordinate y p.2.1.1) :=
    (measurable_fourFiveRealLogCoordinate y).comp
      (measurable_fst.comp (measurable_fst.comp measurable_snd))
  have hz : Measurable (fun p : Real × ((Real × Real) × Real) =>
      fourFiveRealLogCoordinate y p.2.1.2) :=
    (measurable_fourFiveRealLogCoordinate y).comp
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hw : Measurable (fun p : Real × ((Real × Real) × Real) =>
      fourFiveRealLogCoordinate y p.2.2) :=
    (measurable_fourFiveRealLogCoordinate y).comp
      (measurable_snd.comp measurable_snd)
  have hactive : MeasurableSet {p : Real × ((Real × Real) × Real) |
      (A : Real) < p.2.1.1 ∧ (A : Real) < p.2.1.2 ∧
        (A : Real) < p.2.2 ∧
        fourFiveRealLogCoordinate y p.2.1.1 +
          fourFiveRealLogCoordinate y p.2.1.2 +
            fourFiveRealLogCoordinate y p.2.2 < p.1 - 1} :=
    ((measurable_fst.comp (measurable_fst.comp measurable_snd))
      measurableSet_Ioi).inter
      (((measurable_snd.comp (measurable_fst.comp measurable_snd))
        measurableSet_Ioi).inter
        (((measurable_snd.comp measurable_snd) measurableSet_Ioi).inter
          (measurableSet_lt ((hx.add hz).add hw)
            (measurable_fst.sub measurable_const))))
  have hrecip : Measurable (fun p : Real × ((Real × Real) × Real) =>
      (p.1 - fourFiveRealLogCoordinate y p.2.1.1 -
        fourFiveRealLogCoordinate y p.2.1.2 -
          fourFiveRealLogCoordinate y p.2.2)⁻¹) :=
    (((measurable_fst.sub hx).sub hz).sub hw).inv
  unfold fourFiveRealMovingSimplexKernelThree
  exact Measurable.ite hactive hrecip measurable_const

/-! ## Measurable fixed-box proxies -/

def fourFiveActivePhysicalProxyOne
    (y B : Nat) (t : Real) : Real :=
  ∫ x in (y : Real)..(B : Real),
    fourFiveLogLogLebesgueDensity x *
      fourFiveRealMovingSimplexKernelOne y y
        (fourFiveRealLogCoordinate y t) x

def fourFiveActivePhysicalProxyTwo
    (y B : Nat) (t : Real) : Real :=
  ∫ x in (y : Real)..(B : Real),
    ∫ z in (y : Real)..(B : Real),
      fourFiveLogLogLebesgueDensity x *
        fourFiveLogLogLebesgueDensity z *
          fourFiveRealMovingSimplexKernelTwo y y
            (fourFiveRealLogCoordinate y t) x z

def fourFiveActivePhysicalProxyThree
    (y B : Nat) (t : Real) : Real :=
  ∫ x in (y : Real)..(B : Real),
    ∫ z in (y : Real)..(B : Real),
      ∫ w in (y : Real)..(B : Real),
        fourFiveLogLogLebesgueDensity x *
          fourFiveLogLogLebesgueDensity z *
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree y y
                (fourFiveRealLogCoordinate y t) x z w

theorem measurable_fourFiveActivePhysicalProxyOne
    {y B : Nat} (hyB : y <= B) :
    Measurable (fourFiveActivePhysicalProxyOne y B) := by
  have hyB' : (y : Real) <= (B : Real) := by exact_mod_cast hyB
  let box := Set.Ioc (y : Real) (B : Real)
  have hK : Measurable (fun p : Real × Real =>
      fourFiveRealMovingSimplexKernelOne y y
        (fourFiveRealLogCoordinate y p.1) p.2) :=
    (measurable_fourFiveRealMovingSimplexKernelOne_joint y y).comp
      ((measurable_fourFiveRealLogCoordinate y).comp measurable_fst |>.prodMk
        measurable_snd)
  have hjoint : StronglyMeasurable (fun p : Real × Real =>
      fourFiveLogLogLebesgueDensity p.2 *
        fourFiveRealMovingSimplexKernelOne y y
          (fourFiveRealLogCoordinate y p.1) p.2) :=
    ((measurable_fourFiveLogLogLebesgueDensity.comp measurable_snd).mul hK).stronglyMeasurable
  have hparam : StronglyMeasurable (fun t : Real =>
      ∫ x in box, fourFiveLogLogLebesgueDensity x *
        fourFiveRealMovingSimplexKernelOne y y
          (fourFiveRealLogCoordinate y t) x) :=
    hjoint.integral_prod_right'
  change Measurable (fun t : Real =>
    ∫ x in (y : Real)..(B : Real),
      fourFiveLogLogLebesgueDensity x *
        fourFiveRealMovingSimplexKernelOne y y
          (fourFiveRealLogCoordinate y t) x)
  simpa only [intervalIntegral.integral_of_le hyB'] using hparam.measurable

theorem measurable_fourFiveActivePhysicalProxyTwo
    {y B : Nat} (hyB : y <= B) :
    Measurable (fourFiveActivePhysicalProxyTwo y B) := by
  have hyB' : (y : Real) <= (B : Real) := by exact_mod_cast hyB
  let box := Set.Ioc (y : Real) (B : Real)
  have hK : Measurable (fun p : (Real × Real) × Real =>
      fourFiveRealMovingSimplexKernelTwo y y
        (fourFiveRealLogCoordinate y p.1.1) p.1.2 p.2) :=
    (measurable_fourFiveRealMovingSimplexKernelTwo_joint y y).comp
      (((measurable_fourFiveRealLogCoordinate y).comp
        (measurable_fst.comp measurable_fst)).prodMk
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hjoint : StronglyMeasurable (fun p : (Real × Real) × Real =>
      fourFiveLogLogLebesgueDensity p.1.2 *
        fourFiveLogLogLebesgueDensity p.2 *
          fourFiveRealMovingSimplexKernelTwo y y
            (fourFiveRealLogCoordinate y p.1.1) p.1.2 p.2) :=
    (((measurable_fourFiveLogLogLebesgueDensity.comp
      (measurable_snd.comp measurable_fst)).mul
        (measurable_fourFiveLogLogLebesgueDensity.comp measurable_snd)).mul
          hK).stronglyMeasurable
  have hinner : StronglyMeasurable (fun p : Real × Real =>
      ∫ z in box, fourFiveLogLogLebesgueDensity p.2 *
        fourFiveLogLogLebesgueDensity z *
          fourFiveRealMovingSimplexKernelTwo y y
            (fourFiveRealLogCoordinate y p.1) p.2 z) :=
    hjoint.integral_prod_right'
  have houter : StronglyMeasurable (fun t : Real =>
      ∫ x in box, ∫ z in box,
        fourFiveLogLogLebesgueDensity x *
          fourFiveLogLogLebesgueDensity z *
            fourFiveRealMovingSimplexKernelTwo y y
              (fourFiveRealLogCoordinate y t) x z) :=
    hinner.integral_prod_right'
  change Measurable (fun t : Real =>
    ∫ x in (y : Real)..(B : Real),
      ∫ z in (y : Real)..(B : Real),
        fourFiveLogLogLebesgueDensity x *
          fourFiveLogLogLebesgueDensity z *
            fourFiveRealMovingSimplexKernelTwo y y
              (fourFiveRealLogCoordinate y t) x z)
  simpa only [intervalIntegral.integral_of_le hyB'] using houter.measurable

theorem measurable_fourFiveActivePhysicalProxyThree
    {y B : Nat} (hyB : y <= B) :
    Measurable (fourFiveActivePhysicalProxyThree y B) := by
  have hyB' : (y : Real) <= (B : Real) := by exact_mod_cast hyB
  let box := Set.Ioc (y : Real) (B : Real)
  have hK : Measurable (fun p : ((Real × Real) × Real) × Real =>
      fourFiveRealMovingSimplexKernelThree y y
        (fourFiveRealLogCoordinate y p.1.1.1) p.1.1.2 p.1.2 p.2) :=
    (measurable_fourFiveRealMovingSimplexKernelThree_joint y y).comp
      (((measurable_fourFiveRealLogCoordinate y).comp
        (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
          (((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
            (measurable_snd.comp measurable_fst)).prodMk measurable_snd))
  have hjoint : StronglyMeasurable (fun p : ((Real × Real) × Real) × Real =>
      fourFiveLogLogLebesgueDensity p.1.1.2 *
        fourFiveLogLogLebesgueDensity p.1.2 *
          fourFiveLogLogLebesgueDensity p.2 *
            fourFiveRealMovingSimplexKernelThree y y
              (fourFiveRealLogCoordinate y p.1.1.1) p.1.1.2 p.1.2 p.2) :=
    ((((measurable_fourFiveLogLogLebesgueDensity.comp
      (measurable_snd.comp (measurable_fst.comp measurable_fst))).mul
        (measurable_fourFiveLogLogLebesgueDensity.comp
          (measurable_snd.comp measurable_fst))).mul
            (measurable_fourFiveLogLogLebesgueDensity.comp measurable_snd)).mul
              hK).stronglyMeasurable
  have hw : StronglyMeasurable (fun p : (Real × Real) × Real =>
      ∫ w in box, fourFiveLogLogLebesgueDensity p.1.2 *
        fourFiveLogLogLebesgueDensity p.2 *
          fourFiveLogLogLebesgueDensity w *
            fourFiveRealMovingSimplexKernelThree y y
              (fourFiveRealLogCoordinate y p.1.1) p.1.2 p.2 w) :=
    hjoint.integral_prod_right'
  have hz : StronglyMeasurable (fun p : Real × Real =>
      ∫ z in box, ∫ w in box,
        fourFiveLogLogLebesgueDensity p.2 *
          fourFiveLogLogLebesgueDensity z *
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree y y
                (fourFiveRealLogCoordinate y p.1) p.2 z w) :=
    hw.integral_prod_right'
  have hx : StronglyMeasurable (fun t : Real =>
      ∫ x in box, ∫ z in box, ∫ w in box,
        fourFiveLogLogLebesgueDensity x *
          fourFiveLogLogLebesgueDensity z *
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree y y
                (fourFiveRealLogCoordinate y t) x z w) :=
    hz.integral_prod_right'
  change Measurable (fun t : Real =>
    ∫ x in (y : Real)..(B : Real),
      ∫ z in (y : Real)..(B : Real),
        ∫ w in (y : Real)..(B : Real),
          fourFiveLogLogLebesgueDensity x *
            fourFiveLogLogLebesgueDensity z *
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree y y
                  (fourFiveRealLogCoordinate y t) x z w)
  simpa only [intervalIntegral.integral_of_le hyB'] using hx.measurable

/-! ## Sampled endpoint functions and uniform finite bounds -/

def fourFiveLebesgueCellEndpointOne
    (y B : Nat) (t : Real) : Real :=
  fourFiveLebesgueCellProductOne
    (fourFiveMovingSimplexKernelOne y y
      (fourFiveRealLogCoordinate y t)) y B

def fourFiveLebesgueCellEndpointTwo
    (y B : Nat) (t : Real) : Real :=
  fourFiveLebesgueCellProductTwo
    (fourFiveMovingSimplexKernelTwo y y
      (fourFiveRealLogCoordinate y t)) y B

def fourFiveLebesgueCellEndpointThree
    (y B : Nat) (t : Real) : Real :=
  fourFiveLebesgueCellProductThree
    (fourFiveMovingSimplexKernelThree y y
      (fourFiveRealLogCoordinate y t)) y B

theorem measurable_fourFiveLebesgueCellEndpointOne
    (y B : Nat) : Measurable (fourFiveLebesgueCellEndpointOne y B) := by
  unfold fourFiveLebesgueCellEndpointOne fourFiveLebesgueCellProductOne
    fourFiveFiniteProductOne fourFiveMovingSimplexKernelOne
  exact Finset.measurable_sum _ fun n _hn => measurable_const.mul
    ((measurable_fourFiveMovingFaceKernel_parameter y y n 0).comp
      (measurable_fourFiveRealLogCoordinate y))

theorem measurable_fourFiveLebesgueCellEndpointTwo
    (y B : Nat) : Measurable (fourFiveLebesgueCellEndpointTwo y B) := by
  unfold fourFiveLebesgueCellEndpointTwo fourFiveLebesgueCellProductTwo
    fourFiveFiniteProductTwo
  exact Finset.measurable_sum _ fun p _hp => measurable_const.mul
    (Finset.measurable_sum _ fun q _hq => measurable_const.mul
      ((measurable_fourFiveMovingSimplexKernelTwo_parameter y y p q).comp
        (measurable_fourFiveRealLogCoordinate y)))

theorem measurable_fourFiveLebesgueCellEndpointThree
    (y B : Nat) : Measurable (fourFiveLebesgueCellEndpointThree y B) := by
  unfold fourFiveLebesgueCellEndpointThree fourFiveLebesgueCellProductThree
    fourFiveFiniteProductThree
  exact Finset.measurable_sum _ fun p _hp => measurable_const.mul
    (Finset.measurable_sum _ fun q _hq => measurable_const.mul
      (Finset.measurable_sum _ fun r _hr => measurable_const.mul
        ((measurable_fourFiveMovingSimplexKernelThree_parameter y y p q r).comp
          (measurable_fourFiveRealLogCoordinate y))))

private theorem abs_fourFiveFiniteProductOne_le_mass
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (w : ι -> Real) (K : ι -> Real)
    (hK : ∀ i ∈ S, |K i| <= 1) :
    |fourFiveFiniteProductOne S w K| <= ∑ i ∈ S, |w i| := by
  unfold fourFiveFiniteProductOne
  calc
    |∑ i ∈ S, w i * K i| <= ∑ i ∈ S, |w i * K i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ i ∈ S, |w i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      calc
        |w i| * |K i| <= |w i| * 1 :=
          mul_le_mul_of_nonneg_left (hK i hi) (abs_nonneg _)
        _ = |w i| := mul_one _

private theorem abs_fourFiveFiniteProductTwo_le_mass_sq
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (w : ι -> Real) (K : ι -> ι -> Real)
    (hK : ∀ i ∈ S, ∀ j ∈ S, |K i j| <= 1) :
    |fourFiveFiniteProductTwo S w K| <= (∑ i ∈ S, |w i|) ^ 2 := by
  unfold fourFiveFiniteProductTwo
  calc
    |∑ i ∈ S, w i * (∑ j ∈ S, w j * K i j)| <=
        ∑ i ∈ S, |w i * (∑ j ∈ S, w j * K i j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ i ∈ S, |w i| * (∑ j ∈ S, |w j|) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_fourFiveFiniteProductOne_le_mass S w (K i)
          (fun j hj => hK i hi j hj)) (abs_nonneg _)
    _ = (∑ i ∈ S, |w i|) ^ 2 := by
      rw [← Finset.sum_mul]
      ring

private theorem abs_fourFiveFiniteProductThree_le_mass_cu
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (w : ι -> Real) (K : ι -> ι -> ι -> Real)
    (hK : ∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S,
      |K i j k| <= 1) :
    |fourFiveFiniteProductThree S w K| <= (∑ i ∈ S, |w i|) ^ 3 := by
  unfold fourFiveFiniteProductThree
  calc
    |∑ i ∈ S, w i *
        (∑ j ∈ S, w j * (∑ k ∈ S, w k * K i j k))| <=
        ∑ i ∈ S, |w i *
          (∑ j ∈ S, w j * (∑ k ∈ S, w k * K i j k))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ i ∈ S, |w i| * (∑ j ∈ S, |w j|) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_fourFiveFiniteProductTwo_le_mass_sq S w (K i)
          (fun j hj k hk => hK i hi j hj k hk)) (abs_nonneg _)
    _ = (∑ i ∈ S, |w i|) ^ 3 := by
      rw [← Finset.sum_mul]
      ring

theorem abs_fourFiveLebesgueCellEndpointOne_le_mass
    (y B : Nat) (t : Real) :
    |fourFiveLebesgueCellEndpointOne y B t| <=
      ∑ n ∈ Finset.Ioc y B, |fourFiveLogLogLebesgueCellAtom n| := by
  unfold fourFiveLebesgueCellEndpointOne fourFiveLebesgueCellProductOne
  apply abs_fourFiveFiniteProductOne_le_mass
  intro n _hn
  have h := fourFiveRealMovingFaceKernel_nonneg_le_one
    (A := y) (y := y) (u := fourFiveRealLogCoordinate y t)
    (c := 0) (x := (n : Real))
  rw [fourFiveRealMovingFaceKernel_natCast] at h
  unfold fourFiveMovingSimplexKernelOne
  rw [abs_of_nonneg h.1]
  exact h.2

theorem abs_fourFiveLebesgueCellEndpointTwo_le_mass_sq
    (y B : Nat) (t : Real) :
    |fourFiveLebesgueCellEndpointTwo y B t| <=
      (∑ n ∈ Finset.Ioc y B, |fourFiveLogLogLebesgueCellAtom n|) ^ 2 := by
  unfold fourFiveLebesgueCellEndpointTwo fourFiveLebesgueCellProductTwo
  apply abs_fourFiveFiniteProductTwo_le_mass_sq
  intro p hp q hq
  have h := fourFiveRealMovingSimplexKernelTwo_nonneg_le_one
    (A := y) (y := y) (u := fourFiveRealLogCoordinate y t)
    (x := (p : Real)) (z := (q : Real))
  rw [fourFiveRealMovingSimplexKernelTwo_natCast hp hq] at h
  rw [abs_of_nonneg h.1]
  exact h.2

theorem abs_fourFiveLebesgueCellEndpointThree_le_mass_cu
    (y B : Nat) (t : Real) :
    |fourFiveLebesgueCellEndpointThree y B t| <=
      (∑ n ∈ Finset.Ioc y B, |fourFiveLogLogLebesgueCellAtom n|) ^ 3 := by
  unfold fourFiveLebesgueCellEndpointThree fourFiveLebesgueCellProductThree
  apply abs_fourFiveFiniteProductThree_le_mass_cu
  intro p hp q hq r hr
  have h := fourFiveRealMovingSimplexKernelThree_nonneg_le_one
    (A := y) (y := y) (u := fourFiveRealLogCoordinate y t)
    (x := (p : Real)) (z := (q : Real)) (w := (r : Real))
  rw [fourFiveRealMovingSimplexKernelThree_natCast hp hq hr] at h
  rw [abs_of_nonneg h.1]
  exact h.2

/-! ## Proxy identities and pointwise quadrature bounds -/

theorem fourFiveActivePhysicalProxyOne_eq_realCellIntegralSum
    {y B : Nat} (hy : 2 <= y) (hyB : y <= B) (t : Real) :
    fourFiveActivePhysicalProxyOne y B t =
      fourFiveMovingFaceRealCellIntegralSum y B y
        (fourFiveRealLogCoordinate y t) 0 := by
  rw [fourFiveMovingFaceRealCellIntegralSum_eq_interval hy le_rfl hyB]
  rfl

theorem fourFiveActivePhysicalProxyTwo_eq_iteratedRealCellProduct
    {y B : Nat} (hy : 2 <= y) (hyB : y <= B) (t : Real) :
    fourFiveActivePhysicalProxyTwo y B t =
      fourFiveMovingSimplexIteratedRealCellProductTwo y B y
        (fourFiveRealLogCoordinate y t) := by
  rw [fourFiveMovingSimplexIteratedRealCellProductTwo_eq_activePhysical
    hy le_rfl hyB]
  unfold fourFiveActivePhysicalProxyTwo
    fourFiveMovingSimplexActivePhysicalIntegralTwo
  apply intervalIntegral.integral_congr
  intro x _hx
  change
    (∫ z in (y : Real)..(B : Real),
      fourFiveLogLogLebesgueDensity x *
        fourFiveLogLogLebesgueDensity z *
          fourFiveRealMovingSimplexKernelTwo y y
            (fourFiveRealLogCoordinate y t) x z) =
      fourFiveLogLogLebesgueDensity x *
        (∫ z in (y : Real)..(B : Real),
          fourFiveLogLogLebesgueDensity z *
            fourFiveRealMovingSimplexKernelTwo y y
              (fourFiveRealLogCoordinate y t) x z)
  calc
    (∫ z in (y : Real)..(B : Real),
      fourFiveLogLogLebesgueDensity x *
        fourFiveLogLogLebesgueDensity z *
          fourFiveRealMovingSimplexKernelTwo y y
            (fourFiveRealLogCoordinate y t) x z) =
        ∫ z in (y : Real)..(B : Real),
          fourFiveLogLogLebesgueDensity x *
            (fourFiveLogLogLebesgueDensity z *
              fourFiveRealMovingSimplexKernelTwo y y
                (fourFiveRealLogCoordinate y t) x z) := by
      apply intervalIntegral.integral_congr
      intro z _hz
      exact mul_assoc _ _ _
    _ = fourFiveLogLogLebesgueDensity x *
        (∫ z in (y : Real)..(B : Real),
          fourFiveLogLogLebesgueDensity z *
            fourFiveRealMovingSimplexKernelTwo y y
              (fourFiveRealLogCoordinate y t) x z) := by
      rw [intervalIntegral.integral_const_mul]

theorem fourFiveActivePhysicalProxyThree_eq_iteratedRealCellProduct
    {y B : Nat} (hy : 2 <= y) (hyB : y <= B) (t : Real) :
    fourFiveActivePhysicalProxyThree y B t =
      fourFiveMovingSimplexIteratedRealCellProductThree y B y
        (fourFiveRealLogCoordinate y t) := by
  rw [fourFiveMovingSimplexIteratedRealCellProductThree_eq_activePhysical
    hy le_rfl hyB]
  unfold fourFiveActivePhysicalProxyThree
    fourFiveMovingSimplexActivePhysicalIntegralThree
  apply intervalIntegral.integral_congr
  intro x _hx
  change
    (∫ z in (y : Real)..(B : Real),
      ∫ w in (y : Real)..(B : Real),
        fourFiveLogLogLebesgueDensity x *
          fourFiveLogLogLebesgueDensity z *
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree y y
                (fourFiveRealLogCoordinate y t) x z w) =
      fourFiveLogLogLebesgueDensity x *
        (∫ z in (y : Real)..(B : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (y : Real)..(B : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree y y
                  (fourFiveRealLogCoordinate y t) x z w))
  calc
    (∫ z in (y : Real)..(B : Real),
      ∫ w in (y : Real)..(B : Real),
        fourFiveLogLogLebesgueDensity x *
          fourFiveLogLogLebesgueDensity z *
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree y y
                (fourFiveRealLogCoordinate y t) x z w) =
        ∫ z in (y : Real)..(B : Real),
          fourFiveLogLogLebesgueDensity x *
            (fourFiveLogLogLebesgueDensity z *
              (∫ w in (y : Real)..(B : Real),
                fourFiveLogLogLebesgueDensity w *
                  fourFiveRealMovingSimplexKernelThree y y
                    (fourFiveRealLogCoordinate y t) x z w)) := by
      apply intervalIntegral.integral_congr
      intro z _hz
      calc
        (∫ w in (y : Real)..(B : Real),
          fourFiveLogLogLebesgueDensity x *
            fourFiveLogLogLebesgueDensity z *
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree y y
                  (fourFiveRealLogCoordinate y t) x z w) =
            (fourFiveLogLogLebesgueDensity x *
              fourFiveLogLogLebesgueDensity z) *
              (∫ w in (y : Real)..(B : Real),
                fourFiveLogLogLebesgueDensity w *
                  fourFiveRealMovingSimplexKernelThree y y
                    (fourFiveRealLogCoordinate y t) x z w) := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro w _hw
          ring
        _ = fourFiveLogLogLebesgueDensity x *
            (fourFiveLogLogLebesgueDensity z *
              (∫ w in (y : Real)..(B : Real),
                fourFiveLogLogLebesgueDensity w *
                  fourFiveRealMovingSimplexKernelThree y y
                    (fourFiveRealLogCoordinate y t) x z w)) := by
          rw [mul_assoc]
    _ = fourFiveLogLogLebesgueDensity x *
        (∫ z in (y : Real)..(B : Real),
          fourFiveLogLogLebesgueDensity z *
            (∫ w in (y : Real)..(B : Real),
              fourFiveLogLogLebesgueDensity w *
                fourFiveRealMovingSimplexKernelThree y y
                  (fourFiveRealLogCoordinate y t) x z w)) := by
      rw [intervalIntegral.integral_const_mul]

theorem fourFiveActivePhysicalProxyOne_eq_logarithmicKernel
    {y B : Nat} (hy : 2 <= y) (hyB : y <= B) {t : Real}
    (htB : fourFiveRealLogCoordinate y t <=
      fourFiveRealLogCoordinate y (B : Real)) :
    fourFiveActivePhysicalProxyOne y B t =
      fourFiveLogarithmicMovingSimplexKernel 1
        (fourFiveRealLogCoordinate y t) := by
  rw [fourFiveActivePhysicalProxyOne_eq_realCellIntegralSum hy hyB,
    fourFiveMovingFaceRealCellIntegralSum_eq_logarithmicKernel hy hyB htB]

theorem fourFiveActivePhysicalProxyTwo_eq_logarithmicKernel
    {y B : Nat} (hy : 2 <= y) (hyB : y <= B) {t : Real}
    (htB : fourFiveRealLogCoordinate y t <=
      fourFiveRealLogCoordinate y (B : Real)) :
    fourFiveActivePhysicalProxyTwo y B t =
      fourFiveLogarithmicMovingSimplexKernel 2
        (fourFiveRealLogCoordinate y t) := by
  rw [fourFiveActivePhysicalProxyTwo_eq_iteratedRealCellProduct hy hyB,
    fourFiveMovingSimplexIteratedRealCellProductTwo_eq_logarithmicKernel
      hy hyB htB]

theorem fourFiveActivePhysicalProxyThree_eq_logarithmicKernel
    {y B : Nat} (hy : 2 <= y) (hyB : y <= B) {t : Real}
    (htB : fourFiveRealLogCoordinate y t <=
      fourFiveRealLogCoordinate y (B : Real)) :
    fourFiveActivePhysicalProxyThree y B t =
      fourFiveLogarithmicMovingSimplexKernel 3
        (fourFiveRealLogCoordinate y t) := by
  rw [fourFiveActivePhysicalProxyThree_eq_iteratedRealCellProduct hy hyB,
    fourFiveMovingSimplexIteratedRealCellProductThree_eq_logarithmicKernel
      hy hyB htB]

theorem abs_fourFiveLebesgueCellEndpointOne_sub_proxy_le
    {y B : Nat} (hy : 2 <= y) (hyB : y <= B) (t : Real) :
    |fourFiveLebesgueCellEndpointOne y B t -
        fourFiveActivePhysicalProxyOne y B t| <=
      2 * fourFiveLogLogCellMeshBound y := by
  rw [fourFiveActivePhysicalProxyOne_eq_realCellIntegralSum hy hyB]
  exact abs_fourFiveMovingFaceRightEndpointCellSum_sub_real_le
    hy le_rfl hyB

theorem abs_fourFiveLebesgueCellEndpointTwo_sub_proxy_le
    {y B : Nat} {M : Real} (hy : 2 <= y) (hyB : y <= B)
    (hmass : (∑ n ∈ Finset.Ioc y B,
      |fourFiveLogLogLebesgueCellAtom n|) <= M) (t : Real) :
    |fourFiveLebesgueCellEndpointTwo y B t -
        fourFiveActivePhysicalProxyTwo y B t| <=
      4 * fourFiveLogLogCellMeshBound y * M := by
  rw [fourFiveActivePhysicalProxyTwo_eq_iteratedRealCellProduct hy hyB]
  exact abs_fourFiveMovingSimplexRightEndpointProductTwo_sub_iterated_le
    hy le_rfl hyB hmass

theorem abs_fourFiveLebesgueCellEndpointThree_sub_proxy_le
    {y B : Nat} {M : Real} (hy : 2 <= y) (hyB : y <= B)
    (hmass : (∑ n ∈ Finset.Ioc y B,
      |fourFiveLogLogLebesgueCellAtom n|) <= M) (t : Real) :
    |fourFiveLebesgueCellEndpointThree y B t -
        fourFiveActivePhysicalProxyThree y B t| <=
      6 * fourFiveLogLogCellMeshBound y * M ^ 2 := by
  rw [fourFiveActivePhysicalProxyThree_eq_iteratedRealCellProduct hy hyB]
  exact abs_fourFiveMovingSimplexRightEndpointProductThree_sub_iterated_le
    hy le_rfl hyB hmass

/-! ## Outer interval integrability -/

private theorem intervalIntegrable_of_measurable_of_abs_le_const
    {F : Real -> Real} {a b C : Real}
    (hF : Measurable F) (hbound : ∀ t ∈ Set.uIcc a b, |F t| <= C) :
    IntervalIntegrable F volume a b := by
  refine (intervalIntegrable_const (c := C)).mono_fun' ?_ ?_
  · exact hF.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    simpa only [Real.norm_eq_abs] using hbound t (Set.uIoc_subset_uIcc ht)

theorem intervalIntegrable_fourFiveLebesgueCellEndpointOne
    (y B : Nat) (a b : Real) :
    IntervalIntegrable (fourFiveLebesgueCellEndpointOne y B) volume a b := by
  apply intervalIntegrable_of_measurable_of_abs_le_const
    (measurable_fourFiveLebesgueCellEndpointOne y B)
  intro t _ht
  exact abs_fourFiveLebesgueCellEndpointOne_le_mass y B t

theorem intervalIntegrable_fourFiveLebesgueCellEndpointTwo
    (y B : Nat) (a b : Real) :
    IntervalIntegrable (fourFiveLebesgueCellEndpointTwo y B) volume a b := by
  apply intervalIntegrable_of_measurable_of_abs_le_const
    (measurable_fourFiveLebesgueCellEndpointTwo y B)
  intro t _ht
  exact abs_fourFiveLebesgueCellEndpointTwo_le_mass_sq y B t

theorem intervalIntegrable_fourFiveLebesgueCellEndpointThree
    (y B : Nat) (a b : Real) :
    IntervalIntegrable (fourFiveLebesgueCellEndpointThree y B) volume a b := by
  apply intervalIntegrable_of_measurable_of_abs_le_const
    (measurable_fourFiveLebesgueCellEndpointThree y B)
  intro t _ht
  exact abs_fourFiveLebesgueCellEndpointThree_le_mass_cu y B t

theorem intervalIntegrable_fourFiveActivePhysicalProxyOne
    {y B : Nat} (hy : 2 <= y) (hyB : y <= B) (a b : Real) :
    IntervalIntegrable (fourFiveActivePhysicalProxyOne y B) volume a b := by
  let W := ∑ n ∈ Finset.Ioc y B, |fourFiveLogLogLebesgueCellAtom n|
  let C := 2 * fourFiveLogLogCellMeshBound y
  apply intervalIntegrable_of_measurable_of_abs_le_const
    (measurable_fourFiveActivePhysicalProxyOne hyB)
  intro t _ht
  calc
    |fourFiveActivePhysicalProxyOne y B t| =
        |fourFiveLebesgueCellEndpointOne y B t +
          (fourFiveActivePhysicalProxyOne y B t -
            fourFiveLebesgueCellEndpointOne y B t)| := by ring_nf
    _ <= |fourFiveLebesgueCellEndpointOne y B t| +
        |fourFiveActivePhysicalProxyOne y B t -
          fourFiveLebesgueCellEndpointOne y B t| := abs_add_le _ _
    _ = |fourFiveLebesgueCellEndpointOne y B t| +
        |fourFiveLebesgueCellEndpointOne y B t -
          fourFiveActivePhysicalProxyOne y B t| := by rw [abs_sub_comm]
    _ <= W + C := add_le_add
      (abs_fourFiveLebesgueCellEndpointOne_le_mass y B t)
      (abs_fourFiveLebesgueCellEndpointOne_sub_proxy_le hy hyB t)

theorem intervalIntegrable_fourFiveActivePhysicalProxyTwo
    {y B : Nat} {M : Real} (hy : 2 <= y) (hyB : y <= B)
    (hmass : (∑ n ∈ Finset.Ioc y B,
      |fourFiveLogLogLebesgueCellAtom n|) <= M)
    (a b : Real) :
    IntervalIntegrable (fourFiveActivePhysicalProxyTwo y B) volume a b := by
  let W := ∑ n ∈ Finset.Ioc y B, |fourFiveLogLogLebesgueCellAtom n|
  let C := 4 * fourFiveLogLogCellMeshBound y * M
  apply intervalIntegrable_of_measurable_of_abs_le_const
    (measurable_fourFiveActivePhysicalProxyTwo hyB)
  intro t _ht
  calc
    |fourFiveActivePhysicalProxyTwo y B t| =
        |fourFiveLebesgueCellEndpointTwo y B t +
          (fourFiveActivePhysicalProxyTwo y B t -
            fourFiveLebesgueCellEndpointTwo y B t)| := by ring_nf
    _ <= |fourFiveLebesgueCellEndpointTwo y B t| +
        |fourFiveActivePhysicalProxyTwo y B t -
          fourFiveLebesgueCellEndpointTwo y B t| := abs_add_le _ _
    _ = |fourFiveLebesgueCellEndpointTwo y B t| +
        |fourFiveLebesgueCellEndpointTwo y B t -
          fourFiveActivePhysicalProxyTwo y B t| := by rw [abs_sub_comm]
    _ <= W ^ 2 + C := add_le_add
      (abs_fourFiveLebesgueCellEndpointTwo_le_mass_sq y B t)
      (abs_fourFiveLebesgueCellEndpointTwo_sub_proxy_le hy hyB hmass t)

theorem intervalIntegrable_fourFiveActivePhysicalProxyThree
    {y B : Nat} {M : Real} (hy : 2 <= y) (hyB : y <= B)
    (hmass : (∑ n ∈ Finset.Ioc y B,
      |fourFiveLogLogLebesgueCellAtom n|) <= M)
    (a b : Real) :
    IntervalIntegrable (fourFiveActivePhysicalProxyThree y B) volume a b := by
  let W := ∑ n ∈ Finset.Ioc y B, |fourFiveLogLogLebesgueCellAtom n|
  let C := 6 * fourFiveLogLogCellMeshBound y * M ^ 2
  apply intervalIntegrable_of_measurable_of_abs_le_const
    (measurable_fourFiveActivePhysicalProxyThree hyB)
  intro t _ht
  calc
    |fourFiveActivePhysicalProxyThree y B t| =
        |fourFiveLebesgueCellEndpointThree y B t +
          (fourFiveActivePhysicalProxyThree y B t -
            fourFiveLebesgueCellEndpointThree y B t)| := by ring_nf
    _ <= |fourFiveLebesgueCellEndpointThree y B t| +
        |fourFiveActivePhysicalProxyThree y B t -
          fourFiveLebesgueCellEndpointThree y B t| := abs_add_le _ _
    _ = |fourFiveLebesgueCellEndpointThree y B t| +
        |fourFiveLebesgueCellEndpointThree y B t -
          fourFiveActivePhysicalProxyThree y B t| := by rw [abs_sub_comm]
    _ <= W ^ 3 + C := add_le_add
      (abs_fourFiveLebesgueCellEndpointThree_le_mass_cu y B t)
      (abs_fourFiveLebesgueCellEndpointThree_sub_proxy_le hy hyB hmass t)

private theorem fourFiveRealLogCoordinate_le_at_outer_point
    {y A B : Nat} (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    {t : Real} (ht : t ∈ Set.uIcc (A : Real) (B : Real)) :
    fourFiveRealLogCoordinate y t <=
      fourFiveRealLogCoordinate y (B : Real) := by
  have hAB' : (A : Real) <= (B : Real) := by exact_mod_cast hAB
  have ht' : t ∈ Set.Icc (A : Real) (B : Real) := by
    simpa [Set.uIcc_of_le hAB'] using ht
  have hypos : (0 : Real) < (y : Real) := by
    exact_mod_cast (show 0 < y by omega)
  have hyA' : (y : Real) <= (A : Real) := by exact_mod_cast hyA
  exact fourFiveRealLogCoordinate_mono hy
    (hypos.trans_le (hyA'.trans ht'.1)) ht'.2

theorem intervalIntegrable_fourFiveLogarithmicMovingSimplexKernel_one_outer
    {y A B : Nat} (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B) :
    IntervalIntegrable
      (fun t => fourFiveLogarithmicMovingSimplexKernel 1
        (fourFiveRealLogCoordinate y t)) volume (A : Real) (B : Real) := by
  have hproxy := intervalIntegrable_fourFiveActivePhysicalProxyOne
    hy (hyA.trans hAB) (A : Real) (B : Real)
  apply hproxy.congr
  intro t ht
  exact fourFiveActivePhysicalProxyOne_eq_logarithmicKernel
    hy (hyA.trans hAB)
      (fourFiveRealLogCoordinate_le_at_outer_point hy hyA hAB
        (Set.uIoc_subset_uIcc ht))

theorem intervalIntegrable_fourFiveLogarithmicMovingSimplexKernel_two_outer
    {y A B : Nat} {M : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hmass : (∑ n ∈ Finset.Ioc y B,
      |fourFiveLogLogLebesgueCellAtom n|) <= M) :
    IntervalIntegrable
      (fun t => fourFiveLogarithmicMovingSimplexKernel 2
        (fourFiveRealLogCoordinate y t)) volume (A : Real) (B : Real) := by
  have hproxy := intervalIntegrable_fourFiveActivePhysicalProxyTwo
    hy (hyA.trans hAB) hmass (A : Real) (B : Real)
  apply hproxy.congr
  intro t ht
  exact fourFiveActivePhysicalProxyTwo_eq_logarithmicKernel
    hy (hyA.trans hAB)
      (fourFiveRealLogCoordinate_le_at_outer_point hy hyA hAB
        (Set.uIoc_subset_uIcc ht))

theorem intervalIntegrable_fourFiveLogarithmicMovingSimplexKernel_three_outer
    {y A B : Nat} {M : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hmass : (∑ n ∈ Finset.Ioc y B,
      |fourFiveLogLogLebesgueCellAtom n|) <= M) :
    IntervalIntegrable
      (fun t => fourFiveLogarithmicMovingSimplexKernel 3
        (fourFiveRealLogCoordinate y t)) volume (A : Real) (B : Real) := by
  have hproxy := intervalIntegrable_fourFiveActivePhysicalProxyThree
    hy (hyA.trans hAB) hmass (A : Real) (B : Real)
  apply hproxy.congr
  intro t ht
  exact fourFiveActivePhysicalProxyThree_eq_logarithmicKernel
    hy (hyA.trans hAB)
      (fourFiveRealLogCoordinate_le_at_outer_point hy hyA hAB
        (Set.uIoc_subset_uIcc ht))

/-! ## Explicit outer residual bounds -/

private theorem abs_scaled_intervalIntegral_sub_le
    {F G : Real -> Real} {a b c C : Real}
    (hab : a <= b) (hc : 0 <= c)
    (hF : IntervalIntegrable F volume a b)
    (hG : IntervalIntegrable G volume a b)
    (hdiff : ∀ t ∈ Set.uIcc a b, |F t - G t| <= C) :
    |c * (∫ t in a..b, F t) - c * (∫ t in a..b, G t)| <=
      c * (b - a) * C := by
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t => F t - G t)
    (fun t ht => by
      simpa only [Real.norm_eq_abs] using
        hdiff t (Set.uIoc_subset_uIcc ht))
  have habs : |∫ t in a..b, F t - G t| <= C * |b - a| := by
    simpa only [Real.norm_eq_abs] using hnorm
  rw [← mul_sub, ← intervalIntegral.integral_sub hF hG,
    abs_mul, abs_of_nonneg hc]
  calc
    c * |∫ t in a..b, F t - G t| <= c * (C * |b - a|) :=
      mul_le_mul_of_nonneg_left habs hc
    _ = c * (b - a) * C := by
      rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      ring

def fourFiveLebesgueCellAggregationBudget
    (m y A B : Nat) (M : Real) : Real :=
  (1 / Real.log (y : Real)) * ((B : Real) - (A : Real)) *
    match m with
    | 0 => 0
    | 1 => 2 * fourFiveLogLogCellMeshBound y
    | 2 => 4 * fourFiveLogLogCellMeshBound y * M
    | 3 => 6 * fourFiveLogLogCellMeshBound y * M ^ 2
    | _ => 0

theorem fourFiveLebesgueCellAggregationError_one_le
    {y A B : Nat} (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B) :
    fourFiveLebesgueCellAggregationError 1 y A B <=
      (1 / Real.log (y : Real)) * ((B : Real) - (A : Real)) *
        (2 * fourFiveLogLogCellMeshBound y) := by
  let F := fourFiveLebesgueCellEndpointOne y B
  let G : Real -> Real := fun t =>
    fourFiveLogarithmicMovingSimplexKernel 1
      (fourFiveRealLogCoordinate y t)
  have hAB' : (A : Real) <= (B : Real) := by exact_mod_cast hAB
  have hc : 0 <= 1 / Real.log (y : Real) :=
    one_div_nonneg.mpr
      (Real.log_pos (by exact_mod_cast (show 1 < y by omega))).le
  have hF : IntervalIntegrable F volume (A : Real) (B : Real) :=
    intervalIntegrable_fourFiveLebesgueCellEndpointOne y B _ _
  have hG : IntervalIntegrable G volume (A : Real) (B : Real) :=
    intervalIntegrable_fourFiveLogarithmicMovingSimplexKernel_one_outer
      hy hyA hAB
  have hdiff : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      |F t - G t| <= 2 * fourFiveLogLogCellMeshBound y := by
    intro t ht
    have htB := fourFiveRealLogCoordinate_le_at_outer_point hy hyA hAB ht
    change
      |fourFiveLebesgueCellEndpointOne y B t -
          fourFiveLogarithmicMovingSimplexKernel 1
            (fourFiveRealLogCoordinate y t)| <=
        2 * fourFiveLogLogCellMeshBound y
    rw [← fourFiveActivePhysicalProxyOne_eq_logarithmicKernel
      hy (hyA.trans hAB) htB]
    exact abs_fourFiveLebesgueCellEndpointOne_sub_proxy_le
      hy (hyA.trans hAB) t
  unfold fourFiveLebesgueCellAggregationError
    fourFivePhysicalLebesgueCellLayer fourFivePhysicalMovingSimplexLayer
  change |(1 / Real.log (y : Real)) * (∫ t in (A : Real)..(B : Real), F t) -
      (1 / Real.log (y : Real)) * (∫ t in (A : Real)..(B : Real), G t)| <= _
  exact abs_scaled_intervalIntegral_sub_le hAB' hc hF hG hdiff

theorem fourFiveLebesgueCellAggregationError_two_le
    {y A B : Nat} {M : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hmass : (∑ n ∈ Finset.Ioc y B,
      |fourFiveLogLogLebesgueCellAtom n|) <= M) :
    fourFiveLebesgueCellAggregationError 2 y A B <=
      (1 / Real.log (y : Real)) * ((B : Real) - (A : Real)) *
        (4 * fourFiveLogLogCellMeshBound y * M) := by
  let F := fourFiveLebesgueCellEndpointTwo y B
  let G : Real -> Real := fun t =>
    fourFiveLogarithmicMovingSimplexKernel 2
      (fourFiveRealLogCoordinate y t)
  have hAB' : (A : Real) <= (B : Real) := by exact_mod_cast hAB
  have hc : 0 <= 1 / Real.log (y : Real) :=
    one_div_nonneg.mpr
      (Real.log_pos (by exact_mod_cast (show 1 < y by omega))).le
  have hF : IntervalIntegrable F volume (A : Real) (B : Real) :=
    intervalIntegrable_fourFiveLebesgueCellEndpointTwo y B _ _
  have hG : IntervalIntegrable G volume (A : Real) (B : Real) :=
    intervalIntegrable_fourFiveLogarithmicMovingSimplexKernel_two_outer
      hy hyA hAB hmass
  have hdiff : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      |F t - G t| <= 4 * fourFiveLogLogCellMeshBound y * M := by
    intro t ht
    have htB := fourFiveRealLogCoordinate_le_at_outer_point hy hyA hAB ht
    change
      |fourFiveLebesgueCellEndpointTwo y B t -
          fourFiveLogarithmicMovingSimplexKernel 2
            (fourFiveRealLogCoordinate y t)| <=
        4 * fourFiveLogLogCellMeshBound y * M
    rw [← fourFiveActivePhysicalProxyTwo_eq_logarithmicKernel
      hy (hyA.trans hAB) htB]
    exact abs_fourFiveLebesgueCellEndpointTwo_sub_proxy_le
      hy (hyA.trans hAB) hmass t
  unfold fourFiveLebesgueCellAggregationError
    fourFivePhysicalLebesgueCellLayer fourFivePhysicalMovingSimplexLayer
  change |(1 / Real.log (y : Real)) * (∫ t in (A : Real)..(B : Real), F t) -
      (1 / Real.log (y : Real)) * (∫ t in (A : Real)..(B : Real), G t)| <= _
  exact abs_scaled_intervalIntegral_sub_le hAB' hc hF hG hdiff

theorem fourFiveLebesgueCellAggregationError_three_le
    {y A B : Nat} {M : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hmass : (∑ n ∈ Finset.Ioc y B,
      |fourFiveLogLogLebesgueCellAtom n|) <= M) :
    fourFiveLebesgueCellAggregationError 3 y A B <=
      (1 / Real.log (y : Real)) * ((B : Real) - (A : Real)) *
        (6 * fourFiveLogLogCellMeshBound y * M ^ 2) := by
  let F := fourFiveLebesgueCellEndpointThree y B
  let G : Real -> Real := fun t =>
    fourFiveLogarithmicMovingSimplexKernel 3
      (fourFiveRealLogCoordinate y t)
  have hAB' : (A : Real) <= (B : Real) := by exact_mod_cast hAB
  have hc : 0 <= 1 / Real.log (y : Real) :=
    one_div_nonneg.mpr
      (Real.log_pos (by exact_mod_cast (show 1 < y by omega))).le
  have hF : IntervalIntegrable F volume (A : Real) (B : Real) :=
    intervalIntegrable_fourFiveLebesgueCellEndpointThree y B _ _
  have hG : IntervalIntegrable G volume (A : Real) (B : Real) :=
    intervalIntegrable_fourFiveLogarithmicMovingSimplexKernel_three_outer
      hy hyA hAB hmass
  have hdiff : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      |F t - G t| <= 6 * fourFiveLogLogCellMeshBound y * M ^ 2 := by
    intro t ht
    have htB := fourFiveRealLogCoordinate_le_at_outer_point hy hyA hAB ht
    change
      |fourFiveLebesgueCellEndpointThree y B t -
          fourFiveLogarithmicMovingSimplexKernel 3
            (fourFiveRealLogCoordinate y t)| <=
        6 * fourFiveLogLogCellMeshBound y * M ^ 2
    rw [← fourFiveActivePhysicalProxyThree_eq_logarithmicKernel
      hy (hyA.trans hAB) htB]
    exact abs_fourFiveLebesgueCellEndpointThree_sub_proxy_le
      hy (hyA.trans hAB) hmass t
  unfold fourFiveLebesgueCellAggregationError
    fourFivePhysicalLebesgueCellLayer fourFivePhysicalMovingSimplexLayer
  change |(1 / Real.log (y : Real)) * (∫ t in (A : Real)..(B : Real), F t) -
      (1 / Real.log (y : Real)) * (∫ t in (A : Real)..(B : Real), G t)| <= _
  exact abs_scaled_intervalIntegral_sub_le hAB' hc hF hG hdiff

theorem fourFiveLebesgueCellAggregationError_le_budget
    {m y A B : Nat} {M : Real}
    (hm : m <= 3) (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hmass : (∑ n ∈ Finset.Ioc y B,
      |fourFiveLogLogLebesgueCellAtom n|) <= M) :
    fourFiveLebesgueCellAggregationError m y A B <=
      fourFiveLebesgueCellAggregationBudget m y A B M := by
  interval_cases m
  · simp [fourFiveLebesgueCellAggregationError_zero,
      fourFiveLebesgueCellAggregationBudget]
  · simpa [fourFiveLebesgueCellAggregationBudget] using
      fourFiveLebesgueCellAggregationError_one_le hy hyA hAB
  · simpa [fourFiveLebesgueCellAggregationBudget] using
      fourFiveLebesgueCellAggregationError_two_le hy hyA hAB hmass
  · simpa [fourFiveLebesgueCellAggregationBudget] using
      fourFiveLebesgueCellAggregationError_three_le hy hyA hAB hmass

/-! ## Substitution into the layer and ordered-mixture ledgers -/

/-- The continuum-bridge cell entry after residual 2 has been replaced by
its explicit numerical budget and residual 3 has been discharged by the
exact moving-to-fixed identification.  The two remaining entries are the
physical last-prime change and the product-replacement overrun, which are
bounded by their dedicated bridge modules. -/
def fourFiveContinuumBridgeCellBudgetAfterAggregation
    (m y A B : Nat) (E M : Real) : Real :=
  fourFiveLastPrimePhysicalChangeError m y A B +
    fourFiveLebesgueCellAggregationBudget m y A B M +
    fourFivePhysicalProductBudgetOverrun m y A B E M

theorem fourFiveExactContinuumBridgeCellError_zero_le_afterAggregation
    (y A B : Nat) (E M : Real) :
    fourFiveExactContinuumBridgeCellError 0 y A B E M <=
      fourFiveContinuumBridgeCellBudgetAfterAggregation 0 y A B E M := by
  simp [fourFiveExactContinuumBridgeCellError_zero,
    fourFiveContinuumBridgeCellBudgetAfterAggregation,
    fourFiveLebesgueCellAggregationBudget,
    fourFivePhysicalProductBudgetOverrun_zero]

theorem fourFiveExactContinuumBridgeCellError_one_le_afterAggregation
    {y A B : Nat} {E M : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hu : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      2 < fourFiveRealLogCoordinate y t) :
    fourFiveExactContinuumBridgeCellError 1 y A B E M <=
      fourFiveContinuumBridgeCellBudgetAfterAggregation 1 y A B E M := by
  have hagg := fourFiveLebesgueCellAggregationError_one_le hy hyA hAB
  unfold fourFiveExactContinuumBridgeCellError
    fourFiveContinuumBridgeCellBudgetAfterAggregation
    fourFiveLebesgueCellAggregationBudget
  rw [fourFiveMovingToFixedSimplexError_one_eq_zero hu]
  linarith

theorem fourFiveExactContinuumBridgeCellError_two_le_afterAggregation
    {y A B : Nat} {E M : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hmass : (∑ n ∈ Finset.Ioc y B,
      |fourFiveLogLogLebesgueCellAtom n|) <= M)
    (hu : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      3 < fourFiveRealLogCoordinate y t) :
    fourFiveExactContinuumBridgeCellError 2 y A B E M <=
      fourFiveContinuumBridgeCellBudgetAfterAggregation 2 y A B E M := by
  have hagg := fourFiveLebesgueCellAggregationError_two_le
    hy hyA hAB hmass
  unfold fourFiveExactContinuumBridgeCellError
    fourFiveContinuumBridgeCellBudgetAfterAggregation
    fourFiveLebesgueCellAggregationBudget
  rw [fourFiveMovingToFixedSimplexError_two_eq_zero hu]
  linarith

theorem fourFiveExactContinuumBridgeCellError_three_le_afterAggregation
    {y A B : Nat} {E M : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hmass : (∑ n ∈ Finset.Ioc y B,
      |fourFiveLogLogLebesgueCellAtom n|) <= M)
    (hu : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      4 < fourFiveRealLogCoordinate y t) :
    fourFiveExactContinuumBridgeCellError 3 y A B E M <=
      fourFiveContinuumBridgeCellBudgetAfterAggregation 3 y A B E M := by
  have hagg := fourFiveLebesgueCellAggregationError_three_le
    hy hyA hAB hmass
  unfold fourFiveExactContinuumBridgeCellError
    fourFiveContinuumBridgeCellBudgetAfterAggregation
    fourFiveLebesgueCellAggregationBudget
  rw [fourFiveMovingToFixedSimplexError_three_eq_zero hu]
  linarith

theorem fourFiveLastPrimeToContinuumBridge_afterAggregation
    {y A B : Nat} {E M : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hmass : (∑ n ∈ Finset.Ioc y B,
      |fourFiveLogLogLebesgueCellAtom n|) <= M)
    (hu1 : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      2 < fourFiveRealLogCoordinate y t)
    (hu2 : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      3 < fourFiveRealLogCoordinate y t)
    (hu3 : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      4 < fourFiveRealLogCoordinate y t) :
    FourFiveLastPrimeToContinuumBridge y A B E M
      (fourFiveContinuumBridgeCellBudgetAfterAggregation 0 y A B E M)
      (fourFiveContinuumBridgeCellBudgetAfterAggregation 1 y A B E M)
      (fourFiveContinuumBridgeCellBudgetAfterAggregation 2 y A B E M)
      (fourFiveContinuumBridgeCellBudgetAfterAggregation 3 y A B E M) := by
  have hexact := fourFiveLastPrimeToContinuumBridge_exactDecomposition
    (y := y) (A := A) (B := B) hy E M
  unfold FourFiveLastPrimeToContinuumBridge at hexact ⊢
  refine ⟨hexact.1.trans ?_, hexact.2.1.trans ?_,
    hexact.2.2.1.trans ?_, hexact.2.2.2.trans ?_⟩
  · exact fourFiveExactContinuumBridgeCellError_zero_le_afterAggregation
      y A B E M
  · exact add_le_add (le_refl _)
      (fourFiveExactContinuumBridgeCellError_one_le_afterAggregation
        hy hyA hAB hu1)
  · exact add_le_add (le_refl _)
      (fourFiveExactContinuumBridgeCellError_two_le_afterAggregation
        hy hyA hAB hmass hu2)
  · exact add_le_add (le_refl _)
      (fourFiveExactContinuumBridgeCellError_three_le_afterAggregation
        hy hyA hAB hmass hu3)

/-- Final factorial assembly with the exact cell-aggregation residual
replaced by the explicit `2/4/6` dimensional budgets and the moving/fixed
residual removed by equality. -/
theorem fourFiveOrderedPrimeMixtureEstimate_afterAggregation
    {y A B : Nat} {C X0 E M : Real}
    (hC : 0 < C) (hX0 : 3 <= X0) (hyX0 : X0 <= (y : Real))
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hmass : (∑ n ∈ Finset.Ioc y B,
      |fourFiveLogLogLebesgueCellAtom n|) <= M)
    (hu1 : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      2 < fourFiveRealLogCoordinate y t)
    (hu2 : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      3 < fourFiveRealLogCoordinate y t)
    (hu3 : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      4 < fourFiveRealLogCoordinate y t)
    (hPNT : ∀ a b : Real, X0 <= a -> a <= b ->
      abs (((Nat.primeCounting ⌊b⌋₊ : Real) -
          (Nat.primeCounting ⌊a⌋₊ : Real)) -
          (∫ v in a..b, 1 / Real.log v)) <=
        3 * C * b / Real.log a ^ 5) :
    FourFiveOrderedPrimeMixtureEstimate y A B
      (fourFiveContinuumOrderedMixtureMain y A B)
      (fourFiveOrderedMixtureAssemblyError C y A B E M
        (fourFiveContinuumBridgeCellBudgetAfterAggregation 0 y A B E M)
        (fourFiveContinuumBridgeCellBudgetAfterAggregation 1 y A B E M)
        (fourFiveContinuumBridgeCellBudgetAfterAggregation 2 y A B E M)
        (fourFiveContinuumBridgeCellBudgetAfterAggregation 3 y A B E M)) := by
  exact fourFiveOrderedPrimeMixtureEstimate_of_lastPrime_continuumBridge
    (y := y) (A := A) (B := B) (C := C) (X0 := X0) (E := E) (M := M)
    hC hX0 hyX0 hPNT
      (fourFiveLastPrimeToContinuumBridge_afterAggregation
        (y := y) (A := A) (B := B) (E := E) (M := M)
        hy hyA hAB hmass hu1 hu2 hu3)

end Erdos390.WholePaper.BankPaperRealization
