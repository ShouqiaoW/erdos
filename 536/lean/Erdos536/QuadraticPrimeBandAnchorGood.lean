import Erdos536.QuadraticPrimeBandAnchorBase

set_option maxHeartbeats 800000

/-!
# A concrete positive-mass background event

The deep coordinates are required to satisfy the delayed profile and to
have very small normalized mass in each of the three petal labels.  A
finite union bound gives this event fixed categorical mass.  The local
categorical/compatible comparison then transfers the lower bound to the
collapsed-Poisson product law used by the adaptive-anchor argument.
-/

open scoped BigOperators
open Finset Filter Topology

noncomputable section

namespace Erdos536

open PrimeSums

local instance (T : ℕ) :
    DecidablePred (quadraticShallowPred T) :=
  fun p ↦ inferInstanceAs
    (Decidable (p ∈ quadraticShallowCarrier T))

/-- The concrete good event on the complementary (deep) coordinates. -/
def QuadraticDeepBackgroundGood
    (T H : ℕ) (v : QuadraticDeepIndex T → FiveLabel) : Prop :=
  quadraticDeepProfileFailure T H v = false ∧
    ∀ s : Fin 3, quadraticDeepPetalTotal T s v ≤ 1 / 100

noncomputable instance (T H : ℕ) :
    DecidablePred (QuadraticDeepBackgroundGood T H) :=
  Classical.decPred _

/-- Direct categorical weight on the deep-coordinate product. -/
def quadraticDeepCategoricalWeight
    (T : ℕ) (v : QuadraticDeepIndex T → FiveLabel) : ℝ :=
  ∏ p : QuadraticDeepIndex T,
    fiveLabelWeight (reciprocalBernoulli p.1.1) (v p)

/-- Categorical mass of the concrete deep good event. -/
def quadraticDeepGoodCategoricalMass (T H : ℕ) : ℝ :=
  ∑ v : QuadraticDeepIndex T → FiveLabel,
    if QuadraticDeepBackgroundGood T H v then
      quadraticDeepCategoricalWeight T v
    else 0

/-- Collapsed-Poisson compatible mass of the concrete deep good event. -/
def quadraticDeepGoodCompatibleMass (T H : ℕ) : ℝ :=
  ∑ v : QuadraticDeepIndex T → FiveLabel,
    if QuadraticDeepBackgroundGood T H v then
      ∏ p : QuadraticDeepIndex T,
        collapsedPoissonCellWeight
          (reciprocalBernoulli p.1.1) (some (v p))
    else 0

theorem quadraticDeepCategoricalWeight_nonneg
    (T : ℕ) (v : QuadraticDeepIndex T → FiveLabel) :
    0 ≤ quadraticDeepCategoricalWeight T v := by
  unfold quadraticDeepCategoricalWeight
  apply Finset.prod_nonneg
  intro p _hp
  apply fiveLabelWeight_nonneg
    (reciprocalBernoulli_nonneg p.1.1)
  exact reciprocalBernoulli_le_three_quarters
    (mem_quadraticProfilePrimeBand.mp p.1.2).1.one_le

theorem sum_quadraticDeepCategoricalWeight (T : ℕ) :
    (∑ v : QuadraticDeepIndex T → FiveLabel,
        quadraticDeepCategoricalWeight T v) = 1 := by
  unfold quadraticDeepCategoricalWeight
  rw [← Fintype.prod_sum]
  simp only [sum_fiveLabelWeight, Finset.prod_const_one]

private theorem quadraticDeepBad_indicator_le_union
    (T H : ℕ) (v : QuadraticDeepIndex T → FiveLabel) :
    (if ¬QuadraticDeepBackgroundGood T H v then
        quadraticDeepCategoricalWeight T v
      else 0) ≤
      (if quadraticDeepProfileFailure T H v then
          quadraticDeepCategoricalWeight T v
        else 0) +
        ∑ s : Fin 3,
          if (1 / 100 : ℝ) < quadraticDeepPetalTotal T s v then
            quadraticDeepCategoricalWeight T v
          else 0 := by
  classical
  have hw := quadraticDeepCategoricalWeight_nonneg T v
  have htailNonneg :
      ∀ s : Fin 3,
        0 ≤
          if (1 / 100 : ℝ) < quadraticDeepPetalTotal T s v then
            quadraticDeepCategoricalWeight T v
          else 0 := by
    intro s
    split_ifs
    · exact hw
    · norm_num
  by_cases hgood : QuadraticDeepBackgroundGood T H v
  · rw [if_neg (not_not.mpr hgood)]
    exact add_nonneg
      (by
        split_ifs
        · exact hw
        · norm_num)
      (Finset.sum_nonneg fun s _hs ↦ htailNonneg s)
  · rw [if_pos hgood]
    by_cases hprofile :
        quadraticDeepProfileFailure T H v = false
    · have hnotAll :
          ¬∀ s : Fin 3,
            quadraticDeepPetalTotal T s v ≤ 1 / 100 := by
        intro hall
        exact hgood ⟨hprofile, hall⟩
      push_neg at hnotAll
      obtain ⟨s, hs⟩ := hnotAll
      have htail :
          quadraticDeepCategoricalWeight T v ≤
            ∑ t : Fin 3,
              if (1 / 100 : ℝ) <
                  quadraticDeepPetalTotal T t v then
                quadraticDeepCategoricalWeight T v
              else 0 := by
        calc
          quadraticDeepCategoricalWeight T v =
              (if (1 / 100 : ℝ) <
                    quadraticDeepPetalTotal T s v then
                  quadraticDeepCategoricalWeight T v
                else 0) := by
                  rw [if_pos hs]
          _ ≤ _ := by
            exact Finset.single_le_sum
              (s := Finset.univ)
              (f := fun t : Fin 3 =>
                if (1 / 100 : ℝ) <
                    quadraticDeepPetalTotal T t v then
                  quadraticDeepCategoricalWeight T v
                else 0)
              (fun t _ht ↦ htailNonneg t)
              (Finset.mem_univ s)
      simp only [hprofile, Bool.false_eq_true, ↓reduceIte, zero_add]
      exact htail
    · have hprofileTrue :
          quadraticDeepProfileFailure T H v = true :=
        Bool.eq_true_of_not_eq_false hprofile
      simp only [hprofileTrue, ↓reduceIte]
      exact le_add_of_nonneg_right
        (Finset.sum_nonneg fun s _hs ↦ htailNonneg s)

/-- Uniformly in the checked profile horizon, the concrete deep good event
has categorical mass at least `4/5`. -/
theorem eventually_quadraticDeepGoodCategoricalMass_ge_four_fifths :
    ∀ᶠ T : ℕ in atTop, ∀ H : ℕ,
      4 / 5 ≤ quadraticDeepGoodCategoricalMass T H := by
  have hprofile :=
    eventually_quadraticDelayedProfileFailureMass_lt_one_eighth
      (epsilon := (1 : ℝ)) (by norm_num) (by norm_num)
  filter_upwards [
    hprofile,
    eventually_quadraticDeepPetalFailure_categoricalMass_le
  ] with T hprofileT htailT
  intro H
  have hprofileDeep :
      (∑ v : QuadraticDeepIndex T → FiveLabel,
          if quadraticDeepProfileFailure T H v then
            quadraticDeepCategoricalWeight T v
          else 0) <
        1 / 8 := by
    simpa only [quadraticDeepCategoricalWeight] using
      (quadraticDeepProfileFailure_categoricalMass_eq T H).trans_lt
        (hprofileT H)
  have htails :
      (∑ s : Fin 3,
          ∑ v : QuadraticDeepIndex T → FiveLabel,
            if (1 / 100 : ℝ) <
                quadraticDeepPetalTotal T s v then
              quadraticDeepCategoricalWeight T v
            else 0) ≤
        1 / 50 := by
    calc
      _ ≤ ∑ _s : Fin 3, (1 / 150 : ℝ) := by
        apply Finset.sum_le_sum
        intro s _hs
        simpa only [quadraticDeepCategoricalWeight] using htailT s
      _ = 1 / 50 := by
        norm_num [Fin.sum_univ_succ]
  let badMass : ℝ :=
    ∑ v : QuadraticDeepIndex T → FiveLabel,
      if ¬QuadraticDeepBackgroundGood T H v then
        quadraticDeepCategoricalWeight T v
      else 0
  have hbad :
      badMass <
        1 / 8 + 1 / 50 := by
    calc
      badMass ≤
          (∑ v : QuadraticDeepIndex T → FiveLabel,
              if quadraticDeepProfileFailure T H v then
                quadraticDeepCategoricalWeight T v
              else 0) +
            ∑ s : Fin 3,
              ∑ v : QuadraticDeepIndex T → FiveLabel,
                if (1 / 100 : ℝ) <
                    quadraticDeepPetalTotal T s v then
                  quadraticDeepCategoricalWeight T v
                else 0 := by
        unfold badMass
        calc
          _ ≤
              ∑ v : QuadraticDeepIndex T → FiveLabel,
                ((if quadraticDeepProfileFailure T H v then
                    quadraticDeepCategoricalWeight T v
                  else 0) +
                  ∑ s : Fin 3,
                    if (1 / 100 : ℝ) <
                        quadraticDeepPetalTotal T s v then
                      quadraticDeepCategoricalWeight T v
                    else 0) := by
            apply Finset.sum_le_sum
            intro v _hv
            exact quadraticDeepBad_indicator_le_union T H v
          _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_comm]
      _ < 1 / 8 + 1 / 50 :=
        add_lt_add_of_lt_of_le hprofileDeep htails
  have hdecomp :
      quadraticDeepGoodCategoricalMass T H + badMass = 1 := by
    rw [← sum_quadraticDeepCategoricalWeight T]
    unfold quadraticDeepGoodCategoricalMass badMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _hv
    by_cases hgood : QuadraticDeepBackgroundGood T H v
    · simp [hgood]
    · simp [hgood]
  linarith

/-- The quadratic prime cutoff controls the sum of the local squared
categorical/compatible errors on the deep coordinates. -/
theorem quadraticDeep_reciprocalBernoulli_third_sq_le
    {T : ℕ} (hT : 1 ≤ T) :
    (∑ p : QuadraticDeepIndex T,
        (reciprocalBernoulli p.1.1 / 3) ^ 2) ≤
      1 / (9 * (quadraticLowerCutoff T : ℝ)) := by
  let f : ↥(quadraticProfilePrimeBand T) → ℝ :=
    fun p ↦ (reciprocalBernoulli p.1 / 3) ^ 2
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype
      (quadraticShallowPred T) f
  have hshallow :
      0 ≤ ∑ p : QuadraticShallowIndex T, f p.1 := by
    apply Finset.sum_nonneg
    intro p _hp
    exact sq_nonneg _
  calc
    (∑ p : QuadraticDeepIndex T,
        (reciprocalBernoulli p.1.1 / 3) ^ 2) ≤
        (∑ p : QuadraticShallowIndex T, f p.1) +
          ∑ p : QuadraticDeepIndex T, f p.1 :=
      le_add_of_nonneg_left hshallow
    _ = ∑ p : ↥(quadraticProfilePrimeBand T), f p := hsplit
    _ ≤ 1 / (9 * (quadraticLowerCutoff T : ℝ)) := by
      apply sum_reciprocalBernoulli_third_sq_le
        (by
          simpa only [quadraticProfilePrimeBand] using
            quadraticPrimeBand_prime T (1 : ℝ))
        (by
          unfold quadraticLowerCutoff
          exact one_le_pow₀ hT)
        (fun p hp ↦
          (mem_quadraticProfilePrimeBand.mp hp).2.1)

/-- Quantitative comparison between the categorical and compatible masses
of the concrete deep good event. -/
theorem quadraticDeepGood_categorical_compatible_abs_le
    {T : ℕ} (hT : 1 ≤ T) (H : ℕ) :
    |quadraticDeepGoodCategoricalMass T H -
        quadraticDeepGoodCompatibleMass T H| ≤
      16 / (9 * (quadraticLowerCutoff T : ℝ)) := by
  have hlocal :=
    directFiveEvent_compatible_abs_le
      (fun p : QuadraticDeepIndex T ↦
        reciprocalBernoulli p.1.1)
      (QuadraticDeepBackgroundGood T H)
      (fun p ↦ reciprocalBernoulli_nonneg p.1.1)
      (fun p ↦
        reciprocalBernoulli_le_three_quarters
          (mem_quadraticProfilePrimeBand.mp p.1.2).1.one_le)
  calc
    |quadraticDeepGoodCategoricalMass T H -
        quadraticDeepGoodCompatibleMass T H| ≤
        16 *
          ∑ p : QuadraticDeepIndex T,
            (reciprocalBernoulli p.1.1 / 3) ^ 2 := by
      simpa only [
        quadraticDeepGoodCategoricalMass,
        quadraticDeepCategoricalWeight,
        quadraticDeepGoodCompatibleMass] using hlocal
    _ ≤
        16 * (1 / (9 * (quadraticLowerCutoff T : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (quadraticDeep_reciprocalBernoulli_third_sq_le hT)
        (by norm_num)
    _ = 16 / (9 * (quadraticLowerCutoff T : ℝ)) := by
      ring

private theorem eventually_quadraticDeepGood_comparisonError_le :
    ∀ᶠ T : ℕ in atTop,
      16 / (9 * (quadraticLowerCutoff T : ℝ)) ≤ 3 / 10 := by
  have hinv :=
    eventually_inv_quadraticLowerCutoff_le_const_div_square_sq
      (c := (1 / 10 : ℝ)) (by norm_num)
  filter_upwards [hinv, eventually_ge_atTop 1] with T hinvT hT
  have hq :
      (1 : ℝ) ≤ ((T ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast (one_le_pow₀ hT : 1 ≤ T ^ 2)
  have hqSq :
      (1 : ℝ) ≤ (((T ^ 2 : ℕ) : ℝ) ^ 2) :=
    one_le_pow₀ hq
  have hqSqPos :
      (0 : ℝ) < (((T ^ 2 : ℕ) : ℝ) ^ 2) :=
    zero_lt_one.trans_le hqSq
  have hdiv :
      (1 / 10 : ℝ) / (((T ^ 2 : ℕ) : ℝ) ^ 2) ≤
        1 / 10 := by
    apply (div_le_iff₀ hqSqPos).2
    nlinarith
  have hinvCoarse :
      1 / (quadraticLowerCutoff T : ℝ) ≤ 1 / 10 :=
    hinvT.trans hdiv
  calc
    16 / (9 * (quadraticLowerCutoff T : ℝ)) =
        (16 / 9 : ℝ) *
          (1 / (quadraticLowerCutoff T : ℝ)) := by
      ring
    _ ≤ (16 / 9 : ℝ) * (1 / 10) :=
      mul_le_mul_of_nonneg_left hinvCoarse (by norm_num)
    _ ≤ 3 / 10 := by norm_num

/-- Uniformly in the profile horizon, the concrete deep good event has
compatible mass at least `1/2`. -/
theorem eventually_quadraticDeepGoodCompatibleMass_ge_one_half :
    ∀ᶠ T : ℕ in atTop, ∀ H : ℕ,
      1 / 2 ≤ quadraticDeepGoodCompatibleMass T H := by
  filter_upwards [
    eventually_quadraticDeepGoodCategoricalMass_ge_four_fifths,
    eventually_quadraticDeepGood_comparisonError_le,
    eventually_ge_atTop 1
  ] with T hcategorical herror hT
  intro H
  have habs :=
    quadraticDeepGood_categorical_compatible_abs_le hT H
  rw [abs_le] at habs
  have hcat := hcategorical H
  linarith

/-- The concrete whole-band background event used by the two-anchor
construction. -/
def quadraticConcreteAnchorBase (T H : ℕ) :
    Finset (FiveConfiguration (quadraticProfilePrimeBand T)) :=
  quadraticAnchorBase T (QuadraticDeepBackgroundGood T H)

/-- A fixed positive lower bound for the compatible mass of the concrete
whole-band background event. -/
def quadraticConcreteAnchorBaseMassLower : ℝ :=
  quadraticShallowAnchorMassLower * (1 / 2)

theorem quadraticConcreteAnchorBaseMassLower_pos :
    0 < quadraticConcreteAnchorBaseMassLower := by
  unfold quadraticConcreteAnchorBaseMassLower
  exact mul_pos quadraticShallowAnchorMassLower_pos (by norm_num)

/-- The shallow singleton factor and the deep good factor combine to give
a fixed positive compatible mass, uniformly in the profile horizon. -/
theorem eventually_quadraticConcreteAnchorBase_compatibleMass_lower :
    ∀ᶠ T : ℕ in atTop, ∀ H : ℕ,
      quadraticConcreteAnchorBaseMassLower ≤
        ∑ c ∈ quadraticConcreteAnchorBase T H,
          poissonCompatibleConfigurationWeight
            (quadraticProfilePrimeBand T) reciprocalBernoulli c := by
  filter_upwards [
    eventually_quadraticShallowAnchorMass_lower,
    eventually_quadraticDeepGoodCompatibleMass_ge_one_half
  ] with T hshallow hdeep
  intro H
  have hmain :=
    quadraticAnchorBase_compatibleMass_lower
      (T := T) (QuadraticDeepBackgroundGood T H)
      hshallow (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (hdeep H)
  simpa only [
    quadraticConcreteAnchorBaseMassLower,
    quadraticConcreteAnchorBase,
    quadraticDeepGoodCompatibleMass] using hmain

end Erdos536
