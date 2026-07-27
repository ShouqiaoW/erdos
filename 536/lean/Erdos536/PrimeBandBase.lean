import Erdos536.PrimeBandFirstMoment

/-!
# A fixed positive shallow anchor event

The collision-free Poisson-compatible five-state law was chosen so that
the mass of a configuration with one prescribed active label has an exact
factorization.  This file records the finite calculation for the event in
which every coordinate is empty except for one anchor, whose location may
range over a finite reservoir.
-/

open scoped BigOperators
open Finset

namespace Erdos536

/-- The all-empty five-state configuration. -/
def emptyFiveConfiguration (ι : Type*) : ι → FiveLabel :=
  fun _ ↦ 0

/-- Insert one active label into the all-empty configuration. -/
def singletonFiveConfiguration
    {ι : Type*} [DecidableEq ι]
    (l : FiveLabel) (p : ι) : ι → FiveLabel :=
  Function.update (emptyFiveConfiguration ι) p l

theorem singletonFiveConfiguration_injective
    {ι : Type*} [DecidableEq ι]
    {l : FiveLabel} (hl : l ≠ 0) :
    Function.Injective
      (singletonFiveConfiguration (ι := ι) l) := by
  intro p q hpq
  by_contra hpq'
  have h := congrFun hpq p
  simp [singletonFiveConfiguration, emptyFiveConfiguration,
    hpq', hl] at h

/-- The finite family of configurations with exactly one anchor from `A`. -/
def singletonFiveConfigurations
    {ι : Type*} [DecidableEq ι]
    [DecidableEq (ι → FiveLabel)]
    (A : Finset ι) (l : FiveLabel) :
    Finset (ι → FiveLabel) :=
  A.image (singletonFiveConfiguration l)

@[simp]
theorem mem_singletonFiveConfigurations
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Finset ι} {l : FiveLabel} {c : ι → FiveLabel} :
    c ∈ singletonFiveConfigurations A l ↔
      ∃ p ∈ A, c = singletonFiveConfiguration l p := by
  simp [singletonFiveConfigurations, eq_comm]

private theorem prod_singletonFiveConfiguration
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → ℝ) (l : FiveLabel) (hl : l ≠ 0) (p : ι) :
    (∏ i : ι,
        collapsedPoissonCellWeight (r i)
          (some (singletonFiveConfiguration l p i))) =
      (∏ i : ι, Real.exp (-(4 * (r i / 3)))) *
        (r p / 3) := by
  let f : ι → ℝ := fun i ↦
    Real.exp (-(4 * (r i / 3)))
  have hfun :
      (fun i : ι ↦
        collapsedPoissonCellWeight (r i)
          (some (singletonFiveConfiguration l p i))) =
        Function.update f p (f p * (r p / 3)) := by
    funext i
    by_cases hip : i = p
    · subst i
      simp [singletonFiveConfiguration,
        collapsedPoissonCellWeight, f, hl]
      ring
    · simp [singletonFiveConfiguration, emptyFiveConfiguration,
        collapsedPoissonCellWeight, f, hip]
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ p)]
  rw [Finset.prod_eq_mul_prod_diff_singleton
    (Finset.mem_univ p)]
  ring

/-- Exact compatible mass of the one-anchor shallow event. -/
theorem singletonFiveConfigurations_compatibleMass
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → ℝ) (A : Finset ι)
    (l : FiveLabel) (hl : l ≠ 0) :
    (∑ c ∈ singletonFiveConfigurations A l,
        ∏ i : ι,
          collapsedPoissonCellWeight (r i) (some (c i))) =
      Real.exp (-(4 * ∑ i : ι, r i / 3)) *
        ∑ p ∈ A, r p / 3 := by
  rw [singletonFiveConfigurations, Finset.sum_image
    (fun p _hp q _hq hpq ↦
      singletonFiveConfiguration_injective hl hpq)]
  simp_rw [prod_singletonFiveConfiguration r l hl]
  rw [← Finset.mul_sum]
  congr 1
  rw [← Real.exp_sum]
  congr 2
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]

/-- A convenient lower bound from an upper bound on total shallow
intensity and a lower bound on the anchor-reservoir intensity. -/
theorem singletonFiveConfigurations_compatibleMass_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → ℝ) (A : Finset ι)
    (l : FiveLabel) (hl : l ≠ 0)
    {H m : ℝ}
    (hH : (∑ i : ι, r i / 3) ≤ H)
    (hm : m ≤ ∑ p ∈ A, r p / 3)
    (hm0 : 0 ≤ m) :
    Real.exp (-4 * H) * m ≤
      ∑ c ∈ singletonFiveConfigurations A l,
        ∏ i : ι,
          collapsedPoissonCellWeight (r i) (some (c i)) := by
  rw [singletonFiveConfigurations_compatibleMass r A l hl]
  have hexp :
      Real.exp (-4 * H) ≤
        Real.exp (-(4 * ∑ i : ι, r i / 3)) := by
    apply Real.exp_le_exp.mpr
    linarith
  exact mul_le_mul hexp hm hm0 (Real.exp_nonneg _)

/-! ## A finite weighted-tail estimate -/

/-- Weighted total carried by one specified five-state label. -/
noncomputable def fiveLabelWeightedTotal
    {α : Type*} [DecidableEq α]
    (P : Finset α) (u : α → ℝ)
    (l : FiveLabel) (c : FiveConfiguration P) : ℝ :=
  ∑ p : ↥P, if c p = l then u p.1 else 0

private theorem fiveConfiguration_coordinateLabel_mass
    {α : Type*} [DecidableEq α]
    (P : Finset α) (r : α → ℝ)
    (p : ↥P) (l : FiveLabel) :
    (∑ c : FiveConfiguration P,
        if c p = l then fiveConfigurationWeight P r c else 0) =
      fiveLabelWeight (r p.1) l := by
  classical
  let X : ↥P → FiveLabel → ℝ :=
    fun q a ↦ if q = p then if a = l then 1 else 0 else 1
  have hprod :
      (∏ q : ↥P,
          ∑ a : FiveLabel,
            fiveLabelWeight (r q.1) a * X q a) =
        fiveLabelWeight (r p.1) l := by
    rw [Finset.prod_eq_mul_prod_diff_singleton
      (Finset.mem_univ p)]
    have hp :
        (∑ a : FiveLabel,
            fiveLabelWeight (r p.1) a * X p a) =
          fiveLabelWeight (r p.1) l := by
      simp [X]
    rw [hp]
    have hrest :
        (∏ q ∈ Finset.univ \ {p},
            ∑ a : FiveLabel,
              fiveLabelWeight (r q.1) a * X q a) = 1 := by
      apply Finset.prod_eq_one
      intro q hq
      have hqp : q ≠ p := by
        simpa using (Finset.mem_sdiff.mp hq).2
      simp [X, hqp, sum_fiveLabelWeight]
    rw [hrest, mul_one]
  have hexpect :=
    finitePiExpectation_product
      (fun q : ↥P ↦ fiveLabelWeight (r q.1)) X
  change
    (∑ c : FiveConfiguration P,
        finitePiWeight
          (fun q : ↥P ↦ fiveLabelWeight (r q.1)) c *
          ∏ q : ↥P, X q (c q)) =
      ∏ q : ↥P,
        ∑ a : FiveLabel,
          fiveLabelWeight (r q.1) a * X q a at hexpect
  rw [hprod] at hexpect
  calc
    (∑ c : FiveConfiguration P,
        if c p = l then fiveConfigurationWeight P r c else 0) =
      ∑ c : FiveConfiguration P,
        finitePiWeight
          (fun q : ↥P ↦ fiveLabelWeight (r q.1)) c *
          ∏ q : ↥P, X q (c q) := by
      apply Finset.sum_congr rfl
      intro c _hc
      by_cases hcp : c p = l
      · rw [if_pos hcp]
        have hX : (∏ q : ↥P, X q (c q)) = 1 := by
          apply Finset.prod_eq_one
          intro q _hq
          by_cases hqp : q = p
          · subst q
            simp [X, hcp]
          · simp [X, hqp]
        rw [hX, mul_one]
        rfl
      · rw [if_neg hcp]
        have hzero : X p (c p) = 0 := by
          simp [X, hcp]
        rw [Finset.prod_eq_zero (Finset.mem_univ p) hzero,
          mul_zero]
    _ = fiveLabelWeight (r p.1) l := hexpect

/-- Exact first moment of the weighted total of one active label. -/
theorem fiveLabelWeightedTotal_expectation
    {α : Type*} [DecidableEq α]
    (P : Finset α) (r u : α → ℝ)
    (l : FiveLabel) :
    (∑ c : FiveConfiguration P,
        fiveConfigurationWeight P r c *
          fiveLabelWeightedTotal P u l c) =
      ∑ p : ↥P, fiveLabelWeight (r p.1) l * u p.1 := by
  classical
  unfold fiveLabelWeightedTotal
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _hp
  calc
    (∑ c : FiveConfiguration P,
        fiveConfigurationWeight P r c *
          (if c p = l then u p.1 else 0)) =
      (∑ c : FiveConfiguration P,
          if c p = l
          then fiveConfigurationWeight P r c else 0) * u p.1 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _hc
      split_ifs <;> ring
    _ = fiveLabelWeight (r p.1) l * u p.1 := by
      rw [show
        (∑ c : FiveConfiguration P,
            if c p = l then fiveConfigurationWeight P r c else 0) =
          fiveLabelWeight (r p.1) l from
        fiveConfiguration_coordinateLabel_mass P r p l]

/-- Finite Markov inequality for a weighted label total. -/
theorem fiveLabelWeightedTotal_failureMass_le
    {α : Type*} [DecidableEq α]
    (P : Finset α) (r u : α → ℝ)
    (l : FiveLabel) {δ : ℝ}
    (hδ : 0 < δ)
    (hr0 : ∀ p ∈ P, 0 ≤ r p)
    (hr34 : ∀ p ∈ P, r p ≤ 3 / 4)
    (hu : ∀ p ∈ P, 0 ≤ u p) :
    (∑ c : FiveConfiguration P,
        if δ < fiveLabelWeightedTotal P u l c
        then fiveConfigurationWeight P r c else 0) ≤
      (∑ p : ↥P,
          fiveLabelWeight (r p.1) l * u p.1) / δ := by
  classical
  apply (le_div_iff₀ hδ).2
  rw [Finset.sum_mul]
  calc
    (∑ c : FiveConfiguration P,
        (if δ < fiveLabelWeightedTotal P u l c
          then fiveConfigurationWeight P r c else 0) * δ) ≤
      ∑ c : FiveConfiguration P,
        fiveConfigurationWeight P r c *
          fiveLabelWeightedTotal P u l c := by
      apply Finset.sum_le_sum
      intro c _hc
      have hweight :
          0 ≤ fiveConfigurationWeight P r c := by
        rw [fiveConfigurationWeight]
        apply Finset.prod_nonneg
        intro p _hp
        exact fiveLabelWeight_nonneg
          (hr0 p.1 p.2) (hr34 p.1 p.2) (c p)
      have htotal :
          0 ≤ fiveLabelWeightedTotal P u l c := by
        unfold fiveLabelWeightedTotal
        apply Finset.sum_nonneg
        intro p _hp
        split_ifs
        · exact hu p.1 p.2
        · norm_num
      by_cases hc :
          δ < fiveLabelWeightedTotal P u l c
      · rw [if_pos hc]
        exact mul_le_mul_of_nonneg_left hc.le hweight
      · rw [if_neg hc, zero_mul]
        exact mul_nonneg hweight htotal
    _ = ∑ p : ↥P,
        fiveLabelWeight (r p.1) l * u p.1 :=
      fiveLabelWeightedTotal_expectation P r u l

end Erdos536
