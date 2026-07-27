import Erdos536.FiniteBernoulliChernoff
import Erdos536.PrimeBandEvent

/-!
# Finite Chernoff bounds inside the five-state law

For any one of the four active labels, its occurrences on a fixed set of
points are independent Bernoulli variables with parameter `r / 3`.  The
proof below stays entirely in the finite five-state configuration space.
-/

open scoped BigOperators
open Finset

namespace Erdos536

/-- Number of occurrences of an active label on a fixed finite collection
of points. -/
def fiveActiveLabelCountOn
    {α : Type*} [DecidableEq α] {P : Finset α}
    (Q : Finset ↥P) (l : ActiveFiveLabel)
    (c : FiveConfiguration P) : ℕ :=
  (Q.filter fun p ↦ c p = activeFiveLabel l).card

/-- Product Laplace factor for the active-label count. -/
noncomputable def fiveActiveLabelLaplaceFactor
    {α : Type*} [DecidableEq α] {P : Finset α}
    (Q : Finset ↥P) (l : ActiveFiveLabel) (t : ℝ)
    (c : FiveConfiguration P) : ℝ :=
  ∏ p : ↥P,
    if p ∈ Q ∧ c p = activeFiveLabel l then Real.exp (-t) else 1

private theorem sum_fiveLabelWeight_active_tilt
    (r t : ℝ) (l : ActiveFiveLabel) :
    (∑ a : FiveLabel,
      fiveLabelWeight r a *
        (if a = activeFiveLabel l then Real.exp (-t) else 1)) =
      (1 - r / 3) + (r / 3) * Real.exp (-t) := by
  cases l with
  | none =>
      simp [activeFiveLabel, fiveLabelWeight, Fin.sum_univ_succ]
      ring
  | some s =>
      fin_cases s <;>
        simp [activeFiveLabel, petalLabel, fiveLabelWeight,
          Fin.sum_univ_succ] <;>
        ring

theorem fiveActiveLabelLaplaceFactor_eq_exp_count
    {α : Type*} [DecidableEq α] {P : Finset α}
    (Q : Finset ↥P) (l : ActiveFiveLabel) (t : ℝ)
    (c : FiveConfiguration P) :
    fiveActiveLabelLaplaceFactor Q l t c =
      Real.exp (-t * (fiveActiveLabelCountOn Q l c : ℝ)) := by
  rw [fiveActiveLabelLaplaceFactor, fiveActiveLabelCountOn]
  have hfilter :
      (Finset.univ.filter fun p : ↥P ↦
        p ∈ Q ∧ c p = activeFiveLabel l) =
      Q.filter fun p ↦ c p = activeFiveLabel l := by
    ext p
    simp
  rw [← hfilter]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, mul_one]
  rw [Finset.prod_const, ← Real.exp_nat_mul]
  congr 1
  ring

/-- Exact finite product formula for the active-label Laplace transform. -/
theorem fiveActiveLabelLaplaceExpectation_eq_prod
    {α : Type*} [DecidableEq α]
    (P : Finset α) (r : α → ℝ)
    (Q : Finset ↥P) (l : ActiveFiveLabel) (t : ℝ) :
    (∑ c : FiveConfiguration P,
      fiveConfigurationWeight P r c *
        fiveActiveLabelLaplaceFactor Q l t c) =
      ∏ p ∈ Q,
        ((1 - r p.1 / 3) + (r p.1 / 3) * Real.exp (-t)) := by
  classical
  unfold fiveConfigurationWeight fiveActiveLabelLaplaceFactor
  simp_rw [← Finset.prod_mul_distrib]
  let F : (p : ↥P) → FiveLabel → ℝ :=
    fun p a ↦ fiveLabelWeight (r p.1) a *
      (if p ∈ Q ∧ a = activeFiveLabel l then Real.exp (-t) else 1)
  calc
    (∑ c : FiveConfiguration P, ∏ p : ↥P, F p (c p)) =
        ∏ p : ↥P, ∑ a : FiveLabel, F p a :=
      (Fintype.prod_sum F).symm
    _ = (∏ p : ↥P,
        if p ∈ Q then
          ((1 - r p.1 / 3) +
            (r p.1 / 3) * Real.exp (-t))
        else 1) := by
          apply Finset.prod_congr rfl
          intro p _hp
          dsimp [F]
          by_cases hpQ : p ∈ Q
          · rw [if_pos hpQ]
            simpa [hpQ] using
              sum_fiveLabelWeight_active_tilt (r p.1) t l
          · rw [if_neg hpQ]
            simp [hpQ, sum_fiveLabelWeight]
    _ = ∏ p ∈ Q,
        ((1 - r p.1 / 3) + (r p.1 / 3) * Real.exp (-t)) := by
      rw [Finset.prod_ite, Finset.filter_mem_eq_inter,
        Finset.univ_inter, Finset.prod_const_one, mul_one]

/-- The active-label Laplace transform is bounded by the exponential of
the summed local parameters. -/
theorem fiveActiveLabelLaplaceExpectation_le_exp
    {α : Type*} [DecidableEq α]
    {P : Finset α} {r : α → ℝ} {Q : Finset ↥P}
    {l : ActiveFiveLabel} {t : ℝ}
    (hr0 : ∀ p ∈ P, 0 ≤ r p)
    (hr1 : ∀ p ∈ P, r p ≤ 3 / 4) :
    (∑ c : FiveConfiguration P,
      fiveConfigurationWeight P r c *
        fiveActiveLabelLaplaceFactor Q l t c) ≤
      Real.exp ((Real.exp (-t) - 1) *
        ∑ p ∈ Q, r p.1 / 3) := by
  rw [fiveActiveLabelLaplaceExpectation_eq_prod]
  have hlocalNonneg (p : ↥P) (hp : p ∈ Q) :
      0 ≤ (1 - r p.1 / 3) +
        (r p.1 / 3) * Real.exp (-t) := by
    apply add_nonneg
    · exact sub_nonneg.mpr
        (by
          have := hr1 p.1 p.2
          linarith)
    · exact mul_nonneg
        (div_nonneg (hr0 p.1 p.2) (by norm_num))
        (Real.exp_pos _).le
  have hlocal (p : ↥P) (_hp : p ∈ Q) :
      (1 - r p.1 / 3) + (r p.1 / 3) * Real.exp (-t) ≤
        Real.exp ((r p.1 / 3) * (Real.exp (-t) - 1)) := by
    calc
      (1 - r p.1 / 3) + (r p.1 / 3) * Real.exp (-t) =
          1 + (r p.1 / 3) * (Real.exp (-t) - 1) := by ring
      _ ≤ Real.exp ((r p.1 / 3) * (Real.exp (-t) - 1)) := by
        simpa [add_comm] using
          Real.add_one_le_exp
            ((r p.1 / 3) * (Real.exp (-t) - 1))
  calc
    (∏ p ∈ Q,
        ((1 - r p.1 / 3) + (r p.1 / 3) * Real.exp (-t))) ≤
      ∏ p ∈ Q,
        Real.exp ((r p.1 / 3) * (Real.exp (-t) - 1)) :=
      Finset.prod_le_prod hlocalNonneg hlocal
    _ = Real.exp ((Real.exp (-t) - 1) *
        ∑ p ∈ Q, r p.1 / 3) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring

/-- Mass of a lower-count event for one active label. -/
noncomputable def fiveActiveLabelLowerTailMass
    {α : Type*} [DecidableEq α]
    (P : Finset α) (r : α → ℝ)
    (Q : Finset ↥P) (l : ActiveFiveLabel) (k : ℕ) : ℝ :=
  ∑ c : FiveConfiguration P,
    if fiveActiveLabelCountOn Q l c ≤ k
    then fiveConfigurationWeight P r c else 0

/-- Fully finite lower-tail Chernoff bound inside the five-state law. -/
theorem fiveActiveLabelLowerTailMass_le
    {α : Type*} [DecidableEq α]
    {P : Finset α} {r : α → ℝ}
    {Q : Finset ↥P} {l : ActiveFiveLabel}
    {k : ℕ} {t : ℝ}
    (hr0 : ∀ p ∈ P, 0 ≤ r p)
    (hr1 : ∀ p ∈ P, r p ≤ 3 / 4)
    (ht : 0 ≤ t) :
    fiveActiveLabelLowerTailMass P r Q l k ≤
      Real.exp (t * (k : ℝ) +
        (Real.exp (-t) - 1) *
          ∑ p ∈ Q, r p.1 / 3) := by
  have hmoment :=
    fiveActiveLabelLaplaceExpectation_le_exp
      (P := P) (r := r) (Q := Q) (l := l) (t := t) hr0 hr1
  have hfactor : 0 ≤ Real.exp (t * (k : ℝ)) :=
    (Real.exp_pos _).le
  calc
    fiveActiveLabelLowerTailMass P r Q l k ≤
        Real.exp (t * (k : ℝ)) *
          ∑ c : FiveConfiguration P,
            fiveConfigurationWeight P r c *
              fiveActiveLabelLaplaceFactor Q l t c := by
      rw [fiveActiveLabelLowerTailMass, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro c _hc
      by_cases hcount : fiveActiveLabelCountOn Q l c ≤ k
      · rw [if_pos hcount,
          fiveActiveLabelLaplaceFactor_eq_exp_count]
        have hweight : 0 ≤ fiveConfigurationWeight P r c := by
          rw [fiveConfigurationWeight]
          apply Finset.prod_nonneg
          intro p _hp
          exact fiveLabelWeight_nonneg
            (hr0 p.1 p.2)
            (hr1 p.1 p.2)
            (c p)
        have hcast :
            (fiveActiveLabelCountOn Q l c : ℝ) ≤ k := by
          exact_mod_cast hcount
        have hexp :
            1 ≤ Real.exp
              (t * (k : ℝ) +
                (-t * (fiveActiveLabelCountOn Q l c : ℝ))) := by
          rw [Real.one_le_exp_iff]
          nlinarith
        calc
          fiveConfigurationWeight P r c ≤
              fiveConfigurationWeight P r c *
                Real.exp
                  (t * (k : ℝ) +
                    (-t *
                      (fiveActiveLabelCountOn Q l c : ℝ))) := by
            simpa using mul_le_mul_of_nonneg_left hexp hweight
          _ = Real.exp (t * (k : ℝ)) *
              (fiveConfigurationWeight P r c *
                Real.exp
                  (-t *
                    (fiveActiveLabelCountOn Q l c : ℝ))) := by
            rw [Real.exp_add]
            ring
      · rw [if_neg hcount]
        exact mul_nonneg hfactor
          (mul_nonneg
            (by
              rw [fiveConfigurationWeight]
              apply Finset.prod_nonneg
              intro p _hp
              exact fiveLabelWeight_nonneg
                (hr0 p.1 p.2)
                (hr1 p.1 p.2)
                (c p))
            (by
              exact fiveActiveLabelLaplaceFactor_eq_exp_count
                Q l t c ▸ (Real.exp_pos _).le))
    _ ≤ Real.exp (t * (k : ℝ)) *
        Real.exp ((Real.exp (-t) - 1) *
          ∑ p ∈ Q, r p.1 / 3) :=
      mul_le_mul_of_nonneg_left hmoment hfactor
    _ = Real.exp (t * (k : ℝ) +
        (Real.exp (-t) - 1) *
          ∑ p ∈ Q, r p.1 / 3) := by
      rw [Real.exp_add]

end Erdos536
