import Erdos536.FiniteProbability

/-!
# Finite Chernoff bounds for Bernoulli subset laws

Everything here is an identity or inequality between finite sums.  It is
designed for the prime-band prefix estimates, where the points carrying one
fixed active label form an independent Bernoulli subset.
-/

open scoped BigOperators
open Finset

namespace Erdos536

/-- Exponentially tilted total mass of a Bernoulli subset law. -/
noncomputable def subsetCardExponentialMoment
    {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (t : ℝ) : ℝ :=
  ∑ S ∈ P.powerset,
    subsetWeight P q S * Real.exp (-t * (S.card : ℝ))

/-- Exact finite product formula for the exponential moment of the selected
cardinality. -/
theorem subsetCardExponentialMoment_eq_prod
    {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (t : ℝ) :
    subsetCardExponentialMoment P q t =
      ∏ p ∈ P, ((1 - q p) + q p * Real.exp (-t)) := by
  classical
  rw [subsetCardExponentialMoment]
  have hexp (S : Finset α) :
      Real.exp (-t * (S.card : ℝ)) =
        ∏ _p ∈ S, Real.exp (-t) := by
    rw [Finset.prod_const, ← Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [subsetWeight, hexp]
  calc
    (∑ S ∈ P.powerset,
        ((∏ p ∈ S, q p) * ∏ p ∈ P \ S, (1 - q p)) *
          ∏ _p ∈ S, Real.exp (-t)) =
        ∑ S ∈ P.powerset,
          (∏ p ∈ S, q p * Real.exp (-t)) *
            ∏ p ∈ P \ S, (1 - q p) := by
      apply Finset.sum_congr rfl
      intro S _hS
      calc
        ((∏ p ∈ S, q p) * ∏ p ∈ P \ S, (1 - q p)) *
              ∏ _p ∈ S, Real.exp (-t) =
            ((∏ p ∈ S, q p) * ∏ _p ∈ S, Real.exp (-t)) *
              ∏ p ∈ P \ S, (1 - q p) := by ring
        _ = (∏ p ∈ S, q p * Real.exp (-t)) *
              ∏ p ∈ P \ S, (1 - q p) := by
          rw [Finset.prod_mul_distrib]
    _ = ∏ p ∈ P, ((1 - q p) + q p * Real.exp (-t)) := by
      rw [← Finset.prod_add]
      apply Finset.prod_congr rfl
      intro p _hp
      ring

/-- The exact product moment is at most the exponential of the summed
Bernoulli parameters. -/
theorem subsetCardExponentialMoment_le_exp
    {α : Type*} [DecidableEq α]
    {P : Finset α} {q : α → ℝ} {t : ℝ}
    (hq0 : ∀ p ∈ P, 0 ≤ q p)
    (hq1 : ∀ p ∈ P, q p ≤ 1) :
    subsetCardExponentialMoment P q t ≤
      Real.exp ((Real.exp (-t) - 1) * ∑ p ∈ P, q p) := by
  rw [subsetCardExponentialMoment_eq_prod]
  have hlocalNonneg (p : α) (hp : p ∈ P) :
      0 ≤ (1 - q p) + q p * Real.exp (-t) :=
    add_nonneg (sub_nonneg.mpr (hq1 p hp))
      (mul_nonneg (hq0 p hp) (Real.exp_pos _).le)
  have hlocal (p : α) (hp : p ∈ P) :
      (1 - q p) + q p * Real.exp (-t) ≤
        Real.exp (q p * (Real.exp (-t) - 1)) := by
    calc
      (1 - q p) + q p * Real.exp (-t) =
          1 + q p * (Real.exp (-t) - 1) := by ring
      _ ≤ Real.exp (q p * (Real.exp (-t) - 1)) :=
        by simpa [add_comm] using
          Real.add_one_le_exp (q p * (Real.exp (-t) - 1))
  calc
    (∏ p ∈ P, ((1 - q p) + q p * Real.exp (-t))) ≤
        ∏ p ∈ P, Real.exp (q p * (Real.exp (-t) - 1)) := by
      exact Finset.prod_le_prod
        (fun p hp => hlocalNonneg p hp)
        (fun p hp => hlocal p hp)
    _ = Real.exp ((Real.exp (-t) - 1) * ∑ p ∈ P, q p) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring

/-- Mass of the lower-cardinality tail under a finite Bernoulli subset
law. -/
noncomputable def subsetCardLowerTailMass
    {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ P.powerset,
    if S.card ≤ k then subsetWeight P q S else 0

/-- Finite exponential Markov inequality for a Bernoulli lower tail. -/
theorem subsetCardLowerTailMass_le
    {α : Type*} [DecidableEq α]
    {P : Finset α} {q : α → ℝ} {k : ℕ} {t : ℝ}
    (hq0 : ∀ p ∈ P, 0 ≤ q p)
    (hq1 : ∀ p ∈ P, q p ≤ 1)
    (ht : 0 ≤ t) :
    subsetCardLowerTailMass P q k ≤
      Real.exp (t * (k : ℝ) +
        (Real.exp (-t) - 1) * ∑ p ∈ P, q p) := by
  have hmoment :=
    subsetCardExponentialMoment_le_exp
      (P := P) (q := q) (t := t) hq0 hq1
  have hfactorNonneg : 0 ≤ Real.exp (t * (k : ℝ)) :=
    (Real.exp_pos _).le
  calc
    subsetCardLowerTailMass P q k ≤
        Real.exp (t * (k : ℝ)) *
          subsetCardExponentialMoment P q t := by
      rw [subsetCardLowerTailMass, subsetCardExponentialMoment,
        Finset.mul_sum]
      apply Finset.sum_le_sum
      intro S hS
      by_cases hcard : S.card ≤ k
      · rw [if_pos hcard]
        have hweight :
            0 ≤ subsetWeight P q S :=
          subsetWeight_nonneg hq0 hq1
            (Finset.mem_powerset.mp hS)
        have hcast : (S.card : ℝ) ≤ k := by exact_mod_cast hcard
        have hexp :
            1 ≤ Real.exp
              (t * (k : ℝ) + (-t * (S.card : ℝ))) := by
          rw [Real.one_le_exp_iff]
          nlinarith
        calc
          subsetWeight P q S ≤
              subsetWeight P q S *
                Real.exp
                  (t * (k : ℝ) + (-t * (S.card : ℝ))) := by
            simpa using mul_le_mul_of_nonneg_left hexp hweight
          _ = Real.exp (t * (k : ℝ)) *
              (subsetWeight P q S *
                Real.exp (-t * (S.card : ℝ))) := by
            rw [Real.exp_add]
            ring
      · rw [if_neg hcard]
        exact mul_nonneg hfactorNonneg
          (mul_nonneg
            (subsetWeight_nonneg hq0 hq1
              (Finset.mem_powerset.mp hS))
            (Real.exp_pos _).le)
    _ ≤ Real.exp (t * (k : ℝ)) *
        Real.exp ((Real.exp (-t) - 1) * ∑ p ∈ P, q p) :=
      mul_le_mul_of_nonneg_left hmoment hfactorNonneg
    _ = Real.exp (t * (k : ℝ) +
        (Real.exp (-t) - 1) * ∑ p ∈ P, q p) := by
      rw [Real.exp_add]

end Erdos536
