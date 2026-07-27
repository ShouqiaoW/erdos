import Mathlib

/-!
# Rooted finite `L²` identities

This file records the elementary Bayes calculation used after exposing a
finite root variable.  The root law is represented by explicit weights
`μ`, while `g r` is the conditional likelihood of an event given the root
`r`.  Thus the event mass is `β = ∑ r, μ r * g r`, and conditioning changes
the root density by the factor `g r / β`.

The statements use finite sums only.  In particular, the second-moment
estimate is independent of any measure-theoretic conditional-probability
interface.
-/

open scoped BigOperators
open Finset

namespace Erdos536

/-- A nonnegative, normalized collection of weights on a finite set. -/
def IsFiniteRootLaw {ρ : Type*} [DecidableEq ρ]
    (R : Finset ρ) (μ : ρ → ℝ) : Prop :=
  (∀ r ∈ R, 0 ≤ μ r) ∧ ∑ r ∈ R, μ r = 1

theorem IsFiniteRootLaw.nonneg {ρ : Type*} [DecidableEq ρ]
    {R : Finset ρ} {μ : ρ → ℝ} (hμ : IsFiniteRootLaw R μ)
    {r : ρ} (hr : r ∈ R) :
    0 ≤ μ r :=
  hμ.1 r hr

theorem IsFiniteRootLaw.sum_eq_one {ρ : Type*} [DecidableEq ρ]
    {R : Finset ρ} {μ : ρ → ℝ} (hμ : IsFiniteRootLaw R μ) :
    ∑ r ∈ R, μ r = 1 :=
  hμ.2

/-- Expectation under a finite root law, written as an explicit sum. -/
def rootedExpectation {ρ : Type*} [DecidableEq ρ]
    (R : Finset ρ) (μ X : ρ → ℝ) : ℝ :=
  ∑ r ∈ R, μ r * X r

/-- The total mass of an event whose likelihood conditional on `r` is
`g r`. -/
def rootedEventMass {ρ : Type*} [DecidableEq ρ]
    (R : Finset ρ) (μ g : ρ → ℝ) : ℝ :=
  rootedExpectation R μ g

/-- The density of the conditioned root marginal relative to its original
law. -/
noncomputable def rootedBayesDensity {ρ : Type*}
    (β : ℝ) (g : ρ → ℝ) (r : ρ) : ℝ :=
  g r / β

/-- The uncentered second moment under a finite root law. -/
def rootedSecondMoment {ρ : Type*} [DecidableEq ρ]
    (R : Finset ρ) (μ X : ρ → ℝ) : ℝ :=
  rootedExpectation R μ fun r => (X r) ^ 2

/-- The square root of the uncentered second moment. -/
noncomputable def rootedL2Norm {ρ : Type*} [DecidableEq ρ]
    (R : Finset ρ) (μ X : ρ → ℝ) : ℝ :=
  Real.sqrt (rootedSecondMoment R μ X)

theorem rootedExpectation_one {ρ : Type*} [DecidableEq ρ]
    {R : Finset ρ} {μ : ρ → ℝ} (hμ : IsFiniteRootLaw R μ) :
    rootedExpectation R μ (fun _ => 1) = 1 := by
  simpa [rootedExpectation] using hμ.sum_eq_one

theorem rootedSecondMoment_nonneg {ρ : Type*} [DecidableEq ρ]
    {R : Finset ρ} {μ X : ρ → ℝ}
    (hμ : ∀ r ∈ R, 0 ≤ μ r) :
    0 ≤ rootedSecondMoment R μ X := by
  exact Finset.sum_nonneg fun r hr => mul_nonneg (hμ r hr) (sq_nonneg _)

/-- Bayes' density has mean one.  Normalization of `μ` is what makes it a
root probability law; algebraically, only the displayed formula for `β`
and its positivity are needed in this identity. -/
theorem rootedBayesDensity_mean_one {ρ : Type*} [DecidableEq ρ]
    {R : Finset ρ} {μ g : ρ → ℝ} {β : ℝ}
    (_hμ : IsFiniteRootLaw R μ)
    (hβ : rootedEventMass R μ g = β) (hβpos : 0 < β) :
    rootedExpectation R μ (rootedBayesDensity β g) = 1 := by
  have hβ0 : β ≠ 0 := ne_of_gt hβpos
  calc
    rootedExpectation R μ (rootedBayesDensity β g) =
        rootedEventMass R μ g / β := by
      rw [rootedExpectation, rootedEventMass, rootedExpectation,
        Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r _hr
      simp only [rootedBayesDensity]
      ring
    _ = β / β := by rw [hβ]
    _ = 1 := div_self hβ0

/-- The exact second-moment formula for the Bayes density. -/
theorem rootedBayesDensity_secondMoment {ρ : Type*} [DecidableEq ρ]
    (R : Finset ρ) (μ g : ρ → ℝ) (β : ℝ) :
    rootedSecondMoment R μ (rootedBayesDensity β g) =
      rootedSecondMoment R μ g / β ^ 2 := by
  rw [rootedSecondMoment, rootedExpectation, rootedSecondMoment,
    rootedExpectation, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _hr
  simp only [rootedBayesDensity]
  rw [div_pow]
  ring

/-- A scale-free second-moment bound.  If the event mass is at least
`c * w²` and the collision mass is at most `C * w⁴`, the conditioned root
density has second moment at most `C / c²`, uniformly in `w`. -/
theorem rootedBayesDensity_secondMoment_le_of_scale
    {ρ : Type*} [DecidableEq ρ]
    {R : Finset ρ} {μ g : ρ → ℝ} {β c w C : ℝ}
    (hμ : ∀ r ∈ R, 0 ≤ μ r)
    (hc : 0 < c) (hw : 0 < w)
    (hβ : c * w ^ 2 ≤ β)
    (hcollision : rootedSecondMoment R μ g ≤ C * w ^ 4) :
    rootedSecondMoment R μ (rootedBayesDensity β g) ≤ C / c ^ 2 := by
  have hcwpos : 0 < c * w ^ 2 := mul_pos hc (sq_pos_of_pos hw)
  have hβpos : 0 < β := lt_of_lt_of_le hcwpos hβ
  have hdenpos : 0 < c ^ 2 * w ^ 4 := by positivity
  have hden :
      c ^ 2 * w ^ 4 ≤ β ^ 2 := by
    calc
      c ^ 2 * w ^ 4 = (c * w ^ 2) ^ 2 := by ring
      _ ≤ β ^ 2 :=
        (sq_le_sq₀ (le_of_lt hcwpos) (le_of_lt hβpos)).2 hβ
  have hrawnonneg : 0 ≤ rootedSecondMoment R μ g :=
    rootedSecondMoment_nonneg hμ
  have huppnonneg : 0 ≤ C * w ^ 4 :=
    hrawnonneg.trans hcollision
  rw [rootedBayesDensity_secondMoment]
  calc
    rootedSecondMoment R μ g / β ^ 2 ≤
        (C * w ^ 4) / (c ^ 2 * w ^ 4) :=
      div_le_div₀ huppnonneg hcollision hdenpos hden
    _ = C / c ^ 2 := by
      have hw0 : w ≠ 0 := ne_of_gt hw
      field_simp

/-- The preceding estimate, phrased directly as a bound on the `L²` norm. -/
theorem rootedBayesDensity_l2Norm_le_of_scale
    {ρ : Type*} [DecidableEq ρ]
    {R : Finset ρ} {μ g : ρ → ℝ} {β c w C : ℝ}
    (hμ : ∀ r ∈ R, 0 ≤ μ r)
    (hc : 0 < c) (hw : 0 < w)
    (hβ : c * w ^ 2 ≤ β)
    (hcollision : rootedSecondMoment R μ g ≤ C * w ^ 4) :
    rootedL2Norm R μ (rootedBayesDensity β g) ≤ Real.sqrt (C / c ^ 2) := by
  exact Real.sqrt_le_sqrt
    (rootedBayesDensity_secondMoment_le_of_scale
      hμ hc hw hβ hcollision)

/-- Two conditionally independent completions of the same root turn a
one-completion likelihood into its square.  This is the finite-sum form of
the standard two-copy identity. -/
theorem twoIndependentCompletions_eq_secondMoment
    {ρ κ : Type*} [DecidableEq ρ] [DecidableEq κ]
    (R : Finset ρ) (K : ρ → Finset κ)
    (μ : ρ → ℝ) (a : ρ → κ → ℝ) :
    (∑ r ∈ R, μ r *
      ∑ x ∈ K r, ∑ y ∈ K r, a r x * a r y) =
      rootedSecondMoment R μ
        (fun r => ∑ x ∈ K r, a r x) := by
  rw [rootedSecondMoment, rootedExpectation]
  apply Finset.sum_congr rfl
  intro r _hr
  congr 1
  rw [pow_two, Finset.sum_mul_sum]

end Erdos536
