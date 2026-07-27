import Erdos536.BernoulliSquarefree
import Erdos536.RootedL2

/-!
# Rooted identities for the five-state law

The support of one represented state is the finite root variable.  This file
specializes the elementary Bayes and second-moment identities to that root.
The resulting collision sum is the exact finite target of the two-completion
estimates in the prime-band argument.
-/

open scoped BigOperators
open Finset

namespace Erdos536

theorem subtypeBernoulliWeight_eq_subsetWeight
    {α : Type*} [DecidableEq α] (P : Finset α) (r : α → ℝ)
    (S : Finset ↥P) :
    subtypeBernoulliWeight P r S =
      subsetWeight Finset.univ (fun p : ↥P => r p.1) S := by
  rfl

theorem sum_subtypeBernoulliWeight
    {α : Type*} [DecidableEq α] (P : Finset α) (r : α → ℝ) :
    (∑ S : Finset ↥P, subtypeBernoulliWeight P r S) = 1 := by
  simp_rw [subtypeBernoulliWeight_eq_subsetWeight]
  exact sum_subsetWeight Finset.univ (fun p : ↥P => r p.1)

theorem subtypeBernoulliWeight_nonneg
    {α : Type*} [DecidableEq α] {P : Finset α} {r : α → ℝ}
    (hr0 : ∀ p ∈ P, 0 ≤ r p)
    (hr1 : ∀ p ∈ P, r p ≤ 1)
    (S : Finset ↥P) :
    0 ≤ subtypeBernoulliWeight P r S := by
  rw [subtypeBernoulliWeight_eq_subsetWeight]
  exact subsetWeight_nonneg
    (P := Finset.univ) (S := S)
    (fun (p : ↥P) _hp => hr0 p.1 p.2)
    (fun (p : ↥P) _hp => hr1 p.1 p.2)
    (by intro p hp; simp)

theorem subtypeBernoulliWeight_pos
    {α : Type*} [DecidableEq α] {P : Finset α} {r : α → ℝ}
    (hr0 : ∀ p ∈ P, 0 < r p)
    (hr1 : ∀ p ∈ P, r p < 1)
    (S : Finset ↥P) :
    0 < subtypeBernoulliWeight P r S := by
  rw [subtypeBernoulliWeight]
  apply mul_pos
  · apply Finset.prod_pos
    intro p hp
    exact hr0 p.1 p.2
  · apply Finset.prod_pos
    intro p hp
    exact sub_pos.mpr (hr1 p.1 p.2)

/-- Exact annealed collision mass for two completions sharing one represented
support. -/
noncomputable def fiveRootCollision
    {α : Type*} [DecidableEq α] (P : Finset α) (r : α → ℝ)
    (B : FiveConfiguration P → Bool) (s : Fin 3) : ℝ :=
  ∑ S : Finset ↥P,
    (fiveEventSupportMass P r B s S) ^ 2 /
      subtypeBernoulliWeight P r S

theorem fiveRootLikelihood_eventMass
    {α : Type*} [DecidableEq α] (P : Finset α) (r : α → ℝ)
    (B : FiveConfiguration P → Bool) (s : Fin 3)
    (hμ : ∀ S : Finset ↥P, subtypeBernoulliWeight P r S ≠ 0) :
    rootedEventMass Finset.univ
        (subtypeBernoulliWeight P r)
        (fiveRootLikelihood P r B s) =
      fiveEventMass P r B := by
  rw [rootedEventMass, rootedExpectation]
  calc
    (∑ S ∈ Finset.univ,
        subtypeBernoulliWeight P r S *
          fiveRootLikelihood P r B s S) =
        ∑ S : Finset ↥P, fiveEventSupportMass P r B s S := by
      apply Finset.sum_congr rfl
      intro S _hS
      rw [fiveRootLikelihood]
      field_simp [hμ S]
    _ = fiveEventMass P r B := sum_fiveEventSupportMass P r B s

theorem fiveRootLikelihood_secondMoment
    {α : Type*} [DecidableEq α] (P : Finset α) (r : α → ℝ)
    (B : FiveConfiguration P → Bool) (s : Fin 3)
    (hμ : ∀ S : Finset ↥P, subtypeBernoulliWeight P r S ≠ 0) :
    rootedSecondMoment Finset.univ
        (subtypeBernoulliWeight P r)
        (fiveRootLikelihood P r B s) =
      fiveRootCollision P r B s := by
  rw [rootedSecondMoment, rootedExpectation, fiveRootCollision]
  apply Finset.sum_congr rfl
  intro S _hS
  rw [fiveRootLikelihood]
  field_simp [hμ S]

theorem fiveConditionedRootDensity_secondMoment
    {α : Type*} [DecidableEq α] (P : Finset α) (r : α → ℝ)
    (B : FiveConfiguration P → Bool) (s : Fin 3)
    (hμ : ∀ S : Finset ↥P, subtypeBernoulliWeight P r S ≠ 0) :
    rootedSecondMoment Finset.univ
        (subtypeBernoulliWeight P r)
        (rootedBayesDensity (fiveEventMass P r B)
          (fiveRootLikelihood P r B s)) =
      fiveRootCollision P r B s / (fiveEventMass P r B) ^ 2 := by
  rw [rootedBayesDensity_secondMoment,
    fiveRootLikelihood_secondMoment P r B s hμ]

/-- The finite rooted `L²` conclusion in the scale used by the manuscript. -/
theorem fiveConditionedRootDensity_secondMoment_le_of_scale
    {α : Type*} [DecidableEq α] {P : Finset α} {r : α → ℝ}
    {B : FiveConfiguration P → Bool} {s : Fin 3}
    {c w C : ℝ}
    (hr0 : ∀ p ∈ P, 0 ≤ r p)
    (hr1 : ∀ p ∈ P, r p ≤ 1)
    (hμ : ∀ S : Finset ↥P, subtypeBernoulliWeight P r S ≠ 0)
    (hc : 0 < c) (hw : 0 < w)
    (hβ : c * w ^ 2 ≤ fiveEventMass P r B)
    (hcollision : fiveRootCollision P r B s ≤ C * w ^ 4) :
    rootedSecondMoment Finset.univ
        (subtypeBernoulliWeight P r)
        (rootedBayesDensity (fiveEventMass P r B)
          (fiveRootLikelihood P r B s)) ≤
      C / c ^ 2 := by
  apply rootedBayesDensity_secondMoment_le_of_scale
    (fun S _hS => subtypeBernoulliWeight_nonneg hr0 hr1 S)
    hc hw hβ
  rw [fiveRootLikelihood_secondMoment P r B s hμ]
  exact hcollision

end Erdos536
