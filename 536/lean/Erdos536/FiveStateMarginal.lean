import Erdos536.FiveStateCubeLaw
import Erdos536.FiveStateRooted
import Erdos536.AlternativeBandFlattening

/-!
# Marginal distance of a conditioned five-state cube

This module identifies the support-distance field of
`conditionedFiveCubeLaw` with the ordinary finite `L¹` error of its Bayes
density under the reciprocal squarefree product law.
-/

open scoped BigOperators
open Finset

namespace Erdos536

/-- Recover a subtype support from an ordinary finset. -/
def subtypeSupportOf (R T : Finset ℕ) : Finset ↥R :=
  R.attach.filter fun p => p.1 ∈ T

@[simp]
theorem mem_subtypeSupportOf {R T : Finset ℕ} {p : ↥R} :
    p ∈ subtypeSupportOf R T ↔ p.1 ∈ T := by
  simp [subtypeSupportOf]

theorem underlyingValues_subtypeSupportOf
    {R T : Finset ℕ} (hT : T ⊆ R) :
    underlyingValues (subtypeSupportOf R T) = T := by
  ext p
  constructor
  · intro hp
    rw [underlyingValues, Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact mem_subtypeSupportOf.mp hq
  · intro hp
    rw [underlyingValues, Finset.mem_image]
    let q : ↥R := ⟨p, hT hp⟩
    exact ⟨q, mem_subtypeSupportOf.mpr hp, rfl⟩

theorem image_univ_underlyingValues (R : Finset ℕ) :
    (Finset.univ : Finset (Finset ↥R)).image underlyingValues =
      R.powerset := by
  ext T
  constructor
  · intro hT
    obtain ⟨S, _hS, rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_powerset.mpr (underlyingValues_subset S)
  · intro hT
    have hsub := Finset.mem_powerset.mp hT
    apply Finset.mem_image.mpr
    exact ⟨subtypeSupportOf R T, Finset.mem_univ _,
      underlyingValues_subtypeSupportOf hsub⟩

theorem sum_powerset_eq_sum_subtypeSupports
    (R : Finset ℕ) (F : Finset ℕ → ℝ) :
    (∑ T ∈ R.powerset, F T) =
      ∑ S : Finset ↥R, F (underlyingValues S) := by
  rw [← image_univ_underlyingValues R]
  exact Finset.sum_image (fun _ _ _ _ h => underlyingValues_injective h)

theorem subtypeSupportVal_eq_underlyingValues
    {R : Finset ℕ} (S : Finset ↥R) :
    subtypeSupportVal S = underlyingValues S := by
  ext p
  simp [subtypeSupportVal, underlyingValues]

theorem reciprocalBernoulli_pos {p : ℕ} :
    0 < reciprocalBernoulli p := by
  unfold reciprocalBernoulli
  positivity

theorem reciprocalBernoulli_lt_one {p : ℕ} (hp : 0 < p) :
    reciprocalBernoulli p < 1 := by
  unfold reciprocalBernoulli
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hden : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  apply (div_lt_iff₀ hden).2
  linarith

theorem subtypeBernoulliWeight_reciprocal_underlying
    {R : Finset ℕ} (hR : IsPrimeSupport R) (S : Finset ↥R) :
    subtypeBernoulliWeight R reciprocalBernoulli S =
      1 / (squarefreeZ R *
        (primeProduct (underlyingValues S) : ℝ)) := by
  rw [subtypeBernoulliWeight_reciprocal hR,
    subtypeSupportVal_eq_underlyingValues]

theorem conditionedFiveSupportMass_eq_density
    (R : Finset ℕ) (B : FiveConfiguration R → Bool)
    (s : Fin 3) (S : Finset ↥R)
    (hμ : subtypeBernoulliWeight R reciprocalBernoulli S ≠ 0) :
    conditionedFiveSupportMass R reciprocalBernoulli B s S =
      subtypeBernoulliWeight R reciprocalBernoulli S *
        rootedBayesDensity (fiveEventMass R reciprocalBernoulli B)
          (fiveRootLikelihood R reciprocalBernoulli B s) S := by
  rw [conditionedFiveSupportMass_eq_bayes R reciprocalBernoulli B s S hμ]
  rfl

/-- Exact identification of a word's support error with the Bayes-density
`L¹` error on the finite reciprocal squarefree law. -/
theorem conditionedFiveCubeLaw_wordSupportDistance_eq
    (R : Finset ℕ) (hR : IsPrimeSupport R)
    (B : FiveConfiguration R → Bool)
    (hpetals : FiveEventHasPetals R B)
    (hB : 0 < fiveEventMass R reciprocalBernoulli B)
    (s : Fin 3) :
    (conditionedFiveCubeLaw R reciprocalBernoulli B hpetals
      (fun p _hp => reciprocalBernoulli_nonneg p)
      (fun p hp => reciprocalBernoulli_le_three_quarters
        (hR p hp).pos)
      hB).wordSupportDistance (fiveStateWord s) =
      finiteL1Error Finset.univ
        (subtypeBernoulliWeight R reciprocalBernoulli)
        (rootedBayesDensity (fiveEventMass R reciprocalBernoulli B)
          (fiveRootLikelihood R reciprocalBernoulli B s)) := by
  classical
  rw [FiniteCubeLaw.wordSupportDistance,
    sum_powerset_eq_sum_subtypeSupports]
  rw [finiteL1Error, finiteExpectation]
  apply Finset.sum_congr rfl
  intro S _hS
  have hμpos :
      0 < subtypeBernoulliWeight R reciprocalBernoulli S :=
    subtypeBernoulliWeight_pos
      (fun p _hp => reciprocalBernoulli_pos)
      (fun p hp => reciprocalBernoulli_lt_one (hR p hp).pos) S
  rw [conditionedFiveCubeLaw_wordSupportMass
    R reciprocalBernoulli B hpetals
      (fun p _hp => reciprocalBernoulli_nonneg p)
      (fun p hp => reciprocalBernoulli_le_three_quarters
        (hR p hp).pos)
      hB s S]
  rw [subtypeBernoulliWeight_reciprocal_underlying hR S]
  rw [conditionedFiveSupportMass_eq_density R B s S hμpos.ne']
  rw [subtypeBernoulliWeight_reciprocal_underlying hR S]
  have hcanonical :
      0 ≤ 1 / (squarefreeZ R *
        (primeProduct (underlyingValues S) : ℝ)) := by
    rw [← subtypeBernoulliWeight_reciprocal_underlying hR S]
    exact hμpos.le
  rw [show
      1 / (squarefreeZ R *
          (primeProduct (underlyingValues S) : ℝ)) *
            rootedBayesDensity
              (fiveEventMass R reciprocalBernoulli B)
              (fiveRootLikelihood R reciprocalBernoulli B s) S -
          1 / (squarefreeZ R *
            (primeProduct (underlyingValues S) : ℝ)) =
        1 / (squarefreeZ R *
          (primeProduct (underlyingValues S) : ℝ)) *
            (rootedBayesDensity
              (fiveEventMass R reciprocalBernoulli B)
              (fiveRootLikelihood R reciprocalBernoulli B s) S - 1) by
        ring]
  rw [abs_mul, abs_of_nonneg hcanonical]

end Erdos536
