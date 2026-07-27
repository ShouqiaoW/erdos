import Erdos536.Definitions
import Mathlib.Data.Nat.Squarefree
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Squarefree support families

For a finite set of primes, multiplication identifies set union with least
common multiple.  This is the exact bridge used in the manuscript's
squarefree reduction.
-/

open scoped BigOperators
open Finset Nat

namespace Erdos536

/-- The squarefree integer represented by a finite prime support. -/
def primeProduct (S : Finset ℕ) : ℕ :=
  ∏ p ∈ S, p

/-- Every member of a finite support is prime. -/
def IsPrimeSupport (S : Finset ℕ) : Prop :=
  ∀ p ∈ S, Nat.Prime p

theorem isPrimeSupport_mono {S T : Finset ℕ} (hT : IsPrimeSupport T)
    (hST : S ⊆ T) : IsPrimeSupport S :=
  fun p hp => hT p (hST hp)

theorem primeProduct_pos {S : Finset ℕ} (hS : IsPrimeSupport S) :
    0 < primeProduct S := by
  apply Finset.prod_pos
  intro p hp
  exact (hS p hp).pos

theorem primeProduct_ne_zero {S : Finset ℕ} (hS : IsPrimeSupport S) :
    primeProduct S ≠ 0 :=
  (primeProduct_pos hS).ne'

theorem primeFactors_primeProduct {S : Finset ℕ} (hS : IsPrimeSupport S) :
    (primeProduct S).primeFactors = S := by
  exact Nat.primeFactors_prod hS

theorem primeProduct_injective_on_primeSupports
    {S T : Finset ℕ} (hS : IsPrimeSupport S) (hT : IsPrimeSupport T)
    (hprod : primeProduct S = primeProduct T) : S = T := by
  calc
    S = (primeProduct S).primeFactors := (primeFactors_primeProduct hS).symm
    _ = (primeProduct T).primeFactors := by rw [hprod]
    _ = T := primeFactors_primeProduct hT

/-- For squarefree products of primes, set union is exactly LCM. -/
theorem lcm_primeProduct (S T : Finset ℕ)
    (hS : IsPrimeSupport S) (hT : IsPrimeSupport T) :
    Nat.lcm (primeProduct S) (primeProduct T) = primeProduct (S ∪ T) := by
  apply Nat.dvd_antisymm
  · apply Nat.lcm_dvd
    · exact Finset.prod_dvd_prod_of_subset S (S ∪ T) (fun p => p) subset_union_left
    · exact Finset.prod_dvd_prod_of_subset T (S ∪ T) (fun p => p) subset_union_right
  · apply Finset.prod_dvd_of_isRelPrime
    · intro p hp q hq hpq
      have hpPrime : Nat.Prime p := by
        rcases mem_union.mp hp with hpS | hpT
        · exact hS p hpS
        · exact hT p hpT
      have hqPrime : Nat.Prime q := by
        rcases mem_union.mp hq with hqS | hqT
        · exact hS q hqS
        · exact hT q hqT
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes hpPrime hqPrime).mpr hpq)
    · intro p hp
      rcases mem_union.mp hp with hpS | hpT
      · exact (dvd_prod_of_mem (fun q => q) hpS).trans
          (Nat.dvd_lcm_left (primeProduct S) (primeProduct T))
      · exact (dvd_prod_of_mem (fun q => q) hpT).trans
          (Nat.dvd_lcm_right (primeProduct S) (primeProduct T))

/-- The forbidden set-system relation: all three pairwise unions agree. -/
def EqualPairwiseUnions (S₁ S₂ S₃ : Finset ℕ) : Prop :=
  S₁ ∪ S₂ = S₁ ∪ S₃ ∧ S₁ ∪ S₃ = S₂ ∪ S₃

/-- An admissible support family contains no three distinct members with
equal pairwise unions. -/
def Admissible (𝓕 : Finset (Finset ℕ)) : Prop :=
  ∀ ⦃S₁ S₂ S₃ : Finset ℕ⦄,
    S₁ ∈ 𝓕 → S₂ ∈ 𝓕 → S₃ ∈ 𝓕 →
      ({S₁, S₂, S₃} : Finset (Finset ℕ)).card = 3 →
        ¬EqualPairwiseUnions S₁ S₂ S₃

theorem equalPairwiseUnions_lcm
    {S₁ S₂ S₃ : Finset ℕ}
    (h₁ : IsPrimeSupport S₁) (h₂ : IsPrimeSupport S₂)
    (h₃ : IsPrimeSupport S₃) (hU : EqualPairwiseUnions S₁ S₂ S₃) :
    Nat.lcm (primeProduct S₁) (primeProduct S₂) =
        Nat.lcm (primeProduct S₂) (primeProduct S₃) ∧
      Nat.lcm (primeProduct S₂) (primeProduct S₃) =
        Nat.lcm (primeProduct S₁) (primeProduct S₃) := by
  rcases hU with ⟨h12_13, h13_23⟩
  constructor
  · rw [lcm_primeProduct S₁ S₂ h₁ h₂, lcm_primeProduct S₂ S₃ h₂ h₃,
      h12_13, h13_23]
  · rw [lcm_primeProduct S₂ S₃ h₂ h₃, lcm_primeProduct S₁ S₃ h₁ h₃,
      ← h13_23]

theorem lcm_equalPairwiseUnions
    {S₁ S₂ S₃ : Finset ℕ}
    (h₁ : IsPrimeSupport S₁) (h₂ : IsPrimeSupport S₂)
    (h₃ : IsPrimeSupport S₃)
    (hL :
      Nat.lcm (primeProduct S₁) (primeProduct S₂) =
          Nat.lcm (primeProduct S₂) (primeProduct S₃) ∧
        Nat.lcm (primeProduct S₂) (primeProduct S₃) =
          Nat.lcm (primeProduct S₁) (primeProduct S₃)) :
    EqualPairwiseUnions S₁ S₂ S₃ := by
  have hU12 : IsPrimeSupport (S₁ ∪ S₂) := by
    intro p hp
    rcases mem_union.mp hp with hp₁ | hp₂
    · exact h₁ p hp₁
    · exact h₂ p hp₂
  have hU23 : IsPrimeSupport (S₂ ∪ S₃) := by
    intro p hp
    rcases mem_union.mp hp with hp₂ | hp₃
    · exact h₂ p hp₂
    · exact h₃ p hp₃
  have hU13 : IsPrimeSupport (S₁ ∪ S₃) := by
    intro p hp
    rcases mem_union.mp hp with hp₁ | hp₃
    · exact h₁ p hp₁
    · exact h₃ p hp₃
  constructor
  · apply primeProduct_injective_on_primeSupports hU12 hU13
    rw [← lcm_primeProduct S₁ S₂ h₁ h₂, ← lcm_primeProduct S₁ S₃ h₁ h₃]
    exact hL.1.trans hL.2
  · apply primeProduct_injective_on_primeSupports hU13 hU23
    rw [← lcm_primeProduct S₁ S₃ h₁ h₃, ← lcm_primeProduct S₂ S₃ h₂ h₃]
    exact hL.2.symm

/-- Under multiplication of prime supports, admissible families are exactly
LCM-triangle-free families. -/
theorem admissible_iff_image_lcmTriangleFree
    (𝓕 : Finset (Finset ℕ))
    (hprime : ∀ S ∈ 𝓕, IsPrimeSupport S) :
    Admissible 𝓕 ↔ LcmTriangleFree (𝓕.image primeProduct) := by
  constructor
  · intro hadm a b c ha hb hc htriangle
    obtain ⟨S₁, hS₁, rfl⟩ := mem_image.mp ha
    obtain ⟨S₂, hS₂, rfl⟩ := mem_image.mp hb
    obtain ⟨S₃, hS₃, rfl⟩ := mem_image.mp hc
    have h₁ := hprime S₁ hS₁
    have h₂ := hprime S₂ hS₂
    have h₃ := hprime S₃ hS₃
    have htriplePrime :
        ∀ S ∈ ({S₁, S₂, S₃} : Finset (Finset ℕ)), IsPrimeSupport S := by
      intro S hS
      simp only [mem_insert, mem_singleton] at hS
      rcases hS with rfl | rfl | rfl
      · exact h₁
      · exact h₂
      · exact h₃
    have hinj :
        Set.InjOn primeProduct
          (↑({S₁, S₂, S₃} : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
      intro S hS T hT hEq
      exact primeProduct_injective_on_primeSupports
        (htriplePrime S hS) (htriplePrime T hT) hEq
    have hsupportCard :
        ({S₁, S₂, S₃} : Finset (Finset ℕ)).card = 3 := by
      have hcardImage := Finset.card_image_of_injOn hinj
      calc
        ({S₁, S₂, S₃} : Finset (Finset ℕ)).card =
            (({S₁, S₂, S₃} : Finset (Finset ℕ)).image primeProduct).card :=
          hcardImage.symm
        _ = ({primeProduct S₁, primeProduct S₂, primeProduct S₃} : Finset ℕ).card := by
          simp
        _ = 3 := htriangle.1
    apply (hadm hS₁ hS₂ hS₃ hsupportCard)
    exact lcm_equalPairwiseUnions h₁ h₂ h₃ ⟨htriangle.2.1, htriangle.2.2⟩
  · intro hfree S₁ S₂ S₃ hS₁ hS₂ hS₃ hcard hUnions
    have h₁ := hprime S₁ hS₁
    have h₂ := hprime S₂ hS₂
    have h₃ := hprime S₃ hS₃
    have htriplePrime :
        ∀ S ∈ ({S₁, S₂, S₃} : Finset (Finset ℕ)), IsPrimeSupport S := by
      intro S hS
      simp only [mem_insert, mem_singleton] at hS
      rcases hS with rfl | rfl | rfl
      · exact h₁
      · exact h₂
      · exact h₃
    have hinj :
        Set.InjOn primeProduct
          (↑({S₁, S₂, S₃} : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
      intro S hS T hT hEq
      exact primeProduct_injective_on_primeSupports
        (htriplePrime S hS) (htriplePrime T hT) hEq
    have hproductCard :
        ({primeProduct S₁, primeProduct S₂, primeProduct S₃} : Finset ℕ).card = 3 := by
      rw [show
          ({primeProduct S₁, primeProduct S₂, primeProduct S₃} : Finset ℕ) =
            ({S₁, S₂, S₃} : Finset (Finset ℕ)).image primeProduct by simp]
      rw [Finset.card_image_of_injOn hinj, hcard]
    have hL := equalPairwiseUnions_lcm h₁ h₂ h₃ hUnions
    exact (hfree (mem_image.mpr ⟨S₁, hS₁, rfl⟩)
      (mem_image.mpr ⟨S₂, hS₂, rfl⟩)
      (mem_image.mpr ⟨S₃, hS₃, rfl⟩))
      ⟨hproductCard, hL.1, hL.2⟩

end Erdos536
