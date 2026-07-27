import Erdos536.FiveStateCoupling
import Erdos536.SquarefreeCapacity

/-!
# Bernoulli and reciprocal squarefree laws

The local choice `r p = 1 / (p + 1)` is exactly the normalized reciprocal
law on squarefree supports: a support `S ⊆ R` has mass

`1 / (squarefreeZ R * primeProduct S)`.

This file also records the elementary passage between finsets of the subtype
`R` and finsets of natural numbers.
-/

open scoped BigOperators
open Finset

namespace Erdos536

/-- Forget the membership proofs in a finite support on the subtype `R`. -/
def subtypeSupportVal {R : Finset ℕ} (S : Finset ↥R) : Finset ℕ :=
  S.map ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
theorem mem_subtypeSupportVal {R : Finset ℕ} {S : Finset ↥R} {p : ℕ} :
    p ∈ subtypeSupportVal S ↔ ∃ hp : p ∈ R, (⟨p, hp⟩ : ↥R) ∈ S := by
  simp [subtypeSupportVal]

theorem subtypeSupportVal_subset {R : Finset ℕ} (S : Finset ↥R) :
    subtypeSupportVal S ⊆ R := by
  intro p hp
  obtain ⟨hpR, _⟩ := mem_subtypeSupportVal.mp hp
  exact hpR

@[simp]
theorem card_subtypeSupportVal {R : Finset ℕ} (S : Finset ↥R) :
    (subtypeSupportVal S).card = S.card := by
  exact Finset.card_map _

theorem prod_subtype_eq_prod_val {R : Finset ℕ} (S : Finset ↥R)
    (f : ℕ → ℝ) :
    (∏ p ∈ S, f p.1) = ∏ p ∈ subtypeSupportVal S, f p := by
  rw [subtypeSupportVal, Finset.prod_map]
  rfl

theorem prod_subtype_complement_eq_sdiff {R : Finset ℕ}
    (S : Finset ↥R) (f : ℕ → ℝ) :
    (∏ p ∈ (Finset.univ \ S), f p.1) =
      ∏ p ∈ (R \ subtypeSupportVal S), f p := by
  classical
  rw [prod_subtype_eq_prod_val (Finset.univ \ S) f]
  congr 1
  ext p
  by_cases hp : p ∈ R <;> simp [subtypeSupportVal, hp]

/-- The Bernoulli parameter whose odds are `1 / p`. -/
noncomputable def reciprocalBernoulli (p : ℕ) : ℝ :=
  1 / ((p : ℝ) + 1)

theorem one_sub_reciprocalBernoulli {p : ℕ} (hp : 0 < p) :
    1 - reciprocalBernoulli p = (p : ℝ) / ((p : ℝ) + 1) := by
  rw [reciprocalBernoulli]
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem reciprocalBernoulli_nonneg (p : ℕ) :
    0 ≤ reciprocalBernoulli p := by
  unfold reciprocalBernoulli
  positivity

theorem reciprocalBernoulli_le_three_quarters {p : ℕ} (hp : 1 ≤ p) :
    reciprocalBernoulli p ≤ (3 : ℝ) / 4 := by
  unfold reciprocalBernoulli
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  apply (div_le_iff₀ hden).2
  linarith

private theorem reciprocalBernoulli_weight_factorization
    {R : Finset ℕ} (hR : IsPrimeSupport R) (S : Finset ↥R) :
    subtypeBernoulliWeight R reciprocalBernoulli S =
      (∏ p ∈ R, (p : ℝ) / ((p : ℝ) + 1)) *
        ∏ p ∈ subtypeSupportVal S, (p : ℝ)⁻¹ := by
  classical
  rw [subtypeBernoulliWeight, prod_subtype_eq_prod_val,
    prod_subtype_complement_eq_sdiff S
      (fun p => 1 - reciprocalBernoulli p)]
  have hpos : ∀ p ∈ R, 0 < p := fun p hp => (hR p hp).pos
  have hcomplement :
      (∏ p ∈ R \ subtypeSupportVal S,
          (1 - reciprocalBernoulli p)) =
        ∏ p ∈ R \ subtypeSupportVal S,
          (p : ℝ) / ((p : ℝ) + 1) := by
    apply Finset.prod_congr rfl
    intro p hp
    exact one_sub_reciprocalBernoulli
      (hpos p (Finset.mem_sdiff.mp hp).1)
  rw [hcomplement]
  have hselected :
      (∏ p ∈ subtypeSupportVal S, reciprocalBernoulli p) =
        (∏ p ∈ subtypeSupportVal S,
            (p : ℝ) / ((p : ℝ) + 1)) *
          ∏ p ∈ subtypeSupportVal S, (p : ℝ)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hpR := subtypeSupportVal_subset S hp
    have hp0 : (p : ℝ) ≠ 0 := by
      exact_mod_cast (hpos p hpR).ne'
    rw [reciprocalBernoulli]
    field_simp
  rw [hselected]
  have hbase :=
    Finset.prod_sdiff (f := fun p : ℕ =>
      (p : ℝ) / ((p : ℝ) + 1)) (subtypeSupportVal_subset S)
  calc
    (∏ p ∈ subtypeSupportVal S, (p : ℝ) / ((p : ℝ) + 1)) *
          (∏ p ∈ subtypeSupportVal S, (p : ℝ)⁻¹) *
        ∏ p ∈ R \ subtypeSupportVal S,
          (p : ℝ) / ((p : ℝ) + 1) =
        ((∏ p ∈ R \ subtypeSupportVal S,
            (p : ℝ) / ((p : ℝ) + 1)) *
          ∏ p ∈ subtypeSupportVal S,
            (p : ℝ) / ((p : ℝ) + 1)) *
          ∏ p ∈ subtypeSupportVal S, (p : ℝ)⁻¹ := by ring
    _ = (∏ p ∈ R, (p : ℝ) / ((p : ℝ) + 1)) *
          ∏ p ∈ subtypeSupportVal S, (p : ℝ)⁻¹ := by rw [hbase]

theorem subtypeBernoulliWeight_reciprocal
    {R : Finset ℕ} (hR : IsPrimeSupport R) (S : Finset ↥R) :
    subtypeBernoulliWeight R reciprocalBernoulli S =
      1 / (squarefreeZ R * (primeProduct (subtypeSupportVal S) : ℝ)) := by
  classical
  rw [reciprocalBernoulli_weight_factorization hR]
  rw [squarefreeZ_eq_prod]
  have hRpos : ∀ p ∈ R, (0 : ℝ) < p := by
    intro p hp
    exact_mod_cast (hR p hp).pos
  have hprodS :
      (primeProduct (subtypeSupportVal S) : ℝ) =
        ∏ p ∈ subtypeSupportVal S, (p : ℝ) := by
    simp [primeProduct]
  rw [hprodS]
  have hfactor :
      ∀ p ∈ R, (1 : ℝ) + (p : ℝ)⁻¹ = (p + 1) / p := by
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := (hRpos p hp).ne'
    field_simp
  have hZprod :
      (∏ p ∈ R, ((1 : ℝ) + (p : ℝ)⁻¹)) =
        ∏ p ∈ R, ((p : ℝ) + 1) / p := by
    apply Finset.prod_congr rfl
    intro p hp
    exact hfactor p hp
  rw [hZprod]
  simp only [Finset.prod_div_distrib, Finset.prod_inv_distrib, one_div,
    mul_inv, inv_div]

end Erdos536
