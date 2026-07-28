import Erdos390.WholePaper.FactorizationIncidence

/-!
# A finite small-prime incidence bound

This is the combinatorial summation used twice in the thirteen-layer lower
bound.  A collection of distinct selected factors, each divisible by at
least one prime in `small`, consumes at least one unit of the corresponding
prime-valuation capacity of the whole selected product.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

/-- A literal finite form of the incidence inequality. -/
theorem card_le_sum_prod_factorization
    {carriers selected small : Finset ℕ}
    (hsub : carriers ⊆ selected)
    (hselectedPos : ∀ a ∈ selected, 0 < a)
    (hdiv : ∀ a ∈ carriers,
      ∃ ell ∈ small, ell.Prime ∧ ell ∣ a) :
    carriers.card ≤
      ∑ ell ∈ small, (selected.prod id).factorization ell := by
  have hcarrierPos : ∀ a ∈ carriers, 0 < a :=
    fun a ha ↦ hselectedPos a (hsub ha)
  calc
    carriers.card = ∑ a ∈ carriers, 1 := by simp
    _ ≤ ∑ a ∈ carriers, ∑ ell ∈ small, a.factorization ell := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨ell, hell, hellPrime, hellDvd⟩ := hdiv a ha
      have haNe : a ≠ 0 := (hcarrierPos a ha).ne'
      have hone : 1 ≤ a.factorization ell :=
        (hellPrime.dvd_iff_one_le_factorization haNe).mp hellDvd
      exact hone.trans (Finset.single_le_sum
        (fun i _ ↦ Nat.zero_le (a.factorization i)) hell)
    _ ≤ ∑ a ∈ selected, ∑ ell ∈ small, a.factorization ell := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ ↦ Nat.zero_le _)
    _ = ∑ ell ∈ small, ∑ a ∈ selected, a.factorization ell := by
      rw [Finset.sum_comm]
    _ = ∑ ell ∈ small, (selected.prod id).factorization ell := by
      apply Finset.sum_congr rfl
      intro ell _
      exact (Nat.factorization_prod_apply
        (fun a ha ↦ (hselectedPos a ha).ne')).symm

/-- Function-indexed version: injectively chosen carrier factors immediately
give the same incidence bound. -/
theorem card_le_sum_prod_factorization_of_injective_carriers
    {large selected small : Finset ℕ} {carrier : ℕ → ℕ}
    (hcarrierMem : ∀ p ∈ large, carrier p ∈ selected)
    (hcarrierInj : Set.InjOn carrier (large : Set ℕ))
    (hselectedPos : ∀ a ∈ selected, 0 < a)
    (hdiv : ∀ p ∈ large,
      ∃ ell ∈ small, ell.Prime ∧ ell ∣ carrier p) :
    large.card ≤
      ∑ ell ∈ small, (selected.prod id).factorization ell := by
  let carriers := large.image carrier
  have hcard : carriers.card = large.card :=
    Finset.card_image_iff.mpr hcarrierInj
  have hsub : carriers ⊆ selected := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact hcarrierMem p hp
  have hcarrierDiv : ∀ a ∈ carriers,
      ∃ ell ∈ small, ell.Prime ∧ ell ∣ a := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact hdiv p hp
  rw [← hcard]
  exact card_le_sum_prod_factorization hsub hselectedPos hcarrierDiv

end Erdos390.WholePaper
