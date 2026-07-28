import Erdos390.WholePaper.PrimeLayers

/-!
# Finite factorization incidence lemmas

These lemmas turn a prime valuation equal to one into the unique selected
factor carrying that prime.  They are purely finite and contain no analytic
input.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

theorem exists_unique_eq_one_of_sum_eq_one
    {α : Type*} [DecidableEq α] {s : Finset α} {g : α → ℕ}
    (hsum : ∑ a ∈ s, g a = 1) :
    ∃ a ∈ s, g a = 1 ∧
      ∀ b ∈ s, b ≠ a → g b = 0 := by
  induction s using Finset.induction_on with
  | empty => simp at hsum
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha] at hsum
      by_cases hga : g a = 0
      · have hs : ∑ b ∈ s, g b = 1 := by omega
        obtain ⟨b, hb, hgb, hrest⟩ := ih hs
        refine ⟨b, Finset.mem_insert_of_mem hb, hgb, ?_⟩
        intro c hc hcb
        rcases Finset.mem_insert.mp hc with hca | hcs
        · simpa [hca] using hga
        · exact hrest c hcs hcb
      · have hgaOne : g a = 1 := by omega
        have hsZero : ∑ b ∈ s, g b = 0 := by omega
        have hzero : ∀ b ∈ s, g b = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Nat.zero_le _).mp hsZero
        refine ⟨a, Finset.mem_insert_self a s, hgaOne, ?_⟩
        intro b hb hba
        rcases Finset.mem_insert.mp hb with hab | hbs
        · exact (hba hab).elim
        · exact hzero b hbs

/-- If a product has `p`-valuation one, exactly one of its nonzero factors is
divisible by `p`. -/
theorem existsUnique_dvd_of_prod_factorization_eq_one
    {p : ℕ} (hp : p.Prime) {s : Finset ℕ}
    (hsPos : ∀ a ∈ s, 0 < a)
    (hvaluation : (s.prod id).factorization p = 1) :
    ∃! a, a ∈ s ∧ p ∣ a := by
  have hsum : ∑ a ∈ s, a.factorization p = 1 := by
    rw [← Nat.factorization_prod_apply (fun a ha => (hsPos a ha).ne')]
    exact hvaluation
  obtain ⟨a, ha, hva, hrest⟩ :=
    exists_unique_eq_one_of_sum_eq_one hsum
  refine ⟨a, ⟨ha, (hp.dvd_iff_one_le_factorization (hsPos a ha).ne').mpr ?_⟩, ?_⟩
  · omega
  · intro b hb
    by_cases hba : b = a
    · exact hba
    · have hbZero : b.factorization p = 0 := hrest b hb.1 hba
      have hbOne : 1 ≤ b.factorization p :=
        (hp.dvd_iff_one_le_factorization (hsPos b hb.1).ne').mp hb.2
      omega

/-- The unique carrier has the paper's cofactor form `p*q`. -/
theorem existsUnique_eq_prime_mul_of_prod_factorization_eq_one
    {p : ℕ} (hp : p.Prime) {s : Finset ℕ}
    (hsPos : ∀ a ∈ s, 0 < a)
    (hvaluation : (s.prod id).factorization p = 1) :
    ∃! aq : ℕ × ℕ, aq.1 ∈ s ∧ aq.1 = p * aq.2 := by
  obtain ⟨a, ha, hunique⟩ :=
    existsUnique_dvd_of_prod_factorization_eq_one hp hsPos hvaluation
  obtain ⟨q, hq⟩ := ha.2
  refine ⟨(a, q), ⟨ha.1, hq⟩, ?_⟩
  intro bq hbq
  have hdiv : p ∣ bq.1 := ⟨bq.2, hbq.2⟩
  have hfirst : bq.1 = a := hunique bq.1 ⟨hbq.1, hdiv⟩
  apply Prod.ext
  · exact hfirst
  · apply Nat.eq_of_mul_eq_mul_left hp.pos
    calc
      p * bq.2 = bq.1 := hbq.2.symm
      _ = a := hfirst
      _ = p * q := hq

end Erdos390.WholePaper
