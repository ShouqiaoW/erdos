import Erdos390.WholePaper.CentralAnchorExistence

/-!
# Valuation cost of finite central-cofactor modifications

Later bank guards change the routed cofactor at a finite, explicit set of
central marker primes.  This file records the exact valuation cost of that
operation.  It does not assume that a modification is available: both
cofactor choices, the changed marker set, and equality off that set are
literal inputs.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- A positive integer at most `B` has no more than `log_ℓ B` copies of a
prime `ℓ` in its factorization. -/
theorem factorization_le_log_of_pos_le
    {a B ℓ : ℕ} (ha : 0 < a) (haB : a ≤ B) (hℓ : ℓ.Prime) :
    a.factorization ℓ ≤ Nat.log ℓ B := by
  have hpowDvd : ℓ ^ (a.factorization ℓ) ∣ a :=
    (hℓ.pow_dvd_iff_le_factorization ha.ne').mpr le_rfl
  have hpowLe : ℓ ^ (a.factorization ℓ) ≤ a :=
    Nat.le_of_dvd ha hpowDvd
  exact (Nat.le_log_of_pow_le hℓ.one_lt hpowLe).trans
    (Nat.log_mono_right haB)

/-- Changing routed cofactors at the explicit marker set `changed` costs at
most `changed.card * log₂ B` at every prime.  The promotion power of two is
unchanged and therefore cancels from the comparison. -/
theorem centralAnchorDivisor_factorization_le_add_changed_cost
    {n X B ℓ : ℕ} {q q' : ℕ → ℕ} {changed : Finset ℕ}
    (hℓ : ℓ.Prime)
    (hq : IsLargeCentralCofactorChoice n X q)
    (hq' : IsLargeCentralCofactorChoice n X q')
    (hchanged : changed ⊆ largeCentralPrimes n X)
    (hsame : ∀ p ∈ largeCentralPrimes n X,
      p ∉ changed → q' p = q p)
    (hq'Bound : ∀ p ∈ largeCentralPrimes n X, q' p ≤ B) :
    (centralAnchorDivisor n X q').factorization ℓ ≤
      (centralAnchorDivisor n X q).factorization ℓ +
        changed.card * Nat.log 2 B := by
  classical
  let large := largeCentralPrimes n X
  have hpoint : ∀ p ∈ large,
      (q' p).factorization ℓ ≤
        (q p).factorization ℓ +
          if p ∈ changed then Nat.log 2 B else 0 := by
    intro p hp
    by_cases hpChanged : p ∈ changed
    · have hfactorization :
          (q' p).factorization ℓ ≤ Nat.log ℓ B :=
        factorization_le_log_of_pos_le
          (largeCentralCofactor_pos hq' hp) (hq'Bound p hp) hℓ
      have hlog : Nat.log ℓ B ≤ Nat.log 2 B :=
        Nat.log_anti_left Nat.one_lt_two hℓ.two_le
      simp only [hpChanged, if_pos]
      omega
    · rw [if_neg hpChanged, hsame p hp hpChanged]
      omega
  have hfilter : large.filter (fun p ↦ p ∈ changed) = changed := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact fun hp ↦ hp.2
    · intro hp
      exact ⟨hchanged hp, hp⟩
  have hindicator :
      ∑ p ∈ large, (if p ∈ changed then Nat.log 2 B else 0) =
        changed.card * Nat.log 2 B := by
    rw [← Finset.sum_filter, hfilter]
    simp
  have hsum :
      ∑ p ∈ large, (q' p).factorization ℓ ≤
        (∑ p ∈ large, (q p).factorization ℓ) +
          changed.card * Nat.log 2 B := by
    calc
      ∑ p ∈ large, (q' p).factorization ℓ ≤
          ∑ p ∈ large,
            ((q p).factorization ℓ +
              if p ∈ changed then Nat.log 2 B else 0) := by
        exact Finset.sum_le_sum fun p hp ↦ hpoint p hp
      _ = (∑ p ∈ large, (q p).factorization ℓ) +
          ∑ p ∈ large,
            (if p ∈ changed then Nat.log 2 B else 0) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ p ∈ large, (q p).factorization ℓ) +
          changed.card * Nat.log 2 B := by rw [hindicator]
  rw [centralAnchorDivisor_factorization hq',
    centralAnchorDivisor_factorization hq]
  simpa only [large, Nat.add_assoc] using Nat.add_le_add_left hsum _

/-- Additive reserve survives a finite modification after subtracting the
explicit modification budget. -/
theorem centralAnchorReserve_transfer_after_changed_cost
    {n X B ℓ : ℕ} {q q' : ℕ → ℕ} {changed : Finset ℕ}
    {reserve loss tail : ℝ}
    (hℓ : ℓ.Prime)
    (hq : IsLargeCentralCofactorChoice n X q)
    (hq' : IsLargeCentralCofactorChoice n X q')
    (hchanged : changed ⊆ largeCentralPrimes n X)
    (hsame : ∀ p ∈ largeCentralPrimes n X,
      p ∉ changed → q' p = q p)
    (hq'Bound : ∀ p ∈ largeCentralPrimes n X, q' p ≤ B)
    (hcost : ((changed.card * Nat.log 2 B : ℕ) : ℝ) ≤ loss)
    (hreserve : reserve +
        ((centralAnchorDivisor n X q).factorization ℓ : ℝ) ≤ tail) :
    reserve - loss +
        ((centralAnchorDivisor n X q').factorization ℓ : ℝ) ≤ tail := by
  have hvaluationNat :=
    centralAnchorDivisor_factorization_le_add_changed_cost hℓ hq hq'
      hchanged hsame hq'Bound
  have hvaluation :
      ((centralAnchorDivisor n X q').factorization ℓ : ℝ) ≤
        ((centralAnchorDivisor n X q).factorization ℓ : ℝ) +
          ((changed.card * Nat.log 2 B : ℕ) : ℝ) := by
    exact_mod_cast hvaluationNat
  linarith

end

end Erdos390.WholePaper
