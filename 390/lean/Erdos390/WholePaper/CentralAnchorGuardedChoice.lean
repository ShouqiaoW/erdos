import Erdos390.WholePaper.BankAnchorGuardsFinite
import Erdos390.WholePaper.CentralAnchorModificationAlgebra

/-!
# A concrete guarded modification of routed central cofactors

For a finite set of bank markers, row one uses the literal replacement
cofactor `3`.  Every higher positive carry row uses the first of
`r+1,r+2,r+3` which avoids the two incident bank-state cores.  This file is
pure finite arithmetic: it proves that the modified function is still an
actual routed central-cofactor choice and records the exact hypotheses under
which both incident cores are avoided.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- Modify `q` exactly on `changed`.  Row one has only the legal cofactors
`2,3`, so the bank construction separately guarantees that `3` is not an
incident state core.  Higher rows have the three-candidate replacement from
`BankAnchorGuardsFinite`. -/
def guardedCentralCofactor (n : ℕ) (q left right : ℕ → ℕ)
    (changed : Finset ℕ) (p : ℕ) : ℕ :=
  if p ∈ changed then
    if n / p = 1 then 3
    else prefixReplacementCofactor (n / p) (left p) (right p)
  else q p

@[simp]
theorem guardedCentralCofactor_eq_of_not_mem
    {n : ℕ} {q left right : ℕ → ℕ} {changed : Finset ℕ}
    {p : ℕ} (hp : p ∉ changed) :
    guardedCentralCofactor n q left right changed p = q p := by
  simp [guardedCentralCofactor, hp]

@[simp]
theorem guardedCentralCofactor_eq_three_of_mem_row_one
    {n : ℕ} {q left right : ℕ → ℕ} {changed : Finset ℕ}
    {p : ℕ} (hp : p ∈ changed) (hrow : n / p = 1) :
    guardedCentralCofactor n q left right changed p = 3 := by
  simp [guardedCentralCofactor, hp, hrow]

/-- Replacing every changed marker by the displayed row-legal cofactor
preserves the simultaneous routed-choice predicate.  The assumption
`p ≤ n` rules out the row-zero branch for a changed bank marker. -/
theorem guardedCentralCofactor_isChoice
    {R n : ℕ} {q left right : ℕ → ℕ} {changed : Finset ℕ}
    (hq : IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q)
    (hchanged : changed ⊆
      largeCentralPrimes n (centralAnchorCutoff R n))
    (hchangedLe : ∀ p ∈ changed, p ≤ n) :
    IsLargeCentralCofactorChoice n (centralAnchorCutoff R n)
      (guardedCentralCofactor n q left right changed) := by
  intro p hpLarge
  by_cases hpChanged : p ∈ changed
  · have hpLe : p ≤ n := hchangedLe p hpChanged
    have hpChangedLarge := hchanged hpChanged
    rcases hq p hpChangedLarge with hzero |
        ⟨r, hrPos, hrEq, hpRow, _hqLower, _hqUpper⟩
    · exact (not_lt_of_ge hpLe hzero.1).elim
    · subst r
      right
      refine ⟨n / p, hrPos, rfl, hpRow, ?_, ?_⟩
      by_cases hrowOne : n / p = 1
      · simp [guardedCentralCofactor, hpChanged, hrowOne]
      · have hrowTwo : 2 ≤ n / p := by omega
        simp only [guardedCentralCofactor, if_pos hpChanged,
          if_neg hrowOne]
        exact (prefixReplacementCofactor_spec hrowTwo).1
      by_cases hrowOne : n / p = 1
      · simp [guardedCentralCofactor, hpChanged, hrowOne]
      · have hrowTwo : 2 ≤ n / p := by omega
        simp only [guardedCentralCofactor, if_pos hpChanged,
          if_neg hrowOne]
        exact (prefixReplacementCofactor_spec hrowTwo).2.1
  · simpa only [guardedCentralCofactor_eq_of_not_mem hpChanged] using
      hq p hpLarge

/-- At a changed marker the guarded cofactor differs from both incident
state cores.  Row one's extra hypothesis is exactly what the literal bottom
path and the ordinary path supply; all higher rows are automatic. -/
theorem guardedCentralCofactor_ne_incidentCores
    {R n : ℕ} {q left right : ℕ → ℕ} {changed : Finset ℕ}
    (hq : IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q)
    (hchangedLe : ∀ p ∈ changed, p ≤ n)
    (hrowOneAvoid : ∀ p ∈ changed, n / p = 1 →
      3 ≠ left p ∧ 3 ≠ right p)
    {p : ℕ} (hpLarge :
      p ∈ largeCentralPrimes n (centralAnchorCutoff R n))
    (hpChanged : p ∈ changed) :
    guardedCentralCofactor n q left right changed p ≠ left p ∧
      guardedCentralCofactor n q left right changed p ≠ right p := by
  have hpLe : p ≤ n := hchangedLe p hpChanged
  rcases hq p hpLarge with hzero |
      ⟨r, hrPos, hrEq, _hpRow, _hqLower, _hqUpper⟩
  · exact (not_lt_of_ge hpLe hzero.1).elim
  · subst r
    by_cases hrowOne : n / p = 1
    · simpa [guardedCentralCofactor, hpChanged, hrowOne] using
        hrowOneAvoid p hpChanged hrowOne
    · have hrowTwo : 2 ≤ n / p := by omega
      have hspec := prefixReplacementCofactor_spec
        (r := n / p) (left := left p) (right := right p) hrowTwo
      simpa only [guardedCentralCofactor, if_pos hpChanged,
        if_neg hrowOne] using hspec.2.2

/-- The guarded function agrees with the original choice off the literal
changed set, in the exact form consumed by the valuation-cost theorem. -/
theorem guardedCentralCofactor_eq_off_changed
    {R n : ℕ} {q left right : ℕ → ℕ} {changed : Finset ℕ} :
    ∀ p ∈ largeCentralPrimes n (centralAnchorCutoff R n),
      p ∉ changed →
        guardedCentralCofactor n q left right changed p = q p := by
  intro p _hp hpChanged
  exact guardedCentralCofactor_eq_of_not_mem hpChanged

/-- Every guarded cofactor remains in the same fixed prefix bound. -/
theorem guardedCentralCofactor_le_fixedPrefix
    {R n : ℕ} {q left right : ℕ → ℕ} {changed : Finset ℕ}
    (hq : IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q)
    (hchanged : changed ⊆
      largeCentralPrimes n (centralAnchorCutoff R n))
    (hchangedLe : ∀ p ∈ changed, p ≤ n) :
    ∀ p ∈ largeCentralPrimes n (centralAnchorCutoff R n),
      guardedCentralCofactor n q left right changed p ≤ 2 * R + 1 := by
  have hchoice := guardedCentralCofactor_isChoice
    (left := left) (right := right) hq hchanged hchangedLe
  intro p hp
  exact largeCentralCofactor_le_fixedPrefix hchoice hp

/-- Direct specialization of the finite modification estimate to the
concrete guarded function. -/
theorem guardedCentralAnchorDivisor_factorization_le_add_changed_cost
    {R n ℓ : ℕ} {q left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (hℓ : ℓ.Prime)
    (hq : IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q)
    (hchanged : changed ⊆
      largeCentralPrimes n (centralAnchorCutoff R n))
    (hchangedLe : ∀ p ∈ changed, p ≤ n) :
    (centralAnchorDivisor n (centralAnchorCutoff R n)
        (guardedCentralCofactor n q left right changed)).factorization ℓ ≤
      (centralAnchorDivisor n (centralAnchorCutoff R n) q).factorization ℓ +
        changed.card * Nat.log 2 (2 * R + 1) := by
  have hchoice := guardedCentralCofactor_isChoice
    (left := left) (right := right) hq hchanged hchangedLe
  exact centralAnchorDivisor_factorization_le_add_changed_cost
    hℓ hq hchoice hchanged
      (guardedCentralCofactor_eq_off_changed
        (q := q) (left := left) (right := right) (changed := changed))
      (guardedCentralCofactor_le_fixedPrefix
        (left := left) (right := right) hq hchanged hchangedLe)

end

end Erdos390.WholePaper
