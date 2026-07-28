import Erdos390.WholePaper.CentralAnchorGuardedChoice

namespace Erdos390.WholePaper

example (n : ℕ) (q left right : ℕ → ℕ) (changed : Finset ℕ) (p : ℕ) :
    guardedCentralCofactor n q left right changed p =
      if p ∈ changed then
        if n / p = 1 then 3
        else prefixReplacementCofactor (n / p) (left p) (right p)
      else q p :=
  rfl

example
    {n p : ℕ} {q left right : ℕ → ℕ} {changed : Finset ℕ}
    (hp : p ∉ changed) :
    guardedCentralCofactor n q left right changed p = q p :=
  guardedCentralCofactor_eq_of_not_mem hp

example
    {n p : ℕ} {q left right : ℕ → ℕ} {changed : Finset ℕ}
    (hp : p ∈ changed) (hrow : n / p = 1) :
    guardedCentralCofactor n q left right changed p = 3 :=
  guardedCentralCofactor_eq_three_of_mem_row_one hp hrow

example
    {R n : ℕ} {q left right : ℕ → ℕ} {changed : Finset ℕ}
    (hq : ∀ p ∈ largeCentralPrimes n (n / (R + 1)),
      (n < p ∧ p ≤ 2 * n ∧ q p = 1) ∨
        ∃ r : ℕ, 1 ≤ r ∧ r = n / p ∧
          p ∈ stationaryPrimeLayer n r ∧
          r + 1 ≤ q p ∧ q p ≤ 2 * r + 1)
    (hchanged : changed ⊆ largeCentralPrimes n (n / (R + 1)))
    (hchangedLe : ∀ p ∈ changed, p ≤ n) :
    ∀ p ∈ largeCentralPrimes n (n / (R + 1)),
      (n < p ∧ p ≤ 2 * n ∧
          guardedCentralCofactor n q left right changed p = 1) ∨
        ∃ r : ℕ, 1 ≤ r ∧ r = n / p ∧
          p ∈ stationaryPrimeLayer n r ∧
          r + 1 ≤ guardedCentralCofactor n q left right changed p ∧
          guardedCentralCofactor n q left right changed p ≤ 2 * r + 1 := by
  simpa only [centralAnchorCutoff, IsLargeCentralCofactorChoice,
    IsRoutedCentralCofactor] using
      guardedCentralCofactor_isChoice hq hchanged hchangedLe

example
    {R n : ℕ} {q left right : ℕ → ℕ} {changed : Finset ℕ}
    (hq : IsLargeCentralCofactorChoice n (n / (R + 1)) q)
    (hchangedLe : ∀ p ∈ changed, p ≤ n)
    (hrowOneAvoid : ∀ p ∈ changed, n / p = 1 →
      3 ≠ left p ∧ 3 ≠ right p)
    {p : ℕ} (hpLarge : p ∈ largeCentralPrimes n (n / (R + 1)))
    (hpChanged : p ∈ changed) :
    guardedCentralCofactor n q left right changed p ≠ left p ∧
      guardedCentralCofactor n q left right changed p ≠ right p := by
  simpa only [centralAnchorCutoff] using
    guardedCentralCofactor_ne_incidentCores hq hchangedLe hrowOneAvoid
      hpLarge hpChanged

example
    {R n ℓ : ℕ} {q left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (hℓ : ℓ.Prime)
    (hq : IsLargeCentralCofactorChoice n (n / (R + 1)) q)
    (hchanged : changed ⊆ largeCentralPrimes n (n / (R + 1)))
    (hchangedLe : ∀ p ∈ changed, p ≤ n) :
    (((2 ^ residualPromotionCost n (n / (R + 1))) *
          ∏ p ∈ largeCentralPrimes n (n / (R + 1)),
            guardedCentralCofactor n q left right changed p).factorization ℓ) ≤
      ((2 ^ residualPromotionCost n (n / (R + 1))) *
          ∏ p ∈ largeCentralPrimes n (n / (R + 1)), q p).factorization ℓ +
        changed.card * Nat.log 2 (2 * R + 1) := by
  simpa only [centralAnchorCutoff, centralAnchorDivisor,
    largeCentralCofactorProduct] using
      guardedCentralAnchorDivisor_factorization_le_add_changed_cost
        hℓ hq hchanged hchangedLe

example
    {R n : ℕ} {q left right : ℕ → ℕ} {changed : Finset ℕ} :
    ∀ p ∈ largeCentralPrimes n (centralAnchorCutoff R n),
      p ∉ changed →
        guardedCentralCofactor n q left right changed p = q p :=
  guardedCentralCofactor_eq_off_changed

example
    {R n : ℕ} {q left right : ℕ → ℕ} {changed : Finset ℕ}
    (hq : IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q)
    (hchanged : changed ⊆
      largeCentralPrimes n (centralAnchorCutoff R n))
    (hchangedLe : ∀ p ∈ changed, p ≤ n) :
    ∀ p ∈ largeCentralPrimes n (centralAnchorCutoff R n),
      guardedCentralCofactor n q left right changed p ≤ 2 * R + 1 :=
  guardedCentralCofactor_le_fixedPrefix hq hchanged hchangedLe

end Erdos390.WholePaper
