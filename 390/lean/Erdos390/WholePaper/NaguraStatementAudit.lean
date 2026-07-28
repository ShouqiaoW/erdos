import Erdos390.WholePaper.Nagura

/-!
# Expanded statement audit for the verified Nagura ranges

The asymptotic theorem has an existential cutoff.  This audit deliberately
does not rewrite it as the stronger, still-unproved statement for every
`n ≥ 25`.
-/

open Filter Topology

namespace Erdos390.WholePaper.NaguraStatementAudit

example :
    ∀ᶠ n : ℕ in atTop,
      0 < Nat.primeCounting ⌊((6 : ℝ) / 5) * (n : ℝ)⌋₊ -
        Nat.primeCounting n := by
  exact eventually_primeCounting_six_fifths_difference_pos

example :
    ∀ᶠ n : ℕ in atTop,
      ∃ p : ℕ, p.Prime ∧ n < p ∧ 5 * p < 6 * n := by
  simpa only [HasNaguraPrime] using eventually_exists_prime_nagura

example :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ p : ℕ, p.Prime ∧ n < p ∧ 5 * p < 6 * n := by
  simpa only [HasNaguraPrime] using exists_nagura_tail_cutoff

example {n : ℕ} (hnLower : 25 ≤ n) (hnUpper : n < 91639) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ 5 * p < 6 * n := by
  simpa only [HasNaguraPrime] using
    exists_prime_nagura_below_91639 hnLower hnUpper

end Erdos390.WholePaper.NaguraStatementAudit
