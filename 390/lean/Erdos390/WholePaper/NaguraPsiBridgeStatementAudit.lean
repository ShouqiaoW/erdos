import Erdos390.WholePaper.NaguraPsiBridge

/-! Expanded statement audit for the effective Chebyshev bridge. -/

namespace Erdos390.WholePaper.NaguraPsiBridgeStatementAudit

example {a b : ℕ}
    (hTheta : Chebyshev.theta (a : ℝ) < Chebyshev.theta (b : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ a < p ∧ p ≤ b := by
  exact exists_prime_Ioc_of_theta_lt hTheta

example {n : ℕ} (hn : 25 ≤ n)
    (hPsiGap :
      Chebyshev.psi (n : ℝ) +
          2 * Real.sqrt (((6 * n - 1) / 5 : ℕ) : ℝ) *
            Real.log (((6 * n - 1) / 5 : ℕ) : ℝ) <
        Chebyshev.psi (((6 * n - 1) / 5 : ℕ) : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ 5 * p < 6 * n := by
  simpa only [HasNaguraPrime, naguraStrictUpper] using
    hasNaguraPrime_of_psi_gap hn hPsiGap

end Erdos390.WholePaper.NaguraPsiBridgeStatementAudit
