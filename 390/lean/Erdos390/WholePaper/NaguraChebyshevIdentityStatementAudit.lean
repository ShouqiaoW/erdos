import Erdos390.WholePaper.NaguraChebyshevIdentity

/-! Expanded statement audit for Nagura's finite divisor identity. -/

open scoped BigOperators

namespace Erdos390.WholePaper.NaguraChebyshevIdentityStatementAudit

example (n : ℕ) :
    (∑ m ∈ Finset.Ioc 0 n,
      Chebyshev.psi ((n / m : ℕ) : ℝ)) =
        Real.log (n.factorial : ℝ) := by
  exact naguraChebyshevSum_eq_log_factorial n

example (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n,
      ∑ d ∈ k.divisors, ArithmeticFunction.vonMangoldt d) =
        Real.log (n.factorial : ℝ) := by
  exact naguraDivisorLogSum_eq_log_factorial n

end Erdos390.WholePaper.NaguraChebyshevIdentityStatementAudit
