import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# The finite divisor identity behind Nagura's Chebyshev sum

Nagura's fundamental summatory formula starts by expanding each logarithm as
a divisor sum of the von Mangoldt function.  This file records that exact
finite identity, including the factorial endpoint, independently of any
analytic estimate.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open scoped ArithmeticFunction ArithmeticFunction.zeta

/-- Nagura's finite sum `T(n) = ∑_{m=1}^n psi(n/m)`. -/
noncomputable def naguraChebyshevSum (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioc 0 n, Chebyshev.psi ((n / m : ℕ) : ℝ)

/-- Dirichlet-convolution form of Nagura's fundamental finite identity. -/
theorem naguraChebyshevSum_eq_sum_log (n : ℕ) :
    naguraChebyshevSum n =
      ∑ k ∈ Finset.Icc 1 n, Real.log k := by
  have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
    (R := ℝ)
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
    ArithmeticFunction.vonMangoldt n
  have hMain :
      (∑ m ∈ Finset.Ioc 0 n,
        ∑ d ∈ Finset.Ioc 0 (n / m),
          ArithmeticFunction.vonMangoldt d) =
        ∑ k ∈ Finset.Ioc 0 n, Real.log k := by
    calc
      _ = ∑ m ∈ Finset.Ioc 0 n,
          (if m = 0 then 0 else
            ∑ d ∈ Finset.Ioc 0 (n / m),
              ArithmeticFunction.vonMangoldt d) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hm0 : m ≠ 0 := by
          have := (Finset.mem_Ioc.mp hm).1
          omega
        simp [hm0]
      _ = _ := by
        simpa [ArithmeticFunction.log_apply] using h.symm
  have hIntervals : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIntervals]
  simpa [naguraChebyshevSum, Chebyshev.psi] using hMain

/-- The finite divisor sum occurring before Nagura reindexes by multiples. -/
noncomputable def naguraDivisorLogSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n,
    ∑ d ∈ k.divisors, ArithmeticFunction.vonMangoldt d

theorem naguraDivisorLogSum_eq_sum_log (n : ℕ) :
    naguraDivisorLogSum n = ∑ k ∈ Finset.Icc 1 n, Real.log k := by
  unfold naguraDivisorLogSum
  apply Finset.sum_congr rfl
  intro k _hk
  exact ArithmeticFunction.vonMangoldt_sum

/-- Exact factorial form of the finite divisor identity. -/
theorem naguraDivisorLogSum_eq_log_factorial (n : ℕ) :
    naguraDivisorLogSum n = Real.log (n.factorial : ℝ) := by
  rw [naguraDivisorLogSum_eq_sum_log]
  calc
    (∑ k ∈ Finset.Icc 1 n, Real.log k) =
        Real.log (∏ k ∈ Finset.Icc 1 n, (k : ℝ)) := by
      rw [Real.log_prod]
      intro k hk
      have hk0 : k ≠ 0 := by
        have := (Finset.mem_Icc.mp hk).1
        omega
      exact_mod_cast hk0
    _ = Real.log (n.factorial : ℝ) := by
      congr 1
      rw [← Nat.cast_prod]
      norm_cast
      rw [← Finset.Ico_add_one_right_eq_Icc,
        Finset.prod_Ico_id_eq_factorial]

/-- Exact natural-endpoint version of Nagura's fundamental formula. -/
theorem naguraChebyshevSum_eq_log_factorial (n : ℕ) :
    naguraChebyshevSum n = Real.log (n.factorial : ℝ) := by
  rw [naguraChebyshevSum_eq_sum_log]
  exact (naguraDivisorLogSum_eq_sum_log n).symm.trans
    (naguraDivisorLogSum_eq_log_factorial n)

end Erdos390.WholePaper
