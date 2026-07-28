import Erdos390.WholePaper.NaguraExplicitPsiBounds

/-! Expanded statement audit for the explicit Nagura `ψ` chain. -/

namespace Erdos390.WholePaper.NaguraExplicitPsiBoundsStatementAudit

example {k : ℕ} (hk : 0 < k) :
    Chebyshev.psi ((1806 * k : ℕ) : ℝ) <
      (543 : ℝ) / 500 * ((1806 * k : ℕ) : ℝ) := by
  exact psi_mul_1806_lt_1_086 hk

example {k : ℕ} (hk : 150 ≤ k) :
    (229 : ℝ) / 250 * ((30 * k : ℕ) : ℝ) <
      Chebyshev.psi ((30 * k : ℕ) : ℝ) := by
  exact psi_mul_30_gt_0_916 hk

example {n : ℕ} (hn : 4500 ≤ n) :
    (229 : ℝ) / 250 * (n : ℝ) - (687 : ℝ) / 25 <
      Chebyshev.psi (n : ℝ) := by
  exact psi_gt_0_916_mul_sub_27_48 hn

example {n : ℕ} (hn : 0 < n) :
    Chebyshev.psi (n : ℝ) <
      (543 : ℝ) / 500 * (n : ℝ) + (490329 : ℝ) / 250 := by
  exact psi_lt_1_086_mul_add_1961_316 hn

example {k : ℕ} (hk : 0 < k) :
    Chebyshev.psi ((1806 * k : ℕ) : ℝ) - Chebyshev.psi (k : ℝ) ≤
      naguraChebyshevCombination k := by
  exact psi_sub_psi_le_naguraChebyshevCombination hk

example (n : ℕ) :
    naguraLowerChebyshevCombination n ≤ Chebyshev.psi (n : ℝ) := by
  exact naguraLowerChebyshevCombination_le_psi n

end Erdos390.WholePaper.NaguraExplicitPsiBoundsStatementAudit
