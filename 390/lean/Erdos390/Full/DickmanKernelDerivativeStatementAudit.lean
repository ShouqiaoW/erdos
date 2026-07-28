import Erdos390.Full.DickmanBasic

/-!
Independent type audit for the sharp estimate used in the moving-low-row
prime quadrature.  The statement records the essential relative factor `s`.
-/

namespace Erdos390.Full.DickmanKernelDerivativeStatementAudit

open Set
open Erdos390.Full.DickmanBasic

example :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |deriv F (s + t) - F s * deriv F t| ≤ C * s := by
  exact kernel_secondDerivative_first_bound

end Erdos390.Full.DickmanKernelDerivativeStatementAudit
