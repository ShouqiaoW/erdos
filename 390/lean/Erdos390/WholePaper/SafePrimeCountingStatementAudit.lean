import Erdos390.WholePaper.SafePrimeCounting

/-! Expanded statement audit for the safe natural-variable PNT. -/

open Filter Asymptotics

namespace Erdos390.WholePaper.SafePrimeCountingStatementAudit

example :
    (fun n : ℕ => (Nat.primeCounting n : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
  exact SafePrimeCounting.primeCounting_nat_isEquivalent

end Erdos390.WholePaper.SafePrimeCountingStatementAudit
