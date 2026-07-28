import Erdos390.WholePaper.StrongSafePrimeCounting

/-! # Literal statement audit for the strong safe PNT remainder -/

open Filter Asymptotics

namespace Erdos390.WholePaper

example :
    (fun x : ℝ ↦
      (Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log x) =O[atTop]
        (fun x : ℝ ↦ x / Real.log x ^ 2) :=
  SafePrimeCounting.primeCounting_sub_main_isBigO_div_log_sq

end Erdos390.WholePaper
