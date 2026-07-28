import Erdos390.WholePaper.TailValuationTwoSided

/-! # Expanded statement audit for the two-sided tail valuation bound -/

namespace Erdos390.WholePaper

example {a h p : ℕ} (hp : p.Prime) :
    h ≤ (p - 1) *
        ((a + h).factorial.factorization p - a.factorial.factorization p +
          Nat.log2 h + 1) ∧
      (a + h).factorial.factorization p - a.factorial.factorization p ≤
        h / (p - 1) + Nat.log2 (a + h) := by
  exact factorialValuationSub_twoSided hp

end Erdos390.WholePaper
