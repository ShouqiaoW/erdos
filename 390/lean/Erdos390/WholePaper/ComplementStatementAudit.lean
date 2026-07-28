import Erdos390.WholePaper.Complement

/-!
# Expanded statement audit for the complement formulation

This repeats the literal statement from the paper without the local
abbreviations `factorInterval`, `IsAdmissibleEndpoint`,
`HasComplementProduct`, or `complementQuotient`.  In particular, the
quotient is taken in `ℚ`, not by truncated natural-number division.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example {n M : ℕ} (hnM : n < M) :
    (∃ factors : Finset ℕ,
        factors ⊆ Finset.Ioc n M ∧
          factors.prod id = n.factorial) ↔
      ∃ selected : Finset ℕ,
        selected ⊆ Finset.Ioc n M ∧
          ((selected.prod id : ℕ) : ℚ) =
            (M.factorial : ℚ) / (n.factorial : ℚ) ^ 2 := by
  simpa only [IsAdmissibleEndpoint, HasComplementProduct,
    factorInterval, complementQuotient] using
      (complement_formulation (n := n) (M := M) hnM)

end

end Erdos390.WholePaper
