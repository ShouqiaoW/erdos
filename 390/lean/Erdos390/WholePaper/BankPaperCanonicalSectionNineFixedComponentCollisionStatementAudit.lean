import Erdos390.WholePaper.BankPaperCanonicalSectionNineFixedComponentCollision

/-!
# Statement audit for the fixed/component collision closure

The audit expands the exact residual bottom-state predicate, checks its
equivalence with the full census disjointness statement, and records the
finite and eventual closures in source order.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

example {c : Real} {n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (deltaStar : Real) :
    R.BankPaperCanonicalSectionNineBottomStateCollisionExclusions
        deltaStar ↔
      ∀ request : ↑(bankBottomRelevantPaperRequests n),
        let fullRequest :=
          bankBottomRelevantRequestToPaperRequest request
        R.bottom.lowerStateFactor fullRequest ∉
            R.paperFixedExceptionalFactors deltaStar ∧
          (R.bottom.upperStateFactor fullRequest ≠
              R.bottom.donorFactor fullRequest →
            R.bottom.upperStateFactor fullRequest ∉
              R.paperFixedExceptionalFactors deltaStar) := by
  rfl

example {c : Real} {n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (deltaStar : Real) :
    R.BankPaperCanonicalSectionNineFixedComponentCollisionFree deltaStar ↔
      R.BankPaperCanonicalSectionNineBottomStateCollisionExclusions
        deltaStar :=
  R.bankPaperCanonicalSectionNineFixedComponentCollisionFree_iff_bottomStateExclusions
    deltaStar

example {c : Real} {n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (deltaStar : Real)
    (hnarrow :
      5 * upperEndpoint n (upperTailLength c n) ≤ 12 * n) :
    R.BankPaperCanonicalSectionNineFixedComponentCollisionFree deltaStar :=
  R.bankPaperCanonicalSectionNineFixedComponentCollisionFree_of_scaledEndpoint_narrow
    deltaStar hnarrow

end BankPaperRealization

example {c : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (deltaStar : Real),
        R.BankPaperCanonicalSectionNineFixedComponentCollisionFree
          deltaStar :=
  eventually_bankPaperCanonicalSectionNineFixedComponentCollisionFree hc

#check BankPaperRealization.BankPaperCanonicalSectionNineBottomStateCollisionExclusions
#check BankPaperRealization.bankPaperCanonicalSectionNineFixedComponentCollisionFree_iff_bottomStateExclusions
#check BankPaperRealization.bankPaperCanonicalSectionNineFixedComponentCollisionFree_of_scaledEndpoint_narrow
#check eventually_bankPaperCanonicalSectionNineFixedComponentCollisionFree

end

end Erdos390.WholePaper
