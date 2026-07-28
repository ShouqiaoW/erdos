import Erdos390.WholePaper.BankPaperCombinedChargeDepthFirstTerminal

/-!
# Statement audit for the depth-first combined-charge terminal

The census contains the fixed-depth payload and both depth-first terminals.
The examples expand the complete payload and pin down the quantifier order:
capacity depth first, admissible exponent or tangent parameters afterward.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Complete public declaration census -/

#check BankPaperCombinedChargeTerminalAtDepth
#check exists_depth_bankPaperCombinedChargeTerminal_uniform_deltaStar
#check exists_depth_bankPaperCombinedChargeTerminal_uniform_tangentChoice

/-! ## Exact fixed-depth payload -/

example (c deltaStar : ℝ) (depth : ℕ) :
    BankPaperCombinedChargeTerminalAtDepth c deltaStar depth =
      (∀ᶠ n : ℕ in atTop,
        ∃ bank : BankPaperRealization n
            (upperEndpoint n (upperTailLength c n)),
          ∃ certificate : GuardedCentralAnchorCertificate c depth n
              bank.anchorGuardLeftCore bank.anchorGuardRightCore
              (bank.centralChangedMarkers depth),
            centralAnchorDivisor n (centralAnchorCutoff depth n)
                  certificate.q * bank.prechargeBaseStateProduct ∣
                centralTailProduct n (upperTailLength c n) ∧
              (baseBankFactors bank.exactificationState).prod id ∣
                certificate.prechargedTailTarget ∧
              bank.selectorTailCharge
                    (bank.paperFixedExceptionalFactors deltaStar) ∣
                certificate.prechargedTailTarget ∧
              (∀ p ∈ primesUpTo (2 * depth + 1),
                (c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
                      secondOrderScale n +
                    (bank.selectorTailCharge
                      (bank.paperFixedExceptionalFactors deltaStar)).factorization p ≤
                  certificate.prechargedTailTarget.factorization p) ∧
              certificate.selectorTailTarget bank
                    (bank.paperFixedExceptionalFactors deltaStar) *
                  bank.selectorTailCharge
                    (bank.paperFixedExceptionalFactors deltaStar) =
                certificate.prechargedTailTarget ∧
              certificate.prechargedTailTarget *
                  centralAnchorDivisor n (centralAnchorCutoff depth n)
                    certificate.q =
                centralTailProduct n (upperTailLength c n)) := by
  rfl

/-! ## Exact depth-first quantifier order -/

example {c : ℝ} (hc : C0 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      ∀ deltaStar : ℝ, IsPaperCombinedChargeDeltaStar c deltaStar →
        BankPaperCombinedChargeTerminalAtDepth c deltaStar depth :=
  exists_depth_bankPaperCombinedChargeTerminal_uniform_deltaStar hc

example {c : ℝ} (hc : C0 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      ∀ (W : ℕ) (r0 : ℝ), r0 < 2 →
        (IsPaperCombinedChargeDeltaStar c
              (paperCombinedTangentDeltaStar c W r0) ∧
            80 * tangentSelbergCanonicalMainConstant *
                paperCombinedTangentDeltaStar c W r0 <
              tangentPaperHeadGap W r0) ∧
          BankPaperCombinedChargeTerminalAtDepth c
            (paperCombinedTangentDeltaStar c W r0) depth := by
  simpa only [IsPaperCombinedTangentDeltaStar] using
    exists_depth_bankPaperCombinedChargeTerminal_uniform_tangentChoice hc

end

end Erdos390.WholePaper
