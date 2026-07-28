import Erdos390.WholePaper.BankPaperCanonicalSectionNineParameterSynchronization

/-!
# Statement audit for canonical Section 9 parameter synchronization

The single public theorem is checked below with both semantic wrappers
expanded.  This pins down the depth-first quantifier order, every synchronized
cutoff, the literal tangent slack inequality, the complete combined-charge
payload, and the independent eventual scale package.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.Scale

noncomputable section

/-! ## Complete public declaration census -/

#check exists_bankPaperCanonicalSectionNineParameterSynchronization

/-! ## Fully expanded synchronization statement -/

example {c : ℝ} (hc : C0 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      ∃ W : ℕ,
        2 ≤ W ∧
        2 * depth + 1 ≤ W ∧
        fullReciprocalSumUniformCutoff ≤ W ∧
        tangentSelbergMertensBase ≤ W ∧
        canonicalActualMomentCutoff ≤ W ∧
        ∃ r0 : ℝ,
          1 < r0 ∧
          r0 < 3 / 2 ∧
          r0 < 2 ∧
          (IsPaperCombinedChargeDeltaStar c
                (paperCombinedTangentDeltaStar c W r0) ∧
            80 * tangentSelbergCanonicalMainConstant *
                paperCombinedTangentDeltaStar c W r0 <
              tangentPaperHeadGap W r0) ∧
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
                        (bank.paperFixedExceptionalFactors
                          (paperCombinedTangentDeltaStar c W r0)) ∣
                    certificate.prechargedTailTarget ∧
                  (∀ p ∈ primesUpTo (2 * depth + 1),
                    (c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
                          secondOrderScale n +
                        (bank.selectorTailCharge
                          (bank.paperFixedExceptionalFactors
                            (paperCombinedTangentDeltaStar c W r0))).factorization p ≤
                      certificate.prechargedTailTarget.factorization p) ∧
                  certificate.selectorTailTarget bank
                        (bank.paperFixedExceptionalFactors
                          (paperCombinedTangentDeltaStar c W r0)) *
                      bank.selectorTailCharge
                        (bank.paperFixedExceptionalFactors
                          (paperCombinedTangentDeltaStar c W r0)) =
                    certificate.prechargedTailTarget ∧
                  certificate.prechargedTailTarget *
                      centralAnchorDivisor n (centralAnchorCutoff depth n)
                        certificate.q =
                    centralTailProduct n (upperTailLength c n)) ∧
          (∀ᶠ n : ℕ in atTop,
            centralAnchorCutoffThreshold depth ≤ n ∧
              W ≤ yNat n ∧
              yNat n < centralAnchorCutoff depth n ∧
              0 < n ∧
              (yNat n : ℝ) ≤ (n : ℝ) ∧
              (yNat n : ℝ) ^ 2 ≤ (n : ℝ)) := by
  simpa only [IsPaperCombinedTangentDeltaStar,
    BankPaperCombinedChargeTerminalAtDepth] using
      exists_bankPaperCanonicalSectionNineParameterSynchronization hc

end

end Erdos390.WholePaper
