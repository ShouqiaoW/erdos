import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstCutoffAwareDistributedTerminalConnector

/-!
# Expanded statement audit: cutoff-aware distributed Section 9 terminal

This audit assigns the production theorem directly to its fully expanded
public conclusion.  The capacity depth and final width are selected before
the tangent parameters.  Every paper cutoff retained by the connector is
displayed literally.

The tangent admissibility condition, the complete combined-charge event,
and the synchronized distributed terminal are all unfolded below.  Thus no
connector-specific proposition alias hides either eventual payload.

The analytic cutoff `W0` is internal to the construction: the production
proof obtains it before defining the displayed final `W` and proves
`W0 ≤ W`.  Since `W0` is not part of the public theorem type, the exact
statement audit can expose only the resulting final-width contract, not an
additional public `W0 ≤ W` field.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 4000000 in
example
    {c : Real} (hc : C0 < c) :
    ∃ depth W : Nat, ∃ r0 deltaStar : Real,
      201 ≤ depth ∧
        2 ≤ W ∧
        2 * depth + 1 ≤ W ∧
        fullReciprocalSumUniformCutoff ≤ W ∧
        canonicalActualMomentCutoff ≤ W ∧
        1 < r0 ∧
        r0 < 3 / 2 ∧
        ((0 < deltaStar ∧
            deltaStar < 1 / 18 ∧
              paperExceptionalChargeConstant c *
                    (deltaStar / paperExceptionalTheta) ≤
                (c - C0) / 48) ∧
          80 * tangentSelbergCanonicalMainConstant * deltaStar <
            tangentPaperHeadGap W r0) ∧
        (∀ᶠ n : Nat in atTop,
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
                  (c - C0) / (24 * (((p - 1 : Nat) : Real))) *
                        secondOrderScale n +
                      (bank.selectorTailCharge
                        (bank.paperFixedExceptionalFactors
                          deltaStar)).factorization p ≤
                    certificate.prechargedTailTarget.factorization p) ∧
                certificate.selectorTailTarget bank
                      (bank.paperFixedExceptionalFactors deltaStar) *
                    bank.selectorTailCharge
                      (bank.paperFixedExceptionalFactors deltaStar) =
                  certificate.prechargedTailTarget ∧
                certificate.prechargedTailTarget *
                    centralAnchorDivisor n (centralAnchorCutoff depth n)
                      certificate.q =
                  centralTailProduct n (upperTailLength c n)) ∧
        (∀ᶠ n : Nat in atTop,
          ∃ R : BankPaperRealization n
              (upperEndpoint n (upperTailLength c n)),
            ∃ certificate : GuardedCentralAnchorCertificate c depth n
                R.anchorGuardLeftCore R.anchorGuardRightCore
                (R.centralChangedMarkers depth),
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                    certificate.q * R.prechargeBaseStateProduct ∣
                  centralTailProduct n (upperTailLength c n) ∧
                (baseBankFactors R.exactificationState).prod id ∣
                  certificate.prechargedTailTarget ∧
                certificate.prechargedTailTarget *
                    centralAnchorDivisor n (centralAnchorCutoff depth n)
                      certificate.q =
                  centralTailProduct n (upperTailLength c n) ∧
                ∃ Wpayload K : Nat,
                  ∃ selector : Nat → Real,
                    ∃ flow : BankPaperCanonicalTangentPrime n Wpayload →
                        BankPaperCanonicalTangentPrime n Wpayload → Real,
                      ∃ L sigma : Real,
                        R.BankPaperCanonicalSectionNineFinalPayload
                          (K := K) certificate deltaStar selector flow L
                          sigma) := by
  simpa only [
    IsPaperCombinedTangentDeltaStar,
    IsPaperCombinedChargeDeltaStar,
    BankPaperCombinedChargeTerminalAtDepth,
    BankPaperCanonicalDistributedSectionNineTerminalAtDepth] using
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareDistributedTerminal
      hc

/-! ## Public declaration census -/

#check
  exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareDistributedTerminal

end BankPaperRealization

end

end Erdos390.WholePaper
