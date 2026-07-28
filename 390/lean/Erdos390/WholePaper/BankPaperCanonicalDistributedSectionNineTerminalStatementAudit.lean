import Erdos390.WholePaper.BankPaperCanonicalDistributedSectionNineTerminal

/-!
# Statement audit for the distributed Section 9 terminal

The audit expands the finite payload projection, the synchronized fixed-depth
terminal, and the depth-first global contract.  In particular, every
occurrence of `depth` is the same witness selected by the capacity stage.
-/

open scoped BigOperators
open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! ## Exact finite payload projection -/

example
    {c : ℝ} {depth n W K : ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : ℝ) (selector : ℕ → ℝ)
    (flow : BankPaperCanonicalTangentPrime n W →
      BankPaperCanonicalTangentPrime n W → ℝ)
    (L sigma : ℝ)
    (hpayload :
      R.BankPaperCanonicalSectionNineFinalPayload (K := K)
        certificate deltaStar selector flow L sigma) :
    ∃ _output : BankPaperCanonicalPostTangentOutput R certificate
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (R.paperFixedExceptionalFactors deltaStar),
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K ⊆
          factorInterval n
            (upperEndpoint n (upperTailLength c n)) ∧
        R.paperFixedExceptionalFactors deltaStar ⊆
          factorInterval n
            (upperEndpoint n (upperTailLength c n)) ∧
        R.selectorTailCharge
              (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget ∧
        Disjoint (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet
            certificate deltaStar K) ∧
        (∀ slot selected,
          Disjoint (R.paperFixedExceptionalFactors deltaStar)
            (R.exactificationState slot selected)) ∧
        (∀ slot selected,
          Disjoint
            (R.roughCanonicalGuardedCandidateSet
              certificate deltaStar K)
            (R.exactificationState slot selected)) ∧
        Disjoint certificate.anchors
          (R.paperFixedExceptionalFactors deltaStar) ∧
        Disjoint certificate.anchors
          (R.roughCanonicalGuardedCandidateSet
            certificate deltaStar K) :=
  R.bankPaperCanonicalSectionNineFinalPayload_to_outputData
    certificate deltaStar selector flow L sigma hpayload

end BankPaperRealization

/-! ## Exact synchronized fixed-depth contract -/

example (c deltaStar : ℝ) (depth : ℕ) :
    BankPaperCanonicalDistributedSectionNineTerminalAtDepth
        c deltaStar depth =
      (∀ᶠ n : ℕ in atTop,
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
              ∃ W K : ℕ,
                ∃ selector : ℕ → ℝ,
                  ∃ flow : BankPaperCanonicalTangentPrime n W →
                      BankPaperCanonicalTangentPrime n W → ℝ,
                    ∃ L sigma : ℝ,
                      R.BankPaperCanonicalSectionNineFinalPayload (K := K)
                        certificate deltaStar selector flow L sigma) := by
  rfl

example {c deltaStar : ℝ} {depth : ℕ}
    (H :
      BankPaperCanonicalDistributedSectionNineTerminalAtDepth
        c deltaStar depth) :
    BankPaperCanonicalCapacityAtDepth c depth :=
  H.to_canonicalCapacityAtDepth

example {c deltaStar : ℝ} {depth : ℕ}
    (H :
      BankPaperCanonicalDistributedSectionNineTerminalAtDepth
        c deltaStar depth) :
    BankPaperCanonicalPostTangentContinuationAtDepth c depth :=
  H.to_postTangentContinuationAtDepth

example {c deltaStar : ℝ} {depth : ℕ}
    (hc : C0 < c) (hdepth : 201 ≤ depth)
    (H :
      BankPaperCanonicalDistributedSectionNineTerminalAtDepth
        c deltaStar depth) :
    ∀ᶠ n : ℕ in atTop,
      f n ≤ upperEndpoint n (upperTailLength c n) :=
  eventually_bankPaper_f_le_upperEndpoint_of_canonicalDistributedSectionNineTerminalAtDepth
    hc hdepth H

/-! ## Exact depth-first global contract and targets -/

example :
    BankPaperCanonicalDistributedSectionNineTerminal =
      (∀ (c : ℝ), C0 < c →
        ∀ (depth : ℕ), 201 ≤ depth →
          (∀ deltaStar : ℝ,
            IsPaperCombinedChargeDeltaStar c deltaStar →
              BankPaperCombinedChargeTerminalAtDepth c deltaStar depth) →
            ∃ deltaStar : ℝ,
              IsPaperCombinedChargeDeltaStar c deltaStar ∧
                BankPaperCanonicalDistributedSectionNineTerminalAtDepth
                  c deltaStar depth) := by
  rfl

example (H : BankPaperCanonicalDistributedSectionNineTerminal) :
    Tendsto
      (fun n : ℕ =>
        (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) / (n : ℝ))
      atTop (nhds C0) := by
  simpa only [MainNormalizedLimit] using
    mainNormalizedLimit_of_canonicalDistributedSectionNineTerminal H

example (H : BankPaperCanonicalDistributedSectionNineTerminal) :
    mainError =o[atTop] secondOrderScale := by
  simpa only [MainAsymptotic] using
    mainAsymptotic_of_canonicalDistributedSectionNineTerminal H

/-! ## Complete public declaration census -/

#check
  BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_to_outputData
#check BankPaperCanonicalDistributedSectionNineTerminalAtDepth
#check
  BankPaperCanonicalDistributedSectionNineTerminalAtDepth.to_canonicalCapacityAtDepth
#check
  BankPaperCanonicalDistributedSectionNineTerminalAtDepth.to_postTangentContinuationAtDepth
#check
  eventually_bankPaper_f_le_upperEndpoint_of_canonicalDistributedSectionNineTerminalAtDepth
#check BankPaperCanonicalDistributedSectionNineTerminal
#check mainNormalizedLimit_of_canonicalDistributedSectionNineTerminal
#check mainAsymptotic_of_canonicalDistributedSectionNineTerminal

end

end Erdos390.WholePaper
