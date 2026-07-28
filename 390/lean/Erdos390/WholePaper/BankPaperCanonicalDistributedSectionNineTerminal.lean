import Erdos390.WholePaper.BankPaperCanonicalFixedDepthCapacityBridge
import Erdos390.WholePaper.BankPaperCanonicalSectionNineFinalGeometry
import Erdos390.WholePaper.BankPaperCanonicalSectionNineMainAsymptoticConnector

/-!
# Distributed Section 9 terminal at the capacity depth

`BankPaperCanonicalSectionNineFinalPayload` is a genuinely finite object.  It
contains the selected clean multipliers, endpoint collision-freedom, exact
flow and valuation boundaries, the actual post-tangent output, tail-charge
divisibility, and all seven final interval/collision facts.  The capacity
stage, on the other hand, supplies its bank and guarded anchor certificate
existentially.

This file keeps those witnesses synchronized.  The fixed-depth terminal below
asks, eventually, for one capacity-stage bank/certificate together with one
finite final payload for that same bank, certificate, and depth.  It is
strictly more concrete than a post-tangent continuation: its premise exposes
the complete distributed payload rather than assuming the continuation it is
meant to prove.

The existing `BankPaperCanonicalSectionNineOutputAtDepth` is intentionally not
used as an intermediate proposition.  That interface asks for a Section 9
output for every bank/certificate satisfying the three capacity facts,
whereas both the capacity theorem and the finite construction choose one
synchronized existential pair.  Instead we apply
`canonicalPostTangentContinuationData_of_output` directly to the output and
geometry carried by the finite payload.
-/

open scoped BigOperators
open Filter

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! ## Finite payload projection -/

/-- Forget the transport witnesses retained by the final payload and expose
exactly the finite output, divisibility, interval, and collision data consumed
by `canonicalPostTangentContinuationData_of_output`.

No clean-list or analytic hypothesis is discarded before the payload is
constructed: the clean multipliers are fields of the payload, while the
Post-Hfit, actual-P87, and scalar budget hypotheses are the explicit inputs of
`bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack`. -/
theorem bankPaperCanonicalSectionNineFinalPayload_to_outputData
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
            certificate deltaStar K) := by
  unfold BankPaperCanonicalSectionNineFinalPayload at hpayload
  obtain ⟨_multiplier, _hmultiplier, _hdistinct, _hdivergence,
    _hboundary, output, _hselector, hchargeDvd, hgeometry⟩ := hpayload
  unfold BankPaperCanonicalSectionNineFinalGeometry at hgeometry
  obtain ⟨hcandidates, hfixed, hfixedCandidate, hfixedBank,
    hcandidateBank, hanchorsFixed, hanchorsCandidate⟩ := hgeometry
  exact ⟨output, hcandidates, hfixed, hchargeDvd, hfixedCandidate,
    hfixedBank, hcandidateBank, hanchorsFixed, hanchorsCandidate⟩

end BankPaperRealization

/-! ## Synchronized fixed-depth terminal -/

/-- One eventual capacity witness and one complete finite distributed
Section 9 payload, synchronized at the same `n`, bank, guarded anchor
certificate, and capacity depth.

The existential parameters `W`, `K`, `selector`, `flow`, `L`, and `sigma`
remain visible because they are genuine finite construction data. -/
def BankPaperCanonicalDistributedSectionNineTerminalAtDepth
    (c deltaStar : ℝ) (depth : ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
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
                    certificate deltaStar selector flow L sigma

/-- The synchronized terminal retains the complete fixed-depth capacity
premise needed by the fixed-depth upper-endpoint bridge. -/
theorem
    BankPaperCanonicalDistributedSectionNineTerminalAtDepth.to_canonicalCapacityAtDepth
    {c deltaStar : ℝ} {depth : ℕ}
    (H :
      BankPaperCanonicalDistributedSectionNineTerminalAtDepth
        c deltaStar depth) :
    BankPaperCanonicalCapacityAtDepth c depth := by
  simp only [BankPaperCanonicalDistributedSectionNineTerminalAtDepth] at H
  simp only [BankPaperCanonicalCapacityAtDepth]
  filter_upwards [H] with n Hn
  obtain ⟨R, certificate, hcombined, hbaseDvd, htargetTail,
    _W, _K, _selector, _flow, _L, _sigma, _hpayload⟩ := Hn
  exact ⟨R, certificate, hcombined, hbaseDvd, htargetTail⟩

/-- A synchronized finite distributed terminal gives the exact canonical
post-tangent continuation at that same depth.

The capacity argument of the continuation is not used to replace the
terminal witnesses: the terminal already contains its own synchronized
capacity witnesses and finite payload. -/
theorem
    BankPaperCanonicalDistributedSectionNineTerminalAtDepth.to_postTangentContinuationAtDepth
    {c deltaStar : ℝ} {depth : ℕ}
    (H :
      BankPaperCanonicalDistributedSectionNineTerminalAtDepth
        c deltaStar depth) :
    BankPaperCanonicalPostTangentContinuationAtDepth c depth := by
  simp only [BankPaperCanonicalPostTangentContinuationAtDepth]
  intro _hcapacity
  simp only [BankPaperCanonicalDistributedSectionNineTerminalAtDepth] at H
  filter_upwards [H] with n Hn
  obtain ⟨R, certificate, hcombined, hbaseDvd, htargetTail,
    W, K, selector, flow, L, sigma, hpayload⟩ := Hn
  obtain ⟨output, hcandidates, hfixed, hchargeDvd, hfixedCandidate,
    hfixedBank, hcandidateBank, hanchorsFixed, hanchorsCandidate⟩ :=
    R.bankPaperCanonicalSectionNineFinalPayload_to_outputData
      certificate deltaStar selector flow L sigma hpayload
  refine ⟨R, certificate, hcombined, hbaseDvd, htargetTail, ?_⟩
  exact R.canonicalPostTangentContinuationData_of_output certificate
    (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
    (R.paperFixedExceptionalFactors deltaStar) output
    hcandidates hfixed hchargeDvd hfixedCandidate hfixedBank
    hcandidateBank hanchorsFixed hanchorsCandidate

/-! ## Same-depth upper endpoint -/

/-- The complete distributed terminal closes both inputs of the fixed-depth
capacity bridge, hence gives the eventual paper upper endpoint without any
comparison between independently selected depths. -/
theorem
    eventually_bankPaper_f_le_upperEndpoint_of_canonicalDistributedSectionNineTerminalAtDepth
    {c deltaStar : ℝ} {depth : ℕ}
    (hc : C0 < c) (hdepth : 201 ≤ depth)
    (H :
      BankPaperCanonicalDistributedSectionNineTerminalAtDepth
        c deltaStar depth) :
    ∀ᶠ n : ℕ in atTop,
      f n ≤ upperEndpoint n (upperTailLength c n) :=
  eventually_bankPaper_f_le_upperEndpoint_of_fixedDepthCapacity
    hc hdepth H.to_canonicalCapacityAtDepth
      H.to_postTangentContinuationAtDepth

/-! ## Depth-first main terminal -/

/-- The remaining global Section 9 obligation in the depth-first quantifier
order.  After the capacity depth and its uniform combined-charge terminal are
known, one admissible `deltaStar` must carry a synchronized finite distributed
terminal at that exact depth.

This is not a reformulation of a post-tangent continuation: its conclusion is
the explicit finite-payload terminal above. -/
def BankPaperCanonicalDistributedSectionNineTerminal : Prop :=
  ∀ (c : ℝ), C0 < c →
    ∀ (depth : ℕ), 201 ≤ depth →
      (∀ deltaStar : ℝ,
        IsPaperCombinedChargeDeltaStar c deltaStar →
          BankPaperCombinedChargeTerminalAtDepth c deltaStar depth) →
        ∃ deltaStar : ℝ,
          IsPaperCombinedChargeDeltaStar c deltaStar ∧
            BankPaperCanonicalDistributedSectionNineTerminalAtDepth
              c deltaStar depth

/-- The synchronized distributed Section 9 terminal feeds the fixed-depth
main reduction and proves the exact normalized limit. -/
theorem mainNormalizedLimit_of_canonicalDistributedSectionNineTerminal
    (H : BankPaperCanonicalDistributedSectionNineTerminal) :
    MainNormalizedLimit := by
  apply mainNormalizedLimit_of_depthFirstCombinedChargePostTangentContinuation
  intro c hc depth hdepth huniform
  obtain ⟨deltaStar, _hdeltaStar, hterminal⟩ :=
    H c hc depth hdepth huniform
  exact hterminal.to_postTangentContinuationAtDepth

/-- The same synchronized terminal proves the paper's literal small-`o`
statement. -/
theorem mainAsymptotic_of_canonicalDistributedSectionNineTerminal
    (H : BankPaperCanonicalDistributedSectionNineTerminal) :
    MainAsymptotic :=
  mainAsymptotic_iff_mainNormalizedLimit.mpr
    (mainNormalizedLimit_of_canonicalDistributedSectionNineTerminal H)

end

end Erdos390.WholePaper
