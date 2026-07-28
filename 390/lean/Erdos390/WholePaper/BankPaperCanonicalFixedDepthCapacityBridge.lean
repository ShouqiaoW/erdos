import Erdos390.WholePaper.BankPaperCombinedChargeDepthFirstTerminal
import Erdos390.WholePaper.BankPaperMainAsymptoticReduction

/-!
# Fixed-depth capacity bridge to the main reduction

The capacity-aware main reduction names one depth chosen by
`exists_depth_bankPaper_f_le_upperEndpoint_of_canonicalPostTangentContinuation`.
The depth-first combined-charge terminal chooses a depth independently.
There is no reason for those two witnesses to be equal.

This file removes the need for such an equality.  It exposes the literal
capacity premise at an arbitrary fixed depth, proves the upper-endpoint
reduction at that same depth, and observes that
`BankPaperCombinedChargeTerminalAtDepth` already contains exactly those
capacity facts.  Consequently the depth selected by the depth-first charge
theorem can be passed directly to the main reduction.
-/

open scoped BigOperators
open Filter

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## The exact capacity premise at a fixed depth -/

/-- The three eventual capacity facts consumed by
`BankPaperCanonicalPostTangentContinuationAtDepth`, with the depth kept as
an explicit input rather than selected existentially. -/
def BankPaperCanonicalCapacityAtDepth
    (c : ℝ) (depth : ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
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
          certificate.prechargedTailTarget *
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q =
            centralTailProduct n (upperTailLength c n)

/-- The depth-first combined-charge payload retains the complete fixed-depth
capacity premise.  Its extra charge, retained-valuation, and selector-target
facts are discarded only by this projection. -/
theorem BankPaperCombinedChargeTerminalAtDepth.to_canonicalCapacityAtDepth
    {c deltaStar : ℝ} {depth : ℕ}
    (H : BankPaperCombinedChargeTerminalAtDepth c deltaStar depth) :
    BankPaperCanonicalCapacityAtDepth c depth := by
  simp only [BankPaperCombinedChargeTerminalAtDepth] at H
  simp only [BankPaperCanonicalCapacityAtDepth]
  filter_upwards [H] with n Hn
  obtain
      ⟨bank, certificate, hcombined, hbaseDvd, _hchargeDvd,
        _hretained, _hselectorIdentity, htargetTail⟩ := Hn
  exact ⟨bank, certificate, hcombined, hbaseDvd, htargetTail⟩

/-! ## Same-depth upper-endpoint reduction -/

/-- At any fixed depth at least `201`, the actual capacity facts and a
post-tangent continuation at that same depth imply the eventual upper
endpoint.

This is the public fixed-depth form of the reduction previously used only
inside the existential capacity selector. -/
theorem eventually_bankPaper_f_le_upperEndpoint_of_fixedDepthCapacity
    {c : ℝ} {depth : ℕ} (hc : C0 < c) (hdepth : 201 ≤ depth)
    (hcapacity : BankPaperCanonicalCapacityAtDepth c depth)
    (hcontinue :
      BankPaperCanonicalPostTangentContinuationAtDepth c depth) :
    ∀ᶠ n : ℕ in atTop,
      f n ≤ upperEndpoint n (upperTailLength c n) := by
  have hC0Pos : (0 : ℝ) < C0 := by
    norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
  simp only [BankPaperCanonicalCapacityAtDepth] at hcapacity
  simp only [BankPaperCanonicalPostTangentContinuationAtDepth] at hcontinue
  have hrefined := hcontinue hcapacity
  filter_upwards [hrefined,
      eventually_ge_atTop (centralAnchorCutoffThreshold depth),
      eventually_bankAnchor_fixed_le_yNat (2 * depth + 1),
      eventually_yNat_lt_centralAnchorCutoff depth,
      eventually_upperTailLength_le hcPos,
      eventually_ge_atTop 3]
      with n hrefinedN hnCutoff hprefix hyCutoff htail hnThree
  obtain ⟨R, certificate, _, _, _, hpostTangent⟩ := hrefinedN
  obtain ⟨candidates, x, fixed, hcandidates, hfixed, hx, hrowInt,
      hchargeDvd, hresidualValuation, hfixedCandidate, hfixedBank,
      hcandidateBank, hanchorsFixed, hanchorsCandidate⟩ :=
    hpostTangent
  have hfixedPositive : ∀ a ∈ fixed, 0 < a := by
    intro a ha
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp (hfixed ha)).1
  have hvaluationCertificate : ∀ q,
      ((fixed.prod id *
          (baseBankFactors R.exactificationState).prod id).factorization q :
            ℝ) +
          ∑ a ∈ candidates, x a * (a.factorization q : ℝ) =
        (certificate.prechargedTailTarget.factorization q : ℝ) := by
    apply (certificate.valuationCertificate_iff_selectorTailTarget
      R fixed
        (fun q ↦ ∑ a ∈ candidates,
          x a * (a.factorization q : ℝ))
        hfixedPositive hchargeDvd).2
    exact hresidualValuation
  have hadmissible :
      IsAdmissibleEndpoint n
        (upperEndpoint n (upperTailLength c n)) :=
    bankPaper_isAdmissibleEndpoint_of_canonicalPostTangentCertificate
      R (by omega) hnCutoff hprefix hyCutoff htail certificate candidates x
        fixed hcandidates hfixed hx hrowInt hvaluationCertificate
        hfixedCandidate hfixedBank hcandidateBank hanchorsFixed
        hanchorsCandidate
  exact f_le_of_admissible hnThree hadmissible

/-- A fixed-depth combined-charge terminal therefore supplies the capacity
side of the same-depth upper-endpoint bridge directly. -/
theorem
    eventually_bankPaper_f_le_upperEndpoint_of_combinedChargeTerminalAtDepth
    {c deltaStar : ℝ} {depth : ℕ}
    (hc : C0 < c) (hdepth : 201 ≤ depth)
    (hterminal :
      BankPaperCombinedChargeTerminalAtDepth c deltaStar depth)
    (hcontinue :
      BankPaperCanonicalPostTangentContinuationAtDepth c depth) :
    ∀ᶠ n : ℕ in atTop,
      f n ≤ upperEndpoint n (upperTailLength c n) :=
  eventually_bankPaper_f_le_upperEndpoint_of_fixedDepthCapacity
    hc hdepth hterminal.to_canonicalCapacityAtDepth hcontinue

/-! ## The depth-first witness carries its own upper bridge -/

/-- Strengthened view of the existing depth-first terminal: after its depth
has been selected, every admissible charge exponent carries both the full
combined-charge payload and the continuation-to-upper-endpoint bridge at
that exact same depth. -/
theorem
    exists_depth_bankPaperCombinedChargeTerminal_uniform_deltaStar_with_upperEndpointBridge
    {c : ℝ} (hc : C0 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      ∀ deltaStar : ℝ, IsPaperCombinedChargeDeltaStar c deltaStar →
        BankPaperCombinedChargeTerminalAtDepth c deltaStar depth ∧
          (BankPaperCanonicalPostTangentContinuationAtDepth c depth →
            ∀ᶠ n : ℕ in atTop,
              f n ≤ upperEndpoint n (upperTailLength c n)) := by
  obtain ⟨depth, hdepth, huniform⟩ :=
    exists_depth_bankPaperCombinedChargeTerminal_uniform_deltaStar hc
  refine ⟨depth, hdepth, ?_⟩
  intro deltaStar hdelta
  have hterminal := huniform deltaStar hdelta
  exact
    ⟨hterminal,
      eventually_bankPaper_f_le_upperEndpoint_of_combinedChargeTerminalAtDepth
        hc hdepth hterminal⟩

/-! ## Direct main reductions with the depth-first quantifier order -/

/-- A post-tangent supplier which receives the actual depth-first charge
depth and its uniform charge payload proves the exact normalized limit.

Only the depth chosen by
`exists_depth_bankPaperCombinedChargeTerminal_uniform_deltaStar` is used;
no continuation at `bankPaperCapacitySelectedDepth` and no equality of the
two depth witnesses is assumed. -/
theorem
    mainNormalizedLimit_of_depthFirstCombinedChargePostTangentContinuation
    (hcontinue :
      ∀ (c : ℝ) (_hc : C0 < c) (depth : ℕ), 201 ≤ depth →
        (∀ deltaStar : ℝ,
          IsPaperCombinedChargeDeltaStar c deltaStar →
            BankPaperCombinedChargeTerminalAtDepth c deltaStar depth) →
          BankPaperCanonicalPostTangentContinuationAtDepth c depth) :
    MainNormalizedLimit := by
  apply mainNormalizedLimit_of_eventually_f_le_upperScaledEndpoint
  intro c hc
  obtain ⟨depth, hdepth, huniform⟩ :=
    exists_depth_bankPaperCombinedChargeTerminal_uniform_deltaStar hc
  have hdelta :
      IsPaperCombinedChargeDeltaStar c
        (paperCombinedChargeDeltaStar c) :=
    paperCombinedChargeDeltaStar_spec hc
  have hterminal :=
    huniform (paperCombinedChargeDeltaStar c) hdelta
  exact
    eventually_bankPaper_f_le_upperEndpoint_of_combinedChargeTerminalAtDepth
      hc hdepth hterminal (hcontinue c hc depth hdepth huniform)

/-- The same fixed-depth, depth-first bridge with the paper's literal
small-`o` conclusion. -/
theorem mainAsymptotic_of_depthFirstCombinedChargePostTangentContinuation
    (hcontinue :
      ∀ (c : ℝ) (_hc : C0 < c) (depth : ℕ), 201 ≤ depth →
        (∀ deltaStar : ℝ,
          IsPaperCombinedChargeDeltaStar c deltaStar →
            BankPaperCombinedChargeTerminalAtDepth c deltaStar depth) →
          BankPaperCanonicalPostTangentContinuationAtDepth c depth) :
    MainAsymptotic :=
  mainAsymptotic_iff_mainNormalizedLimit.mpr
    (mainNormalizedLimit_of_depthFirstCombinedChargePostTangentContinuation
      hcontinue)

end

end Erdos390.WholePaper
