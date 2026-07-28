import Erdos390.WholePaper.BankPaperCanonicalFixedDepthCapacityBridge

/-!
# Statement audit for the fixed-depth capacity bridge

The audit expands the exact three-fact capacity premise and checks every
public theorem in source order.  The depth-first examples retain one and the
same `depth`; no comparison with `bankPaperCapacitySelectedDepth` appears.
-/

open scoped BigOperators
open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Exact fixed-depth capacity premise -/

example (c : ℝ) (depth : ℕ) :
    BankPaperCanonicalCapacityAtDepth c depth =
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
              certificate.prechargedTailTarget *
                  centralAnchorDivisor n (centralAnchorCutoff depth n)
                    certificate.q =
                centralTailProduct n (upperTailLength c n)) := by
  rfl

example {c deltaStar : ℝ} {depth : ℕ}
    (H : BankPaperCombinedChargeTerminalAtDepth c deltaStar depth) :
    BankPaperCanonicalCapacityAtDepth c depth :=
  H.to_canonicalCapacityAtDepth

/-! ## Same-depth endpoint bridges -/

example {c : ℝ} {depth : ℕ} (hc : C0 < c) (hdepth : 201 ≤ depth)
    (hcapacity : BankPaperCanonicalCapacityAtDepth c depth)
    (hcontinue :
      BankPaperCanonicalPostTangentContinuationAtDepth c depth) :
    ∀ᶠ n : ℕ in atTop,
      f n ≤ upperEndpoint n (upperTailLength c n) :=
  eventually_bankPaper_f_le_upperEndpoint_of_fixedDepthCapacity
    hc hdepth hcapacity hcontinue

example {c deltaStar : ℝ} {depth : ℕ}
    (hc : C0 < c) (hdepth : 201 ≤ depth)
    (hterminal :
      BankPaperCombinedChargeTerminalAtDepth c deltaStar depth)
    (hcontinue :
      BankPaperCanonicalPostTangentContinuationAtDepth c depth) :
    ∀ᶠ n : ℕ in atTop,
      f n ≤ upperEndpoint n (upperTailLength c n) :=
  eventually_bankPaper_f_le_upperEndpoint_of_combinedChargeTerminalAtDepth
    hc hdepth hterminal hcontinue

/-! ## Exact depth-first bridge -/

example {c : ℝ} (hc : C0 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      ∀ deltaStar : ℝ, IsPaperCombinedChargeDeltaStar c deltaStar →
        BankPaperCombinedChargeTerminalAtDepth c deltaStar depth ∧
          (BankPaperCanonicalPostTangentContinuationAtDepth c depth →
            ∀ᶠ n : ℕ in atTop,
              f n ≤ upperEndpoint n (upperTailLength c n)) :=
  exists_depth_bankPaperCombinedChargeTerminal_uniform_deltaStar_with_upperEndpointBridge
    hc

/-! ## Exact main targets -/

example
    (hcontinue :
      ∀ (c : ℝ) (_hc : C0 < c) (depth : ℕ), 201 ≤ depth →
        (∀ deltaStar : ℝ,
          IsPaperCombinedChargeDeltaStar c deltaStar →
            BankPaperCombinedChargeTerminalAtDepth c deltaStar depth) →
          BankPaperCanonicalPostTangentContinuationAtDepth c depth) :
    Tendsto
      (fun n : ℕ =>
        (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) / (n : ℝ))
      atTop (nhds C0) := by
  simpa only [MainNormalizedLimit] using
    mainNormalizedLimit_of_depthFirstCombinedChargePostTangentContinuation
      hcontinue

example
    (hcontinue :
      ∀ (c : ℝ) (_hc : C0 < c) (depth : ℕ), 201 ≤ depth →
        (∀ deltaStar : ℝ,
          IsPaperCombinedChargeDeltaStar c deltaStar →
            BankPaperCombinedChargeTerminalAtDepth c deltaStar depth) →
          BankPaperCanonicalPostTangentContinuationAtDepth c depth) :
    mainError =o[atTop] secondOrderScale := by
  simpa only [MainAsymptotic] using
    mainAsymptotic_of_depthFirstCombinedChargePostTangentContinuation
      hcontinue

/-! ## Complete public declaration census -/

#check BankPaperCanonicalCapacityAtDepth
#check
  BankPaperCombinedChargeTerminalAtDepth.to_canonicalCapacityAtDepth
#check eventually_bankPaper_f_le_upperEndpoint_of_fixedDepthCapacity
#check
  eventually_bankPaper_f_le_upperEndpoint_of_combinedChargeTerminalAtDepth
#check
  exists_depth_bankPaperCombinedChargeTerminal_uniform_deltaStar_with_upperEndpointBridge
#check
  mainNormalizedLimit_of_depthFirstCombinedChargePostTangentContinuation
#check
  mainAsymptotic_of_depthFirstCombinedChargePostTangentContinuation

end

end Erdos390.WholePaper
