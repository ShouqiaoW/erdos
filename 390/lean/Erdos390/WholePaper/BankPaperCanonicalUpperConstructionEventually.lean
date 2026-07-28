import Erdos390.WholePaper.BankPaperCanonicalUpperConstructionReduction
import Erdos390.WholePaper.BankPaperPrechargeCapacityEventually
import Erdos390.WholePaper.BankPaperSelectorTailTarget

/-!
# Eventual canonical upper construction from a post-tangent continuation

The precharge-capacity stage already constructs, eventually, the paper bank,
the guarded central-anchor certificate, and the three exact divisibility and
product facts for the precharged tail.  The theorem below consumes those
witnesses and discharges all numerical cutoff conditions by existing
eventual estimates.

No selector or tangent existence is asserted here.  Instead, one explicit
continuation supplies the remaining finite candidate set, feasible weights,
integral complete-rough row sums, residual selector valuation identity, and
collision guards after seeing the actual capacity-stage witnesses.  The
residual identity is stated for `selectorTailTarget`; its charged form is
derived here before applying the canonical exactification reduction.
-/

open scoped BigOperators
open Filter

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- The exact post-tangent continuation still needed after the capacity
stage has fixed `depth`.  It may depend on the actual endpoint, bank, guarded
anchor certificate, and all three capacity-stage facts. -/
def BankPaperCanonicalPostTangentContinuationAtDepth
    (c : ℝ) (depth : ℕ) : Prop :=
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
              centralTailProduct n (upperTailLength c n)) →
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
            ∃ candidates : Finset ℕ, ∃ x : ℕ → ℝ,
              ∃ fixed : Finset ℕ,
                candidates ⊆
                    factorInterval n
                      (upperEndpoint n (upperTailLength c n)) ∧
                fixed ⊆
                    factorInterval n
                      (upperEndpoint n (upperTailLength c n)) ∧
                (∀ a ∈ candidates, 0 ≤ x a ∧ x a ≤ 1) ∧
                (∀ label ∈ completeRoughLabelSet (yNat n) candidates,
                  ∃ k : ℤ,
                    ∑ a ∈ completeRoughRowFiber
                        (yNat n) candidates label, x a = (k : ℝ)) ∧
                R.selectorTailCharge fixed ∣
                  certificate.prechargedTailTarget ∧
                (∀ q,
                  ∑ a ∈ candidates,
                      x a * (a.factorization q : ℝ) =
                    ((certificate.selectorTailTarget R fixed).factorization q :
                      ℝ)) ∧
                Disjoint fixed candidates ∧
                (∀ slot selected,
                  Disjoint fixed (R.exactificationState slot selected)) ∧
                (∀ slot selected,
                  Disjoint candidates
                    (R.exactificationState slot selected)) ∧
                Disjoint certificate.anchors fixed ∧
                Disjoint certificate.anchors candidates

private theorem eventually_bankPaper_f_le_upperEndpoint_of_capacityAtDepth
    {c : ℝ} {depth : ℕ} (hc : C0 < c) (hdepth : 201 ≤ depth)
    (hcapacity :
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
                centralTailProduct n (upperTailLength c n))
    (hcontinue :
      BankPaperCanonicalPostTangentContinuationAtDepth c depth) :
    ∀ᶠ n : ℕ in atTop,
      f n ≤ upperEndpoint n (upperTailLength c n) := by
  have hC0Pos : (0 : ℝ) < C0 := by
    norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
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

/-- Weakest depth-ordered connector supplied by the existing capacity
theorem: capacity first chooses one admissible `depth`; only then must a
post-tangent continuation be supplied for that depth. -/
theorem exists_depth_bankPaper_f_le_upperEndpoint_of_canonicalPostTangentContinuation
    {c : ℝ} (hc : C0 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      (BankPaperCanonicalPostTangentContinuationAtDepth c depth →
        ∀ᶠ n : ℕ in atTop,
          f n ≤ upperEndpoint n (upperTailLength c n)) := by
  obtain ⟨depth, hdepth, hcapacity⟩ :=
    exists_eventually_bankPaperPrechargedTailTarget hc
  refine ⟨depth, hdepth, fun hcontinue ↦ ?_⟩
  exact eventually_bankPaper_f_le_upperEndpoint_of_capacityAtDepth
    hc hdepth hcapacity hcontinue

/-- Eventual paper upper bound, conditional only on a continuation producing
the still-missing canonical post-tangent finite data for every actual
capacity-stage bank and guarded anchor certificate. -/
theorem eventually_bankPaper_f_le_upperEndpoint_of_canonicalPostTangentContinuation
    {c : ℝ} (hc : C0 < c)
    (hcontinuation :
      ∀ depth : ℕ, 201 ≤ depth →
        ∀ᶠ n : ℕ in atTop,
          ∀ (R : BankPaperRealization n
                (upperEndpoint n (upperTailLength c n)))
            (certificate : GuardedCentralAnchorCertificate c depth n
              R.anchorGuardLeftCore R.anchorGuardRightCore
              (R.centralChangedMarkers depth)),
            (hcombined :
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                    certificate.q * R.prechargeBaseStateProduct ∣
                centralTailProduct n (upperTailLength c n)) →
            (hbaseDvd :
              (baseBankFactors R.exactificationState).prod id ∣
                certificate.prechargedTailTarget) →
            (htargetTail :
              certificate.prechargedTailTarget *
                    centralAnchorDivisor n
                      (centralAnchorCutoff depth n) certificate.q =
                centralTailProduct n (upperTailLength c n)) →
            ∃ candidates : Finset ℕ, ∃ x : ℕ → ℝ,
              ∃ fixed : Finset ℕ,
                candidates ⊆
                    factorInterval n
                      (upperEndpoint n (upperTailLength c n)) ∧
                fixed ⊆
                    factorInterval n
                      (upperEndpoint n (upperTailLength c n)) ∧
                (∀ a ∈ candidates, 0 ≤ x a ∧ x a ≤ 1) ∧
                (∀ label ∈ completeRoughLabelSet (yNat n) candidates,
                  ∃ k : ℤ,
                    ∑ a ∈ completeRoughRowFiber
                        (yNat n) candidates label, x a = (k : ℝ)) ∧
                R.selectorTailCharge fixed ∣
                  certificate.prechargedTailTarget ∧
                (∀ q,
                  ∑ a ∈ candidates,
                      x a * (a.factorization q : ℝ) =
                    ((certificate.selectorTailTarget R fixed).factorization q :
                      ℝ)) ∧
                Disjoint fixed candidates ∧
                (∀ slot selected,
                  Disjoint fixed (R.exactificationState slot selected)) ∧
                (∀ slot selected,
                  Disjoint candidates
                    (R.exactificationState slot selected)) ∧
                Disjoint certificate.anchors fixed ∧
                Disjoint certificate.anchors candidates) :
    ∀ᶠ n : ℕ in atTop,
      f n ≤ upperEndpoint n (upperTailLength c n) := by
  obtain ⟨depth, hdepth, hbridge⟩ :=
    exists_depth_bankPaper_f_le_upperEndpoint_of_canonicalPostTangentContinuation
      hc
  apply hbridge
  simp only [BankPaperCanonicalPostTangentContinuationAtDepth]
  intro hcapacity
  have hcontinue := hcontinuation depth hdepth
  filter_upwards [hcapacity, hcontinue]
      with n hcapacityN hcontinueN
  obtain ⟨R, certificate, hcombined, hbaseDvd, htargetTail⟩ :=
    hcapacityN
  obtain ⟨candidates, x, fixed, hcandidates, hfixed, hx, hrowInt,
      hchargeDvd, hresidualValuation, hfixedCandidate, hfixedBank,
      hcandidateBank, hanchorsFixed, hanchorsCandidate⟩ :=
    hcontinueN R certificate hcombined hbaseDvd htargetTail
  refine ⟨R, certificate, hcombined, hbaseDvd, htargetTail, ?_⟩
  exact ⟨candidates, x, fixed, hcandidates, hfixed, hx, hrowInt,
    hchargeDvd, hresidualValuation, hfixedCandidate, hfixedBank,
    hcandidateBank, hanchorsFixed, hanchorsCandidate⟩

end

end Erdos390.WholePaper
