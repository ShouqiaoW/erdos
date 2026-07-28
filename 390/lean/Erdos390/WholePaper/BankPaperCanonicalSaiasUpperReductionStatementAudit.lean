import Erdos390.WholePaper.BankPaperCanonicalSaiasUpperReduction

/-!
Statement audit for the forward Saias-to-upper-construction reduction.

The audited theorem returns both the literal active-row quota bound and the
admissible endpoint.  Its hypotheses visibly retain the HT--Saias endpoint
envelope, the rowwise main/transition/head allowances, and a separate
selector handoff consuming those row bounds.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

example
    {c : ℝ} {depth n : ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (candidates fixed : Finset ℕ)
    (output : BankPaperCanonicalPostTangentOutput R certificate
      candidates fixed) :
    ∃ selector : ℕ → ℝ,
      (∀ a ∈ candidates,
        0 ≤ selector a ∧ selector a ≤ 1) ∧
      (∀ label ∈ completeRoughLabelSet (yNat n) candidates,
        ∃ k : ℤ,
          ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
            selector a = (k : ℝ)) ∧
      ∀ q,
        ((fixed.prod id *
            (baseBankFactors R.exactificationState).prod id).factorization q :
              ℝ) +
            ∑ a ∈ candidates,
              selector a * (a.factorization q : ℝ) =
          ((certificate.prechargedTailTarget).factorization q : ℝ) :=
  ⟨output.selector, output.feasible, output.rowIntegral,
    output.valuationCertificate⟩

example
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ W K : ℕ}
    {α β L : ℝ} {c : ℝ} {depth n : ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hprefix : 2 * depth + 1 ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (htail : upperTailLength c n ≤ n)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset ℕ)
    (E : CanonicalCompleteRoughRow (yNat n)
      (roughRawCandidateSet n (upperTailLength c n) K) → ℝ)
    (hWy : W ≤ yNat n)
    (hKh : K * upperTailLength c n ≤ n)
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ yNat n) (hy2 : 2 ≤ yNat n)
    (hlogs : ∀ row : CanonicalCompleteRoughRow (yNat n)
        (roughRawCandidateSet n (upperTailLength c n) K),
      row.1 ≤ n → ∀ i : Fin 4,
        Real.log (roughPhysicalNatEndpoint
            ((2 * n + upperTailLength c n) / row.1)
            ((2 * n) / row.1)
            ((2 * n - K * upperTailLength c n) / row.1)
            (n / row.1) i : ℝ) ≤
          5 * Real.log (yNat n : ℝ))
    (hmain : ∀ row : CanonicalCompleteRoughRow (yNat n)
        (roughRawCandidateSet n (upperTailLength c n) K),
      row.1 ≤ n →
        roughPhysicalDickmanTransitionLedger
            (roughHeadDensity W) α β L
            ((2 * n + upperTailLength c n) / row.1)
            ((2 * n) / row.1)
            ((2 * n - K * upperTailLength c n) / row.1)
            (n / row.1) (yNat n) ≤ E row)
    (htransition : ∀ row : CanonicalCompleteRoughRow (yNat n)
        (roughRawCandidateSet n (upperTailLength c n) K),
      row.1 ≤ n →
        roughPhysicalSaiasTransitionBudget eta
            (roughHeadDensity W) α β L
            ((2 * n + upperTailLength c n) / row.1)
            ((2 * n) / row.1)
            ((2 * n - K * upperTailLength c n) / row.1)
            (n / row.1) (yNat n) ≤ E row)
    (hhead : ∀ row : CanonicalCompleteRoughRow (yNat n)
        (roughRawCandidateSet n (upperTailLength c n) K),
      row.1 ≤ n →
        roughCanonicalFixedHeadShiftLedger W n
            (upperTailLength c n) K (yNat n) α β L row ≤ E row)
    (hselector :
      (∀ row : CanonicalCompleteRoughRow (yNat n)
          (roughRawCandidateSet n (upperTailLength c n) K),
        row.1 ≤ n →
          |roughCanonicalRawRowQuotaError W n
              (upperTailLength c n) K (yNat n) α β L row| ≤
            3 * E row) →
        BankPaperCanonicalPostTangentOutput R certificate
          (roughRawCandidateSet n (upperTailLength c n) K) fixed)
    (hcandidates : roughRawCandidateSet n (upperTailLength c n) K ⊆
      factorInterval n (upperEndpoint n (upperTailLength c n)))
    (hfixed : fixed ⊆
      factorInterval n (upperEndpoint n (upperTailLength c n)))
    (hfixedCandidate : Disjoint fixed
      (roughRawCandidateSet n (upperTailLength c n) K))
    (hfixedBank : ∀ slot selected,
      Disjoint fixed (R.exactificationState slot selected))
    (hcandidateBank : ∀ slot selected,
      Disjoint (roughRawCandidateSet n (upperTailLength c n) K)
        (R.exactificationState slot selected))
    (hanchorsFixed : Disjoint certificate.anchors fixed)
    (hanchorsCandidate : Disjoint certificate.anchors
      (roughRawCandidateSet n (upperTailLength c n) K)) :
    (∀ row : CanonicalCompleteRoughRow (yNat n)
        (roughRawCandidateSet n (upperTailLength c n) K),
      row.1 ≤ n →
        |roughCanonicalRawRowQuotaError W n
            (upperTailLength c n) K (yNat n) α β L row| ≤
          3 * E row) ∧
      IsAdmissibleEndpoint n
        (upperEndpoint n (upperTailLength c n)) :=
  bankPaper_activeRoughRowQuota_and_isAdmissibleEndpoint_of_canonicalSaiasHandoff
    hBV R hdepth hnCutoff hprefix hyCutoff htail certificate fixed E hWy hKh
      happrox hY hy2 hlogs hmain htransition hhead hselector hcandidates
      hfixed hfixedCandidate hfixedBank hcandidateBank hanchorsFixed
      hanchorsCandidate

end

end Erdos390.WholePaper
