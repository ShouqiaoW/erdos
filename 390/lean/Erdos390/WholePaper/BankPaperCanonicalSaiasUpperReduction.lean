import Erdos390.WholePaper.BankPaperCanonicalUpperConstructionReduction
import Erdos390.WholePaper.RoughSaiasCanonicalRowBridge

/-!
# Forward canonical Saias-to-upper-construction reduction

The weighted HT--Saias development and the canonical upper-construction
terminal deliberately live on opposite sides of the still-missing selector
and tangent-flow argument.  Merely importing both modules would not connect
them.  This file gives the honest forward reduction.

For every active complete-rough row, the endpoint envelope and the three
displayed paper-scale ledger inequalities imply the literal raw-row quota
bound.  A separate selector handoff must turn that family of bounds into an
actual feasible, row-integral, valuation-exact post-tangent selector.  Only
then is the existing canonical upper-construction theorem invoked.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- Exact finite output required after the analytic row estimates have been
consumed by the still-separate selector and tangent-flow construction.  This
contains precisely the three `x`-dependent premises of
`bankPaper_isAdmissibleEndpoint_of_canonicalPostTangentCertificate`; all
geometric and collision premises stay outside the structure. -/
structure BankPaperCanonicalPostTangentOutput
    {c : ℝ} {depth n : ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (candidates fixed : Finset ℕ) where
  selector : ℕ → ℝ
  feasible : ∀ a ∈ candidates,
    0 ≤ selector a ∧ selector a ≤ 1
  rowIntegral :
    ∀ label ∈ completeRoughLabelSet (yNat n) candidates,
      ∃ k : ℤ,
        ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
          selector a = (k : ℝ)
  valuationCertificate : ∀ q,
    ((fixed.prod id *
        (baseBankFactors R.exactificationState).prod id).factorization q : ℝ) +
        ∑ a ∈ candidates,
          selector a * (a.factorization q : ℝ) =
      ((certificate.prechargedTailTarget).factorization q : ℝ)

/-- Honest conditional path from the literal HT--Saias endpoint envelope to
the canonical upper construction.

The conclusion retains the active-row estimate as its first component.  The
second component is obtained only through `hselector`: that premise is the
unproved selector/tangent-flow handoff which must consume the entire family
of active-row estimates and return the exact post-tangent finite output.
Rows with label greater than `n` are not discarded from the terminal: their
treatment, together with all-row integrality, remains part of that handoff.

The allowance is row-dependent.  In the paper one takes
`E row = C_W * (X_row / L^2 + 1)`.  Thus the three hypotheses `hmain`,
`htransition`, and `hhead` state exactly the remaining absorption tasks,
while `happrox` is the literal HT--Saias endpoint envelope. -/
theorem bankPaper_activeRoughRowQuota_and_isAdmissibleEndpoint_of_canonicalSaiasHandoff
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
        (upperEndpoint n (upperTailLength c n)) := by
  have hrowError :
      ∀ row : CanonicalCompleteRoughRow (yNat n)
          (roughRawCandidateSet n (upperTailLength c n) K),
        row.1 ≤ n →
          |roughCanonicalRawRowQuotaError W n
              (upperTailLength c n) K (yNat n) α β L row| ≤
            3 * E row := by
    intro row hrowN
    exact roughCanonicalRawRowQuotaError_abs_le_three_mul_paperAllowance
      hBV hWy row hrowN hKh happrox hY hy2
        (hlogs row hrowN) (hmain row hrowN)
        (htransition row hrowN) (hhead row hrowN)
  let output := hselector hrowError
  constructor
  · exact hrowError
  · exact bankPaper_isAdmissibleEndpoint_of_canonicalPostTangentCertificate
      R hdepth hnCutoff hprefix hyCutoff htail certificate
        (roughRawCandidateSet n (upperTailLength c n) K)
        output.selector fixed hcandidates hfixed output.feasible
        output.rowIntegral output.valuationCertificate hfixedCandidate
        hfixedBank hcandidateBank hanchorsFixed hanchorsCandidate

end

end Erdos390.WholePaper
