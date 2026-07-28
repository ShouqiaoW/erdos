import Erdos390.WholePaper.BankPaperCanonicalUpperConstructionReduction

/-! # Expanded statement audit for the canonical upper reduction -/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

example
    {c : ℝ} {depth n : ℕ}
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
    (candidates : Finset ℕ) (x : ℕ → ℝ) (fixed : Finset ℕ)
    (hcandidates : candidates ⊆
      factorInterval n (upperEndpoint n (upperTailLength c n)))
    (hfixed : fixed ⊆
      factorInterval n (upperEndpoint n (upperTailLength c n)))
    (hx : ∀ a ∈ candidates, 0 ≤ x a ∧ x a ≤ 1)
    (hrowInt : ∀ label ∈ completeRoughLabelSet (yNat n) candidates,
      ∃ k : ℤ,
        ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
          x a = (k : ℝ))
    (hvaluationCertificate : ∀ q,
      ((fixed.prod id *
          (baseBankFactors R.exactificationState).prod id).factorization q : ℝ) +
          ∑ a ∈ candidates, x a * (a.factorization q : ℝ) =
        ((certificate.prechargedTailTarget).factorization q : ℝ))
    (hfixedCandidate : Disjoint fixed candidates)
    (hfixedBank : ∀ slot selected,
      Disjoint fixed (R.exactificationState slot selected))
    (hcandidateBank : ∀ slot selected,
      Disjoint candidates (R.exactificationState slot selected))
    (hanchorsFixed : Disjoint certificate.anchors fixed)
    (hanchorsCandidate : Disjoint certificate.anchors candidates) :
    IsAdmissibleEndpoint n
      (upperEndpoint n (upperTailLength c n)) :=
  bankPaper_isAdmissibleEndpoint_of_canonicalPostTangentCertificate
    R hdepth hnCutoff hprefix hyCutoff htail certificate candidates x fixed
      hcandidates hfixed hx hrowInt hvaluationCertificate hfixedCandidate
      hfixedBank hcandidateBank hanchorsFixed hanchorsCandidate

end

end Erdos390.WholePaper
