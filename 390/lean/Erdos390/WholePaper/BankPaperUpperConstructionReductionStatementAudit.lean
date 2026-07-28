import Erdos390.WholePaper.BankPaperUpperConstructionReduction

/-! # Expanded statement audit for the upper-construction reduction -/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

example
    {A Row : Type*} [Fintype A] [Fintype Row]
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
    (row : A → Row) (rowSignature : Row → ℕ →₀ ℕ)
    (hrowSignatureInj : Function.Injective rowSignature)
    (value : A → ℕ) (x : A → ℝ) (fixed : Finset ℕ)
    (hvalueInj : Function.Injective value)
    (hvalue : ∀ a, value a ∈
      factorInterval n (upperEndpoint n (upperTailLength c n)))
    (hfixed : fixed ⊆
      factorInterval n (upperEndpoint n (upperTailLength c n)))
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hrowInt : ∀ r, ∃ k : ℤ,
      ∑ a ∈ rowSet row r, x a = (k : ℝ))
    (hsignature : ∀ a,
      completeRoughSignature (yNat n) (value a) =
        rowSignature (row a))
    (hvaluationCertificate : ∀ q,
      ((fixed.prod id *
          (baseBankFactors R.exactificationState).prod id).factorization q : ℝ) +
          ∑ a, x a * ((value a).factorization q : ℝ) =
        ((certificate.prechargedTailTarget).factorization q : ℝ))
    (hfixedCandidate : Disjoint fixed (Finset.univ.image value))
    (hfixedBank : ∀ slot selected,
      Disjoint fixed (R.exactificationState slot selected))
    (hcandidateBank : ∀ slot selected,
      Disjoint (Finset.univ.image value)
        (R.exactificationState slot selected))
    (hanchorsFixed : Disjoint certificate.anchors fixed)
    (hanchorsCandidate :
      Disjoint certificate.anchors (Finset.univ.image value)) :
    IsAdmissibleEndpoint n
      (upperEndpoint n (upperTailLength c n)) :=
  bankPaper_isAdmissibleEndpoint_of_postTangentCertificate
    R hdepth hnCutoff hprefix hyCutoff htail certificate row rowSignature
      hrowSignatureInj value x fixed hvalueInj hvalue hfixed hx hrowInt
      hsignature hvaluationCertificate hfixedCandidate hfixedBank
      hcandidateBank hanchorsFixed hanchorsCandidate

end

end Erdos390.WholePaper
