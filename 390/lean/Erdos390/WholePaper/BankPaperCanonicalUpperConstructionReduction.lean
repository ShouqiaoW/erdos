import Erdos390.WholePaper.BankPaperUpperConstructionReduction
import Erdos390.WholePaper.CanonicalCompleteRoughRows

/-!
# Canonical complete-rough reduction for the upper construction

The generic post-tangent reduction permits an arbitrary finite coordinate
type and an arbitrary injectively labelled row type.  For the paper
construction there is a literal choice: the coordinates are the elements of
the finite candidate set, and the rows are the complete rough labels actually
attained on that set.

This specialization exposes only the data that still have mathematical
content.  Candidate values are subtype values, row signatures are
factorizations of attained complete rough labels, and row integrality is
stated directly on the ambient complete-rough fibers.  The value and row
injectivity conditions and the complete-signature compatibility are supplied
by the canonical finite construction.  Analytic row estimates, selector
existence, row integrality, and the exact valuation ledger are deliberately
not imported as if they proved this conditional terminal: the latter two
remain explicit hypotheses below.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- A post-tangent certificate on a literal finite candidate set, with
integer sums on every attained complete-rough-label fiber, suffices for the
paper's complete discrete upper construction.  All fixed-factor, valuation,
bank-collision, and anchor-collision hypotheses remain explicit. -/
theorem bankPaper_isAdmissibleEndpoint_of_canonicalPostTangentCertificate
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
      (upperEndpoint n (upperTailLength c n)) := by
  classical
  have hcandidateUniverse :
      Finset.univ.image
          (canonicalCompleteRoughCandidateValue candidates) =
        candidates := by
    ext value
    constructor
    · intro hvalue
      obtain ⟨candidate, _hmem, hcandidate⟩ :=
        Finset.mem_image.mp hvalue
      rw [← hcandidate]
      exact candidate.property
    · intro hvalue
      apply Finset.mem_image.mpr
      refine ⟨⟨value, hvalue⟩, Finset.mem_univ _, ?_⟩
      rfl
  have hcandidateValue :
      ∀ a : CompleteRoughCandidate candidates,
        canonicalCompleteRoughCandidateValue candidates a ∈
          factorInterval n
            (upperEndpoint n (upperTailLength c n)) :=
    fun a ↦
      canonicalCompleteRoughCandidateValue_mem_factorInterval
        hcandidates a
  have hxCanonical :
      ∀ a : CompleteRoughCandidate candidates,
        0 ≤ x (canonicalCompleteRoughCandidateValue candidates a) ∧
          x (canonicalCompleteRoughCandidateValue candidates a) ≤ 1 := by
    intro a
    simpa only [canonicalCompleteRoughCandidateValue] using
      hx a.1 a.2
  have hrowIntCanonical :
      ∀ row : CanonicalCompleteRoughRow (yNat n) candidates,
        ∃ k : ℤ,
          ∑ a ∈ rowSet
              (canonicalCompleteRoughRow (yNat n) candidates) row,
            x (canonicalCompleteRoughCandidateValue candidates a) =
              (k : ℝ) :=
    canonicalCompleteRough_rowSums_integer_of_rowFiberSums_integer
      (yNat n) candidates x hrowInt
  have hvaluationCanonical : ∀ q,
      ((fixed.prod id *
          (baseBankFactors R.exactificationState).prod id).factorization q : ℝ) +
          ∑ a : CompleteRoughCandidate candidates,
            x (canonicalCompleteRoughCandidateValue candidates a) *
              ((canonicalCompleteRoughCandidateValue candidates a).factorization q : ℝ) =
        ((certificate.prechargedTailTarget).factorization q : ℝ) := by
    intro q
    have hsum :
        (∑ a : CompleteRoughCandidate candidates,
          x (canonicalCompleteRoughCandidateValue candidates a) *
            ((canonicalCompleteRoughCandidateValue candidates a).factorization q : ℝ)) =
          ∑ a ∈ candidates, x a * (a.factorization q : ℝ) := by
      simpa only [Finset.univ_eq_attach,
        canonicalCompleteRoughCandidateValue] using
          (Finset.sum_attach candidates
            (fun a ↦ x a * (a.factorization q : ℝ)))
    rw [hsum]
    exact hvaluationCertificate q
  have hfixedCandidateCanonical :
      Disjoint fixed
        (Finset.univ.image
          (canonicalCompleteRoughCandidateValue candidates)) := by
    simpa only [hcandidateUniverse] using hfixedCandidate
  have hcandidateBankCanonical : ∀ slot selected,
      Disjoint
        (Finset.univ.image
          (canonicalCompleteRoughCandidateValue candidates))
        (R.exactificationState slot selected) := by
    intro slot selected
    simpa only [hcandidateUniverse] using
      hcandidateBank slot selected
  have hanchorsCandidateCanonical :
      Disjoint certificate.anchors
        (Finset.univ.image
          (canonicalCompleteRoughCandidateValue candidates)) := by
    simpa only [hcandidateUniverse] using hanchorsCandidate
  exact bankPaper_isAdmissibleEndpoint_of_postTangentCertificate
    R hdepth hnCutoff hprefix hyCutoff htail certificate
      (canonicalCompleteRoughRow (yNat n) candidates)
      (canonicalCompleteRoughRowSignature (yNat n) candidates)
      (canonicalCompleteRoughRowSignature_injective (yNat n) candidates)
      (canonicalCompleteRoughCandidateValue candidates)
      (fun a ↦ x (canonicalCompleteRoughCandidateValue candidates a)) fixed
      (canonicalCompleteRoughCandidateValue_injective candidates)
      hcandidateValue hfixed hxCanonical hrowIntCanonical
      (completeRoughSignature_eq_canonicalCompleteRoughRowSignature
        (yNat n) candidates)
      hvaluationCanonical hfixedCandidateCanonical hfixedBank
      hcandidateBankCanonical hanchorsFixed hanchorsCandidateCanonical

end

end Erdos390.WholePaper
