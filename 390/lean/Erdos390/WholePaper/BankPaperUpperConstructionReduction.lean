import Erdos390.WholePaper.BankPaperGuardedUpperProductAssembly
import Erdos390.WholePaper.BankPaperPrechargedTailTarget

/-!
# Reduction of the upper construction to the post-tangent certificate

At this interface all analytic and combinatorial selector work is represented
by its literal finite output: feasible weights, integral complete-signature
row sums, and an exact valuation identity after charging the fixed factors and
the actual precharged bank.  The theorem below performs every remaining
operation: floating rounding, concrete bank exactification, external-anchor
assembly, and conversion to an admissible endpoint.

This is a conditional reduction, not an existence theorem for those finite
outputs.  In particular, the bank realization, guarded anchor certificate,
feasible selector weights, integral row sums, exact valuation ledger, and
collision guards all remain inputs.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- A literal post-tangent certificate, together with the explicit collision
and interval guards, is sufficient for the complete discrete upper
construction at the paper endpoint. -/
theorem bankPaper_isAdmissibleEndpoint_of_postTangentCertificate
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
      (upperEndpoint n (upperTailLength c n)) := by
  have hMThree : upperEndpoint n (upperTailLength c n) ≤ 3 * n :=
    upperEndpoint_le_three_mul htail
  have hvaluePos : ∀ a, 0 < value a := by
    intro a
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp (hvalue a)).1
  have hvalueLe : ∀ a,
      value a ≤ upperEndpoint n (upperTailLength c n) := by
    intro a
    exact (Finset.mem_Ioc.mp (hvalue a)).2
  have hfixedPositive : ∀ a ∈ fixed, 0 < a := by
    intro a ha
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp (hfixed ha)).1
  obtain ⟨X, positive, negative, _, _, _, _, _, _, _, _, _, _, _, _,
      hproduct⟩ :=
    bankPaper_guarded_integral_exactification
      row rowSignature hrowSignatureInj value n
      (upperEndpoint n (upperTailLength c n))
      certificate.prechargedTailTarget x fixed R hMThree hvalueInj
      hvaluePos hvalueLe hx hrowInt hsignature hvaluationCertificate
      hfixedPositive hfixedCandidate hfixedBank hcandidateBank
      certificate.prechargedTailTarget_pos
  have hanchorsSelected :
      Disjoint certificate.anchors (selectedFactorSet value X) :=
    hanchorsCandidate.mono Finset.Subset.rfl
      (selectedFactorSet_subset_candidateUniverse value X)
  have hresidualProduct :
      (R.exactificationResidualFactorSet
        fixed positive negative value X).prod id =
          certificate.prechargedTailTarget := by
    simpa only [BankPaperRealization.exactificationResidualFactorSet] using
      hproduct
  exact R.isAdmissibleEndpoint_of_exactificationResidual
    hdepth hnCutoff hprefix hyCutoff certificate fixed hfixed
      positive negative value X hvalue hanchorsFixed hanchorsSelected
      hresidualProduct
      certificate.prechargedTailTarget_mul_centralAnchorDivisor

end

end Erdos390.WholePaper
