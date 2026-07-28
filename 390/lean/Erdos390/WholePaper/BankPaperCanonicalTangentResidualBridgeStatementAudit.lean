import Erdos390.WholePaper.BankPaperCanonicalTangentResidualBridge

/-! # Expanded statement audit for the canonical tangent residual bridge -/

open scoped BigOperators

namespace Erdos390.WholePaper.BankPaperCanonicalTangentResidualBridgeStatementAudit

open Erdos390.Full.ArithmeticModel

noncomputable section

example
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ)
    (p : ↥(primeBand n W)) :
    bankPaperCanonicalTangentPrimeLabel p = p.1 ∧
      bankPaperCanonicalSelectorValuationDeficit
          R certificate fixed candidates x p.1 =
        ((certificate.selectorTailTarget R fixed).factorization p.1 : ℝ) -
          ∑ a ∈ candidates, x a * (a.factorization p.1 : ℝ) ∧
      bankPaperCanonicalTangentResidual
          R certificate fixed candidates x p =
        ((certificate.selectorTailTarget R fixed).factorization p.1 : ℝ) -
          ∑ a ∈ candidates, x a * (a.factorization p.1 : ℝ) := by
  constructor
  · rfl
  constructor <;> rfl

example
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ)
    (hbalance :
      ∑ p ∈ primeBand n W,
        (((certificate.selectorTailTarget R fixed).factorization p : ℝ) -
          ∑ a ∈ candidates, x a * (a.factorization p : ℝ)) = 0) :
    (∑ p : ↥(primeBand n W),
      (((certificate.selectorTailTarget R fixed).factorization p.1 : ℝ) -
        ∑ a ∈ candidates, x a * (a.factorization p.1 : ℝ))) = 0 := by
  have hbalance' : BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
      R certificate fixed candidates x := by
    simpa only [BankPaperCanonicalPostRoundingPrimeBandBalance,
      bankPaperCanonicalSelectorValuationDeficit] using hbalance
  simpa only [bankPaperCanonicalTangentResidual,
    bankPaperCanonicalSelectorValuationDeficit] using
    sum_bankPaperCanonicalTangentResidual_eq_zero
      R certificate fixed candidates x hbalance'

example
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ)
    (hrowIntegral :
      ∀ label ∈ completeRoughLabelSet (yNat n) candidates,
        ∃ k : ℤ,
          ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
            x a = (k : ℝ))
    (pivot : ↥(primeBand n W))
    (hbalance :
      ∑ p ∈ primeBand n W,
        (((certificate.selectorTailTarget R fixed).factorization p : ℝ) -
          ∑ a ∈ candidates, x a * (a.factorization p : ℝ)) = 0)
    (hsupport : ∀ q, q.Prime → q ∉ primeBand n W →
      ((certificate.selectorTailTarget R fixed).factorization q : ℝ) -
          ∑ a ∈ candidates, x a * (a.factorization q : ℝ) = 0)
    (L sigma : ℝ) :
    (∀ label ∈ completeRoughLabelSet (yNat n) candidates,
      ∃ k : ℤ,
        ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
          x a = (k : ℝ)) ∧
      (∑ p : ↥(primeBand n W),
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates x p) = 0 ∧
      (∀ p : ↥(primeBand n W),
        tangentFlowDivergence
            (tangentStarFlow pivot
              (bankPaperCanonicalTangentResidual
                R certificate fixed candidates x)) p =
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates x p) ∧
      ∀ q,
        (∑ request : TangentSplitRequest
              (tangentStarPositiveEdges pivot
                (bankPaperCanonicalTangentResidual
                  R certificate fixed candidates x)) L sigma
              (tangentStarEdgeFlow pivot
                (bankPaperCanonicalTangentResidual
                  R certificate fixed candidates x)),
            tangentSplitRequestWeight request *
              (((tangentSplitRequestSource
                    (tangentStarEdgeSource
                      bankPaperCanonicalTangentPrimeLabel)
                    request).factorization q : ℝ) -
                ((tangentSplitRequestTarget
                    (tangentStarEdgeTarget
                      bankPaperCanonicalTangentPrimeLabel)
                    request).factorization q : ℝ))) =
          ((certificate.selectorTailTarget R fixed).factorization q : ℝ) -
            ∑ a ∈ candidates, x a * (a.factorization q : ℝ) := by
  have hrowIntegral' :
      BankPaperCanonicalSelectorRowIntegral n candidates x := by
    simpa only [BankPaperCanonicalSelectorRowIntegral] using hrowIntegral
  have hbalance' : BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
      R certificate fixed candidates x := by
    simpa only [BankPaperCanonicalPostRoundingPrimeBandBalance,
      bankPaperCanonicalSelectorValuationDeficit] using hbalance
  have hsupport' : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
      R certificate fixed candidates x := by
    simpa only [BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand,
      bankPaperCanonicalSelectorValuationDeficit] using hsupport
  simpa only [BankPaperCanonicalSelectorRowIntegral,
    bankPaperCanonicalSelectorValuationDeficit] using
    bankPaperCanonicalSelectorRowIntegral_and_tangentStarBoundary
      R certificate fixed candidates x hrowIntegral' pivot hbalance'
        hsupport' L sigma

/-! ## Supporting public API -/

#check BankPaperCanonicalTangentPrime
#check bankPaperCanonicalTangentPrimeLabel_injective
#check bankPaperCanonicalTangentPrimeLabel_prime
#check bankPaperCanonicalTangentPrimeLabel_le_yNat
#check bankPaperCanonicalSelectorValuationDeficit_eq_zero_of_not_prime
#check sum_bankPaperCanonicalTangentPrime_factorization
#check sum_bankPaperCanonicalTangentResidual_mul_factorization_eq_deficit
#check bankPaperCanonicalTangentStarSplitRequest_boundary_eq_selectorDeficit

end

end Erdos390.WholePaper.BankPaperCanonicalTangentResidualBridgeStatementAudit
