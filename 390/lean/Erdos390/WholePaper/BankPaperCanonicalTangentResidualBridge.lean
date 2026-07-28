import Erdos390.WholePaper.BankPaperCanonicalSaiasUpperReduction
import Erdos390.WholePaper.BankPaperSelectorTailTarget
import Erdos390.WholePaper.TangentStarSplitRequestBridge

/-!
# Literal canonical residual for the selector-to-tangent handoff

The canonical Saias reduction currently stops at a selector continuation: it
does not yet construct the pre-tangent rounded selector.  This file removes
the *generic residual* ambiguity without asserting that missing construction.

For a supplied selector `x`, the residual coordinate at a medium prime is
defined literally as

`valuation(selectorTailTarget) - valuation(x)`.

The two remaining selector inputs are named explicitly.  The post-rounding
prime-band balance says that these coordinates sum to zero, while prime-band
support says that the selector already has the target valuation at every
prime outside the band.  Neither fact follows merely from
`roughCanonicalRawRowQuotaError`: that quantity is a complete-rough row quota
error, not a prime-coordinate valuation identity.

From those inputs, the finite prime residual has zero total mass and its
positive star split requests have exactly the valuation deficit required by
`tangentUpdate_valuation_eq_target`.  The final theorem also retains the
all-row integrality input verbatim.  It does not claim that clean common
multipliers, feasibility of the tangent update, or the selector itself have
already been constructed.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Literal selector deficit and its finite prime domain -/

/-- The actual finite vertex type used by the canonical tangent star: the
natural primes in the paper band `W < p <= yNat n`. -/
abbrev BankPaperCanonicalTangentPrime (n W : ℕ) :=
  ↥(primeBand n W)

/-- The natural-number label of a canonical tangent vertex. -/
def bankPaperCanonicalTangentPrimeLabel
    {n W : ℕ} (p : BankPaperCanonicalTangentPrime n W) : ℕ :=
  p.1

/-- The literal valuation still missing from a supplied selector: target
valuation minus its current weighted valuation. -/
def bankPaperCanonicalSelectorValuationDeficit
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ) (q : ℕ) : ℝ :=
  ((certificate.selectorTailTarget R fixed).factorization q : ℝ) -
    ∑ a ∈ candidates, x a * (a.factorization q : ℝ)

/-- Restriction of the literal selector deficit to the finite medium-prime
vertex type consumed by the star transport. -/
def bankPaperCanonicalTangentResidual
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ)
    (p : BankPaperCanonicalTangentPrime n W) : ℝ :=
  bankPaperCanonicalSelectorValuationDeficit
    R certificate fixed candidates x p.1

/-- Exact post-rounding balance needed from the missing selector stage.  It
is deliberately an input proposition, not a consequence attributed to the
analytic complete-rough row quota error. -/
def BankPaperCanonicalPostRoundingPrimeBandBalance
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ) : Prop :=
  ∑ p ∈ primeBand n W,
      bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed candidates x p = 0

/-- Outside the tangent prime band, a prime valuation must already agree
with the residual selector target.  Non-prime coordinates vanish
automatically and therefore are not included in this premise. -/
def BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ) : Prop :=
  ∀ q, q.Prime → q ∉ primeBand n W →
    bankPaperCanonicalSelectorValuationDeficit
      R certificate fixed candidates x q = 0

/-- Literal all-complete-rough-row integrality input expected from the
rounded selector. -/
def BankPaperCanonicalSelectorRowIntegral
    (n : ℕ) (candidates : Finset ℕ) (x : ℕ → ℝ) : Prop :=
  ∀ label ∈ completeRoughLabelSet (yNat n) candidates,
    ∃ k : ℤ,
      ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
        x a = (k : ℝ)

/-! ## Prime-label geometry and exact residual algebra -/

/-- The subtype-to-natural prime label map is injective. -/
theorem bankPaperCanonicalTangentPrimeLabel_injective
    {n W : ℕ} :
    Function.Injective
      (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W)) := by
  intro p q hpq
  exact Subtype.ext hpq

/-- Every canonical tangent label is prime. -/
theorem bankPaperCanonicalTangentPrimeLabel_prime
    {n W : ℕ} (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p).Prime := by
  exact prime_of_mem_primeBand p.2

/-- Every canonical tangent label lies below the paper smooth cutoff. -/
theorem bankPaperCanonicalTangentPrimeLabel_le_yNat
    {n W : ℕ} (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalTangentPrimeLabel p ≤ yNat n := by
  exact le_yNat_of_mem_primeBand p.2

/-- At a non-prime coordinate, both the target and every candidate
factorization vanish. -/
theorem bankPaperCanonicalSelectorValuationDeficit_eq_zero_of_not_prime
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ) {q : ℕ}
    (hq : ¬q.Prime) :
    bankPaperCanonicalSelectorValuationDeficit
      R certificate fixed candidates x q = 0 := by
  simp [bankPaperCanonicalSelectorValuationDeficit,
    Nat.factorization_eq_zero_of_not_prime _ hq]

/-- The explicit post-rounding band-balance input is exactly zero total mass
on the finite tangent vertex type. -/
theorem sum_bankPaperCanonicalTangentResidual_eq_zero
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ)
    (hbalance : BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
      R certificate fixed candidates x) :
    (∑ p : BankPaperCanonicalTangentPrime n W,
      bankPaperCanonicalTangentResidual
        R certificate fixed candidates x p) = 0 := by
  calc
    (∑ p : BankPaperCanonicalTangentPrime n W,
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates x p) =
        ∑ p ∈ primeBand n W,
          bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates x p := by
      simpa only [bankPaperCanonicalTangentResidual] using
        (Finset.sum_subtype (primeBand n W) (fun _p ↦ Iff.rfl)
          (fun p ↦ bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates x p)).symm
    _ = 0 := hbalance

/-- Prime labels form the standard factorization basis on the finite band.
This statement is independent of the selector and is useful for exposing
the exact support requirement. -/
theorem sum_bankPaperCanonicalTangentPrime_factorization
    {n W : ℕ} (coefficient : ℕ → ℝ) (q : ℕ) :
    (∑ p : BankPaperCanonicalTangentPrime n W,
        coefficient p.1 *
          ((bankPaperCanonicalTangentPrimeLabel p).factorization q : ℝ)) =
      if q ∈ primeBand n W then coefficient q else 0 := by
  calc
    (∑ p : BankPaperCanonicalTangentPrime n W,
        coefficient p.1 *
          ((bankPaperCanonicalTangentPrimeLabel p).factorization q : ℝ)) =
        ∑ p ∈ primeBand n W,
          coefficient p * (p.factorization q : ℝ) := by
      simpa only [bankPaperCanonicalTangentPrimeLabel] using
        (Finset.sum_subtype (primeBand n W) (fun _p ↦ Iff.rfl)
          (fun p ↦ coefficient p * (p.factorization q : ℝ))).symm
    _ = if q ∈ primeBand n W then coefficient q else 0 := by
      by_cases hq : q ∈ primeBand n W
      · rw [if_pos hq, Finset.sum_eq_single q]
        · simp only [(prime_of_mem_primeBand hq).factorization_self,
            Nat.cast_one, mul_one]
        · intro p hp hpq
          have hpPrime : p.Prime := prime_of_mem_primeBand hp
          have hfactorization : p.factorization q = 0 := by
            by_contra hnonzero
            exact hpq (hpPrime.eq_of_factorization_pos hnonzero)
          simp only [hfactorization, Nat.cast_zero, mul_zero]
        · exact fun hqNotMem ↦ (hqNotMem hq).elim
      · rw [if_neg hq]
        apply Finset.sum_eq_zero
        intro p hp
        have hpPrime : p.Prime := prime_of_mem_primeBand hp
        have hpq : p ≠ q := by
          intro hpq
          apply hq
          simpa only [hpq] using hp
        have hfactorization : p.factorization q = 0 := by
          by_contra hnonzero
          exact hpq (hpPrime.eq_of_factorization_pos hnonzero)
        simp only [hfactorization, Nat.cast_zero, mul_zero]

/-- The finite prime residual expands to the full selector valuation deficit.
The only non-definitional input is exact agreement outside the prime band. -/
theorem sum_bankPaperCanonicalTangentResidual_mul_factorization_eq_deficit
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ)
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
      R certificate fixed candidates x) (q : ℕ) :
    (∑ p : BankPaperCanonicalTangentPrime n W,
        bankPaperCanonicalTangentResidual
            R certificate fixed candidates x p *
          ((bankPaperCanonicalTangentPrimeLabel p).factorization q : ℝ)) =
      bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed candidates x q := by
  calc
    (∑ p : BankPaperCanonicalTangentPrime n W,
        bankPaperCanonicalTangentResidual
            R certificate fixed candidates x p *
          ((bankPaperCanonicalTangentPrimeLabel p).factorization q : ℝ)) =
        if q ∈ primeBand n W then
          bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates x q
        else 0 := by
      simpa only [bankPaperCanonicalTangentResidual] using
        sum_bankPaperCanonicalTangentPrime_factorization
          (n := n) (W := W)
          (fun p ↦ bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates x p) q
    _ = bankPaperCanonicalSelectorValuationDeficit
          R certificate fixed candidates x q := by
      by_cases hqBand : q ∈ primeBand n W
      · rw [if_pos hqBand]
      · rw [if_neg hqBand]
        by_cases hqPrime : q.Prime
        · exact (hsupport q hqPrime hqBand).symm
        · exact (bankPaperCanonicalSelectorValuationDeficit_eq_zero_of_not_prime
            R certificate fixed candidates x hqPrime).symm

/-! ## Instantiation of the star split-request boundary -/

/-- Literal canonical instantiation of the generic star bridge.  Its first
component is the exact divergence at every prime vertex; its second component
is the target-minus-selector valuation required by the tangent update. -/
theorem bankPaperCanonicalTangentStarSplitRequest_boundary_eq_selectorDeficit
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ)
    (pivot : BankPaperCanonicalTangentPrime n W)
    (hbalance : BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
      R certificate fixed candidates x)
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
      R certificate fixed candidates x)
    (L sigma : ℝ) :
    (∀ p : BankPaperCanonicalTangentPrime n W,
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
          bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates x q := by
  have hsum :
      (∑ p : BankPaperCanonicalTangentPrime n W,
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates x p) = 0 :=
    sum_bankPaperCanonicalTangentResidual_eq_zero
      R certificate fixed candidates x hbalance
  constructor
  · exact tangentStarFlow_divergence_eq hsum
  · intro q
    calc
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
          ∑ p : BankPaperCanonicalTangentPrime n W,
            bankPaperCanonicalTangentResidual
                R certificate fixed candidates x p *
              ((bankPaperCanonicalTangentPrimeLabel p).factorization q : ℝ) :=
        tangentStarSplitRequest_factorizationBoundary_eq_residual
          hsum bankPaperCanonicalTangentPrimeLabel L sigma q
      _ = bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates x q :=
        sum_bankPaperCanonicalTangentResidual_mul_factorization_eq_deficit
          R certificate fixed candidates x hsupport q

/-- Minimal honest canonical selector-to-star boundary package.  The
row-integrality premise is retained unchanged as a separate conjunct because
the downstream selector stage needs it; the residual algebra neither derives
nor consumes it. -/
theorem bankPaperCanonicalSelectorRowIntegral_and_tangentStarBoundary
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ)
    (hrowIntegral : BankPaperCanonicalSelectorRowIntegral n candidates x)
    (pivot : BankPaperCanonicalTangentPrime n W)
    (hbalance : BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
      R certificate fixed candidates x)
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
      R certificate fixed candidates x)
    (L sigma : ℝ) :
    BankPaperCanonicalSelectorRowIntegral n candidates x ∧
      (∑ p : BankPaperCanonicalTangentPrime n W,
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates x p) = 0 ∧
      (∀ p : BankPaperCanonicalTangentPrime n W,
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
          bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates x q := by
  have hsum := sum_bankPaperCanonicalTangentResidual_eq_zero
    R certificate fixed candidates x hbalance
  have hstar :=
    bankPaperCanonicalTangentStarSplitRequest_boundary_eq_selectorDeficit
      R certificate fixed candidates x pivot hbalance hsupport L sigma
  exact ⟨hrowIntegral, hsum, hstar.1, hstar.2⟩

end

end Erdos390.WholePaper
