import Erdos390.WholePaper.BankPaperFixedExceptionalValuationFibers

/-!
# Expanded statement audit for the fixed exceptional valuation fibres

These examples keep the literal exceptional set, canonical complete
smooth/rough decomposition, physical divided interval, and Selberg constants
visible at the public interface.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

example (n h : ℕ) (deltaStar : ℝ) :
    paperExceptionalSmoothParts n h deltaStar =
      (paperExceptionalUpperFactors n h deltaStar).image
        (completeSmoothPart (yNat n)) :=
  rfl

example (n h : ℕ) (deltaStar : ℝ) (b : ℕ) :
    paperExceptionalSmoothFiber n h deltaStar b =
      (paperExceptionalUpperFactors n h deltaStar).filter
        (fun a ↦ completeSmoothPart (yNat n) a = b) :=
  rfl

example (n h y b : ℕ) :
    paperExceptionalRoughCandidates n h y b =
      reducedResidueIoc (roughHeadModulus y)
        ((2 * n) / b) ((2 * n + h) / b) :=
  rfl

example {n h b : ℕ} {deltaStar : ℝ} :
    b ∈ paperExceptionalSmoothParts n h deltaStar ↔
      ∃ a ∈ paperExceptionalUpperFactors n h deltaStar,
        completeSmoothPart (yNat n) a = b :=
  mem_paperExceptionalSmoothParts

example {n h a b : ℕ} {deltaStar : ℝ} :
    a ∈ paperExceptionalSmoothFiber n h deltaStar b ↔
      a ∈ paperExceptionalUpperFactors n h deltaStar ∧
        completeSmoothPart (yNat n) a = b :=
  mem_paperExceptionalSmoothFiber

example {n h y b r : ℕ} :
    r ∈ paperExceptionalRoughCandidates n h y b ↔
      (2 * n) / b < r ∧ r ≤ (2 * n + h) / b ∧
        Nat.Coprime r (roughHeadModulus y) :=
  mem_paperExceptionalRoughCandidates

example {n h a : ℕ} {deltaStar : ℝ}
    (ha : a ∈ paperExceptionalUpperFactors n h deltaStar) :
    0 < a :=
  paperExceptionalUpperFactors_pos ha

example {n h p : ℕ} {deltaStar : ℝ} (hp : p ≤ yNat n) :
    ((paperExceptionalUpperFactors n h deltaStar).prod id).factorization p =
      ∑ b ∈ paperExceptionalSmoothParts n h deltaStar,
        b.factorization p *
          (paperExceptionalSmoothFiber n h deltaStar b).card :=
  paperExceptionalUpperFactors_prod_factorization_eq_smoothFiberSum hp

example {n h b : ℕ} {deltaStar : ℝ} :
    Set.InjOn (completeRoughLabel (yNat n))
      (paperExceptionalSmoothFiber n h deltaStar b : Set ℕ) :=
  completeRoughLabel_injOn_paperExceptionalSmoothFiber

example {n h a b : ℕ} {deltaStar : ℝ}
    (ha : a ∈ paperExceptionalSmoothFiber n h deltaStar b) :
    completeRoughLabel (yNat n) a ∈
      reducedResidueIoc (roughHeadModulus (yNat n))
        ((2 * n) / b) ((2 * n + h) / b) := by
  simpa only [paperExceptionalRoughCandidates] using
    (completeRoughLabel_mem_paperExceptionalRoughCandidates ha)

example {n h b : ℕ} {deltaStar : ℝ} :
    (paperExceptionalSmoothFiber n h deltaStar b).card ≤
      (reducedResidueIoc (roughHeadModulus (yNat n))
        ((2 * n) / b) ((2 * n + h) / b)).card := by
  simpa only [paperExceptionalRoughCandidates] using
    (paperExceptionalSmoothFiber_card_le_roughCandidates
      (n := n) (h := h) (b := b) (deltaStar := deltaStar))

example {n h p : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    {deltaStar : ℝ} (hp : p ≤ yNat n) :
    ((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p ≤
      ∑ b ∈ paperExceptionalSmoothParts n h deltaStar,
        b.factorization p *
          (paperExceptionalSmoothFiber n h deltaStar b).card :=
  R.paperFixedExceptionalFactors_prod_factorization_le_smoothFiberSum hp

example {n h p : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    {deltaStar : ℝ} (hp : p ≤ yNat n) :
    ((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p ≤
      ∑ b ∈ paperExceptionalSmoothParts n h deltaStar,
        b.factorization p *
          (reducedResidueIoc (roughHeadModulus (yNat n))
            ((2 * n) / b) ((2 * n + h) / b)).card := by
  simpa only [paperExceptionalRoughCandidates] using
    R.paperFixedExceptionalFactors_prod_factorization_le_roughCandidateSum hp

example :
    ∀ᶠ y : ℕ in atTop, ∀ n h b : ℕ,
      ((reducedResidueIoc (roughHeadModulus y)
        ((2 * n) / b) ((2 * n + h) / b)).card : ℝ) ≤
        ((((2 * n + h) / b - (2 * n) / b : ℕ) : ℝ) *
            (tangentSelbergCanonicalMainConstant /
              Real.log (y : ℝ)) +
          tangentSelbergCanonicalLambdaConstant ^ 2 * (y : ℝ) ^ 4 /
            Real.log (y : ℝ) ^ 2) := by
  simpa only [paperExceptionalRoughCandidates] using
    eventually_paperExceptionalRoughCandidates_card_le_canonicalLambdaSquare

example :
    ∀ᶠ n : ℕ in atTop, ∀ h b : ℕ, ∀ deltaStar : ℝ,
      ((paperExceptionalSmoothFiber n h deltaStar b).card : ℝ) ≤
        ((((2 * n + h) / b - (2 * n) / b : ℕ) : ℝ) *
            (tangentSelbergCanonicalMainConstant /
              Real.log (yNat n : ℝ)) +
          tangentSelbergCanonicalLambdaConstant ^ 2 *
              (yNat n : ℝ) ^ 4 /
            Real.log (yNat n : ℝ) ^ 2) :=
  eventually_paperExceptionalSmoothFiber_card_le_canonicalLambdaSquare

end

end Erdos390.WholePaper
