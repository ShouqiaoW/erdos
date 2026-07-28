import Erdos390.WholePaper.GuardedIntegralExactification

/-!
# Literal expanded statement audit for guarded integral exactification

The audit repeats the concrete bank-state type, every capacity/change/count
and guard input, and every product, valuation, rough-count, and disjointness
output.  No result structure abbreviates the terminal claim.
-/

open scoped BigOperators

namespace Erdos390.WholePaper.GuardedIntegralExactificationStatementAudit

noncomputable section

example
    {A R : Type*} [Fintype A] [Fintype R]
    (row : A → R) (rowSignature : R → ℕ →₀ ℕ)
    (hrowSignatureInj : Function.Injective rowSignature)
    (value : A → ℕ) (M y Y : ℕ) (P : Finset ℕ)
    (β : ↑P → ℕ) (x : A → ℝ) (fixed : Finset ℕ)
    (state : Erdos390.WholePaper.SignedBankSlot β → Bool → Finset ℕ)
    (hM : 0 < M)
    (hvalueInj : Function.Injective value)
    (hvaluePos : ∀ a, 0 < value a)
    (hvalueLe : ∀ a, value a ≤ M)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hrowInt : ∀ r, ∃ k : ℤ,
      ∑ a ∈ Erdos390.WholePaper.rowSet row r, x a = (k : ℝ))
    (hsignature : ∀ a,
      Erdos390.WholePaper.completeRoughSignature y (value a) =
        rowSignature (row a))
    (hPprime : ∀ p, p ∈ P → p.Prime)
    (hprimeSupport : ∀ p, p.Prime → p ≤ y → p ∈ P)
    (hcapacity : ∀ p : ↑P,
      4 * Nat.log 2 M * Nat.log p.1 M ≤ β p)
    (hcertificate : ∀ q,
      ((fixed.prod id *
          (Erdos390.WholePaper.baseBankFactors state).prod id).factorization q : ℝ) +
          ∑ a, x a * ((value a).factorization q : ℝ) =
        (Y.factorization q : ℝ))
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hbankPositive : ∀ g b a, a ∈ state g b → 0 < a)
    (hcross : ∀ g h, g ≠ h → ∀ b c,
      Disjoint (state g b) (state h c))
    (hpathChange : ∀ g,
      Erdos390.WholePaper.integerValuationVector ((state g true).prod id) -
          Erdos390.WholePaper.integerValuationVector
            ((state g false).prod id) =
        Erdos390.WholePaper.embeddedSignedBankSlotChange
          (fun p : ↑P ↦ p.1) g)
    (hbankRows : ∀ g signature,
      Erdos390.WholePaper.completeSignatureMultiplicity y
          (state g false) signature =
        Erdos390.WholePaper.completeSignatureMultiplicity y
          (state g true) signature)
    (hfixedCandidate : Disjoint fixed (Finset.univ.image value))
    (hfixedBank : ∀ g b, Disjoint fixed (state g b))
    (hcandidateBank : ∀ g b,
      Disjoint (Finset.univ.image value) (state g b))
    (hY : 0 < Y) :
    ∃ X : A → ℝ, ∃ positive negative : ↑P → ℕ,
      (∀ a, X a = 0 ∨ X a = 1) ∧
      (∀ r, ∑ a ∈ Erdos390.WholePaper.rowSet row r, X a =
        ∑ a ∈ Erdos390.WholePaper.rowSet row r, x a) ∧
      (∀ p, positive p ≤ β p) ∧
      (∀ p, negative p ≤ β p) ∧
      (∀ p, positive p + negative p ≤ β p) ∧
      (∀ q,
        (((Erdos390.WholePaper.chosenBankFactors state
            (Erdos390.WholePaper.signedBankStateChoice
              positive negative)).prod id).factorization q : ℤ) -
            (((Erdos390.WholePaper.baseBankFactors state).prod id).factorization q : ℤ) =
          -Erdos390.WholePaper.integralRoundingError value X
            (fixed.prod id *
              (Erdos390.WholePaper.baseBankFactors state).prod id) Y q) ∧
      (∀ signature,
        Erdos390.WholePaper.completeSignatureMultiplicity y
            (Erdos390.WholePaper.chosenBankFactors state
              (Erdos390.WholePaper.signedBankStateChoice
                positive negative)) signature =
          Erdos390.WholePaper.completeSignatureMultiplicity y
            (Erdos390.WholePaper.baseBankFactors state) signature) ∧
      (∀ signature,
        (Erdos390.WholePaper.completeSignatureMultiplicity y
            (Erdos390.WholePaper.selectedFactorSet value X) signature : ℝ) =
          ∑ a ∈ Finset.univ.filter
            (fun a ↦ Erdos390.WholePaper.completeRoughSignature y
              (value a) = signature), x a) ∧
      Disjoint fixed
        (Erdos390.WholePaper.chosenBankFactors state
          (Erdos390.WholePaper.signedBankStateChoice positive negative)) ∧
      Disjoint fixed (Erdos390.WholePaper.selectedFactorSet value X) ∧
      Disjoint
        (Erdos390.WholePaper.chosenBankFactors state
          (Erdos390.WholePaper.signedBankStateChoice positive negative))
        (Erdos390.WholePaper.selectedFactorSet value X) ∧
      (∀ q,
        ((Erdos390.WholePaper.guardedFinalFactorSet fixed state
            (Erdos390.WholePaper.signedBankStateChoice positive negative)
              value X).prod id).factorization q = Y.factorization q) ∧
      (Erdos390.WholePaper.guardedFinalFactorSet fixed state
          (Erdos390.WholePaper.signedBankStateChoice positive negative)
            value X).prod id = Y := by
  exact Erdos390.WholePaper.guarded_integral_exactification
    row rowSignature hrowSignatureInj value M y Y P β x fixed state hM
    hvalueInj hvaluePos hvalueLe hx hrowInt hsignature hPprime
    hprimeSupport hcapacity hcertificate hfixedPositive hbankPositive
    hcross hpathChange hbankRows hfixedCandidate hfixedBank hcandidateBank hY

end

end Erdos390.WholePaper.GuardedIntegralExactificationStatementAudit
