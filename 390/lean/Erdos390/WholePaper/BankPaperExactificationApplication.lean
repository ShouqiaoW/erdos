import Erdos390.WholePaper.BankPaperExactificationState

/-!
# Concrete application of guarded exactification to the paper bank

This is the expanded terminal obtained by specializing the generic guarded
exactification theorem to the literal rounding-prime support, beta reserve,
smooth cutoff, and opposite-orientation bank state.  The endpoint bound
`M ≤ 3n` supplies the capacity inequality.  Prime-support facts and all
state-local obligations are discharged by the concrete bank API.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- Guarded integral exactification with the actual paper bank.  In
particular, `baseBankFactors R.exactificationState` is the union of the
precharged state-zero paths, even though slots are reindexed by the opposite
orientation to align their signed changes with the generic convention. -/
theorem bankPaper_guarded_integral_exactification
    {A Row : Type*} [Fintype A] [Fintype Row]
    (row : A → Row) (rowSignature : Row → ℕ →₀ ℕ)
    (hrowSignatureInj : Function.Injective rowSignature)
    (value : A → ℕ) (n M Y : ℕ) (x : A → ℝ)
    (fixed : Finset ℕ) (R : BankPaperRealization n M)
    (hMThree : M ≤ 3 * n)
    (hvalueInj : Function.Injective value)
    (hvaluePos : ∀ a, 0 < value a)
    (hvalueLe : ∀ a, value a ≤ M)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hrowInt : ∀ r, ∃ k : ℤ,
      ∑ a ∈ rowSet row r, x a = (k : ℝ))
    (hsignature : ∀ a,
      completeRoughSignature (yNat n) (value a) =
        rowSignature (row a))
    (hcertificate : ∀ q,
      ((fixed.prod id *
          (baseBankFactors R.exactificationState).prod id).factorization q : ℝ) +
          ∑ a, x a * ((value a).factorization q : ℝ) =
        (Y.factorization q : ℝ))
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hfixedCandidate : Disjoint fixed (Finset.univ.image value))
    (hfixedBank : ∀ g b,
      Disjoint fixed (R.exactificationState g b))
    (hcandidateBank : ∀ g b,
      Disjoint (Finset.univ.image value) (R.exactificationState g b))
    (hY : 0 < Y) :
    ∃ X : A → ℝ,
      ∃ positive negative : ↑(bankRoundingPrimeSupport n) → ℕ,
      (∀ a, X a = 0 ∨ X a = 1) ∧
      (∀ r, ∑ a ∈ rowSet row r, X a =
        ∑ a ∈ rowSet row r, x a) ∧
      (∀ p, positive p ≤ bankRoundingBetaOnSupport n p) ∧
      (∀ p, negative p ≤ bankRoundingBetaOnSupport n p) ∧
      (∀ p, positive p + negative p ≤
        bankRoundingBetaOnSupport n p) ∧
      (∀ q,
        (((chosenBankFactors R.exactificationState
            (signedBankStateChoice positive negative)).prod id).factorization q : ℤ) -
            (((baseBankFactors R.exactificationState).prod id).factorization q : ℤ) =
          -integralRoundingError value X
            (fixed.prod id *
              (baseBankFactors R.exactificationState).prod id) Y q) ∧
      (∀ signature,
        completeSignatureMultiplicity (yNat n)
            (chosenBankFactors R.exactificationState
              (signedBankStateChoice positive negative)) signature =
          completeSignatureMultiplicity (yNat n)
            (baseBankFactors R.exactificationState) signature) ∧
      (∀ signature,
        (completeSignatureMultiplicity (yNat n)
            (selectedFactorSet value X) signature : ℝ) =
          ∑ a ∈ Finset.univ.filter
            (fun a ↦ completeRoughSignature (yNat n) (value a) = signature),
              x a) ∧
      Disjoint fixed
        (chosenBankFactors R.exactificationState
          (signedBankStateChoice positive negative)) ∧
      Disjoint fixed (selectedFactorSet value X) ∧
      Disjoint
        (chosenBankFactors R.exactificationState
          (signedBankStateChoice positive negative))
        (selectedFactorSet value X) ∧
      (∀ q,
        ((guardedFinalFactorSet fixed R.exactificationState
            (signedBankStateChoice positive negative)
              value X).prod id).factorization q = Y.factorization q) ∧
      (guardedFinalFactorSet fixed R.exactificationState
          (signedBankStateChoice positive negative)
            value X).prod id = Y := by
  have hMPos : 0 < M := by
    have hn := R.ordinary.one_le_n
    have htwo := R.ordinary.two_mul_n_le_M
    omega
  have hPprime : ∀ p, p ∈ bankRoundingPrimeSupport n → p.Prime := by
    intro p hp
    exact bankRoundingPrimeSupport_prime hp
  have hprimeSupport : ∀ p, p.Prime → p ≤ yNat n →
      p ∈ bankRoundingPrimeSupport n := by
    intro p hp hpy
    rw [bankRoundingPrimeSupport, Nat.mem_primesBelow]
    exact ⟨by omega, hp⟩
  have hcapacity : ∀ p : ↑(bankRoundingPrimeSupport n),
      4 * Nat.log 2 M * Nat.log p.1 M ≤
        bankRoundingBetaOnSupport n p := by
    intro p
    simpa only [bankRoundingBetaOnSupport] using
      (roundingErrorBox_le_bankRoundingBeta
        (n := n) (M := M) (p := p.1) hMThree)
  exact guarded_integral_exactification
    row rowSignature hrowSignatureInj value M (yNat n) Y
    (bankRoundingPrimeSupport n) (bankRoundingBetaOnSupport n) x fixed
    R.exactificationState hMPos hvalueInj hvaluePos hvalueLe hx hrowInt
    hsignature hPprime hprimeSupport hcapacity hcertificate
    hfixedPositive
    (fun g b a ha ↦ R.exactificationState_positive g b ha)
    (fun g h hne b c ↦
      R.exactificationState_disjoint_of_slot_ne hne b c)
    (fun g ↦ R.exactificationState_productChange g)
    (fun g signature ↦
      R.exactificationState_completeSignatureMultiplicity_eq g signature)
    hfixedCandidate hfixedBank hcandidateBank hY

end

end Erdos390.WholePaper
