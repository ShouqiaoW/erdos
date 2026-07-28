import Erdos390.WholePaper.GuardedExactificationProduct

/-!
# Guarded integral exactification

This is the finite terminal statement from the rounding argument.  The bank
is input as literal two-state finite factor sets indexed by concrete signed
slots.  Capacity, path valuation changes, row multiplicities, and every
collision guard are separate hypotheses about those sets.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

theorem integralRoundingError_eq_zero_outside_prime_support
    {A R : Type*} [Fintype A] [Fintype R]
    (row : A → R) (rowSignature : R → ℕ →₀ ℕ)
    (value : A → ℕ) (hvalueInj : Function.Injective value)
    (hvaluePos : ∀ a, 0 < value a)
    (y : ℕ) (P : Finset ℕ) (X x : A → ℝ) (B₀ Y : ℕ)
    (hX : ∀ a, X a = 0 ∨ X a = 1)
    (hrows : ∀ r, ∑ a ∈ rowSet row r, X a =
      ∑ a ∈ rowSet row r, x a)
    (hsignature : ∀ a,
      completeRoughSignature y (value a) = rowSignature (row a))
    (hprimeSupport : ∀ q, q.Prime → q ≤ y → q ∈ P)
    (hcertificate : ∀ q,
      (B₀.factorization q : ℝ) +
          ∑ a, x a * ((value a).factorization q : ℝ) =
        (Y.factorization q : ℝ)) :
    ∀ q, q ∉ P → integralRoundingError value X B₀ Y q = 0 := by
  intro q hq
  have hcast := integralRoundingError_cast_eq value hvalueInj hvaluePos
    X x hX B₀ Y q (hcertificate q)
  have hround : roundingValuationError value X x q = 0 := by
    by_cases hqPrime : q.Prime
    · apply roundingValuationError_eq_zero_of_complete_rows
        row rowSignature value y X x hrows hsignature
      exact Nat.lt_of_not_ge fun hqy ↦ hq (hprimeSupport q hqPrime hqy)
    · simp [roundingValuationError,
        Nat.factorization_eq_zero_of_not_prime _ hqPrime]
  rw [hround] at hcast
  exact_mod_cast hcast

theorem integralRoundingError_in_capacity_box
    {A : Type*} [Fintype A]
    (value : A → ℕ) (hvalueInj : Function.Injective value)
    (hvaluePos : ∀ a, 0 < value a)
    (M : ℕ) (P : Finset ℕ) (X x : A → ℝ) (B₀ Y : ℕ)
    (hX : ∀ a, X a = 0 ∨ X a = 1)
    (hcertificate : ∀ q,
      (B₀.factorization q : ℝ) +
          ∑ a, x a * ((value a).factorization q : ℝ) =
        (Y.factorization q : ℝ))
    (herrorBox : ∀ p, p.Prime →
      |roundingValuationError value X x p| ≤
        (4 * Nat.log 2 M * Nat.log p M : ℝ))
    (β : ↑P → ℕ)
    (hPprime : ∀ p, p ∈ P → p.Prime)
    (hcapacity : ∀ p : ↑P,
      4 * Nat.log 2 M * Nat.log p.1 M ≤ β p) :
    ∀ p : ↑P,
      |integralRoundingError value X B₀ Y p.1| ≤ (β p : ℤ) := by
  intro p
  have hcast := integralRoundingError_cast_eq value hvalueInj hvaluePos
    X x hX B₀ Y p.1 (hcertificate p.1)
  have hbound := herrorBox p.1 (hPprime p.1 p.2)
  have hcapacityReal :
      (4 * Nat.log 2 M * Nat.log p.1 M : ℝ) ≤ (β p : ℝ) := by
    exact_mod_cast hcapacity p
  have hreal :
      |(integralRoundingError value X B₀ Y p.1 : ℝ)| ≤ (β p : ℝ) := by
    rw [hcast]
    exact hbound.trans hcapacityReal
  exact_mod_cast hreal

/-- Guarded integral exactification with an explicit finite signed bank.

The conclusion displays the rounded vector, the exact number of positive
and negative slots used at each coordinate, the literal final bank and
selected-factor products, every complete rough-row count, all three
pairwise guards, coordinatewise factorization equality, and ordinary
natural-number product equality. -/
theorem guarded_integral_exactification
    {A R : Type*} [Fintype A] [Fintype R]
    (row : A → R) (rowSignature : R → ℕ →₀ ℕ)
    (hrowSignatureInj : Function.Injective rowSignature)
    (value : A → ℕ) (M y Y : ℕ) (P : Finset ℕ)
    (β : ↑P → ℕ) (x : A → ℝ) (fixed : Finset ℕ)
    (state : SignedBankSlot β → Bool → Finset ℕ)
    (hM : 0 < M)
    (hvalueInj : Function.Injective value)
    (hvaluePos : ∀ a, 0 < value a)
    (hvalueLe : ∀ a, value a ≤ M)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hrowInt : ∀ r, ∃ k : ℤ,
      ∑ a ∈ rowSet row r, x a = (k : ℝ))
    (hsignature : ∀ a,
      completeRoughSignature y (value a) = rowSignature (row a))
    (hPprime : ∀ p, p ∈ P → p.Prime)
    (hprimeSupport : ∀ p, p.Prime → p ≤ y → p ∈ P)
    (hcapacity : ∀ p : ↑P,
      4 * Nat.log 2 M * Nat.log p.1 M ≤ β p)
    (hcertificate : ∀ q,
      ((fixed.prod id * (baseBankFactors state).prod id).factorization q : ℝ) +
          ∑ a, x a * ((value a).factorization q : ℝ) =
        (Y.factorization q : ℝ))
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hbankPositive : ∀ g b a, a ∈ state g b → 0 < a)
    (hcross : ∀ g h, g ≠ h → ∀ b c,
      Disjoint (state g b) (state h c))
    (hpathChange : ∀ g,
      integerValuationVector ((state g true).prod id) -
          integerValuationVector ((state g false).prod id) =
        embeddedSignedBankSlotChange (fun p : ↑P ↦ p.1) g)
    (hbankRows : ∀ g signature,
      completeSignatureMultiplicity y (state g false) signature =
        completeSignatureMultiplicity y (state g true) signature)
    (hfixedCandidate : Disjoint fixed (Finset.univ.image value))
    (hfixedBank : ∀ g b, Disjoint fixed (state g b))
    (hcandidateBank : ∀ g b,
      Disjoint (Finset.univ.image value) (state g b))
    (hY : 0 < Y) :
    ∃ X : A → ℝ, ∃ positive negative : ↑P → ℕ,
      (∀ a, X a = 0 ∨ X a = 1) ∧
      (∀ r, ∑ a ∈ rowSet row r, X a =
        ∑ a ∈ rowSet row r, x a) ∧
      (∀ p, positive p ≤ β p) ∧
      (∀ p, negative p ≤ β p) ∧
      (∀ p, positive p + negative p ≤ β p) ∧
      (∀ q,
        (((chosenBankFactors state
            (signedBankStateChoice positive negative)).prod id).factorization q : ℤ) -
            (((baseBankFactors state).prod id).factorization q : ℤ) =
          -integralRoundingError value X
            (fixed.prod id * (baseBankFactors state).prod id) Y q) ∧
      (∀ signature,
        completeSignatureMultiplicity y
            (chosenBankFactors state
              (signedBankStateChoice positive negative)) signature =
          completeSignatureMultiplicity y
            (baseBankFactors state) signature) ∧
      (∀ signature,
        (completeSignatureMultiplicity y
            (selectedFactorSet value X) signature : ℝ) =
          ∑ a ∈ Finset.univ.filter
            (fun a ↦ completeRoughSignature y (value a) = signature), x a) ∧
      Disjoint fixed
        (chosenBankFactors state
          (signedBankStateChoice positive negative)) ∧
      Disjoint fixed (selectedFactorSet value X) ∧
      Disjoint
        (chosenBankFactors state
          (signedBankStateChoice positive negative))
        (selectedFactorSet value X) ∧
      (∀ q,
        ((guardedFinalFactorSet fixed state
            (signedBankStateChoice positive negative) value X).prod id).factorization q =
          Y.factorization q) ∧
      (guardedFinalFactorSet fixed state
          (signedBankStateChoice positive negative) value X).prod id = Y := by
  classical
  obtain ⟨X, hX, hrows, herrorBox⟩ :=
    floating_rounding_valuationErrorBox row value M x hM hvaluePos
      hvalueLe hx hrowInt
  let B₀ : ℕ := fixed.prod id * (baseBankFactors state).prod id
  let e : ℕ → ℤ := integralRoundingError value X B₀ Y
  have heBox : ∀ p : ↑P, |e p.1| ≤ (β p : ℤ) := by
    exact integralRoundingError_in_capacity_box value hvalueInj hvaluePos
      M P X x B₀ Y hX hcertificate herrorBox β hPprime hcapacity
  have heOutside : ∀ q, q ∉ P → e q = 0 := by
    exact integralRoundingError_eq_zero_outside_prime_support
      row rowSignature value hvalueInj hvaluePos y P X x B₀ Y hX hrows
      hsignature hprimeSupport hcertificate
  obtain ⟨positive, negative, hpositive, hnegative, htotal, hslotSum⟩ :=
    exists_bounded_embeddedBankStateChoice β
      (fun p : ↑P ↦ p.1) (fun p ↦ -e p.1) (fun p ↦ by
        simpa only [abs_neg] using heBox p)
  let choice : SignedBankSlot β → Bool :=
    signedBankStateChoice positive negative
  have hslotSumActual :
      (∑ g : SignedBankSlot β,
        if choice g then
          embeddedSignedBankSlotChange (fun p : ↑P ↦ p.1) g else 0) =
        -e := by
    calc
      (∑ g : SignedBankSlot β,
          if choice g then
            embeddedSignedBankSlotChange (fun p : ↑P ↦ p.1) g else 0) =
          embeddedBankVector (fun p : ↑P ↦ p.1)
            (fun p ↦ -e p.1) := hslotSum
      _ = -e := embeddedBankVector_subtype_neg_eq P e heOutside
  have hbankChange : ∀ q,
      (((chosenBankFactors state choice).prod id).factorization q : ℤ) -
          (((baseBankFactors state).prod id).factorization q : ℤ) =
        -e q := by
    intro q
    rw [chosenBankFactors_factorization_sub_base state choice
      (embeddedSignedBankSlotChange (fun p : ↑P ↦ p.1))
      hbankPositive hcross hpathChange q]
    exact congrFun hslotSumActual q
  have hbankRowInvariant : ∀ signature,
      completeSignatureMultiplicity y (chosenBankFactors state choice) signature =
        completeSignatureMultiplicity y (baseBankFactors state) signature :=
    completeSignatureMultiplicity_bankState_invariant y state choice hcross
      hbankRows
  have hselectedRows : ∀ signature,
      (completeSignatureMultiplicity y
          (selectedFactorSet value X) signature : ℝ) =
        ∑ a ∈ Finset.univ.filter
          (fun a ↦ completeRoughSignature y (value a) = signature), x a :=
    completeSignatureMultiplicity_selectedFactorSet_cast_eq
      row rowSignature hrowSignatureInj value hvalueInj y X x hX hrows
        hsignature
  have hfixedFinalBank : Disjoint fixed (chosenBankFactors state choice) :=
    disjoint_chosenBankFactors_of_disjoint_states_left fixed state choice
      hfixedBank
  have hfixedSelected : Disjoint fixed (selectedFactorSet value X) :=
    hfixedCandidate.mono (Finset.Subset.rfl)
      (selectedFactorSet_subset_candidateUniverse value X)
  have hbankSelected :
      Disjoint (chosenBankFactors state choice) (selectedFactorSet value X) :=
    disjoint_chosenBankFactors_selectedFactorSet state choice value X
      hcandidateBank
  have hfactorization : ∀ q,
      ((guardedFinalFactorSet fixed state choice value X).prod id).factorization q =
        Y.factorization q := by
    intro q
    have hsplit := guardedFinalFactorSet_factorization fixed state choice
      value X hfixedPositive hbankPositive hvaluePos hfixedFinalBank
      hfixedSelected hbankSelected q
    have hbaseBankNe : (baseBankFactors state).prod id ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro a ha
      obtain ⟨g, _hg, haState⟩ := Finset.mem_biUnion.mp ha
      exact (hbankPositive g false a haState).ne'
    have hfixedNe : fixed.prod id ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun a ha ↦
        (hfixedPositive a ha).ne'
    have hbaseSplit :
        (B₀.factorization q : ℤ) =
          ((fixed.prod id).factorization q : ℤ) +
            (((baseBankFactors state).prod id).factorization q : ℤ) := by
      dsimp only [B₀]
      rw [Nat.factorization_mul hfixedNe hbaseBankNe]
      rfl
    have heDef : e q =
        (((selectedFactorSet value X).prod id).factorization q : ℤ) +
          (B₀.factorization q : ℤ) - (Y.factorization q : ℤ) := rfl
    have hsplitInt :
        (((guardedFinalFactorSet fixed state choice value X).prod id).factorization q : ℤ) =
          ((fixed.prod id).factorization q : ℤ) +
            (((chosenBankFactors state choice).prod id).factorization q : ℤ) +
              (((selectedFactorSet value X).prod id).factorization q : ℤ) := by
      exact_mod_cast hsplit
    have hfinalInt :
        (((guardedFinalFactorSet fixed state choice value X).prod id).factorization q : ℤ) =
          (Y.factorization q : ℤ) := by
      calc
        (((guardedFinalFactorSet fixed state choice value X).prod id).factorization q : ℤ) =
            ((fixed.prod id).factorization q : ℤ) +
              (((chosenBankFactors state choice).prod id).factorization q : ℤ) +
                (((selectedFactorSet value X).prod id).factorization q : ℤ) :=
          hsplitInt
        _ = (Y.factorization q : ℤ) := by
          linear_combination (hbankChange q) - heDef - hbaseSplit
    exact_mod_cast hfinalInt
  have hfixedNe : fixed.prod id ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a ha ↦ (hfixedPositive a ha).ne'
  have hfinalBankNe : (chosenBankFactors state choice).prod id ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    obtain ⟨g, _hg, haState⟩ := Finset.mem_biUnion.mp ha
    exact (hbankPositive g (choice g) a haState).ne'
  have hselectedNe : (selectedFactorSet value X).prod id ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp ha
    exact (hvaluePos i).ne'
  have hfinalNe :
      (guardedFinalFactorSet fixed state choice value X).prod id ≠ 0 := by
    rw [guardedFinalFactorSet_prod_eq fixed state choice value X
      hfixedFinalBank hfixedSelected hbankSelected]
    exact mul_ne_zero (mul_ne_zero hfixedNe hfinalBankNe) hselectedNe
  have hproduct :
      (guardedFinalFactorSet fixed state choice value X).prod id = Y :=
    Nat.eq_of_factorization_eq hfinalNe hY.ne' hfactorization
  refine ⟨X, positive, negative, hX, hrows, hpositive, hnegative, htotal,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [choice, e, B₀] using hbankChange
  · simpa only [choice] using hbankRowInvariant
  · exact hselectedRows
  · simpa only [choice] using hfixedFinalBank
  · exact hfixedSelected
  · simpa only [choice] using hbankSelected
  · simpa only [choice] using hfactorization
  · simpa only [choice] using hproduct

end

end Erdos390.WholePaper
