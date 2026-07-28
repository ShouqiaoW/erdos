import Erdos390.WholePaper.ValuationError
import Erdos390.WholePaper.BankRoughSignatures
import Erdos390.WholePaper.GuardedBankSelection

/-!
# Finite algebra for guarded integral exactification

This file contains only finite constructions.  A concrete two-sided bank has
one positive and one negative family of `β p` slots at every explicit
coordinate `p`.  Given a vector in the `β`-box, the toggled slots are the
first required copies in the corresponding families.  No bank-existence,
capacity, donor, or collision assertion is introduced here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The integral coordinates selected by a zero-one real vector. -/
def integralSelection {A : Type*} [Fintype A] (X : A → ℝ) : Finset A := by
  classical
  exact Finset.univ.filter fun a ↦ X a = 1

/-- The literal set of selected integer factors. -/
def selectedFactorSet {A : Type*} [Fintype A]
    (value : A → ℕ) (X : A → ℝ) : Finset ℕ :=
  (integralSelection X).image value

/-- Union of one explicitly chosen state from every concrete path slot. -/
def chosenBankFactors {G : Type*} [Fintype G]
    (state : G → Bool → Finset ℕ) (choice : G → Bool) : Finset ℕ := by
  classical
  exact Finset.univ.biUnion fun g ↦ state g (choice g)

/-- The state-zero bank is a special chosen-state union. -/
def baseBankFactors {G : Type*} [Fintype G]
    (state : G → Bool → Finset ℕ) : Finset ℕ :=
  chosenBankFactors state fun _ ↦ false

theorem sum_integralSelection_eq_sum_mul
    {A : Type*} [Fintype A] (X : A → ℝ)
    (hX : ∀ a, X a = 0 ∨ X a = 1) (weight : A → ℝ) :
    (∑ a ∈ integralSelection X, weight a) = ∑ a, X a * weight a := by
  classical
  unfold integralSelection
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _ha
  rcases hX a with hzero | hone
  · simp [hzero]
  · simp [hone]

theorem selectedFactorSet_factorization
    {A : Type*} [Fintype A] (value : A → ℕ)
    (hvalueInj : Function.Injective value)
    (hvaluePos : ∀ a, 0 < value a) (X : A → ℝ) (q : ℕ) :
    ((selectedFactorSet value X).prod id).factorization q =
      ∑ a ∈ integralSelection X, (value a).factorization q := by
  classical
  unfold selectedFactorSet
  rw [Nat.factorization_prod_apply]
  · rw [Finset.sum_image (fun _ _ _ _ h ↦ hvalueInj h)]
    rfl
  · intro b hb
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hb
    exact (hvaluePos a).ne'

theorem selectedFactorSet_factorization_cast
    {A : Type*} [Fintype A] (value : A → ℕ)
    (hvalueInj : Function.Injective value)
    (hvaluePos : ∀ a, 0 < value a) (X : A → ℝ)
    (hX : ∀ a, X a = 0 ∨ X a = 1) (q : ℕ) :
    (((selectedFactorSet value X).prod id).factorization q : ℝ) =
      ∑ a, X a * ((value a).factorization q : ℝ) := by
  rw [selectedFactorSet_factorization value hvalueInj hvaluePos X q,
    Nat.cast_sum]
  exact sum_integralSelection_eq_sum_mul X hX
    (fun a ↦ ((value a).factorization q : ℝ))

theorem completeSignatureMultiplicity_selectedFactorSet
    {A : Type*} [Fintype A] (y : ℕ) (value : A → ℕ)
    (hvalueInj : Function.Injective value) (X : A → ℝ)
    (signature : ℕ →₀ ℕ) :
    completeSignatureMultiplicity y (selectedFactorSet value X) signature =
      ((integralSelection X).filter
        (fun a ↦ completeRoughSignature y (value a) = signature)).card := by
  classical
  unfold completeSignatureMultiplicity selectedFactorSet
  rw [Finset.filter_image,
    Finset.card_image_of_injective _ hvalueInj]

theorem integralSelection_filter_card_cast
    {A : Type*} [Fintype A] (X : A → ℝ)
    (hX : ∀ a, X a = 0 ∨ X a = 1)
    (predicate : A → Prop) [DecidablePred predicate] :
    ((((integralSelection X).filter predicate).card : ℕ) : ℝ) =
      ∑ a ∈ (Finset.univ.filter predicate), X a := by
  classical
  have hsubset : (integralSelection X).filter predicate ⊆
      Finset.univ.filter predicate := by
    intro a ha
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ a, (Finset.mem_filter.mp ha).2⟩
  calc
    ((((integralSelection X).filter predicate).card : ℕ) : ℝ) =
        ∑ a ∈ (integralSelection X).filter predicate, (1 : ℝ) := by
      simp
    _ = ∑ a ∈ (integralSelection X).filter predicate, X a := by
      apply Finset.sum_congr rfl
      intro a ha
      have haSelected : X a = 1 := by
        exact (Finset.mem_filter.mp
          (Finset.mem_filter.mp ha).1).2
      rw [haSelected]
    _ = ∑ a ∈ (Finset.univ.filter predicate), X a := by
      apply Finset.sum_subset hsubset
      intro a ha haNotSelected
      rcases hX a with hzero | hone
      · exact hzero
      · exfalso
        apply haNotSelected
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ a, hone⟩,
            (Finset.mem_filter.mp ha).2⟩

/-- The selected factors retain every complete rough-row mass, provided
the finite row labels are injective complete signatures. -/
theorem completeSignatureMultiplicity_selectedFactorSet_cast_eq
    {A R : Type*} [Fintype A] [Fintype R]
    (row : A → R) (rowSignature : R → ℕ →₀ ℕ)
    (hrowSignatureInj : Function.Injective rowSignature)
    (value : A → ℕ) (hvalueInj : Function.Injective value)
    (y : ℕ) (X x : A → ℝ)
    (hX : ∀ a, X a = 0 ∨ X a = 1)
    (hrows : ∀ r, ∑ a ∈ rowSet row r, X a =
      ∑ a ∈ rowSet row r, x a)
    (hsignature : ∀ a,
      completeRoughSignature y (value a) = rowSignature (row a))
    (signature : ℕ →₀ ℕ) :
    (completeSignatureMultiplicity y
        (selectedFactorSet value X) signature : ℝ) =
      ∑ a ∈ Finset.univ.filter
        (fun a ↦ completeRoughSignature y (value a) = signature), x a := by
  classical
  rw [completeSignatureMultiplicity_selectedFactorSet y value hvalueInj X,
    integralSelection_filter_card_cast X hX]
  by_cases hrow : ∃ r, rowSignature r = signature
  · obtain ⟨r, rfl⟩ := hrow
    have hfilter : Finset.univ.filter
        (fun a ↦ completeRoughSignature y (value a) = rowSignature r) =
        rowSet row r := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_rowSet]
      rw [hsignature a]
      exact hrowSignatureInj.eq_iff
    rw [hfilter, hrows r]
  · have hfilter : Finset.univ.filter
        (fun a ↦ completeRoughSignature y (value a) = signature) = ∅ := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty, iff_false]
      intro ha
      apply hrow
      exact ⟨row a, (hsignature a).symm.trans ha⟩
    rw [hfilter]
    simp

theorem chosenBankFactors_pairwiseDisjoint
    {G : Type*} [Fintype G] [DecidableEq G]
    (state : G → Bool → Finset ℕ) (choice : G → Bool)
    (hcross : ∀ g h, g ≠ h → ∀ b c,
      Disjoint (state g b) (state h c)) :
    ((Finset.univ : Finset G) : Set G).PairwiseDisjoint
      (fun g ↦ state g (choice g)) := by
  intro g _hg h _hh hne
  exact hcross g h hne (choice g) (choice h)

theorem chosenBankFactors_prod_eq
    {G : Type*} [Fintype G] [DecidableEq G]
    (state : G → Bool → Finset ℕ) (choice : G → Bool)
    (hcross : ∀ g h, g ≠ h → ∀ b c,
      Disjoint (state g b) (state h c)) :
    (chosenBankFactors state choice).prod id =
      ∏ g : G, (state g (choice g)).prod id := by
  classical
  unfold chosenBankFactors
  rw [Finset.prod_biUnion
    (chosenBankFactors_pairwiseDisjoint state choice hcross)]

theorem chosenBankFactors_factorization
    {G : Type*} [Fintype G] [DecidableEq G]
    (state : G → Bool → Finset ℕ) (choice : G → Bool)
    (hpositive : ∀ g b a, a ∈ state g b → 0 < a)
    (hcross : ∀ g h, g ≠ h → ∀ b c,
      Disjoint (state g b) (state h c)) (q : ℕ) :
    ((chosenBankFactors state choice).prod id).factorization q =
      ∑ g : G, ((state g (choice g)).prod id).factorization q := by
  rw [chosenBankFactors_prod_eq state choice hcross,
    Nat.factorization_prod_apply]
  intro g _hg
  exact Finset.prod_ne_zero_iff.mpr fun a ha ↦
    (hpositive g (choice g) a ha).ne'

/-- The valuation change of an actually selected bank union is the sum of
the concrete product changes of exactly its toggled slots. -/
theorem chosenBankFactors_factorization_sub_base
    {G : Type*} [Fintype G] [DecidableEq G]
    (state : G → Bool → Finset ℕ) (choice : G → Bool)
    (change : G → BankVector ℕ)
    (hpositive : ∀ g b a, a ∈ state g b → 0 < a)
    (hcross : ∀ g h, g ≠ h → ∀ b c,
      Disjoint (state g b) (state h c))
    (hpathChange : ∀ g,
      integerValuationVector ((state g true).prod id) -
          integerValuationVector ((state g false).prod id) = change g)
    (q : ℕ) :
    (((chosenBankFactors state choice).prod id).factorization q : ℤ) -
        (((baseBankFactors state).prod id).factorization q : ℤ) =
      (∑ g : G, if choice g then change g else 0) q := by
  unfold baseBankFactors
  rw [chosenBankFactors_factorization state choice hpositive hcross q,
    chosenBankFactors_factorization state (fun _ ↦ false) hpositive hcross q]
  push_cast
  rw [← Finset.sum_sub_distrib]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro g _hg
  cases hchoice : choice g
  · simp
  · simp only [if_true]
    have hgq := congrFun (hpathChange g) q
    exact hgq

theorem completeSignatureMultiplicity_chosenBankFactors
    {G : Type*} [Fintype G] [DecidableEq G]
    (y : ℕ) (state : G → Bool → Finset ℕ) (choice : G → Bool)
    (hcross : ∀ g h, g ≠ h → ∀ b c,
      Disjoint (state g b) (state h c)) (signature : ℕ →₀ ℕ) :
    completeSignatureMultiplicity y (chosenBankFactors state choice) signature =
      ∑ g : G, completeSignatureMultiplicity y (state g (choice g)) signature := by
  classical
  have hpair := chosenBankFactors_pairwiseDisjoint state choice hcross
  have hpairFilter :
      ((Finset.univ : Finset G) : Set G).PairwiseDisjoint
        (fun g ↦ (state g (choice g)).filter
          (fun a ↦ completeRoughSignature y a = signature)) := by
    intro g _hg h _hh hne
    exact (hpair (Finset.mem_univ g) (Finset.mem_univ h) hne).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  unfold completeSignatureMultiplicity chosenBankFactors
  rw [Finset.filter_biUnion, Finset.card_biUnion hpairFilter]

theorem completeSignatureMultiplicity_bankState_invariant
    {G : Type*} [Fintype G] [DecidableEq G]
    (y : ℕ) (state : G → Bool → Finset ℕ) (choice : G → Bool)
    (hcross : ∀ g h, g ≠ h → ∀ b c,
      Disjoint (state g b) (state h c))
    (hrow : ∀ g signature,
      completeSignatureMultiplicity y (state g false) signature =
        completeSignatureMultiplicity y (state g true) signature) :
    ∀ signature,
      completeSignatureMultiplicity y (chosenBankFactors state choice) signature =
        completeSignatureMultiplicity y (baseBankFactors state) signature := by
  intro signature
  unfold baseBankFactors
  rw [completeSignatureMultiplicity_chosenBankFactors y state choice hcross,
    completeSignatureMultiplicity_chosenBankFactors y state (fun _ ↦ false)
      hcross]
  apply Finset.sum_congr rfl
  intro g _hg
  cases hchoice : choice g
  · rfl
  · exact hrow g signature |>.symm

/-- Integer rounded-minus-fractional valuation error, expressed only with
actual selected products and the charged base/target factorizations. -/
def integralRoundingError {A : Type*} [Fintype A]
    (value : A → ℕ) (X : A → ℝ) (B₀ Y q : ℕ) : ℤ :=
  (((selectedFactorSet value X).prod id).factorization q : ℤ) +
    (B₀.factorization q : ℤ) - (Y.factorization q : ℤ)

theorem integralRoundingError_cast_eq
    {A : Type*} [Fintype A] (value : A → ℕ)
    (hvalueInj : Function.Injective value)
    (hvaluePos : ∀ a, 0 < value a) (X x : A → ℝ)
    (hX : ∀ a, X a = 0 ∨ X a = 1) (B₀ Y q : ℕ)
    (hcertificate :
      (B₀.factorization q : ℝ) +
          ∑ a, x a * ((value a).factorization q : ℝ) =
        (Y.factorization q : ℝ)) :
    (integralRoundingError value X B₀ Y q : ℝ) =
      roundingValuationError value X x q := by
  rw [integralRoundingError]
  push_cast
  rw [selectedFactorSet_factorization_cast value hvalueInj hvaluePos X hX q]
  unfold roundingValuationError
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  linarith

/-- Complete rough-row preservation kills every valuation error above the
rough cutoff. -/
theorem roundingValuationError_eq_zero_of_complete_rows
    {A R : Type*} [Fintype A] [Fintype R]
    (row : A → R) (rowSignature : R → ℕ →₀ ℕ)
    (value : A → ℕ) (y : ℕ) (X x : A → ℝ)
    (hrows : ∀ r, ∑ a ∈ rowSet row r, X a =
      ∑ a ∈ rowSet row r, x a)
    (hsignature : ∀ a,
      completeRoughSignature y (value a) = rowSignature (row a))
    {q : ℕ} (hyq : y < q) :
    roundingValuationError value X x q = 0 := by
  classical
  unfold roundingValuationError
  rw [← Finset.sum_fiberwise Finset.univ row
    (fun a ↦ (X a - x a) * (value a).factorization q)]
  apply Finset.sum_eq_zero
  intro r _hr
  have hfactorization : ∀ a ∈ rowSet row r,
      (value a).factorization q = rowSignature r q := by
    intro a ha
    have haRow : row a = r := mem_rowSet.mp ha
    have happly := congrArg (fun s : ℕ →₀ ℕ ↦ s q) (hsignature a)
    change completeRoughSignature y (value a) q =
      rowSignature (row a) q at happly
    rw [completeRoughSignature_apply, if_pos hyq, haRow] at happly
    exact happly
  calc
    (∑ a ∈ Finset.univ with row a = r,
        (X a - x a) * (value a).factorization q) =
        ∑ a ∈ rowSet row r,
          (X a - x a) * (rowSignature r q : ℝ) := by
      apply Finset.sum_congr
      · rfl
      · intro a ha
        rw [hfactorization a ha]
    _ = (∑ a ∈ rowSet row r, (X a - x a)) *
        (rowSignature r q : ℝ) := by rw [Finset.sum_mul]
    _ = 0 := by
      rw [Finset.sum_sub_distrib, hrows r, sub_self, zero_mul]

/-- A finitely supported error is exactly the embedded vector of its
coordinates on the explicit support. -/
theorem embeddedBankVector_subtype_neg_eq
    {Q : Type*} [DecidableEq Q] (P : Finset Q) (e : Q → ℤ)
    (houtside : ∀ q, q ∉ P → e q = 0) :
    embeddedBankVector (fun p : ↑P ↦ p.1) (fun p ↦ -e p.1) = -e := by
  classical
  funext q
  simp only [embeddedBankVector, Finset.sum_apply, Pi.smul_apply,
    Pi.neg_apply]
  by_cases hq : q ∈ P
  · let p : ↑P := ⟨q, hq⟩
    rw [Finset.sum_eq_single p]
    · simp [coordinateUnit, p]
    · intro p' _hp' hp'ne
      have hvalne : p'.1 ≠ q := by
        intro h
        apply hp'ne
        apply Subtype.ext
        simpa only [p] using h
      simp [coordinateUnit, hvalne]
    · simp
  ·
    have hne (p : ↑P) : p.1 ≠ q := by
      intro h
      exact hq (h ▸ p.2)
    simp [coordinateUnit, hne, houtside q hq]

end

end Erdos390.WholePaper
