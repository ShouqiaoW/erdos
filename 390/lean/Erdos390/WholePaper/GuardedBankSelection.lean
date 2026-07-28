import Erdos390.WholePaper.BankPathAlgebra

/-! # Explicit finite selection from a two-sided signed-unit bank -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

abbrev SignedBankSlot {P : Type*} (β : P → ℕ) :=
  Σ p : P, Sum (Fin (β p)) (Fin (β p))

def signedBankSlotChange {P : Type*} [DecidableEq P] {β : P → ℕ}
    (g : SignedBankSlot β) : BankVector P :=
  match g.2 with
  | Sum.inl _ => coordinateUnit g.1
  | Sum.inr _ => -coordinateUnit g.1

/-- Embed a finite coordinate vector into an actual target coordinate type. -/
def embeddedBankVector {P Q : Type*} [Fintype P] [DecidableEq Q]
    (coordinate : P → Q) (z : BankVector P) : BankVector Q :=
  ∑ p : P, (z p) • coordinateUnit (coordinate p)

/-- Actual-coordinate unit change of one signed bank slot. -/
def embeddedSignedBankSlotChange
    {P Q : Type*} [DecidableEq Q] {β : P → ℕ}
    (coordinate : P → Q) (g : SignedBankSlot β) : BankVector Q :=
  match g.2 with
  | Sum.inl _ => coordinateUnit (coordinate g.1)
  | Sum.inr _ => -coordinateUnit (coordinate g.1)

def signedBankStateChoice {P : Type*} {β : P → ℕ}
    (positive negative : P → ℕ) (g : SignedBankSlot β) : Bool :=
  match g.2 with
  | Sum.inl i => decide (i.1 < positive g.1)
  | Sum.inr i => decide (i.1 < negative g.1)

private theorem card_fin_filter_val_lt {n k : ℕ} (hk : k ≤ n) :
    ((Finset.univ : Finset (Fin n)).filter fun i ↦ i.1 < k).card = k := by
  apply Finset.card_eq_of_bijective
    (fun i hi ↦ (⟨i, lt_of_lt_of_le hi hk⟩ : Fin n))
  · intro a ha
    have ha' : a.1 < k := (Finset.mem_filter.mp ha).2
    exact ⟨a.1, ha', by apply Fin.ext; rfl⟩
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi
  · intro i j hi hj hij
    exact Fin.ext_iff.mp hij

private theorem sum_fin_if_val_lt
    {V : Type*} [AddCommGroup V] [Module ℤ V]
    {n k : ℕ} (hk : k ≤ n) (v : V) :
    (∑ i : Fin n, if i.1 < k then v else 0) = (k : ℤ) • v := by
  classical
  calc
    (∑ i : Fin n, if i.1 < k then v else 0) =
        ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i ↦ i.1 < k), v := by
      simp only [Finset.sum_filter]
    _ = (((Finset.univ : Finset (Fin n)).filter
          (fun i ↦ i.1 < k)).card : ℤ) • v := by
      simp
    _ = (k : ℤ) • v := by rw [card_fin_filter_val_lt hk]

theorem sum_signedBankSlotChange_of_choice
    {P : Type*} [Fintype P] [DecidableEq P]
    (β positive negative : P → ℕ)
    (hpositive : ∀ p, positive p ≤ β p)
    (hnegative : ∀ p, negative p ≤ β p) :
    (∑ g : SignedBankSlot β,
        if signedBankStateChoice positive negative g then
          signedBankSlotChange g else 0) =
      signedUnitPathChange positive negative := by
  classical
  funext q
  simp only [Fintype.sum_sigma, Fintype.sum_sum_type, Finset.sum_apply,
    signedBankStateChoice, signedBankSlotChange, decide_eq_true_eq,
    signedUnitPathChange, Pi.add_apply, Pi.smul_apply, ite_apply,
    Pi.zero_apply, Pi.neg_apply]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [sum_fin_if_val_lt (hpositive p) (coordinateUnit p q),
    sum_fin_if_val_lt (hnegative p) (-(coordinateUnit p q))]

theorem sum_embeddedSignedBankSlotChange_of_choice
    {P Q : Type*} [Fintype P] [DecidableEq P] [DecidableEq Q]
    (β positive negative : P → ℕ) (coordinate : P → Q)
    (hpositive : ∀ p, positive p ≤ β p)
    (hnegative : ∀ p, negative p ≤ β p) :
    (∑ g : SignedBankSlot β,
        if signedBankStateChoice positive negative g then
          embeddedSignedBankSlotChange coordinate g else 0) =
      embeddedBankVector coordinate
        (signedUnitPathChange positive negative) := by
  classical
  funext q
  simp only [Fintype.sum_sigma, Fintype.sum_sum_type, Finset.sum_apply,
    signedBankStateChoice, embeddedSignedBankSlotChange,
    decide_eq_true_eq, embeddedBankVector,
    Pi.smul_apply, ite_apply, Pi.zero_apply, Pi.neg_apply]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [sum_fin_if_val_lt (hpositive p) (coordinateUnit (coordinate p) q),
    sum_fin_if_val_lt (hnegative p) (-(coordinateUnit (coordinate p) q))]
  rw [signedUnitPathChange_apply]
  ring

theorem exists_bounded_signedBankStateChoice
    {P : Type*} [Fintype P] [DecidableEq P]
    (β : P → ℕ) (z : BankVector P)
    (hz : ∀ p, |z p| ≤ (β p : ℤ)) :
    ∃ positive negative : P → ℕ,
      (∀ p, positive p ≤ β p) ∧
      (∀ p, negative p ≤ β p) ∧
      (∀ p, positive p + negative p ≤ β p) ∧
      (∑ g : SignedBankSlot β,
        if signedBankStateChoice positive negative g then
          signedBankSlotChange g else 0) = z := by
  obtain ⟨positive, negative, hpositive, hnegative, htotal, hchange⟩ :=
    twoSidedUnitPaths_boxUniversal β z hz
  refine ⟨positive, negative, hpositive, hnegative, htotal, ?_⟩
  rw [sum_signedBankSlotChange_of_choice β positive negative
    hpositive hnegative]
  exact hchange

theorem exists_bounded_embeddedBankStateChoice
    {P Q : Type*} [Fintype P] [DecidableEq P] [DecidableEq Q]
    (β : P → ℕ) (coordinate : P → Q) (z : BankVector P)
    (hz : ∀ p, |z p| ≤ (β p : ℤ)) :
    ∃ positive negative : P → ℕ,
      (∀ p, positive p ≤ β p) ∧
      (∀ p, negative p ≤ β p) ∧
      (∀ p, positive p + negative p ≤ β p) ∧
      (∑ g : SignedBankSlot β,
        if signedBankStateChoice positive negative g then
          embeddedSignedBankSlotChange coordinate g else 0) =
        embeddedBankVector coordinate z := by
  obtain ⟨positive, negative, hpositive, hnegative, htotal, hchange⟩ :=
    twoSidedUnitPaths_boxUniversal β z hz
  refine ⟨positive, negative, hpositive, hnegative, htotal, ?_⟩
  rw [sum_embeddedSignedBankSlotChange_of_choice β positive negative
    coordinate hpositive hnegative, hchange]

end

end Erdos390.WholePaper
