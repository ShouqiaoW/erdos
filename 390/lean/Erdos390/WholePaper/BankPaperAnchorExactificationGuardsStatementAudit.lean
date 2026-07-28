import Erdos390.WholePaper.BankPaperAnchorExactificationGuards

/-! # Expanded statement audit for anchor/exactification bank guards -/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! The path-to-global-census bridge is literal for the actual realized
ordinary and relevant-bottom components. -/

example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.pathComponentCensus slot ⊆ R.allComponentOccurrences :=
  R.pathComponentCensus_subset_allComponentOccurrences slot

example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (selected : Bool) :
    R.exactificationState slot selected ⊆ R.allComponentOccurrences :=
  R.exactificationState_subset_allComponentOccurrences slot selected

/-! The guarded states remain the literal oppositely reindexed paper paths.
In particular the upstream signed product change and exact one-endpoint-per-
component cardinalities have not been weakened by the guard layer. -/

example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.exactificationState slot false =
        R.pathStateZero (bankPaperOppositeSlot slot) ∧
      R.exactificationState slot true =
        R.pathStateOne (bankPaperOppositeSlot slot) :=
  ⟨R.exactificationState_false slot, R.exactificationState_true slot⟩

example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    integerValuationVector ((R.exactificationState slot true).prod id) -
        integerValuationVector ((R.exactificationState slot false).prod id) =
      embeddedSignedBankSlotChange
        (fun p : ↑(bankRoundingPrimeSupport n) ↦ p.1) slot :=
  R.exactificationState_productChange slot

example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    (R.exactificationState slot false).card =
        Fintype.card (BankPaperPathComponent (bankPaperOppositeSlot slot)) ∧
      (R.exactificationState slot true).card =
        Fintype.card (BankPaperPathComponent
          (bankPaperOppositeSlot slot)) := by
  rw [R.exactificationState_false, R.exactificationState_true]
  exact ⟨R.pathStateZero_card (bankPaperOppositeSlot slot),
    R.pathStateOne_card (bankPaperOppositeSlot slot)⟩

/-! The three generic finite-set lifts expose exactly their sole hypotheses;
none accepts a target product or target-divisibility assumption. -/

example {n M : ℕ} (R : BankPaperRealization n M)
    (anchors : Finset ℕ)
    (hdisjoint : Disjoint anchors R.allComponentOccurrences)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (selected : Bool) :
    Disjoint anchors (R.exactificationState slot selected) :=
  R.disjoint_exactificationState_of_disjoint_allComponentOccurrences
    anchors hdisjoint slot selected

example {n M : ℕ} (R : BankPaperRealization n M)
    (anchors : Finset ℕ)
    (hstates : ∀ slot selected,
      Disjoint anchors (R.exactificationState slot selected))
    (choice : SignedBankSlot (bankRoundingBetaOnSupport n) → Bool) :
    Disjoint anchors
      (chosenBankFactors R.exactificationState choice) :=
  R.disjoint_chosenExactificationBank_of_disjoint_states
    anchors hstates choice

example {n M : ℕ} (R : BankPaperRealization n M)
    (anchors : Finset ℕ)
    (hstates : ∀ slot selected,
      Disjoint anchors (R.exactificationState slot selected)) :
    Disjoint anchors (baseBankFactors R.exactificationState) :=
  R.disjoint_baseExactificationBank_of_disjoint_states anchors hstates

example {c : ℝ} {depth n M : ℕ}
    (R : BankPaperRealization n M) (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hfixed : 2 * depth + 1 ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (selected : Bool) :
    Disjoint certificate.anchors
      (R.exactificationState slot selected) :=
  R.guardedCentralAnchors_disjoint_exactificationState
    hdepth hnCutoff hfixed hyCutoff certificate slot selected

example {c : ℝ} {depth n M : ℕ}
    (R : BankPaperRealization n M) (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hfixed : 2 * depth + 1 ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)) :
    Disjoint certificate.anchors
        (baseBankFactors R.exactificationState) ∧
      ∀ choice : SignedBankSlot (bankRoundingBetaOnSupport n) → Bool,
        Disjoint certificate.anchors
          (chosenBankFactors R.exactificationState choice) := by
  refine ⟨R.guardedCentralAnchors_disjoint_baseExactificationBank
      hdepth hnCutoff hfixed hyCutoff certificate, ?_⟩
  intro choice
  exact R.guardedCentralAnchors_disjoint_chosenExactificationBank
    hdepth hnCutoff hfixed hyCutoff certificate choice

example {c : ℝ} {depth n M : ℕ}
    (R : BankPaperRealization n M) (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hfixed : 2 * depth + 1 ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)) :
    (∀ slot selected,
      Disjoint certificate.anchors
        (R.exactificationState slot selected)) ∧
      Disjoint certificate.anchors
        (baseBankFactors R.exactificationState) ∧
      ∀ choice : SignedBankSlot (bankRoundingBetaOnSupport n) → Bool,
        Disjoint certificate.anchors
          (chosenBankFactors R.exactificationState choice) :=
  R.guardedCentralAnchor_exactificationGuards
    hdepth hnCutoff hfixed hyCutoff certificate

example (c : ℝ) (depth : ℕ) (hdepth : 2 ≤ depth) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (M : ℕ) (R : BankPaperRealization n M)
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth)),
        (∀ slot selected,
          Disjoint certificate.anchors
            (R.exactificationState slot selected)) ∧
          Disjoint certificate.anchors
            (baseBankFactors R.exactificationState) ∧
          ∀ choice : SignedBankSlot (bankRoundingBetaOnSupport n) → Bool,
            Disjoint certificate.anchors
              (chosenBankFactors R.exactificationState choice) :=
  BankPaperRealization.eventually_guardedCentralAnchor_exactificationGuards
    c depth hdepth

end

end Erdos390.WholePaper
