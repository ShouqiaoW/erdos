import Erdos390.WholePaper.BankAnchorCollisionFree
import Erdos390.WholePaper.BankPaperExactificationState

/-!
# Central-anchor guards for the concrete exactification states

Every Boolean exactification state is one endpoint from every component in
one oppositely reindexed paper path.  Hence it is a subset of that path's
component census, and ultimately of the global actual bank census.  The
complete anchor/census collision theorem therefore supplies the anchor--bank
part of the final residual disjointness ledger.  (The `fixed` argument of
concrete exactification is the separate residual fixed set, not the external
anchors.)  The same argument is lifted through the literal `biUnion`
defining the base and an arbitrary chosen bank state.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

namespace BankPaperRealization

/-- Every component occurrence in one full path belongs to the global actual
bank census. -/
theorem pathComponentCensus_subset_allComponentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.pathComponentCensus slot ⊆ R.allComponentOccurrences := by
  intro occurrence hoccurrence
  rw [pathComponentCensus, Finset.mem_biUnion] at hoccurrence
  obtain ⟨component, _hcomponent, hcomponentOccurrence⟩ := hoccurrence
  rw [allComponentOccurrences, Finset.mem_union]
  cases component with
  | inl source =>
      left
      rw [ordinaryComponentOccurrences, Finset.mem_biUnion]
      refine ⟨BankOrdinaryPaperRealization.requestOfSource slot source,
        Finset.mem_attach _ _, ?_⟩
      simpa only [pathComponentOccurrences] using hcomponentOccurrence
  | inr move =>
      right
      rw [bottomComponentOccurrences,
        BankBottomPaperRealization.relevantComponentOccurrences,
        Finset.mem_biUnion]
      refine ⟨bankPaperBottomRelevantRequestOfMove slot move,
        Finset.mem_attach _ _, ?_⟩
      simpa only [pathComponentOccurrences,
        bankBottomRelevantRequestToPaperRequest_ofMove] using
          hcomponentOccurrence

/-- In particular every oppositely reindexed Boolean exactification state is
a subset of the global actual bank census. -/
theorem exactificationState_subset_allComponentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (selected : Bool) :
    R.exactificationState slot selected ⊆ R.allComponentOccurrences := by
  intro occurrence hoccurrence
  apply R.pathComponentCensus_subset_allComponentOccurrences
    (bankPaperOppositeSlot slot)
  cases selected
  · exact R.pathStateZero_subset_componentCensus
      (bankPaperOppositeSlot slot)
      (by simpa only [exactificationState_false] using hoccurrence)
  · exact R.pathStateOne_subset_componentCensus
      (bankPaperOppositeSlot slot)
      (by simpa only [exactificationState_true] using hoccurrence)

/-- Any set disjoint from the global component census is disjoint from each
Boolean exactification state. -/
theorem disjoint_exactificationState_of_disjoint_allComponentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M) (anchors : Finset ℕ)
    (hdisjoint : Disjoint anchors R.allComponentOccurrences)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (selected : Bool) :
    Disjoint anchors (R.exactificationState slot selected) :=
  hdisjoint.mono Finset.Subset.rfl
    (R.exactificationState_subset_allComponentOccurrences slot selected)

/-- Lift statewise disjointness through the literal `biUnion` defining an
arbitrary chosen bank state. -/
theorem disjoint_chosenExactificationBank_of_disjoint_states
    {n M : ℕ} (R : BankPaperRealization n M) (anchors : Finset ℕ)
    (hstates : ∀ slot selected,
      Disjoint anchors (R.exactificationState slot selected))
    (choice : SignedBankSlot (bankRoundingBetaOnSupport n) → Bool) :
    Disjoint anchors
      (chosenBankFactors R.exactificationState choice) := by
  classical
  rw [Finset.disjoint_left]
  intro occurrence hanchor hchosen
  rw [chosenBankFactors, Finset.mem_biUnion] at hchosen
  obtain ⟨slot, _hslot, hstate⟩ := hchosen
  exact (Finset.disjoint_left.mp (hstates slot (choice slot)))
    hanchor hstate

/-- The precharged state-zero union is the constant-false specialization of
the preceding chosen-state guard. -/
theorem disjoint_baseExactificationBank_of_disjoint_states
    {n M : ℕ} (R : BankPaperRealization n M) (anchors : Finset ℕ)
    (hstates : ∀ slot selected,
      Disjoint anchors (R.exactificationState slot selected)) :
    Disjoint anchors (baseBankFactors R.exactificationState) := by
  simpa only [baseBankFactors] using
    R.disjoint_chosenExactificationBank_of_disjoint_states anchors hstates
      (fun _slot ↦ false)

/-! ## Guarded-certificate specializations -/

/-- A complete guarded certificate is disjoint from either Boolean state of
every concrete signed bank slot. -/
theorem guardedCentralAnchors_disjoint_exactificationState
    {c : ℝ} {depth n M : ℕ}
    (R : BankPaperRealization n M) (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hfixed : 2 * depth + 1 ≤ Erdos390.Full.ArithmeticModel.yNat n)
    (hyCutoff : Erdos390.Full.ArithmeticModel.yNat n <
      centralAnchorCutoff depth n)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (selected : Bool) :
    Disjoint certificate.anchors
      (R.exactificationState slot selected) := by
  exact R.disjoint_exactificationState_of_disjoint_allComponentOccurrences
    certificate.anchors
    (R.guardedCentralAnchors_disjoint_allComponentOccurrences
      hdepth hnCutoff hfixed hyCutoff certificate)
    slot selected

/-- Function-shaped form of the preceding theorem, convenient when the
final three-way residual guard is assembled. -/
theorem guardedCentralAnchors_disjoint_exactificationStates
    {c : ℝ} {depth n M : ℕ}
    (R : BankPaperRealization n M) (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hfixed : 2 * depth + 1 ≤ Erdos390.Full.ArithmeticModel.yNat n)
    (hyCutoff : Erdos390.Full.ArithmeticModel.yNat n <
      centralAnchorCutoff depth n)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)) :
    ∀ slot selected,
      Disjoint certificate.anchors
        (R.exactificationState slot selected) := by
  intro slot selected
  exact R.guardedCentralAnchors_disjoint_exactificationState
    hdepth hnCutoff hfixed hyCutoff certificate slot selected

/-- The complete guarded anchors are disjoint from the literal precharged
bank base. -/
theorem guardedCentralAnchors_disjoint_baseExactificationBank
    {c : ℝ} {depth n M : ℕ}
    (R : BankPaperRealization n M) (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hfixed : 2 * depth + 1 ≤ Erdos390.Full.ArithmeticModel.yNat n)
    (hyCutoff : Erdos390.Full.ArithmeticModel.yNat n <
      centralAnchorCutoff depth n)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)) :
    Disjoint certificate.anchors
      (baseBankFactors R.exactificationState) := by
  apply R.disjoint_baseExactificationBank_of_disjoint_states
  exact R.guardedCentralAnchors_disjoint_exactificationStates
    hdepth hnCutoff hfixed hyCutoff certificate

/-- The same guard holds for every actual Boolean toggle choice. -/
theorem guardedCentralAnchors_disjoint_chosenExactificationBank
    {c : ℝ} {depth n M : ℕ}
    (R : BankPaperRealization n M) (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hfixed : 2 * depth + 1 ≤ Erdos390.Full.ArithmeticModel.yNat n)
    (hyCutoff : Erdos390.Full.ArithmeticModel.yNat n <
      centralAnchorCutoff depth n)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (choice : SignedBankSlot (bankRoundingBetaOnSupport n) → Bool) :
    Disjoint certificate.anchors
      (chosenBankFactors R.exactificationState choice) := by
  apply R.disjoint_chosenExactificationBank_of_disjoint_states
  exact R.guardedCentralAnchors_disjoint_exactificationStates
    hdepth hnCutoff hfixed hyCutoff certificate

/-- Expanded finite bundle supplying the individual-state, base-bank, and
arbitrary-toggle guards simultaneously. -/
theorem guardedCentralAnchor_exactificationGuards
    {c : ℝ} {depth n M : ℕ}
    (R : BankPaperRealization n M) (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hfixed : 2 * depth + 1 ≤ Erdos390.Full.ArithmeticModel.yNat n)
    (hyCutoff : Erdos390.Full.ArithmeticModel.yNat n <
      centralAnchorCutoff depth n)
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
          (chosenBankFactors R.exactificationState choice) := by
  refine ⟨?_, ?_, ?_⟩
  · exact R.guardedCentralAnchors_disjoint_exactificationStates
      hdepth hnCutoff hfixed hyCutoff certificate
  · exact R.guardedCentralAnchors_disjoint_baseExactificationBank
      hdepth hnCutoff hfixed hyCutoff certificate
  · intro choice
    exact R.guardedCentralAnchors_disjoint_chosenExactificationBank
      hdepth hnCutoff hfixed hyCutoff certificate choice

/-- Eventual universal terminal at fixed depth.  It quantifies the paper
endpoint, actual realization, certificate, and toggle choice only after the
asymptotic threshold has been crossed. -/
theorem eventually_guardedCentralAnchor_exactificationGuards
    (c : ℝ) (depth : ℕ) (hdepth : 2 ≤ depth) :
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
              (chosenBankFactors R.exactificationState choice) := by
  filter_upwards [
      eventually_guardedCentralAnchors_disjoint_allComponentOccurrences
        c depth hdepth] with n hcollision
  intro M R certificate
  have hstates : ∀ slot selected,
      Disjoint certificate.anchors
        (R.exactificationState slot selected) := by
    intro slot selected
    exact R.disjoint_exactificationState_of_disjoint_allComponentOccurrences
      certificate.anchors (hcollision M R certificate) slot selected
  refine ⟨hstates, ?_, ?_⟩
  · exact R.disjoint_baseExactificationBank_of_disjoint_states
      certificate.anchors hstates
  · intro choice
    exact R.disjoint_chosenExactificationBank_of_disjoint_states
      certificate.anchors hstates choice

end BankPaperRealization

end

end Erdos390.WholePaper
