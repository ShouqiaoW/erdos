import Erdos390.WholePaper.GuardedUpperProductAssembly
import Erdos390.WholePaper.BankPaperExactificationApplication
import Erdos390.WholePaper.BankPaperAnchorExactificationGuards
import Erdos390.WholePaper.BankPaperFinalFactorSetInterval

/-!
# Final guarded upper-product assembly for the concrete paper bank

The residual complement selection returned by exactification is the union of
its genuinely fixed factors, the chosen paper-bank state, and the selected
candidate factors.  The guarded central anchors remain a fourth, external
family.  This file joins that external family to the exactified residual set
and exposes exactly the two missing cross-family guards:

* anchors versus the exactification-fixed factors;
* anchors versus the selected candidates (or, more uniformly, their whole
  candidate universe).

Anchor versus bank-state disjointness is discharged by the concrete guarded
collision theorem.  The remaining product input is also kept literal:
exactification supplies `residual.prod = Y`, while the caller must still
supply `Y * centralAnchorDivisor = centralTailProduct`.  No quotient or
unstated disjointness is manufactured here.
-/

namespace Erdos390.WholePaper

noncomputable section

namespace BankPaperRealization

/-- The complete residual complement selection produced after Boolean bank
replacement and integral candidate selection. -/
def exactificationResidualFactorSet
    {A : Type*} [Fintype A] {n M : ℕ}
    (R : BankPaperRealization n M) (fixed : Finset ℕ)
    (positive negative : ↑(bankRoundingPrimeSupport n) → ℕ)
    (value : A → ℕ) (X : A → ℝ) : Finset ℕ :=
  guardedFinalFactorSet fixed R.exactificationState
    (signedBankStateChoice positive negative) value X

/-- The complement selection assembled from the external guarded central
anchors and the exactification residual selection. -/
def guardedComplementFactorSet
    {A : Type*} [Fintype A] {c : ℝ} {depth n M : ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset ℕ)
    (positive negative : ↑(bankRoundingPrimeSupport n) → ℕ)
    (value : A → ℕ) (X : A → ℝ) : Finset ℕ :=
  certificate.anchors ∪
    R.exactificationResidualFactorSet fixed positive negative value X

/-! ## The two genuinely missing anchor guards -/

/-- Exact cross-family guard.  The anchor/bank branch is automatic; only
anchor/fixed and anchor/selected disjointness remain as inputs. -/
theorem guardedCentralAnchors_disjoint_exactificationResidualFactorSet
    {A : Type*} [Fintype A] {c : ℝ} {depth n M : ℕ}
    (R : BankPaperRealization n M) (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hprefix : 2 * depth + 1 ≤ Erdos390.Full.ArithmeticModel.yNat n)
    (hyCutoff : Erdos390.Full.ArithmeticModel.yNat n <
      centralAnchorCutoff depth n)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset ℕ)
    (positive negative : ↑(bankRoundingPrimeSupport n) → ℕ)
    (value : A → ℕ) (X : A → ℝ)
    (hanchorsFixed : Disjoint certificate.anchors fixed)
    (hanchorsSelected :
      Disjoint certificate.anchors (selectedFactorSet value X)) :
    Disjoint certificate.anchors
      (R.exactificationResidualFactorSet
        fixed positive negative value X) := by
  have hanchorsBank : Disjoint certificate.anchors
      (chosenBankFactors R.exactificationState
        (signedBankStateChoice positive negative)) :=
    R.guardedCentralAnchors_disjoint_chosenExactificationBank
      hdepth hnCutoff hprefix hyCutoff certificate
        (signedBankStateChoice positive negative)
  rw [exactificationResidualFactorSet, guardedFinalFactorSet]
  exact Finset.disjoint_union_right.mpr
    ⟨Finset.disjoint_union_right.mpr
      ⟨hanchorsFixed, hanchorsBank⟩, hanchorsSelected⟩

/-- Uniform form in which anchors avoid the whole candidate universe before
the integral selection `X` is known. -/
theorem guardedCentralAnchors_disjoint_exactificationResidualFactorSet_of_candidateUniverse
    {A : Type*} [Fintype A] {c : ℝ} {depth n M : ℕ}
    (R : BankPaperRealization n M) (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hprefix : 2 * depth + 1 ≤ Erdos390.Full.ArithmeticModel.yNat n)
    (hyCutoff : Erdos390.Full.ArithmeticModel.yNat n <
      centralAnchorCutoff depth n)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset ℕ)
    (positive negative : ↑(bankRoundingPrimeSupport n) → ℕ)
    (value : A → ℕ) (X : A → ℝ)
    (hanchorsFixed : Disjoint certificate.anchors fixed)
    (hanchorsCandidate :
      Disjoint certificate.anchors (Finset.univ.image value)) :
    Disjoint certificate.anchors
      (R.exactificationResidualFactorSet
        fixed positive negative value X) := by
  apply R.guardedCentralAnchors_disjoint_exactificationResidualFactorSet
    hdepth hnCutoff hprefix hyCutoff certificate fixed positive negative
      value X hanchorsFixed
  exact hanchorsCandidate.mono Finset.Subset.rfl
    (selectedFactorSet_subset_candidateUniverse value X)

/-- Expanded four-family collision census: the fixed, chosen-bank, selected,
and aggregate residual sets are all displayed separately. -/
theorem guardedCentralAnchor_exactificationResidualGuards_of_candidateUniverse
    {A : Type*} [Fintype A] {c : ℝ} {depth n M : ℕ}
    (R : BankPaperRealization n M) (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hprefix : 2 * depth + 1 ≤ Erdos390.Full.ArithmeticModel.yNat n)
    (hyCutoff : Erdos390.Full.ArithmeticModel.yNat n <
      centralAnchorCutoff depth n)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset ℕ)
    (positive negative : ↑(bankRoundingPrimeSupport n) → ℕ)
    (value : A → ℕ) (X : A → ℝ)
    (hanchorsFixed : Disjoint certificate.anchors fixed)
    (hanchorsCandidate :
      Disjoint certificate.anchors (Finset.univ.image value)) :
    Disjoint certificate.anchors fixed ∧
      Disjoint certificate.anchors
        (chosenBankFactors R.exactificationState
          (signedBankStateChoice positive negative)) ∧
      Disjoint certificate.anchors (selectedFactorSet value X) ∧
      Disjoint certificate.anchors
        (R.exactificationResidualFactorSet
          fixed positive negative value X) := by
  have hanchorsBank :=
    R.guardedCentralAnchors_disjoint_chosenExactificationBank
      hdepth hnCutoff hprefix hyCutoff certificate
        (signedBankStateChoice positive negative)
  have hanchorsSelected :
      Disjoint certificate.anchors (selectedFactorSet value X) :=
    hanchorsCandidate.mono Finset.Subset.rfl
      (selectedFactorSet_subset_candidateUniverse value X)
  have hanchorsResidual :=
    R.guardedCentralAnchors_disjoint_exactificationResidualFactorSet
      hdepth hnCutoff hprefix hyCutoff certificate fixed positive negative
        value X hanchorsFixed hanchorsSelected
  exact ⟨hanchorsFixed, hanchorsBank, hanchorsSelected, hanchorsResidual⟩

/-! ## Interval and product assembly -/

theorem exactificationResidualFactorSet_subset_factorInterval
    {A : Type*} [Fintype A] {n M : ℕ}
    (R : BankPaperRealization n M)
    (fixed : Finset ℕ) (hfixed : fixed ⊆ factorInterval n M)
    (positive negative : ↑(bankRoundingPrimeSupport n) → ℕ)
    (value : A → ℕ) (X : A → ℝ)
    (hvalue : ∀ a, value a ∈ factorInterval n M) :
    R.exactificationResidualFactorSet fixed positive negative value X ⊆
      factorInterval n M := by
  simpa only [exactificationResidualFactorSet] using
    R.guardedFinalFactorSet_subset_factorInterval fixed hfixed
      (signedBankStateChoice positive negative) value X hvalue

/-- The assembled complement selection is still contained in the complete
factor interval. -/
theorem guardedComplementFactorSet_subset_factorInterval
    {A : Type*} [Fintype A] {c : ℝ} {depth n h : ℕ}
    (R : BankPaperRealization n (2 * n + h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset ℕ)
    (hfixed : fixed ⊆ factorInterval n (2 * n + h))
    (positive negative : ↑(bankRoundingPrimeSupport n) → ℕ)
    (value : A → ℕ) (X : A → ℝ)
    (hvalue : ∀ a, value a ∈ factorInterval n (2 * n + h)) :
    R.guardedComplementFactorSet certificate fixed positive negative value X
      ⊆ factorInterval n (2 * n + h) := by
  rw [guardedComplementFactorSet]
  apply Finset.union_subset
  · intro anchor hanchor
    have hcentral := Finset.mem_Ioc.mp
      (certificate.anchors_subset hanchor)
    exact Finset.mem_Ioc.mpr ⟨hcentral.1, hcentral.2.trans (by omega)⟩
  · exact R.exactificationResidualFactorSet_subset_factorInterval
      fixed hfixed positive negative value X hvalue

/-- Exact complement-product identity.  The final premise is the remaining
tail quotient identity not supplied by exactification itself. -/
theorem guardedComplementFactorSet_prod
    {A : Type*} [Fintype A] {c : ℝ} {depth n h Y : ℕ}
    (R : BankPaperRealization n (2 * n + h))
    (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hprefix : 2 * depth + 1 ≤ Erdos390.Full.ArithmeticModel.yNat n)
    (hyCutoff : Erdos390.Full.ArithmeticModel.yNat n <
      centralAnchorCutoff depth n)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset ℕ)
    (positive negative : ↑(bankRoundingPrimeSupport n) → ℕ)
    (value : A → ℕ) (X : A → ℝ)
    (hanchorsFixed : Disjoint certificate.anchors fixed)
    (hanchorsSelected :
      Disjoint certificate.anchors (selectedFactorSet value X))
    (hresidualProduct :
      (R.exactificationResidualFactorSet
        fixed positive negative value X).prod id = Y)
    (hYTail :
      Y * centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q =
        centralTailProduct n h) :
    (R.guardedComplementFactorSet certificate fixed positive negative value X).prod id =
      Nat.choose (2 * n) n * centralTailProduct n h := by
  have hdisjoint :=
    R.guardedCentralAnchors_disjoint_exactificationResidualFactorSet
      hdepth hnCutoff hprefix hyCutoff certificate fixed positive negative
        value X hanchorsFixed hanchorsSelected
  have hresidualTail :
      (R.exactificationResidualFactorSet
          fixed positive negative value X).prod id *
          centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q =
        centralTailProduct n h := by
    rw [hresidualProduct]
    exact hYTail
  simpa only [guardedComplementFactorSet] using
    guardedCentral_union_residual_prod hdisjoint certificate.anchors_prod
      hresidualTail

/-- Concrete admissibility terminal obtained from the exactification product
and the one still-explicit tail product identity. -/
theorem isAdmissibleEndpoint_of_exactificationResidual
    {A : Type*} [Fintype A] {c : ℝ} {depth n h Y : ℕ}
    (R : BankPaperRealization n (2 * n + h))
    (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hprefix : 2 * depth + 1 ≤ Erdos390.Full.ArithmeticModel.yNat n)
    (hyCutoff : Erdos390.Full.ArithmeticModel.yNat n <
      centralAnchorCutoff depth n)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset ℕ)
    (hfixed : fixed ⊆ factorInterval n (2 * n + h))
    (positive negative : ↑(bankRoundingPrimeSupport n) → ℕ)
    (value : A → ℕ) (X : A → ℝ)
    (hvalue : ∀ a, value a ∈ factorInterval n (2 * n + h))
    (hanchorsFixed : Disjoint certificate.anchors fixed)
    (hanchorsSelected :
      Disjoint certificate.anchors (selectedFactorSet value X))
    (hresidualProduct :
      (R.exactificationResidualFactorSet
        fixed positive negative value X).prod id = Y)
    (hYTail :
      Y * centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q =
        centralTailProduct n h) :
    IsAdmissibleEndpoint n (2 * n + h) := by
  have hresidualSubset :=
    R.exactificationResidualFactorSet_subset_factorInterval
      fixed hfixed positive negative value X hvalue
  have hdisjoint :=
    R.guardedCentralAnchors_disjoint_exactificationResidualFactorSet
      hdepth hnCutoff hprefix hyCutoff certificate fixed positive negative
        value X hanchorsFixed hanchorsSelected
  have hresidualTail :
      (R.exactificationResidualFactorSet
          fixed positive negative value X).prod id *
          centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q =
        centralTailProduct n h := by
    rw [hresidualProduct]
    exact hYTail
  exact certificate.isAdmissibleEndpoint_of_residual
    (lt_of_lt_of_le Nat.zero_lt_one R.ordinary.one_le_n)
      hresidualSubset hdisjoint
      hresidualTail

/-! ## Expanded final bundle -/

/-- The complete post-exactification assembly.  Candidate-universe
disjointness is used so the input can be fixed before `X` is selected. -/
theorem guardedExactification_finalAssembly
    {A : Type*} [Fintype A] {c : ℝ} {depth n h Y : ℕ}
    (R : BankPaperRealization n (2 * n + h))
    (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hprefix : 2 * depth + 1 ≤ Erdos390.Full.ArithmeticModel.yNat n)
    (hyCutoff : Erdos390.Full.ArithmeticModel.yNat n <
      centralAnchorCutoff depth n)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset ℕ)
    (hfixed : fixed ⊆ factorInterval n (2 * n + h))
    (positive negative : ↑(bankRoundingPrimeSupport n) → ℕ)
    (value : A → ℕ) (X : A → ℝ)
    (hvalue : ∀ a, value a ∈ factorInterval n (2 * n + h))
    (hanchorsFixed : Disjoint certificate.anchors fixed)
    (hanchorsCandidate :
      Disjoint certificate.anchors (Finset.univ.image value))
    (hresidualProduct :
      (R.exactificationResidualFactorSet
        fixed positive negative value X).prod id = Y)
    (hYTail :
      Y * centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q =
        centralTailProduct n h) :
    Disjoint certificate.anchors
        (R.exactificationResidualFactorSet
          fixed positive negative value X) ∧
      R.exactificationResidualFactorSet fixed positive negative value X ⊆
        factorInterval n (2 * n + h) ∧
      R.guardedComplementFactorSet certificate fixed positive negative value X
        ⊆ factorInterval n (2 * n + h) ∧
      (R.exactificationResidualFactorSet
        fixed positive negative value X).prod id = Y ∧
      (R.guardedComplementFactorSet certificate fixed positive negative
        value X).prod id =
          Nat.choose (2 * n) n * centralTailProduct n h ∧
      IsAdmissibleEndpoint n (2 * n + h) := by
  have hanchorsSelected : Disjoint certificate.anchors
      (selectedFactorSet value X) :=
    hanchorsCandidate.mono Finset.Subset.rfl
      (selectedFactorSet_subset_candidateUniverse value X)
  have hdisjoint :=
    R.guardedCentralAnchors_disjoint_exactificationResidualFactorSet
      hdepth hnCutoff hprefix hyCutoff certificate fixed positive negative
        value X hanchorsFixed hanchorsSelected
  have hresidualSubset :=
    R.exactificationResidualFactorSet_subset_factorInterval
      fixed hfixed positive negative value X hvalue
  have hfinalSubset :=
    R.guardedComplementFactorSet_subset_factorInterval certificate fixed
      hfixed positive negative value X hvalue
  have hfinalProduct :=
    R.guardedComplementFactorSet_prod hdepth hnCutoff hprefix hyCutoff
      certificate fixed positive negative value X hanchorsFixed
        hanchorsSelected hresidualProduct hYTail
  have hadmissible :=
    R.isAdmissibleEndpoint_of_exactificationResidual
      hdepth hnCutoff hprefix hyCutoff certificate fixed hfixed
        positive negative value X hvalue hanchorsFixed hanchorsSelected
          hresidualProduct hYTail
  exact ⟨hdisjoint, hresidualSubset, hfinalSubset, hresidualProduct,
    hfinalProduct, hadmissible⟩

end BankPaperRealization

end

end Erdos390.WholePaper
