import Erdos390.WholePaper.BankPaperGuardedUpperProductAssembly

/-! # Expanded statement audit for the concrete guarded final assembly -/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

example {A : Type*} [Fintype A] {c : ℝ} {depth n h Y : ℕ}
    (R : BankPaperRealization n (2 * n + h))
    (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hprefix : 2 * depth + 1 ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
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
      IsAdmissibleEndpoint n (2 * n + h) :=
  R.guardedExactification_finalAssembly hdepth hnCutoff hprefix hyCutoff
    certificate fixed hfixed positive negative value X hvalue
      hanchorsFixed hanchorsCandidate hresidualProduct hYTail

/-- Audit the exact missing cross-family hypotheses separately: anchors must
avoid the exactification-fixed set and the selected candidate set; the bank
branch is discharged internally. -/
example {A : Type*} [Fintype A] {c : ℝ} {depth n M : ℕ}
    (R : BankPaperRealization n M) (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hprefix : 2 * depth + 1 ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
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
        fixed positive negative value X) :=
  R.guardedCentralAnchors_disjoint_exactificationResidualFactorSet
    hdepth hnCutoff hprefix hyCutoff certificate fixed positive negative
      value X hanchorsFixed hanchorsSelected

example {A : Type*} [Fintype A] {c : ℝ} {depth n h Y : ℕ}
    (R : BankPaperRealization n (2 * n + h))
    (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hprefix : 2 * depth + 1 ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
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
    IsAdmissibleEndpoint n (2 * n + h) :=
  R.isAdmissibleEndpoint_of_exactificationResidual
    hdepth hnCutoff hprefix hyCutoff certificate fixed hfixed
      positive negative value X hvalue hanchorsFixed hanchorsSelected
        hresidualProduct hYTail

/-! The two public definitions are audited by their literal unfoldings. -/

example {A : Type*} [Fintype A] {n M : ℕ}
    (R : BankPaperRealization n M) (fixed : Finset ℕ)
    (positive negative : ↑(bankRoundingPrimeSupport n) → ℕ)
    (value : A → ℕ) (X : A → ℝ) :
    R.exactificationResidualFactorSet fixed positive negative value X =
      guardedFinalFactorSet fixed R.exactificationState
        (signedBankStateChoice positive negative) value X := by
  rfl

example {A : Type*} [Fintype A] {c : ℝ} {depth n M : ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset ℕ)
    (positive negative : ↑(bankRoundingPrimeSupport n) → ℕ)
    (value : A → ℕ) (X : A → ℝ) :
    R.guardedComplementFactorSet certificate fixed positive negative value X =
      certificate.anchors ∪
        R.exactificationResidualFactorSet
          fixed positive negative value X := by
  rfl

/-! Audit the candidate-universe form used before the integral selector is
known. -/

example {A : Type*} [Fintype A] {c : ℝ} {depth n M : ℕ}
    (R : BankPaperRealization n M) (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hprefix : 2 * depth + 1 ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
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
        fixed positive negative value X) :=
  R.guardedCentralAnchors_disjoint_exactificationResidualFactorSet_of_candidateUniverse
    hdepth hnCutoff hprefix hyCutoff certificate fixed positive negative
      value X hanchorsFixed hanchorsCandidate

/-! The expanded guard bundle retains all four collision statements. -/

example {A : Type*} [Fintype A] {c : ℝ} {depth n M : ℕ}
    (R : BankPaperRealization n M) (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hprefix : 2 * depth + 1 ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
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
          fixed positive negative value X) :=
  R.guardedCentralAnchor_exactificationResidualGuards_of_candidateUniverse
    hdepth hnCutoff hprefix hyCutoff certificate fixed positive negative
      value X hanchorsFixed hanchorsCandidate

/-! Audit the two interval-support layers independently. -/

example {A : Type*} [Fintype A] {n M : ℕ}
    (R : BankPaperRealization n M)
    (fixed : Finset ℕ) (hfixed : fixed ⊆ factorInterval n M)
    (positive negative : ↑(bankRoundingPrimeSupport n) → ℕ)
    (value : A → ℕ) (X : A → ℝ)
    (hvalue : ∀ a, value a ∈ factorInterval n M) :
    R.exactificationResidualFactorSet fixed positive negative value X ⊆
      factorInterval n M :=
  R.exactificationResidualFactorSet_subset_factorInterval
    fixed hfixed positive negative value X hvalue

example {A : Type*} [Fintype A] {c : ℝ} {depth n h : ℕ}
    (R : BankPaperRealization n (2 * n + h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset ℕ)
    (hfixed : fixed ⊆ factorInterval n (2 * n + h))
    (positive negative : ↑(bankRoundingPrimeSupport n) → ℕ)
    (value : A → ℕ) (X : A → ℝ)
    (hvalue : ∀ a, value a ∈ factorInterval n (2 * n + h)) :
    R.guardedComplementFactorSet certificate fixed positive negative value X ⊆
      factorInterval n (2 * n + h) :=
  R.guardedComplementFactorSet_subset_factorInterval
    certificate fixed hfixed positive negative value X hvalue

/-! The product theorem is audited separately from admissibility so its
division-free tail identity remains visible. -/

example {A : Type*} [Fintype A] {c : ℝ} {depth n h Y : ℕ}
    (R : BankPaperRealization n (2 * n + h))
    (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hprefix : 2 * depth + 1 ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
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
      Nat.choose (2 * n) n * centralTailProduct n h :=
  R.guardedComplementFactorSet_prod
    hdepth hnCutoff hprefix hyCutoff certificate fixed positive negative
      value X hanchorsFixed hanchorsSelected hresidualProduct hYTail

end

end Erdos390.WholePaper
