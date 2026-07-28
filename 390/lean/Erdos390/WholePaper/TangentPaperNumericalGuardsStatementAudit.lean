import Erdos390.WholePaper.TangentPaperNumericalGuards

/-! # Expanded statement audit for the literal Section 9 guard family -/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

example {n M : ℕ} (R : BankPaperRealization n M) :
    R.tangentPaperBankRows = R.allMarkers ∧
      R.tangentPaperDedicatedRows = ∅ :=
  ⟨rfl, rfl⟩

example
    {c : ℝ} {depth n M : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ) :
    R.tangentPaperNumericalGuardSet certificate fixedExceptional =
      certificate.anchors ∪ fixedExceptional ∪ R.prechargeDonorSet ∪
        R.prechargeBaseState ∪ R.prechargeAlternateState := rfl

example {n M : ℕ} (R : BankPaperRealization n M) :
    R.tangentPaperBankRows.card =
        Fintype.card (BankPaperMarkerRequest n) ∧
      R.tangentPaperDedicatedRows.card = 0 ∧
      R.tangentPaperDedicatedRows ⊆ R.tangentPaperBankRows :=
  ⟨R.tangentPaperBankRows_card_eq_componentCount,
    R.tangentPaperDedicatedRows_card,
    R.tangentPaperDedicatedRows_subset_bankRows⟩

example {n M : ℕ} (R : BankPaperRealization n M) :
    R.tangentPaperBankRows.card ≤ bankPaperAnchorMarkerBudget n :=
  R.tangentPaperBankRows_card_le_anchorMarkerBudget

example {n M y : ℕ} (R : BankPaperRealization n M)
    (multipliers : Finset ℕ) :
    tangentDedicatedRowMultipliers y R.tangentPaperDedicatedRows
      multipliers = ∅ :=
  R.tangentDedicatedRowMultipliers_tangentPaperDedicatedRows multipliers

example
    {c : ℝ} {depth n M : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n) :
    (R.tangentPaperNumericalGuardSet certificate fixedExceptional).card ≤
      (residualCentralPrimes n
          (centralAnchorCutoff depth n)).card +
        (largeCentralPrimes n
          (centralAnchorCutoff depth n)).card +
        fixedExceptional.card +
        3 * Fintype.card (BankPaperMarkerRequest n) :=
  R.tangentPaperNumericalGuardSet_card_le
    certificate fixedExceptional hnCutoff

example
    {c : ℝ} {depth n M : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n) :
    (R.tangentPaperNumericalGuardSet certificate fixedExceptional).card ≤
      (residualCentralPrimes n
          (centralAnchorCutoff depth n)).card +
        (largeCentralPrimes n
          (centralAnchorCutoff depth n)).card +
        fixedExceptional.card + 3 * bankPaperAnchorMarkerBudget n :=
  R.tangentPaperNumericalGuardSet_card_le_anchorMarkerBudget
    certificate fixedExceptional hnCutoff

example
    {c : ℝ} {depth n W y ℓ P : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hPrefix : 2 * depth + 1 ≤ W)
    (hWℓ : W < ℓ) (hℓy : ℓ ≤ y)
    (hyCutoff : y < centralAnchorCutoff depth n)
    (hℓPrime : ℓ.Prime)
    (hP : P ∈ largeCentralPrimes n
      (centralAnchorCutoff depth n)) :
    ¬ℓ ∣ largeCentralAnchor certificate.q P :=
  mediumPrime_not_dvd_guardedLargeCentralAnchor certificate hPrefix hWℓ
    hℓy hyCutoff hℓPrime hP

example
    {c : ℝ} {depth n W y u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ y)
    (hyCutoff : y < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    certificate.anchors.filter (fun g ↦ u ∣ g ∨ v ∣ g) ⊆
      {promotedCentralFactor n u, promotedCentralFactor n v} :=
  guardedCentralAnchors_pairPrimeDivisors_subset certificate hTwoW
    hPrefix hWv hvu huy hyCutoff huPrime hvPrime

example
    {c : ℝ} {depth n W y u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ y)
    (hyCutoff : y < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (certificate.anchors.filter (fun g ↦ u ∣ g ∨ v ∣ g)).card ≤ 2 :=
  card_guardedCentralAnchors_pairPrimeDivisors_le_two certificate hTwoW
    hPrefix hWv hvu huy hyCutoff huPrime hvPrime

example
    {c : ℝ} {depth n M K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ) :
    R.tangentPaperPairNumericalGuards certificate fixedExceptional
        K h u v =
      (R.tangentPaperNumericalGuardSet certificate fixedExceptional).filter
        (fun g ↦ g ≤ 2 * n - K * h ∧ (u ∣ g ∨ v ∣ g)) := rfl

example
    {c : ℝ} {depth n M K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M) :
    R.tangentPaperPairNumericalGuards certificate fixedExceptional
        K h u v ⊆
      certificate.anchors.filter (fun g ↦ u ∣ g ∨ v ∣ g) ∪
        R.prechargeBaseState ∪ R.prechargeAlternateState :=
  R.tangentPaperPairNumericalGuards_subset_anchor_states
    certificate fixedExceptional hfixedTail

example
    {c : ℝ} {depth n M W K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (R.tangentPaperPairNumericalGuards certificate fixedExceptional
      K h u v).card ≤
        2 + 2 * Fintype.card (BankPaperMarkerRequest n) :=
  R.tangentPaperPairNumericalGuards_card_le_componentCount
    certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
      hyCutoff huPrime hvPrime

example
    {c : ℝ} {depth n M W K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (R.tangentPaperPairNumericalGuards certificate fixedExceptional
      K h u v).card ≤ 2 + 2 * bankPaperAnchorMarkerBudget n :=
  R.tangentPaperPairNumericalGuards_card_le_anchorMarkerBudget
    certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
      hyCutoff huPrime hvPrime

example
    {c : ℝ} {depth n M K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u) :
    tangentLabelGuardDeletedMultipliers u
        (R.tangentPaperNumericalGuardSet certificate fixedExceptional)
        (tangentCommonMultiplierInterval n K h u v) =
      tangentLabelGuardDeletedMultipliers u
        (R.tangentPaperPairNumericalGuards certificate fixedExceptional
          K h u v)
        (tangentCommonMultiplierInterval n K h u v) :=
  R.tangentLabelGuardDeletedMultipliers_numericalGuardSet_eq_pair_left
    certificate fixedExceptional hu hv hvu

example
    {c : ℝ} {depth n M K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u) :
    tangentLabelGuardDeletedMultipliers v
        (R.tangentPaperNumericalGuardSet certificate fixedExceptional)
        (tangentCommonMultiplierInterval n K h u v) =
      tangentLabelGuardDeletedMultipliers v
        (R.tangentPaperPairNumericalGuards certificate fixedExceptional
          K h u v)
        (tangentCommonMultiplierInterval n K h u v) :=
  R.tangentLabelGuardDeletedMultipliers_numericalGuardSet_eq_pair_right
    certificate fixedExceptional hu hv hvu

example
    {c : ℝ} {depth n M K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u) :
    tangentEndpointGuardDeletedMultipliers u v
        (R.tangentPaperNumericalGuardSet certificate fixedExceptional)
        (tangentCommonMultiplierInterval n K h u v) =
      tangentEndpointGuardDeletedMultipliers u v
        (R.tangentPaperPairNumericalGuards certificate fixedExceptional
          K h u v)
        (tangentCommonMultiplierInterval n K h u v) :=
  R.tangentEndpointGuardDeletedMultipliers_numericalGuardSet_eq_pair
    certificate fixedExceptional hu hv hvu

example
    {c : ℝ} {depth n M W K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (tangentEndpointGuardDeletedMultipliers u v
      (R.tangentPaperNumericalGuardSet certificate fixedExceptional)
      (tangentCommonMultiplierInterval n K h u v)).card ≤
        4 + 4 * Fintype.card (BankPaperMarkerRequest n) :=
  R.card_tangentEndpointGuardDeletedMultipliers_numericalGuardSet_le
    certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
      hyCutoff huPrime hvPrime

example
    {c : ℝ} {depth n M W K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    ((tangentCommonMultiplierInterval n K h u v).filter
          (fun a ↦ u * a ∈
            R.tangentPaperNumericalGuardSet certificate fixedExceptional) ∪
        (tangentCommonMultiplierInterval n K h u v).filter
          (fun a ↦ v * a ∈
            R.tangentPaperNumericalGuardSet certificate fixedExceptional)).card ≤
      4 + 4 * bankPaperAnchorMarkerBudget n := by
  exact
    R.card_tangentEndpointGuardDeletedMultipliers_numericalGuardSet_le_budget
      certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
        hyCutoff huPrime hvPrime

example
    {c : ℝ} {depth n M W K h Phead X0 u v : ℕ}
    {left right : ℕ → ℕ} {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (Finset.Ioc (n / v) ((2 * n - K * h) / u)).card ≤
      (tangentCleanCommonMultiplierList n K h Phead X0 (yNat n) u v
        R.tangentPaperDedicatedRows
        (R.tangentPaperNumericalGuardSet certificate fixedExceptional)).card +
      (tangentHeadBadMultipliers Phead
        (Finset.Ioc (n / v) ((2 * n - K * h) / u))).card +
      (tangentExceptionalMultipliers n X0 (yNat n)
        (Finset.Ioc (n / v) ((2 * n - K * h) / u))).card +
      4 + 4 * bankPaperAnchorMarkerBudget n := by
  exact R.tangentPaperCommonMultiplier_finite_deletion_ledger
    certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
      hyCutoff huPrime hvPrime

end

end Erdos390.WholePaper
