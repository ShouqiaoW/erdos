import Erdos390.WholePaper.BankPaperCanonicalGuardLocalRowLedger

/-!
# Expanded statement audit for the guard-local rough-row ledger

This audit records the exact finite conclusions separately from the three
remaining explicit obligations: a local census, guarded broad-pool supply,
and guarded-row capacity.  It covers all 15 public definitions and all 24
public theorems in the ledger; the one private cardinality helper is covered
transitively through the public donor/base multiplicity theorem.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! ## Complete definition audit -/

example
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) :
    R.roughCanonicalGuardSet certificate deltaStar =
      R.tangentPaperNumericalGuardSet certificate
        (R.paperFixedExceptionalFactors deltaStar) := by
  rfl

example (n label : ℕ) (deltaStar : ℝ) :
    RoughCanonicalExceptionalLabel n deltaStar label ↔
      2 * (n : ℝ) / (label : ℝ) < (n : ℝ) ^ deltaStar := by
  rfl

example (n label : ℕ) (deltaStar : ℝ) :
    RoughCanonicalActiveNonexceptionalLabel n deltaStar label ↔
      label ≠ 1 ∧
        (n : ℝ) ^ deltaStar ≤ 2 * (n : ℝ) / (label : ℝ) := by
  rfl

example
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K : ℕ) :
    R.roughCanonicalGuardedCandidateSet certificate deltaStar K =
      roughRawCandidateSet n h K \
        R.tangentPaperNumericalGuardSet certificate
          (R.paperFixedExceptionalFactors deltaStar) := by
  rfl

example
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (W K label : ℕ) :
    R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label =
      roughCanonicalBroadCorrectionPool W n h K (yNat n) label \
        R.roughCanonicalGuardSet certificate deltaStar := by
  rfl

example
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    R.roughCanonicalGuardedRow certificate deltaStar K label =
      completeRoughRowFiber (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        label := by
  rfl

example
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    R.roughCanonicalGuardDeletedRow certificate deltaStar K label =
      completeRoughRowFiber (yNat n) (roughRawCandidateSet n h K) label ∩
        R.roughCanonicalGuardSet certificate deltaStar := by
  rfl

example {n M : ℕ} (R : BankPaperRealization n M) (label : ℕ) :
    {donor : ↑R.prechargeDonorSet //
      completeRoughLabel (yNat n) donor.1 = label} ≃
    {base : ↑R.prechargeBaseState //
      completeRoughLabel (yNat n) base.1 = label} :=
  R.prechargeDonorBaseRowEquiv label

example {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ) :
    R.roughCanonicalPostchargeRowTargetInt deltaStar label =
      (roughUpperCompleteRoughRowTarget n h (yNat n) label : ℤ) -
        (completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) label : ℤ) -
        (completeLabelMultiplicity (yNat n)
          R.prechargeBaseState label : ℤ) := by
  rfl

example {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ) :
    R.roughCanonicalPostchargeRowTarget deltaStar label =
      (roughUpperCompleteRoughRowTarget n h (yNat n) label : ℝ) -
        (completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) label : ℝ) -
        (completeLabelMultiplicity (yNat n)
          R.prechargeBaseState label : ℝ) := by
  rfl

example (n h K label : ℕ) (x : ℕ → ℝ) :
    roughCanonicalRawRowDiscrepancy n h K label x =
      (roughUpperCompleteRoughRowTarget n h (yNat n) label : ℝ) -
        ∑ a ∈ completeRoughRowFiber (yNat n)
          (roughRawCandidateSet n h K) label, x a := by
  rfl

example
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) (x : ℕ → ℝ) :
    R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
        K label x =
      R.roughCanonicalPostchargeRowTarget deltaStar label -
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          x a := by
  rfl

example
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label budget : ℕ) :
    RoughCanonicalGuardLocalCensusBound R certificate deltaStar K label
        budget ↔
      (R.roughCanonicalGuardDeletedRow certificate deltaStar K label).card ≤
        budget := by
  rfl

example
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (W K label minimum : ℕ) :
    RoughCanonicalGuardedBroadPoolCapacity R certificate deltaStar W K
        label minimum ↔
      minimum ≤
        (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
          W K label).card := by
  rfl

example
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    RoughCanonicalPostchargeRowCapacity R certificate deltaStar K label ↔
      R.roughCanonicalPostchargeRowTarget deltaStar label ≤
        ((R.roughCanonicalGuardedRow certificate deltaStar K label).card : ℝ) := by
  rfl

/-! ## Complete public theorem audit -/

example
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K : ℕ) :
    R.roughCanonicalGuardedCandidateSet certificate deltaStar K ⊆
      roughRawCandidateSet n h K :=
  R.roughCanonicalGuardedCandidateSet_subset_rawCandidateSet
    certificate deltaStar K

example
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K : ℕ) :
    Disjoint
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (R.roughCanonicalGuardSet certificate deltaStar) :=
  R.roughCanonicalGuardedCandidateSet_disjoint_guardSet
    certificate deltaStar K

example
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (W K label : ℕ) :
    R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label ⊆
      roughCanonicalBroadCorrectionPool W n h K (yNat n) label :=
  R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
    certificate deltaStar W K label

example
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    R.roughCanonicalGuardedRow certificate deltaStar K label =
      completeRoughRowFiber (yNat n) (roughRawCandidateSet n h K) label \
        R.roughCanonicalGuardSet certificate deltaStar :=
  R.roughCanonicalGuardedRow_eq_rawRow_sdiff_guardSet
    certificate deltaStar K label

example
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    Disjoint
      (R.roughCanonicalGuardedRow certificate deltaStar K label)
      (R.roughCanonicalGuardDeletedRow certificate deltaStar K label) :=
  R.roughCanonicalGuardedRow_disjoint_guardDeletedRow
    certificate deltaStar K label

example
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    R.roughCanonicalGuardedRow certificate deltaStar K label ∪
        R.roughCanonicalGuardDeletedRow certificate deltaStar K label =
      completeRoughRowFiber (yNat n) (roughRawCandidateSet n h K) label :=
  R.roughCanonicalGuardedRow_union_guardDeletedRow
    certificate deltaStar K label

example
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (W K label : ℕ) :
    R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label ⊆
      R.roughCanonicalGuardedRow certificate deltaStar K label :=
  R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
    certificate deltaStar W K label

example {n M : ℕ} (R : BankPaperRealization n M)
    (donor : ↑R.prechargeDonorSet) :
    completeRoughLabel (yNat n)
        (R.prechargeDonorBaseEquiv donor).1 =
      completeRoughLabel (yNat n) donor.1 :=
  R.prechargeDonorBaseEquiv_completeRoughLabel donor

example
    {n M : ℕ} (R : BankPaperRealization n M) (label : ℕ) :
    completeLabelMultiplicity (yNat n) R.prechargeBaseState label =
      completeLabelMultiplicity (yNat n) R.prechargeDonorSet label :=
  R.prechargeBaseState_completeLabelMultiplicity_eq_donorSet label

example {n label : ℕ} {deltaStar : ℝ} (hlabel : label ≠ 1) :
    RoughCanonicalActiveNonexceptionalLabel n deltaStar label ∨
      RoughCanonicalExceptionalLabel n deltaStar label :=
  roughCanonical_activeNonexceptional_or_exceptional hlabel

example {y label : ℕ} {A B : Finset ℕ} (hAB : A ⊆ B) :
    completeLabelMultiplicity y A label ≤
      completeLabelMultiplicity y B label :=
  completeLabelMultiplicity_mono hAB

example {y label : ℕ} {A B : Finset ℕ} (hAB : Disjoint A B) :
    completeLabelMultiplicity y (A ∪ B) label =
      completeLabelMultiplicity y A label +
        completeLabelMultiplicity y B label :=
  completeLabelMultiplicity_union_of_disjoint hAB

example {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ)
    (hexceptional : RoughCanonicalExceptionalLabel n deltaStar label) :
    completeLabelMultiplicity (yNat n)
        (R.paperFixedExceptionalFactors deltaStar ∪ R.prechargeDonorSet)
        label =
      roughUpperCompleteRoughRowTarget n h (yNat n) label :=
  R.paperFixedExceptional_union_prechargeDonor_multiplicity_eq_upperTarget_of_exceptional
    deltaStar label hexceptional

example
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ) :
    completeLabelMultiplicity (yNat n)
        (R.paperFixedExceptionalFactors deltaStar) label +
      completeLabelMultiplicity (yNat n) R.prechargeBaseState label ≤
        roughUpperCompleteRoughRowTarget n h (yNat n) label :=
  R.paperFixedExceptional_add_prechargeBase_multiplicity_le_upperTarget
    deltaStar label

example
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ)
    (hexceptional : RoughCanonicalExceptionalLabel n deltaStar label) :
    completeLabelMultiplicity (yNat n)
        (R.paperFixedExceptionalFactors deltaStar) label +
      completeLabelMultiplicity (yNat n) R.prechargeBaseState label =
        roughUpperCompleteRoughRowTarget n h (yNat n) label :=
  R.paperFixedExceptional_add_prechargeBase_multiplicity_eq_upperTarget_of_exceptional
    deltaStar label hexceptional

example
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ) :
    R.roughCanonicalPostchargeRowTarget deltaStar label =
        (R.roughCanonicalPostchargeRowTargetInt deltaStar label : ℝ) ∧
      0 ≤ R.roughCanonicalPostchargeRowTarget deltaStar label :=
  ⟨R.roughCanonicalPostchargeRowTarget_eq_intCast deltaStar label,
    R.roughCanonicalPostchargeRowTarget_nonneg deltaStar label⟩

example
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ)
    (hexceptional : RoughCanonicalExceptionalLabel n deltaStar label) :
    R.roughCanonicalPostchargeRowTargetInt deltaStar label = 0 ∧
      R.roughCanonicalPostchargeRowTarget deltaStar label = 0 :=
  ⟨R.roughCanonicalPostchargeRowTargetInt_eq_zero_of_exceptional
      deltaStar label hexceptional,
    R.roughCanonicalPostchargeRowTarget_eq_zero_of_exceptional
      deltaStar label hexceptional⟩

example
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) (x : ℕ → ℝ) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
        x a) +
      ∑ a ∈ R.roughCanonicalGuardDeletedRow certificate deltaStar
        K label, x a =
      ∑ a ∈ completeRoughRowFiber (yNat n)
        (roughRawCandidateSet n h K) label, x a :=
  R.sum_roughCanonicalGuardedRow_add_sum_guardDeletedRow
    certificate deltaStar K label x

example
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) (x : ℕ → ℝ) :
    R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
        K label x -
      roughCanonicalRawRowDiscrepancy n h K label x =
      -(completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) label : ℝ) -
        (completeLabelMultiplicity (yNat n)
          R.prechargeBaseState label : ℝ) +
        ∑ a ∈ R.roughCanonicalGuardDeletedRow certificate deltaStar
          K label, x a :=
  R.roughCanonicalGuardLocalDiscrepancyLedger
    certificate deltaStar K label x

example {n h K : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    Disjoint (roughRawCandidateSet n h K)
      (R.paperFixedExceptionalFactors deltaStar) :=
  R.roughRawCandidateSet_disjoint_paperFixedExceptionalFactors deltaStar

example {n h K : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h)) :
    Disjoint (roughRawCandidateSet n h K) R.prechargeDonorSet :=
  R.roughRawCandidateSet_disjoint_prechargeDonorSet

example
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    R.roughCanonicalGuardDeletedRow certificate deltaStar K label ⊆
      certificate.anchors ∪ R.prechargeBaseState ∪
        R.prechargeAlternateState :=
  R.roughCanonicalGuardDeletedRow_subset_anchors_union_bankStates
    certificate deltaStar K label

-- These are intentionally propositions to be supplied by later finite or
-- analytic work; this module does not manufacture them.
#check RoughCanonicalGuardLocalCensusBound
#check RoughCanonicalGuardedBroadPoolCapacity
#check RoughCanonicalPostchargeRowCapacity

end BankPaperRealization

end


end Erdos390.WholePaper
