import Erdos390.WholePaper.BankPaperCanonicalRoughRowCorrection
import Erdos390.WholePaper.BankPaperFixedExceptionalBacking
import Erdos390.WholePaper.TangentPaperNumericalGuards

/-!
# Guard-local canonical rough-row ledger

This module isolates the finite bookkeeping that occurs when the paper
passes from the raw canonical rough candidates to the candidates left after
the numerical guards

`Gamma_num = anchors ∪ G_fix ∪ E_donor ∪ G_bank^0 ∪ G_bank^1`.

Only literal finite-set identities are proved here.  In particular, this
file does **not** assume or assert a local guard census, a lower bound for a
guarded broad pool, or enough guarded-row capacity for a corrected selector.
Those still-missing estimates are exposed at the end as named propositions.

The postcharge target is kept in `Real` form for the correction algebra and
in `Int` form for its exact integrality witness.  Its nonnegativity is a
finite consequence of the actual donor/base row-preserving bijection and of
the disjoint upper-tail backing of the fixed exceptional factors and donors.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! ## Literal guarded candidates and row pieces -/

/-- The actual five-family numerical guard set, specialized to the fixed
exceptional set belonging to the realized bank. -/
def roughCanonicalGuardSet
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) : Finset ℕ :=
  R.tangentPaperNumericalGuardSet certificate
    (R.paperFixedExceptionalFactors deltaStar)

/-- The raw lower candidates which survive every numerical guard. -/
def roughCanonicalGuardedCandidateSet
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K : ℕ) : Finset ℕ :=
  roughRawCandidateSet n h K \
    R.roughCanonicalGuardSet certificate deltaStar

/-- The broad correction pool after deleting all numerical guards. -/
def roughCanonicalGuardedBroadCorrectionPool
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (W K label : ℕ) : Finset ℕ :=
  roughCanonicalBroadCorrectionPool W n h K (yNat n) label \
    R.roughCanonicalGuardSet certificate deltaStar

/-- One complete rough row of the surviving guarded candidates. -/
def roughCanonicalGuardedRow
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) : Finset ℕ :=
  completeRoughRowFiber (yNat n)
    (R.roughCanonicalGuardedCandidateSet certificate deltaStar K) label

/-- The raw coordinates in one row which are removed by the numerical
guards.  This is the paper's local deletion set `D_R`. -/
def roughCanonicalGuardDeletedRow
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) : Finset ℕ :=
  completeRoughRowFiber (yNat n) (roughRawCandidateSet n h K) label ∩
    R.roughCanonicalGuardSet certificate deltaStar

theorem roughCanonicalGuardedCandidateSet_subset_rawCandidateSet
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K : ℕ) :
    R.roughCanonicalGuardedCandidateSet certificate deltaStar K ⊆
      roughRawCandidateSet n h K := by
  exact Finset.sdiff_subset

theorem roughCanonicalGuardedCandidateSet_disjoint_guardSet
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K : ℕ) :
    Disjoint
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (R.roughCanonicalGuardSet certificate deltaStar) := by
  exact Finset.sdiff_disjoint

theorem roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (W K label : ℕ) :
    R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label ⊆
      roughCanonicalBroadCorrectionPool W n h K (yNat n) label := by
  exact Finset.sdiff_subset

/-- The guarded broad pool remains in the guarded row.  No nonemptiness or
cardinality lower bound is used. -/
theorem roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (W K label : ℕ) :
    R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label ⊆
      R.roughCanonicalGuardedRow certificate deltaStar K label := by
  intro a ha
  have haPool := Finset.mem_sdiff.mp ha
  have haRawRow := roughCanonicalBroadCorrectionPool_subset_rawRow
    W n h K (yNat n) label haPool.1
  have haRawData := mem_completeRoughRowFiber.mp haRawRow
  apply mem_completeRoughRowFiber.mpr
  refine ⟨?_, haRawData.2⟩
  exact Finset.mem_sdiff.mpr ⟨haRawData.1, haPool.2⟩

/-- Filtering after deleting the guards is the same as deleting the guards
inside each raw complete rough row. -/
theorem roughCanonicalGuardedRow_eq_rawRow_sdiff_guardSet
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    R.roughCanonicalGuardedRow certificate deltaStar K label =
      completeRoughRowFiber (yNat n)
          (roughRawCandidateSet n h K) label \
        R.roughCanonicalGuardSet certificate deltaStar := by
  ext a
  simp only [roughCanonicalGuardedRow,
    roughCanonicalGuardedCandidateSet, mem_completeRoughRowFiber,
    Finset.mem_sdiff]
  tauto

/-- The surviving and deleted parts are disjoint. -/
theorem roughCanonicalGuardedRow_disjoint_guardDeletedRow
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    Disjoint
      (R.roughCanonicalGuardedRow certificate deltaStar K label)
      (R.roughCanonicalGuardDeletedRow certificate deltaStar K label) := by
  rw [Finset.disjoint_left]
  intro a haGuarded haDeleted
  rw [R.roughCanonicalGuardedRow_eq_rawRow_sdiff_guardSet
    certificate deltaStar K label, Finset.mem_sdiff] at haGuarded
  rw [roughCanonicalGuardDeletedRow, Finset.mem_inter] at haDeleted
  exact haGuarded.2 haDeleted.2

/-- The two row pieces exhaust the original raw row. -/
theorem roughCanonicalGuardedRow_union_guardDeletedRow
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    R.roughCanonicalGuardedRow certificate deltaStar K label ∪
        R.roughCanonicalGuardDeletedRow certificate deltaStar K label =
      completeRoughRowFiber (yNat n)
        (roughRawCandidateSet n h K) label := by
  rw [R.roughCanonicalGuardedRow_eq_rawRow_sdiff_guardSet
    certificate deltaStar K label]
  ext a
  simp only [roughCanonicalGuardDeletedRow, Finset.mem_union,
    Finset.mem_sdiff, Finset.mem_inter]
  tauto

/-- Exact additive decomposition of any real row mass into its surviving
and guard-deleted parts. -/
theorem sum_roughCanonicalGuardedRow_add_sum_guardDeletedRow
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
        (roughRawCandidateSet n h K) label, x a := by
  rw [← Finset.sum_union
      (R.roughCanonicalGuardedRow_disjoint_guardDeletedRow
        certificate deltaStar K label),
    R.roughCanonicalGuardedRow_union_guardDeletedRow
      certificate deltaStar K label]

/-! ## The donor/base row-preserving bijection -/

/-- The actual donor-to-base equivalence preserves the integer complete
rough label, not only the vector signature. -/
theorem prechargeDonorBaseEquiv_completeRoughLabel
    {n M : ℕ} (R : BankPaperRealization n M)
    (donor : ↑R.prechargeDonorSet) :
    completeRoughLabel (yNat n)
        (R.prechargeDonorBaseEquiv donor).1 =
      completeRoughLabel (yNat n) donor.1 := by
  apply completeRoughSignature_eq_iff_label_eq.mp
  change completeRoughSignature (yNat n)
      (R.prechargeDonorToBase donor).1 =
    completeRoughSignature (yNat n) donor.1
  exact R.prechargeDonorToBase_completeRoughSignature donor

/-- Restrict the actual donor/base equivalence to one complete rough row. -/
def prechargeDonorBaseRowEquiv
    {n M : ℕ} (R : BankPaperRealization n M) (label : ℕ) :
    {donor : ↑R.prechargeDonorSet //
      completeRoughLabel (yNat n) donor.1 = label} ≃
    {base : ↑R.prechargeBaseState //
      completeRoughLabel (yNat n) base.1 = label} :=
  R.prechargeDonorBaseEquiv.subtypeEquiv fun donor ↦ by
    rw [R.prechargeDonorBaseEquiv_completeRoughLabel donor]

/-- Re-express a literal finite-state row count as the cardinality of the
corresponding subtype. -/
private theorem completeLabelMultiplicity_eq_subtype_card
    (y : ℕ) (state : Finset ℕ) (label : ℕ) :
    completeLabelMultiplicity y state label =
      Fintype.card {a : ↑state // completeRoughLabel y a.1 = label} := by
  classical
  rw [completeLabelMultiplicity, ← Fintype.card_coe]
  apply Fintype.card_congr
  exact
    { toFun := fun a ↦
        ⟨⟨a.1, (Finset.mem_filter.mp a.2).1⟩,
          (Finset.mem_filter.mp a.2).2⟩
      invFun := fun a ↦
        ⟨a.1.1, Finset.mem_filter.mpr ⟨a.1.2, a.2⟩⟩
      left_inv := by
        intro a
        apply Subtype.ext
        rfl
      right_inv := by
        intro a
        apply Subtype.ext
        rfl }

/-- Donor and base multiplicities agree in every complete rough row.  The
proof is the cardinality equality induced by the literal restricted
`prechargeDonorBaseEquiv`. -/
theorem prechargeBaseState_completeLabelMultiplicity_eq_donorSet
    {n M : ℕ} (R : BankPaperRealization n M) (label : ℕ) :
    completeLabelMultiplicity (yNat n) R.prechargeBaseState label =
      completeLabelMultiplicity (yNat n) R.prechargeDonorSet label := by
  rw [completeLabelMultiplicity_eq_subtype_card,
    completeLabelMultiplicity_eq_subtype_card]
  exact (Fintype.card_congr
    (R.prechargeDonorBaseRowEquiv label)).symm

/-! ## Upper-tail ownership and the postcharge target -/

/-- A complete rough label is exceptional exactly when its literal real
scale is below the paper cutoff `n ^ deltaStar`.  This is the same strict
comparison used in `paperExceptionalUpperFactors`; it is deliberately not
the rounded natural-number cutoff used later for tangent clean lists. -/
def RoughCanonicalExceptionalLabel
    (n : ℕ) (deltaStar : ℝ) (label : ℕ) : Prop :=
  2 * (n : ℝ) / (label : ℝ) < (n : ℝ) ^ deltaStar

/-- The rows on which the paper performs the nonsmooth correction are the
non-smooth, nonexceptional rows: `label != 1` and
`n ^ deltaStar <= 2n / label`. -/
def RoughCanonicalActiveNonexceptionalLabel
    (n : ℕ) (deltaStar : ℝ) (label : ℕ) : Prop :=
  label ≠ 1 ∧ (n : ℝ) ^ deltaStar ≤ 2 * (n : ℝ) / (label : ℝ)

/-- Every non-smooth row is either active nonexceptional or exceptional.
No asymptotic hypothesis is needed for this literal order dichotomy. -/
theorem roughCanonical_activeNonexceptional_or_exceptional
    {n label : ℕ} {deltaStar : ℝ} (hlabel : label ≠ 1) :
    RoughCanonicalActiveNonexceptionalLabel n deltaStar label ∨
      RoughCanonicalExceptionalLabel n deltaStar label := by
  by_cases hactive :
      (n : ℝ) ^ deltaStar ≤ 2 * (n : ℝ) / (label : ℝ)
  · exact Or.inl ⟨hlabel, hactive⟩
  · exact Or.inr (lt_of_not_ge hactive)

/-- Complete-label multiplicity is monotone under finite-set containment. -/
theorem completeLabelMultiplicity_mono
    {y label : ℕ} {A B : Finset ℕ} (hAB : A ⊆ B) :
    completeLabelMultiplicity y A label ≤
      completeLabelMultiplicity y B label := by
  unfold completeLabelMultiplicity
  apply Finset.card_le_card
  intro a ha
  have haData := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨hAB haData.1, haData.2⟩

/-- Multiplicity is additive on a disjoint union. -/
theorem completeLabelMultiplicity_union_of_disjoint
    {y label : ℕ} {A B : Finset ℕ} (hAB : Disjoint A B) :
    completeLabelMultiplicity y (A ∪ B) label =
      completeLabelMultiplicity y A label +
        completeLabelMultiplicity y B label := by
  have hfilter : Disjoint
      (A.filter fun a ↦ completeRoughLabel y a = label)
      (B.filter fun a ↦ completeRoughLabel y a = label) :=
    hAB.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  unfold completeLabelMultiplicity
  rw [Finset.filter_union,
    Finset.card_union_of_disjoint hfilter]

/-- On an exceptional complete rough row, every upper-tail occurrence is
either an actual donor or belongs to the complementary fixed exceptional
set.  Thus their union exhausts that row, not merely a subset of it. -/
theorem paperFixedExceptional_union_prechargeDonor_multiplicity_eq_upperTarget_of_exceptional
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ)
    (hexceptional : RoughCanonicalExceptionalLabel n deltaStar label) :
    completeLabelMultiplicity (yNat n)
        (R.paperFixedExceptionalFactors deltaStar ∪ R.prechargeDonorSet)
        label =
      roughUpperCompleteRoughRowTarget n h (yNat n) label := by
  unfold completeLabelMultiplicity roughUpperCompleteRoughRowTarget
    completeRoughRowFiber
  apply congrArg Finset.card
  ext a
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨haFixed | haDonor, haLabel⟩
    · exact ⟨R.paperFixedExceptionalFactors_subset_upperBlock deltaStar
        haFixed, haLabel⟩
    · have haUpper : a ∈ roughUpperBlock n h := by
        simpa only [roughUpperBlock, upperEndpoint] using
          R.prechargeDonorSet_subset_tail haDonor
      exact ⟨haUpper, haLabel⟩
  · rintro ⟨haUpper, haLabel⟩
    by_cases haDonor : a ∈ R.prechargeDonorSet
    · exact ⟨Or.inr haDonor, haLabel⟩
    · refine ⟨Or.inl ?_, haLabel⟩
      apply (R.mem_paperFixedExceptionalFactors (a := a)).2
      refine ⟨haUpper, ?_, haDonor⟩
      simpa only [RoughCanonicalExceptionalLabel, haLabel] using
        hexceptional

/-- Replacing donors by their row-preserving bank bases preserves the
exact exhaustion of an exceptional upper row. -/
theorem paperFixedExceptional_add_prechargeBase_multiplicity_eq_upperTarget_of_exceptional
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ)
    (hexceptional : RoughCanonicalExceptionalLabel n deltaStar label) :
    completeLabelMultiplicity (yNat n)
        (R.paperFixedExceptionalFactors deltaStar) label +
      completeLabelMultiplicity (yNat n) R.prechargeBaseState label =
        roughUpperCompleteRoughRowTarget n h (yNat n) label := by
  calc
    completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) label +
        completeLabelMultiplicity (yNat n) R.prechargeBaseState label =
        completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) label +
        completeLabelMultiplicity (yNat n) R.prechargeDonorSet label := by
      rw [R.prechargeBaseState_completeLabelMultiplicity_eq_donorSet label]
    _ = completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar ∪
            R.prechargeDonorSet) label :=
      (completeLabelMultiplicity_union_of_disjoint
        (R.paperFixedExceptionalFactors_disjoint_prechargeDonorSet
          deltaStar)).symm
    _ = roughUpperCompleteRoughRowTarget n h (yNat n) label :=
      R.paperFixedExceptional_union_prechargeDonor_multiplicity_eq_upperTarget_of_exceptional
        deltaStar label hexceptional

/-- Fixed exceptional factors and bank bases consume no more tokens in a
row than the literal upper row contains.  Donors are used for this finite
comparison and then replaced by bases through the row equivalence above. -/
theorem paperFixedExceptional_add_prechargeBase_multiplicity_le_upperTarget
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ) :
    completeLabelMultiplicity (yNat n)
        (R.paperFixedExceptionalFactors deltaStar) label +
      completeLabelMultiplicity (yNat n) R.prechargeBaseState label ≤
        roughUpperCompleteRoughRowTarget n h (yNat n) label := by
  have hbacking :
      R.paperFixedExceptionalFactors deltaStar ∪ R.prechargeDonorSet ⊆
        roughUpperBlock n h := by
    simpa only [roughUpperBlock, upperEndpoint] using
      R.paperFixedExceptionalBacking_subset_tail deltaStar
  calc
    completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) label +
        completeLabelMultiplicity (yNat n) R.prechargeBaseState label =
        completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) label +
        completeLabelMultiplicity (yNat n) R.prechargeDonorSet label := by
      rw [R.prechargeBaseState_completeLabelMultiplicity_eq_donorSet label]
    _ = completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar ∪
            R.prechargeDonorSet) label :=
      (completeLabelMultiplicity_union_of_disjoint
        (R.paperFixedExceptionalFactors_disjoint_prechargeDonorSet
          deltaStar)).symm
    _ ≤ completeLabelMultiplicity (yNat n) (roughUpperBlock n h) label :=
      completeLabelMultiplicity_mono hbacking
    _ = roughUpperCompleteRoughRowTarget n h (yNat n) label := rfl

/-- Integer form of the postcharge quota
`t_R - m_R(G_fix) - m_R(G_bank^0)`. -/
def roughCanonicalPostchargeRowTargetInt
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ) : ℤ :=
  (roughUpperCompleteRoughRowTarget n h (yNat n) label : ℤ) -
    (completeLabelMultiplicity (yNat n)
      (R.paperFixedExceptionalFactors deltaStar) label : ℤ) -
    (completeLabelMultiplicity (yNat n)
      R.prechargeBaseState label : ℤ)

/-- Real form of the same postcharge quota, used by the fractional
correction algebra. -/
def roughCanonicalPostchargeRowTarget
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ) : ℝ :=
  (roughUpperCompleteRoughRowTarget n h (yNat n) label : ℝ) -
    (completeLabelMultiplicity (yNat n)
      (R.paperFixedExceptionalFactors deltaStar) label : ℝ) -
    (completeLabelMultiplicity (yNat n)
      R.prechargeBaseState label : ℝ)

theorem roughCanonicalPostchargeRowTarget_eq_intCast
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ) :
    R.roughCanonicalPostchargeRowTarget deltaStar label =
      (R.roughCanonicalPostchargeRowTargetInt deltaStar label : ℝ) := by
  simp [roughCanonicalPostchargeRowTarget,
    roughCanonicalPostchargeRowTargetInt]

/-- The integer postcharge quota is exactly zero on every exceptional
complete rough row: all upper tokens there are already fixed or banked. -/
theorem roughCanonicalPostchargeRowTargetInt_eq_zero_of_exceptional
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ)
    (hexceptional : RoughCanonicalExceptionalLabel n deltaStar label) :
    R.roughCanonicalPostchargeRowTargetInt deltaStar label = 0 := by
  have hrow :=
    R.paperFixedExceptional_add_prechargeBase_multiplicity_eq_upperTarget_of_exceptional
      deltaStar label hexceptional
  have hrowInt :
      (completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) label : ℤ) +
        (completeLabelMultiplicity (yNat n)
          R.prechargeBaseState label : ℤ) =
      (roughUpperCompleteRoughRowTarget n h (yNat n) label : ℤ) := by
    exact_mod_cast hrow
  unfold roughCanonicalPostchargeRowTargetInt
  linarith

/-- Real form of the same paper fact: exceptional rows have `q_R = 0`. -/
theorem roughCanonicalPostchargeRowTarget_eq_zero_of_exceptional
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ)
    (hexceptional : RoughCanonicalExceptionalLabel n deltaStar label) :
    R.roughCanonicalPostchargeRowTarget deltaStar label = 0 := by
  rw [R.roughCanonicalPostchargeRowTarget_eq_intCast deltaStar label,
    R.roughCanonicalPostchargeRowTargetInt_eq_zero_of_exceptional
      deltaStar label hexceptional]
  norm_num

/-- Nonnegativity needs no analytic row census: it follows from the actual
upper-tail ownership injection. -/
theorem roughCanonicalPostchargeRowTarget_nonneg
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ) :
    0 ≤ R.roughCanonicalPostchargeRowTarget deltaStar label := by
  have hfinite :=
    R.paperFixedExceptional_add_prechargeBase_multiplicity_le_upperTarget
      deltaStar label
  have hreal :
      (completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) label : ℝ) +
        (completeLabelMultiplicity (yNat n)
          R.prechargeBaseState label : ℝ) ≤
      (roughUpperCompleteRoughRowTarget n h (yNat n) label : ℝ) := by
    exact_mod_cast hfinite
  unfold roughCanonicalPostchargeRowTarget
  linarith

/-! ## Exact local discrepancy ledger -/

/-- Raw row discrepancy before removing the numerical guards. -/
def roughCanonicalRawRowDiscrepancy
    (n h K label : ℕ) (x : ℕ → ℝ) : ℝ :=
  (roughUpperCompleteRoughRowTarget n h (yNat n) label : ℝ) -
    ∑ a ∈ completeRoughRowFiber (yNat n)
      (roughRawCandidateSet n h K) label, x a

/-- Postcharge discrepancy on the candidates surviving all guards. -/
def roughCanonicalPostchargeRowDiscrepancy
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) (x : ℕ → ℝ) : ℝ :=
  R.roughCanonicalPostchargeRowTarget deltaStar label -
    ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
      x a

/-- Exact guard-local ledger.  It is purely the identity
`raw row = surviving row ⊔ deleted row` together with the definition of
the postcharge quota. -/
theorem roughCanonicalGuardLocalDiscrepancyLedger
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
          K label, x a := by
  rw [roughCanonicalPostchargeRowDiscrepancy,
    roughCanonicalRawRowDiscrepancy,
    roughCanonicalPostchargeRowTarget,
    ← R.sum_roughCanonicalGuardedRow_add_sum_guardDeletedRow
      certificate deltaStar K label x]
  ring

/-! ## Exact support reduction for the local deletion set -/

/-- Fixed exceptional factors cannot themselves be raw lower candidates. -/
theorem roughRawCandidateSet_disjoint_paperFixedExceptionalFactors
    {n h K : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    Disjoint (roughRawCandidateSet n h K)
      (R.paperFixedExceptionalFactors deltaStar) := by
  exact (roughUpperBlock_disjoint_rawCandidateSet n h K).symm.mono
    (by rfl) (R.paperFixedExceptionalFactors_subset_upperBlock deltaStar)

/-- Actual donors also lie strictly above every raw lower candidate. -/
theorem roughRawCandidateSet_disjoint_prechargeDonorSet
    {n h K : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h)) :
    Disjoint (roughRawCandidateSet n h K) R.prechargeDonorSet := by
  have hdonor : R.prechargeDonorSet ⊆ roughUpperBlock n h := by
    simpa only [roughUpperBlock, upperEndpoint] using
      R.prechargeDonorSet_subset_tail
  exact (roughUpperBlock_disjoint_rawCandidateSet n h K).symm.mono
    (by rfl) hdonor

/-- Consequently, the only guard families which can delete a raw lower
coordinate are anchors and the two bank endpoint states.  This is a support
statement, not the still-missing per-row cardinality census. -/
theorem roughCanonicalGuardDeletedRow_subset_anchors_union_bankStates
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    R.roughCanonicalGuardDeletedRow certificate deltaStar K label ⊆
      certificate.anchors ∪ R.prechargeBaseState ∪
        R.prechargeAlternateState := by
  intro a ha
  have haData := Finset.mem_inter.mp ha
  have haRaw := (mem_completeRoughRowFiber.mp haData.1).1
  have haGuard := haData.2
  simp only [roughCanonicalGuardSet, tangentPaperNumericalGuardSet,
    Finset.mem_union] at haGuard
  simp only [Finset.mem_union]
  rcases haGuard with (((haAnchor | haFixed) | haDonor) | haBase) | haAlt
  · exact Or.inl (Or.inl haAnchor)
  · exact ((Finset.disjoint_left.mp
      (R.roughRawCandidateSet_disjoint_paperFixedExceptionalFactors
        deltaStar)) haRaw haFixed).elim
  · exact ((Finset.disjoint_left.mp
      (R.roughRawCandidateSet_disjoint_prechargeDonorSet
        (K := K))) haRaw haDonor).elim
  · exact Or.inl (Or.inr haBase)
  · exact Or.inr haAlt

/-! ## Explicit remaining finite/analytic obligations -/

/-- A proposed local guard census is deliberately data, not a theorem of
the finite ledger.  The paper only needs a fixed small `budget`. -/
def RoughCanonicalGuardLocalCensusBound
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label budget : ℕ) : Prop :=
  (R.roughCanonicalGuardDeletedRow certificate deltaStar K label).card ≤
    budget

/-- A lower bound for the guarded broad correction pool.  Establishing it
uniformly in active rows is the missing rough-number capacity estimate. -/
def RoughCanonicalGuardedBroadPoolCapacity
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (W K label minimum : ℕ) : Prop :=
  minimum ≤
    (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
      W K label).card

/-- Capacity of the entire guarded row for its nonnegative postcharge
target.  This does not follow merely from upper-tail ownership. -/
def RoughCanonicalPostchargeRowCapacity
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) : Prop :=
  R.roughCanonicalPostchargeRowTarget deltaStar label ≤
    ((R.roughCanonicalGuardedRow certificate deltaStar K label).card : ℝ)

end BankPaperRealization

end

end Erdos390.WholePaper
