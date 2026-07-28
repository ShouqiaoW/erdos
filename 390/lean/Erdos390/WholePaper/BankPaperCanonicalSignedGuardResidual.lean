import Erdos390.WholePaper.BankPaperCanonicalGuardCapacityReduction
import Erdos390.WholePaper.BankPaperFixedExceptionalValuationFibers
import Erdos390.WholePaper.BankPaperPrechargeAsymptotic
import Erdos390.WholePaper.ExceptionalValuationSums

/-!
# Signed exceptional and guard residual ledger

This module gives literal names to the two signed terms in the final rough
residual identity.  They are intentionally separate from the nonnegative
fixed-factor charge used for divisibility.

`roughCanonicalSignedExceptionalResidual` is the exceptional-row portion of
the raw upper-minus-lower comparison.  The order of its two finite sums is
not replaced by a sum of absolute values.  `roughCanonicalAggregateGuardResidual`
is the paper's three-term guard difference: restored raw weights deleted in
nonexceptional rows, restored exceptional donors, and the negative bank-base
charge.

The exact four-term sign convention and its triangle reduction are proved at
the end.  The aggregate guard term is bounded and absorbed unconditionally
from the literal finite census, and the correction-pool valuation census is
also closed by the global Legendre prefix bound.  The genuinely signed
exceptional estimate and the uniform correction-density estimate remain
exposed as named propositions rather than being confused with the already
proved nonnegative exceptional charge bound.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Elementary finite valuation envelopes -/

/-- A finite family contained in `(lo,hi]` has total `p`-valuation at most
its cardinality times the binary logarithm of `hi`.  The binary logarithm
is deliberately used as a uniform upper bound for every prime base. -/
theorem sum_factorization_cast_le_card_mul_log_two
    {S : Finset Nat} {lo hi p : Nat} (hp : p.Prime)
    (hS : S ⊆ Finset.Ioc lo hi) :
    (∑ a ∈ S, (a.factorization p : Real)) ≤
      (S.card : Real) * (Nat.log 2 hi : Real) := by
  have hNat :
      ∑ a ∈ S, a.factorization p ≤ S.card * Nat.log 2 hi := by
    calc
      ∑ a ∈ S, a.factorization p ≤
          ∑ _a ∈ S, Nat.log 2 hi := by
        apply Finset.sum_le_sum
        intro a ha
        have haIoc := Finset.mem_Ioc.mp (hS ha)
        exact (factorization_le_log_of_pos_le
          (Nat.zero_lt_of_lt haIoc.1) haIoc.2 hp).trans
            (Nat.log_anti_left Nat.one_lt_two hp.two_le)
      _ = S.card * Nat.log 2 hi := by simp
  exact_mod_cast hNat

/-- A feasible nonnegative weight cannot increase a nonnegative valuation
sum.  This is the precise justification used below when a deleted raw
coordinate is replaced by its unweighted valuation. -/
theorem abs_sum_weight_mul_factorization_le_sum_factorization
    {S : Finset Nat} {weight : Nat → Real} {p : Nat}
    (hweight : ∀ a ∈ S, 0 ≤ weight a ∧ weight a ≤ 1) :
    abs (∑ a ∈ S, weight a * (a.factorization p : Real)) ≤
      ∑ a ∈ S, (a.factorization p : Real) := by
  have hsumNonneg :
      0 ≤ ∑ a ∈ S, weight a * (a.factorization p : Real) := by
    apply Finset.sum_nonneg
    intro a ha
    exact mul_nonneg (hweight a ha).1 (Nat.cast_nonneg _)
  rw [abs_of_nonneg hsumNonneg]
  apply Finset.sum_le_sum
  intro a ha
  exact mul_le_of_le_one_left (Nat.cast_nonneg _) (hweight a ha).2

/-- The valuation of a union is no larger than the sum of the valuations
of its two constituent families.  No disjointness is required. -/
theorem sum_factorization_union_le
    (S T : Finset Nat) (p : Nat) :
    (∑ a ∈ S ∪ T, (a.factorization p : Real)) ≤
      (∑ a ∈ S, (a.factorization p : Real)) +
        ∑ a ∈ T, (a.factorization p : Real) := by
  calc
    (∑ a ∈ S ∪ T, (a.factorization p : Real)) =
        ∑ a ∈ S ∪ (T \ S), (a.factorization p : Real) := by
      rw [Finset.union_sdiff_self_eq_union]
    _ = (∑ a ∈ S, (a.factorization p : Real)) +
          ∑ a ∈ T \ S, (a.factorization p : Real) := by
      rw [Finset.sum_union Finset.disjoint_sdiff]
    _ ≤ (∑ a ∈ S, (a.factorization p : Real)) +
          ∑ a ∈ T, (a.factorization p : Real) := by
      have hsdiff :
          (∑ a ∈ T \ S, (a.factorization p : Real)) ≤
            ∑ a ∈ T, (a.factorization p : Real) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          (fun (a : Nat) _ha _hnew ↦
            (Nat.cast_nonneg (a.factorization p) :
              (0 : Real) ≤ (a.factorization p : Real)))
      exact add_le_add le_rfl hsdiff

/-! ## Literal signed exceptional term -/

/-- Raw lower candidates in exceptional complete rough rows. -/
def roughCanonicalExceptionalRawLowerSet
    (n h K : Nat) (deltaStar : Real) : Finset Nat := by
  classical
  exact (roughRawCandidateSet n h K).filter fun a =>
    RoughCanonicalExceptionalLabel n deltaStar
      (completeRoughLabel (yNat n) a)

@[simp]
theorem mem_roughCanonicalExceptionalRawLowerSet
    {n h K a : Nat} {deltaStar : Real} :
    a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar ↔
      a ∈ roughRawCandidateSet n h K ∧
        RoughCanonicalExceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) a) := by
  classical
  simp only [roughCanonicalExceptionalRawLowerSet, Finset.mem_filter]

/-- The paper's signed exceptional-row discrepancy
`sum_{a in E_exc} v_p(a) - sum_{a in H_exc} x_raw(a) v_p(a)`.

No absolute value is taken inside either sum. -/
def roughCanonicalSignedExceptionalResidual
    (n h K : Nat) (deltaStar : Real)
    (rawWeight : Nat -> Real) (p : Nat) : Real :=
  (∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
      (a.factorization p : Real)) -
    ∑ a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar,
      rawWeight a * (a.factorization p : Real)

/-- The upper half of the signed exceptional term is exactly the valuation
of the product of all literal exceptional upper factors. -/
theorem sum_paperExceptionalUpperFactors_factorization_eq_prod
    (n h : Nat) (deltaStar : Real) (p : Nat) :
    (∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
        (a.factorization p : Real)) =
      (((paperExceptionalUpperFactors n h deltaStar).prod id).factorization p :
        Real) := by
  have hNat :
      ((paperExceptionalUpperFactors n h deltaStar).prod id).factorization p =
        ∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
          a.factorization p :=
    Nat.factorization_prod_apply
      (fun (a : Nat) ha ↦ (paperExceptionalUpperFactors_pos ha).ne')
  rw [hNat]
  push_cast
  rfl

/-- Rigorous positive-charge envelope for the signed exceptional term.
This loses the core-first cancellation and is therefore not advertised as
the paper's strict `N/(pL)` estimate. -/
theorem abs_roughCanonicalSignedExceptionalResidual_le_positive_parts
    {n h K p : Nat} {deltaStar : Real} {rawWeight : Nat → Real}
    (hweight : ∀ a ∈
      roughCanonicalExceptionalRawLowerSet n h K deltaStar,
        0 ≤ rawWeight a) :
    abs (roughCanonicalSignedExceptionalResidual n h K deltaStar
        rawWeight p) ≤
      (∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
          (a.factorization p : Real)) +
        ∑ a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar,
          rawWeight a * (a.factorization p : Real) := by
  unfold roughCanonicalSignedExceptionalResidual
  have hlower : 0 ≤
      ∑ a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar,
        rawWeight a * (a.factorization p : Real) := by
    apply Finset.sum_nonneg
    intro a ha
    exact mul_nonneg (hweight a ha) (Nat.cast_nonneg _)
  have hupper : 0 ≤
      ∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
        (a.factorization p : Real) := by
    positivity
  exact (abs_sub _ _).trans_eq
    (by rw [abs_of_nonneg hupper, abs_of_nonneg hlower])

/-! ## Literal aggregate guard difference -/

/-- Raw lower coordinates deleted by the numerical guards in
nonexceptional rows.  The smooth row is included whenever it is
nonexceptional, as in the paper's set `D_ne`. -/
def roughCanonicalNonexceptionalGuardDeletedSet
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K : Nat) : Finset Nat := by
  classical
  exact ((roughRawCandidateSet n h K) ∩
      R.roughCanonicalGuardSet certificate deltaStar).filter fun a =>
    ¬ RoughCanonicalExceptionalLabel n deltaStar
      (completeRoughLabel (yNat n) a)

@[simp]
theorem mem_roughCanonicalNonexceptionalGuardDeletedSet
    {c : Real} {depth n h K a : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) :
    a ∈ R.roughCanonicalNonexceptionalGuardDeletedSet certificate
        deltaStar K ↔
      a ∈ roughRawCandidateSet n h K ∧
        a ∈ R.roughCanonicalGuardSet certificate deltaStar ∧
        ¬ RoughCanonicalExceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) a) := by
  classical
  simp only [roughCanonicalNonexceptionalGuardDeletedSet,
    Finset.mem_filter, Finset.mem_inter, and_assoc]

/-- Designated donors whose complete rough row is exceptional. -/
def roughCanonicalExceptionalDonorSet
    {n h : Nat} (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : Real) : Finset Nat := by
  classical
  exact R.prechargeDonorSet.filter fun a =>
    RoughCanonicalExceptionalLabel n deltaStar
      (completeRoughLabel (yNat n) a)

@[simp]
theorem mem_roughCanonicalExceptionalDonorSet
    {n h a : Nat} (R : BankPaperRealization n (upperEndpoint n h))
    {deltaStar : Real} :
    a ∈ R.roughCanonicalExceptionalDonorSet deltaStar ↔
      a ∈ R.prechargeDonorSet ∧
        RoughCanonicalExceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) a) := by
  classical
  simp only [roughCanonicalExceptionalDonorSet, Finset.mem_filter]

/-- The exceptional donors are a literal filtered subfamily of all donors. -/
theorem roughCanonicalExceptionalDonorSet_subset_prechargeDonorSet
    {n h : Nat} (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : Real) :
    R.roughCanonicalExceptionalDonorSet deltaStar ⊆
      R.prechargeDonorSet := by
  classical
  exact Finset.filter_subset _ _

/-- Globally, as rowwise, fixed exceptional factors and donor occurrences
cannot delete raw lower coordinates.  Thus only central anchors and the two
bank endpoint states occur in the first guard-residual sum. -/
theorem roughCanonicalNonexceptionalGuardDeletedSet_subset_support
    {c : Real} {depth n h : Nat} {left right : Nat → Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K : Nat) :
    R.roughCanonicalNonexceptionalGuardDeletedSet certificate deltaStar K ⊆
      certificate.anchors ∪ R.prechargeBaseState ∪
        R.prechargeAlternateState := by
  intro a ha
  have haData :=
    (R.mem_roughCanonicalNonexceptionalGuardDeletedSet certificate
      deltaStar).mp ha
  have haRaw := haData.1
  have haGuard := haData.2.1
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

/-- The complete signed guard difference from the paper:

* restore raw weight on lower coordinates deleted outside exceptional rows;
* restore donor terms which were already present in the signed exceptional
  discrepancy;
* subtract the bank-base tokens which replace those donors.
-/
def roughCanonicalAggregateGuardResidual
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K : Nat) (rawWeight : Nat -> Real)
    (p : Nat) : Real :=
  (∑ a ∈ R.roughCanonicalNonexceptionalGuardDeletedSet certificate
        deltaStar K,
      rawWeight a * (a.factorization p : Real)) +
    (∑ a ∈ R.roughCanonicalExceptionalDonorSet deltaStar,
      (a.factorization p : Real)) -
    ∑ a ∈ R.prechargeBaseState, (a.factorization p : Real)

set_option maxHeartbeats 2000000 in
/-- The guard difference is bounded by the absolute values of its three
literal signed components.  This deliberately does not replace the signed
exceptional term by the positive exceptional charge. -/
theorem abs_roughCanonicalAggregateGuardResidual_le_components
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K : Nat) (rawWeight : Nat -> Real)
    (p : Nat) :
    abs (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
      rawWeight p) <=
      abs (∑ a ∈ R.roughCanonicalNonexceptionalGuardDeletedSet certificate
          deltaStar K,
        rawWeight a * (a.factorization p : Real)) +
      abs (∑ a ∈ R.roughCanonicalExceptionalDonorSet deltaStar,
        (a.factorization p : Real)) +
      abs (∑ a ∈ R.prechargeBaseState,
        (a.factorization p : Real)) := by
  unfold roughCanonicalAggregateGuardResidual
  have hadd := abs_add_le
    (∑ a ∈ R.roughCanonicalNonexceptionalGuardDeletedSet certificate
        deltaStar K,
      rawWeight a * (a.factorization p : Real))
    (∑ a ∈ R.roughCanonicalExceptionalDonorSet deltaStar,
      (a.factorization p : Real))
  have hsub := abs_sub
    ((∑ a ∈ R.roughCanonicalNonexceptionalGuardDeletedSet certificate
        deltaStar K,
      rawWeight a * (a.factorization p : Real)) +
      ∑ a ∈ R.roughCanonicalExceptionalDonorSet deltaStar,
        (a.factorization p : Real))
    (∑ a ∈ R.prechargeBaseState, (a.factorization p : Real))
  exact hsub.trans (add_le_add hadd le_rfl)

/-! ## A uniform finite guard-profile bound -/

/-- At a medium prime, only the corresponding promoted central anchors can
carry valuation.  The pair-divisor census, specialized to `(p,p)`, gives a
safe cardinality two, and every anchor is at most `2n`. -/
theorem sum_guardedCentralAnchors_factorization_le_two_mul_log_two
    {c : Real} {depth n W p : Nat} {left right : Nat → Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWp : W < p) (hpY : p ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hp : p.Prime) :
    (∑ a ∈ certificate.anchors, (a.factorization p : Real)) ≤
      2 * (Nat.log 2 (3 * n) : Real) := by
  let divisors := certificate.anchors.filter (fun a ↦ p ∣ a)
  have hsum :
      (∑ a ∈ divisors, (a.factorization p : Real)) =
        ∑ a ∈ certificate.anchors, (a.factorization p : Real) := by
    apply Finset.sum_subset
    · exact Finset.filter_subset _ _
    · intro a haAnchor haNotDivisors
      have hnotDvd : ¬ p ∣ a := by
        intro hpa
        exact haNotDivisors (Finset.mem_filter.mpr ⟨haAnchor, hpa⟩)
      simp [Nat.factorization_eq_zero_of_not_dvd hnotDvd]
  have hcard : divisors.card ≤ 2 := by
    have hpair := card_guardedCentralAnchors_pairPrimeDivisors_le_two
      certificate hTwoW hPrefix hWp (le_refl p) hpY hyCutoff hp hp
    simpa only [divisors, or_self] using hpair
  have hdivisorsSubset : divisors ⊆ Finset.Ioc n (3 * n) := by
    intro a ha
    have haAnchor := (Finset.mem_filter.mp ha).1
    have haIoc := Finset.mem_Ioc.mp (certificate.anchors_subset haAnchor)
    exact Finset.mem_Ioc.mpr ⟨haIoc.1, haIoc.2.trans (by omega)⟩
  calc
    (∑ a ∈ certificate.anchors, (a.factorization p : Real)) =
        ∑ a ∈ divisors, (a.factorization p : Real) := hsum.symm
    _ ≤ (divisors.card : Real) * (Nat.log 2 (3 * n) : Real) :=
      sum_factorization_cast_le_card_mul_log_two hp hdivisorsSubset
    _ ≤ 2 * (Nat.log 2 (3 * n) : Real) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (Nat.cast_nonneg _)

/-- Donor, base, and alternate bank states each have at most the global
marker budget many endpoints, all lying below the realized endpoint. -/
theorem precharge_guard_state_factorization_bounds
    {n M p : Nat} (R : BankPaperRealization n M)
    (hp : p.Prime) (hendpoint : M ≤ 3 * n) :
    ((∑ a ∈ R.prechargeDonorSet, (a.factorization p : Real)) ≤
        (bankPaperAnchorMarkerBudget n : Real) *
          (Nat.log 2 (3 * n) : Real)) ∧
      ((∑ a ∈ R.prechargeBaseState, (a.factorization p : Real)) ≤
        (bankPaperAnchorMarkerBudget n : Real) *
          (Nat.log 2 (3 * n) : Real)) ∧
      ((∑ a ∈ R.prechargeAlternateState,
          (a.factorization p : Real)) ≤
        (bankPaperAnchorMarkerBudget n : Real) *
          (Nat.log 2 (3 * n) : Real)) := by
  have hcomponent : Fintype.card (BankPaperMarkerRequest n) ≤
      bankPaperAnchorMarkerBudget n :=
    R.prechargeComponentCount_le_anchorMarkerBudget
  have hcardScale :
      (Fintype.card (BankPaperMarkerRequest n) : Real) *
          (Nat.log 2 (3 * n) : Real) ≤
        (bankPaperAnchorMarkerBudget n : Real) *
          (Nat.log 2 (3 * n) : Real) := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcomponent)
      (Nat.cast_nonneg _)
  have hdonorSubset : R.prechargeDonorSet ⊆ Finset.Ioc n (3 * n) := by
    intro a ha
    have haIoc := Finset.mem_Ioc.mp (R.prechargeDonorSet_subset_tail ha)
    exact Finset.mem_Ioc.mpr ⟨by omega, haIoc.2.trans hendpoint⟩
  have hbaseSubset : R.prechargeBaseState ⊆ Finset.Ioc n (3 * n) := by
    intro a ha
    have haIoc : n < a ∧ a ≤ M := by
      simpa only [factorInterval, Finset.mem_Ioc] using
        R.prechargeBaseState_subset_factorInterval ha
    exact Finset.mem_Ioc.mpr ⟨haIoc.1, haIoc.2.trans hendpoint⟩
  have haltSubset : R.prechargeAlternateState ⊆ Finset.Ioc n (3 * n) := by
    intro a ha
    have haIoc : n < a ∧ a ≤ M := by
      simpa only [factorInterval, Finset.mem_Ioc] using
        R.prechargeAlternateState_subset_factorInterval ha
    exact Finset.mem_Ioc.mpr ⟨haIoc.1, haIoc.2.trans hendpoint⟩
  constructor
  · calc
      (∑ a ∈ R.prechargeDonorSet, (a.factorization p : Real)) ≤
          (R.prechargeDonorSet.card : Real) *
            (Nat.log 2 (3 * n) : Real) :=
        sum_factorization_cast_le_card_mul_log_two hp hdonorSubset
      _ = (Fintype.card (BankPaperMarkerRequest n) : Real) *
            (Nat.log 2 (3 * n) : Real) := by
        rw [R.prechargeDonorSet_card]
      _ ≤ _ := hcardScale
  · constructor
    · calc
        (∑ a ∈ R.prechargeBaseState, (a.factorization p : Real)) ≤
            (R.prechargeBaseState.card : Real) *
              (Nat.log 2 (3 * n) : Real) :=
          sum_factorization_cast_le_card_mul_log_two hp hbaseSubset
        _ = (Fintype.card (BankPaperMarkerRequest n) : Real) *
              (Nat.log 2 (3 * n) : Real) := by
          rw [R.prechargeBaseState_card]
        _ ≤ _ := hcardScale
    · calc
        (∑ a ∈ R.prechargeAlternateState,
            (a.factorization p : Real)) ≤
            (R.prechargeAlternateState.card : Real) *
              (Nat.log 2 (3 * n) : Real) :=
          sum_factorization_cast_le_card_mul_log_two hp haltSubset
        _ = (Fintype.card (BankPaperMarkerRequest n) : Real) *
              (Nat.log 2 (3 * n) : Real) := by
          rw [R.prechargeAlternateState_card]
        _ ≤ _ := hcardScale

/-- A realization-independent majorant for the whole literal guard
difference at one medium prime. -/
def roughCanonicalAggregateGuardResidualMajorant (n : Nat) : Real :=
  (2 + 4 * (bankPaperAnchorMarkerBudget n : Real)) *
    (Nat.log 2 (3 * n) : Real)

/-- The finite guard majorant is nonnegative at every endpoint. -/
theorem roughCanonicalAggregateGuardResidualMajorant_nonneg (n : Nat) :
    0 ≤ roughCanonicalAggregateGuardResidualMajorant n := by
  unfold roughCanonicalAggregateGuardResidualMajorant
  positivity

set_option maxHeartbeats 8000000 in
/-- Complete finite estimate for the literal three-term guard difference.
The raw-weight premise is only feasibility on the literal raw candidate
set; no signed cancellation and no exceptional-charge estimate is used. -/
theorem abs_roughCanonicalAggregateGuardResidual_le_majorant
    {c : Real} {depth n h W K p : Nat} {left right : Nat → Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (rawWeight : Nat → Real)
    (hweight : ∀ a ∈ roughRawCandidateSet n h K,
      0 ≤ rawWeight a ∧ rawWeight a ≤ 1)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWp : W < p) (hpY : p ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hp : p.Prime) (hendpoint : upperEndpoint n h ≤ 3 * n) :
    abs (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
      rawWeight p) ≤ roughCanonicalAggregateGuardResidualMajorant n := by
  let deleted := R.roughCanonicalNonexceptionalGuardDeletedSet certificate
    deltaStar K
  let donors := R.roughCanonicalExceptionalDonorSet deltaStar
  have hdeletedWeight : ∀ a ∈ deleted,
      0 ≤ rawWeight a ∧ rawWeight a ≤ 1 := by
    intro a ha
    exact hweight a
      ((R.mem_roughCanonicalNonexceptionalGuardDeletedSet certificate
        deltaStar).mp ha).1
  have hdeletedSupport : deleted ⊆
      certificate.anchors ∪ R.prechargeBaseState ∪
        R.prechargeAlternateState := by
    exact R.roughCanonicalNonexceptionalGuardDeletedSet_subset_support
      certificate deltaStar K
  have hdeleted :
      abs (∑ a ∈ deleted,
          rawWeight a * (a.factorization p : Real)) ≤
        (∑ a ∈ certificate.anchors, (a.factorization p : Real)) +
          (∑ a ∈ R.prechargeBaseState,
            (a.factorization p : Real)) +
          ∑ a ∈ R.prechargeAlternateState,
            (a.factorization p : Real) := by
    calc
      abs (∑ a ∈ deleted,
          rawWeight a * (a.factorization p : Real)) ≤
          ∑ a ∈ deleted, (a.factorization p : Real) :=
        abs_sum_weight_mul_factorization_le_sum_factorization hdeletedWeight
      _ ≤ ∑ a ∈
          certificate.anchors ∪ R.prechargeBaseState ∪
            R.prechargeAlternateState,
          (a.factorization p : Real) :=
        Finset.sum_le_sum_of_subset_of_nonneg hdeletedSupport
          (fun (a : Nat) _ha _hnew ↦
            Nat.cast_nonneg (a.factorization p))
      _ ≤ ((∑ a ∈ certificate.anchors,
            (a.factorization p : Real)) +
          ∑ a ∈ R.prechargeBaseState,
            (a.factorization p : Real)) +
          ∑ a ∈ R.prechargeAlternateState,
            (a.factorization p : Real) := by
        have houterUnion := sum_factorization_union_le
          (certificate.anchors ∪ R.prechargeBaseState)
          R.prechargeAlternateState p
        have hinnerUnion := sum_factorization_union_le certificate.anchors
          R.prechargeBaseState p
        exact houterUnion.trans (add_le_add hinnerUnion le_rfl)
  have hdonorsSubset : donors ⊆ R.prechargeDonorSet := by
    exact R.roughCanonicalExceptionalDonorSet_subset_prechargeDonorSet
      deltaStar
  have hdonors :
      abs (∑ a ∈ donors, (a.factorization p : Real)) ≤
        ∑ a ∈ R.prechargeDonorSet,
          (a.factorization p : Real) := by
    rw [abs_of_nonneg (by positivity :
      0 ≤ ∑ a ∈ donors, (a.factorization p : Real))]
    exact Finset.sum_le_sum_of_subset_of_nonneg hdonorsSubset
      (fun (a : Nat) _ha _hnew ↦ Nat.cast_nonneg (a.factorization p))
  have hbaseAbs :
      abs (∑ a ∈ R.prechargeBaseState,
        (a.factorization p : Real)) =
      ∑ a ∈ R.prechargeBaseState,
        (a.factorization p : Real) := by
    rw [abs_of_nonneg]
    positivity
  have hanchor :=
    sum_guardedCentralAnchors_factorization_le_two_mul_log_two
      certificate hTwoW hPrefix hWp hpY hyCutoff hp
  have hbank := R.precharge_guard_state_factorization_bounds hp hendpoint
  have hcomponents :=
    R.abs_roughCanonicalAggregateGuardResidual_le_components certificate
      deltaStar K rawWeight p
  change abs (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
      rawWeight p) ≤ roughCanonicalAggregateGuardResidualMajorant n
  change abs (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
      rawWeight p) ≤ _ at hcomponents
  change abs (∑ a ∈ deleted,
      rawWeight a * (a.factorization p : Real)) ≤ _ at hdeleted
  change abs (∑ a ∈ donors, (a.factorization p : Real)) ≤ _ at hdonors
  rw [hbaseAbs] at hcomponents
  calc
    abs (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
        rawWeight p) ≤
      ((∑ a ∈ certificate.anchors, (a.factorization p : Real)) +
          (∑ a ∈ R.prechargeBaseState, (a.factorization p : Real)) +
          ∑ a ∈ R.prechargeAlternateState, (a.factorization p : Real)) +
        (∑ a ∈ R.prechargeDonorSet, (a.factorization p : Real)) +
        ∑ a ∈ R.prechargeBaseState, (a.factorization p : Real) := by
      exact hcomponents.trans
        (add_le_add (add_le_add hdeleted hdonors) le_rfl)
    _ ≤
      ((2 * (Nat.log 2 (3 * n) : Real) +
          (bankPaperAnchorMarkerBudget n : Real) *
            (Nat.log 2 (3 * n) : Real)) +
          (bankPaperAnchorMarkerBudget n : Real) *
            (Nat.log 2 (3 * n) : Real)) +
        (bankPaperAnchorMarkerBudget n : Real) *
          (Nat.log 2 (3 * n) : Real) +
        (bankPaperAnchorMarkerBudget n : Real) *
          (Nat.log 2 (3 * n) : Real) := by
      exact add_le_add
        (add_le_add
          (add_le_add
            (add_le_add hanchor hbank.2.1)
            hbank.2.2)
          hbank.1)
        hbank.2.1
    _ = roughCanonicalAggregateGuardResidualMajorant n := by
      unfold roughCanonicalAggregateGuardResidualMajorant
      ring

/-! ## Uniform absorption of the guard majorant -/

/-- The normalized real model needed after multiplying the guard error by
the largest permitted prime and by the extra logarithm in the strict rate. -/
def bankPaperGuardCubicNormalizedCost (n : Nat) : Real :=
  y n ^ 3 * L n ^ 2 / secondOrderScale n

/-- The normalized guard model is exactly `log(n)^3/n^(1/3)`. -/
theorem bankPaperGuardCubicNormalizedCost_eq
    {n : Nat} (hn : 1 < n) :
    bankPaperGuardCubicNormalizedCost n =
      L n ^ 3 / (n : Real) ^ (1 / 3 : Real) := by
  calc
    bankPaperGuardCubicNormalizedCost n =
        L n * bankPaperPrechargeCubicNormalizedCost n := by
      unfold bankPaperGuardCubicNormalizedCost
      unfold bankPaperPrechargeCubicNormalizedCost
      ring
    _ = L n * (L n ^ 2 / (n : Real) ^ (1 / 3 : Real)) := by
      rw [bankPaperPrechargeCubicNormalizedCost_eq hn]
    _ = L n ^ 3 / (n : Real) ^ (1 / 3 : Real) := by ring

/-- The normalized cubic guard model tends to zero. -/
theorem bankPaperGuardCubicNormalizedCost_tendsto_zero :
    Tendsto bankPaperGuardCubicNormalizedCost atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : Real ↦
        Real.log x ^ (3 : Real) / x ^ (1 / 3 : Real))
      atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (3 : Real)
      (by norm_num : (0 : Real) < 1 / 3)).tendsto_div_nhds_zero
  have hnat : Tendsto
      (fun n : Nat ↦
        Real.log (n : Real) ^ 3 / (n : Real) ^ (1 / 3 : Real))
      atTop (nhds 0) := by
    simpa [Real.rpow_natCast] using
      hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  simpa only [L] using
    (bankPaperGuardCubicNormalizedCost_eq hn).symm

/-- Equivalently, `y^3*L^2` is little-o of the second-order scale. -/
theorem y_cubed_mul_L_sq_isLittleO_secondOrderScale :
    (fun n : Nat ↦ y n ^ 3 * L n ^ 2) =o[atTop]
      secondOrderScale := by
  have hzero : ∀ᶠ n : Nat in atTop,
      secondOrderScale n = 0 → y n ^ 3 * L n ^ 2 = 0 := by
    filter_upwards [eventually_secondOrderScale_pos] with n hscale hzero
    exact (hscale.ne' hzero).elim
  apply (isLittleO_iff_tendsto' hzero).mpr
  simpa only [bankPaperGuardCubicNormalizedCost] using
    bankPaperGuardCubicNormalizedCost_tendsto_zero

/-- The realization-independent guard majorant remains negligible after
multiplication by `yNat*L`, exactly the uniform factor needed for
`p ≤ yNat` at the strict `N/(pL)` scale. -/
theorem roughCanonicalAggregateGuardResidualMajorant_scaled_isLittleO :
    (fun n : Nat ↦
      (yNat n : Real) * L n *
        roughCanonicalAggregateGuardResidualMajorant n) =o[atTop]
      secondOrderScale := by
  have hconstant :
      (fun _n : Nat ↦ (2 : Real)) =O[atTop]
        (fun n : Nat ↦ (yNat n : Real) ^ 2) := by
    apply IsBigO.of_bound 2
    filter_upwards [eventually_bankBottom_six_le_yNat] with n hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2),
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (yNat n : Real))]
    have hyOne : (1 : Real) ≤ yNat n := by exact_mod_cast (show 1 ≤ yNat n by omega)
    nlinarith [sq_nonneg ((yNat n : Real) - 1)]
  have hcoefficientRaw := hconstant.add
    (bankPaperAnchorMarkerBudget_isBigO_yNat_sq.const_mul_left (4 : Real))
  have hcoefficient :
      (fun n : Nat ↦
        2 + 4 * (bankPaperAnchorMarkerBudget n : Real)) =O[atTop]
          (fun n : Nat ↦ (yNat n : Real) ^ 2) := by
    apply hcoefficientRaw.congr'
    · exact Eventually.of_forall fun _n ↦ rfl
    · exact Eventually.of_forall fun _n ↦ rfl
  have hySqRaw := bankPaperPrecharge_yNat_isBigO_y.mul
    bankPaperPrecharge_yNat_isBigO_y
  have hySq :
      (fun n : Nat ↦ (yNat n : Real) ^ 2) =O[atTop]
        (fun n : Nat ↦ y n ^ 2) := by
    apply hySqRaw.congr'
    · exact Eventually.of_forall fun _n ↦ by ring
    · exact Eventually.of_forall fun _n ↦ by ring
  have hcoefficientY := hcoefficient.trans hySq
  have hraw :=
    (((bankPaperPrecharge_yNat_isBigO_y.mul
        (isBigO_refl L atTop)).mul hcoefficientY).mul
      natLog_two_three_mul_isBigO_L)
  have hmajorant :
      (fun n : Nat ↦
        (yNat n : Real) * L n *
          roughCanonicalAggregateGuardResidualMajorant n) =O[atTop]
        (fun n : Nat ↦ y n ^ 3 * L n ^ 2) := by
    apply hraw.congr'
    · exact Eventually.of_forall fun n ↦ by
        unfold roughCanonicalAggregateGuardResidualMajorant
        ring
    · exact Eventually.of_forall fun _n ↦ by ring
  exact hmajorant.trans_isLittleO
    y_cubed_mul_L_sq_isLittleO_secondOrderScale

/-- Normalized limit form of the scaled guard-majorant estimate. -/
theorem roughCanonicalAggregateGuardResidualMajorant_scaled_tendsto_zero :
    Tendsto
      (fun n : Nat ↦
        ((yNat n : Real) * L n *
          roughCanonicalAggregateGuardResidualMajorant n) /
            secondOrderScale n)
      atTop (nhds 0) :=
  roughCanonicalAggregateGuardResidualMajorant_scaled_isLittleO.tendsto_div_nhds_zero

/-- Uniform strict-rate form of the preceding little-o estimate. -/
theorem eventually_roughCanonicalAggregateGuardResidualMajorant_le_strictScale
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : Nat in atTop, ∀ p : Nat, p.Prime → p ≤ yNat n →
      roughCanonicalAggregateGuardResidualMajorant n ≤
        epsilon * secondOrderScale n / ((p : Real) * L n) := by
  have hsmall :=
    roughCanonicalAggregateGuardResidualMajorant_scaled_tendsto_zero.eventually
      (eventually_lt_nhds hepsilon)
  filter_upwards [hsmall, eventually_secondOrderScale_pos,
    eventually_gt_atTop 1] with n hsmallN hscale hn
  intro p hp hpY
  have hpPos : (0 : Real) < p := by exact_mod_cast hp.pos
  have hL : 0 < L n := L_pos hn
  have hmajorant :
      0 ≤ roughCanonicalAggregateGuardResidualMajorant n :=
    roughCanonicalAggregateGuardResidualMajorant_nonneg n
  have hpYReal : (p : Real) ≤ yNat n := by exact_mod_cast hpY
  have hscaledLe :
      (p : Real) * L n * roughCanonicalAggregateGuardResidualMajorant n ≤
        (yNat n : Real) * L n *
          roughCanonicalAggregateGuardResidualMajorant n := by
    calc
      (p : Real) * L n *
          roughCanonicalAggregateGuardResidualMajorant n =
        (p : Real) *
          (L n * roughCanonicalAggregateGuardResidualMajorant n) := by ring
      _ ≤ (yNat n : Real) *
          (L n * roughCanonicalAggregateGuardResidualMajorant n) :=
        mul_le_mul_of_nonneg_right hpYReal
          (mul_nonneg hL.le hmajorant)
      _ = (yNat n : Real) * L n *
          roughCanonicalAggregateGuardResidualMajorant n := by ring
  have hratioLe :
      ((p : Real) * L n * roughCanonicalAggregateGuardResidualMajorant n) /
          secondOrderScale n ≤
        ((yNat n : Real) * L n *
          roughCanonicalAggregateGuardResidualMajorant n) /
            secondOrderScale n :=
    div_le_div_of_nonneg_right hscaledLe hscale.le
  have hscaled :
      (p : Real) * L n * roughCanonicalAggregateGuardResidualMajorant n <
        epsilon * secondOrderScale n := by
    exact (div_lt_iff₀ hscale).mp (hratioLe.trans_lt hsmallN)
  apply (le_div_iff₀ (mul_pos hpPos hL)).2
  calc
    roughCanonicalAggregateGuardResidualMajorant n * ((p : Real) * L n) =
        (p : Real) * L n * roughCanonicalAggregateGuardResidualMajorant n := by
      ring
    _ ≤ epsilon * secondOrderScale n := hscaled.le

/-! ## Literal aggregate nonsmooth row correction -/

/-- The attained raw complete-rough labels on which the paper applies its
constant-pool correction: nonsmooth and nonexceptional, with the real
cutoff convention left unchanged. -/
def roughCanonicalActiveRawCorrectionLabels
    (n h K : Nat) (deltaStar : Real) : Finset Nat := by
  classical
  exact
    (completeRoughLabelSet (yNat n) (roughRawCandidateSet n h K)).filter
      (RoughCanonicalActiveNonexceptionalLabel n deltaStar)

@[simp]
theorem mem_roughCanonicalActiveRawCorrectionLabels
    {n h K label : Nat} {deltaStar : Real} :
    label ∈ roughCanonicalActiveRawCorrectionLabels n h K deltaStar ↔
      label ∈ completeRoughLabelSet (yNat n)
        (roughRawCandidateSet n h K) ∧
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label := by
  classical
  simp only [roughCanonicalActiveRawCorrectionLabels, Finset.mem_filter]

/-- The signed constant added to every broad-pool coordinate in one raw
complete-rough row. -/
def roughCanonicalRawCorrectionDensityAtLabel
    (W n h K : Nat) (alpha beta logScale : Real)
    (label : Nat) : Real :=
  bankPaperConstantPoolCorrectionDensity
    (completeRoughRowFiber (yNat n) (roughRawCandidateSet n h K) label)
    (roughCanonicalBroadCorrectionPool W n h K (yNat n) label)
    (roughHeadCompatibleRawWeight W n h K alpha beta logScale)
    (roughUpperCompleteRoughRowTarget n h (yNat n) label : Real)

/-- The paper's full signed row-correction contribution at one prime,
summed only after every active physical row has retained its sign. -/
def roughCanonicalAggregateRawRowCorrection
    (W n h K : Nat) (deltaStar alpha beta logScale : Real)
    (p : Nat) : Real :=
  ∑ label ∈ roughCanonicalActiveRawCorrectionLabels n h K deltaStar,
    ∑ a ∈ roughCanonicalBroadCorrectionPool W n h K (yNat n) label,
      roughCanonicalRawCorrectionDensityAtLabel
          W n h K alpha beta logScale label *
        (a.factorization p : Real)

/-- On an attained active label, the literal density is the already
formalized row-quota error divided by the broad-pool cardinality. -/
theorem roughCanonicalRawCorrectionDensityAtLabel_eq_quotaError_div
    {W n h K label : Nat} {alpha beta logScale deltaStar : Real}
    (hlabel : label ∈
      roughCanonicalActiveRawCorrectionLabels n h K deltaStar) :
    roughCanonicalRawCorrectionDensityAtLabel
        W n h K alpha beta logScale label =
      roughCanonicalRawRowQuotaError W n h K (yNat n)
          alpha beta logScale
          ⟨label, (mem_roughCanonicalActiveRawCorrectionLabels.mp
            hlabel).1⟩ /
        ((roughCanonicalBroadCorrectionPool
          W n h K (yNat n) label).card : Real) := by
  simpa only [roughCanonicalRawCorrectionDensityAtLabel] using
    roughCanonicalRawRowCorrectionDensity_eq_quotaError_div
      W n h K (yNat n) alpha beta logScale
        ⟨label, (mem_roughCanonicalActiveRawCorrectionLabels.mp
          hlabel).1⟩

/-- Exact row-first factorization of the aggregate correction. -/
theorem roughCanonicalAggregateRawRowCorrection_eq_density_mul_valuationSum
    (W n h K : Nat) (deltaStar alpha beta logScale : Real)
    (p : Nat) :
    roughCanonicalAggregateRawRowCorrection W n h K deltaStar
        alpha beta logScale p =
      ∑ label ∈ roughCanonicalActiveRawCorrectionLabels n h K deltaStar,
        roughCanonicalRawCorrectionDensityAtLabel
            W n h K alpha beta logScale label *
          (∑ a ∈ roughCanonicalBroadCorrectionPool
              W n h K (yNat n) label,
            (a.factorization p : Real)) := by
  unfold roughCanonicalAggregateRawRowCorrection
  apply Finset.sum_congr rfl
  intro label _hlabel
  rw [Finset.mul_sum]

/-- All algebraic loss in the aggregate row correction is exactly the
outer triangle inequality.  The valuation census below will further reduce
the remaining analytic input to a uniform bound for the literal correction
density, not a sign convention. -/
theorem abs_roughCanonicalAggregateRawRowCorrection_le_rowwise
    (W n h K : Nat) (deltaStar alpha beta logScale : Real)
    (p : Nat) :
    abs (roughCanonicalAggregateRawRowCorrection W n h K deltaStar
      alpha beta logScale p) ≤
      ∑ label ∈ roughCanonicalActiveRawCorrectionLabels n h K deltaStar,
        abs (roughCanonicalRawCorrectionDensityAtLabel
          W n h K alpha beta logScale label) *
          (∑ a ∈ roughCanonicalBroadCorrectionPool
              W n h K (yNat n) label,
            (a.factorization p : Real)) := by
  rw [roughCanonicalAggregateRawRowCorrection_eq_density_mul_valuationSum]
  calc
    abs (∑ label ∈
        roughCanonicalActiveRawCorrectionLabels n h K deltaStar,
      roughCanonicalRawCorrectionDensityAtLabel
          W n h K alpha beta logScale label *
        (∑ a ∈ roughCanonicalBroadCorrectionPool
            W n h K (yNat n) label,
          (a.factorization p : Real))) ≤
      ∑ label ∈
          roughCanonicalActiveRawCorrectionLabels n h K deltaStar,
        abs (roughCanonicalRawCorrectionDensityAtLabel
            W n h K alpha beta logScale label *
          (∑ a ∈ roughCanonicalBroadCorrectionPool
              W n h K (yNat n) label,
            (a.factorization p : Real))) :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ label ∈
          roughCanonicalActiveRawCorrectionLabels n h K deltaStar,
        abs (roughCanonicalRawCorrectionDensityAtLabel
          W n h K alpha beta logScale label) *
          (∑ a ∈ roughCanonicalBroadCorrectionPool
              W n h K (yNat n) label,
            (a.factorization p : Real)) := by
      apply Finset.sum_congr rfl
      intro label _hlabel
      rw [abs_mul, abs_of_nonneg (show
        0 ≤ ∑ a ∈ roughCanonicalBroadCorrectionPool
            W n h K (yNat n) label,
          (a.factorization p : Real) by
        positivity)]

/-- The active correction pools are disjoint pieces of the broad lower
block.  Dropping head freedom and using the elementary Legendre prefix
bound gives a uniform `4n/p` envelope for their total valuation. -/
theorem sum_activeRawCorrectionPool_factorization_le_four_mul_div_prime
    (W n h K : Nat) (deltaStar : Real) {p : Nat} (hp : p.Prime) :
    (∑ label ∈ roughCanonicalActiveRawCorrectionLabels n h K deltaStar,
      ∑ a ∈ roughCanonicalBroadCorrectionPool
          W n h K (yNat n) label,
        (a.factorization p : Real)) ≤
      4 * (n : Real) / (p : Real) := by
  let broad := roughHeadFree W (roughBroadLowerBlock n h K)
  let active := roughCanonicalActiveRawCorrectionLabels n h K deltaStar
  let attained := completeRoughLabelSet (yNat n) broad
  let relevant := active.filter (fun label ↦ label ∈ attained)
  have hrelevantSubset : relevant ⊆ attained := by
    intro label hlabel
    exact (Finset.mem_filter.mp hlabel).2
  have hrestricted :
      (∑ label ∈ relevant,
        ∑ a ∈ completeRoughRowFiber (yNat n) broad label,
          (a.factorization p : Real)) =
        ∑ label ∈ active,
          ∑ a ∈ completeRoughRowFiber (yNat n) broad label,
            (a.factorization p : Real) := by
    apply Finset.sum_subset
    · exact Finset.filter_subset _ _
    · intro label hactive hnotRelevant
      have hnotAttained : label ∉ attained := by
        intro hattained
        exact hnotRelevant (Finset.mem_filter.mpr ⟨hactive, hattained⟩)
      have hempty : completeRoughRowFiber (yNat n) broad label = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hnonempty
        exact hnotAttained
          (mem_completeRoughLabelSet_iff_rowFiber_nonempty.mpr hnonempty)
      rw [hempty]
      simp
  have hactiveLeBroad :
      (∑ label ∈ active,
        ∑ a ∈ completeRoughRowFiber (yNat n) broad label,
          (a.factorization p : Real)) ≤
        ∑ a ∈ broad, (a.factorization p : Real) := by
    rw [← hrestricted]
    calc
      (∑ label ∈ relevant,
        ∑ a ∈ completeRoughRowFiber (yNat n) broad label,
          (a.factorization p : Real)) ≤
          ∑ label ∈ attained,
            ∑ a ∈ completeRoughRowFiber (yNat n) broad label,
              (a.factorization p : Real) :=
        Finset.sum_le_sum_of_subset_of_nonneg hrelevantSubset
          (fun label _ha _hnew ↦ by positivity)
      _ = ∑ a ∈ broad, (a.factorization p : Real) := by
        symm
        exact sum_eq_sum_completeRoughRowFibers (yNat n) broad
          (fun (a : Nat) ↦ (a.factorization p : Real))
  have hbroadSubset : broad ⊆ Finset.Icc 1 (2 * n) := by
    intro a ha
    have haBroad := (mem_roughHeadFree.mp ha).1
    have haIoc := Finset.mem_Ioc.mp haBroad
    exact Finset.mem_Icc.mpr ⟨by omega, haIoc.2.trans (Nat.sub_le _ _)⟩
  have hbroadPrefix :
      (∑ a ∈ broad, (a.factorization p : Real)) ≤
        ∑ a ∈ Finset.Icc 1 (2 * n),
          (a.factorization p : Real) :=
    Finset.sum_le_sum_of_subset_of_nonneg hbroadSubset
      (fun (a : Nat) _ha _hnew ↦ Nat.cast_nonneg (a.factorization p))
  calc
    (∑ label ∈ roughCanonicalActiveRawCorrectionLabels n h K deltaStar,
      ∑ a ∈ roughCanonicalBroadCorrectionPool
          W n h K (yNat n) label,
        (a.factorization p : Real)) =
        ∑ label ∈ active,
          ∑ a ∈ completeRoughRowFiber (yNat n) broad label,
            (a.factorization p : Real) := by
      rfl
    _ ≤ ∑ a ∈ broad, (a.factorization p : Real) := hactiveLeBroad
    _ ≤ ∑ a ∈ Finset.Icc 1 (2 * n),
          (a.factorization p : Real) := hbroadPrefix
    _ ≤ 2 * ((2 * n : Nat) : Real) / (p : Real) :=
      sum_factorization_Icc_cast_le_two_mul_div_prime hp
    _ = 4 * (n : Real) / (p : Real) := by
      push_cast
      ring

/-- A uniform absolute density bound reduces the full signed aggregate row
correction to the preceding global valuation envelope. -/
theorem abs_roughCanonicalAggregateRawRowCorrection_le_uniformDensity
    {W n h K p : Nat} {deltaStar alpha beta logScale densityBound : Real}
    (hp : p.Prime) (hdensityNonneg : 0 ≤ densityBound)
    (hdensity : ∀ label ∈
      roughCanonicalActiveRawCorrectionLabels n h K deltaStar,
      abs (roughCanonicalRawCorrectionDensityAtLabel
        W n h K alpha beta logScale label) ≤ densityBound) :
    abs (roughCanonicalAggregateRawRowCorrection W n h K deltaStar
      alpha beta logScale p) ≤
        densityBound * (4 * (n : Real) / (p : Real)) := by
  calc
    abs (roughCanonicalAggregateRawRowCorrection W n h K deltaStar
      alpha beta logScale p) ≤
      ∑ label ∈ roughCanonicalActiveRawCorrectionLabels n h K deltaStar,
        abs (roughCanonicalRawCorrectionDensityAtLabel
          W n h K alpha beta logScale label) *
          (∑ a ∈ roughCanonicalBroadCorrectionPool
              W n h K (yNat n) label,
            (a.factorization p : Real)) :=
      abs_roughCanonicalAggregateRawRowCorrection_le_rowwise
        W n h K deltaStar alpha beta logScale p
    _ ≤ ∑ label ∈
          roughCanonicalActiveRawCorrectionLabels n h K deltaStar,
        densityBound *
          (∑ a ∈ roughCanonicalBroadCorrectionPool
              W n h K (yNat n) label,
            (a.factorization p : Real)) := by
      apply Finset.sum_le_sum
      intro label hlabel
      exact mul_le_mul_of_nonneg_right (hdensity label hlabel) (by positivity)
    _ = densityBound *
        (∑ label ∈
          roughCanonicalActiveRawCorrectionLabels n h K deltaStar,
          ∑ a ∈ roughCanonicalBroadCorrectionPool
              W n h K (yNat n) label,
            (a.factorization p : Real)) := by
      rw [Finset.mul_sum]
    _ ≤ densityBound * (4 * (n : Real) / (p : Real)) :=
      mul_le_mul_of_nonneg_left
        (sum_activeRawCorrectionPool_factorization_le_four_mul_div_prime
          W n h K deltaStar hp) hdensityNonneg

/-- At the literal `C/(4L²)` density scale, the aggregate correction has
the strict paper rate `C*N/(pL)` exactly, with no asymptotic algebra left. -/
theorem abs_roughCanonicalAggregateRawRowCorrection_le_strictScale_of_density
    {W n h K p : Nat} {deltaStar alpha beta densityConstant : Real}
    (hn : 1 < n) (hp : p.Prime) (hdensityConstant : 0 ≤ densityConstant)
    (hdensity : ∀ label ∈
      roughCanonicalActiveRawCorrectionLabels n h K deltaStar,
      abs (roughCanonicalRawCorrectionDensityAtLabel
        W n h K alpha beta (L n) label) ≤
          densityConstant / (4 * L n ^ 2)) :
    abs (roughCanonicalAggregateRawRowCorrection W n h K deltaStar
      alpha beta (L n) p) ≤
        densityConstant * secondOrderScale n / ((p : Real) * L n) := by
  have hL : 0 < L n := L_pos hn
  have hpReal : (0 : Real) < p := by exact_mod_cast hp.pos
  have hdensityBoundNonneg :
      0 ≤ densityConstant / (4 * L n ^ 2) := by positivity
  have hfinite :=
    abs_roughCanonicalAggregateRawRowCorrection_le_uniformDensity hp
      hdensityBoundNonneg hdensity
  calc
    abs (roughCanonicalAggregateRawRowCorrection W n h K deltaStar
      alpha beta (L n) p) ≤
        (densityConstant / (4 * L n ^ 2)) *
          (4 * (n : Real) / (p : Real)) := hfinite
    _ = densityConstant * secondOrderScale n / ((p : Real) * L n) := by
      unfold secondOrderScale
      rw [show Real.log (n : Real) = L n by rfl]
      field_simp [hL.ne', hpReal.ne']

/-! ## Exact final sign ledger and quantitative reduction -/

/-- The exact sign convention of the completed rough residual. -/
def roughCanonicalCompleteSignedResidual
    (rawResidual signedExceptional rowCorrection aggregateGuard : Real) :
    Real :=
  rawResidual - signedExceptional - rowCorrection + aggregateGuard

/-- Unfolding the complete residual preserves all four paper signs. -/
theorem roughCanonicalCompleteSignedResidual_eq
    (rawResidual signedExceptional rowCorrection aggregateGuard : Real) :
    roughCanonicalCompleteSignedResidual rawResidual signedExceptional
        rowCorrection aggregateGuard =
      rawResidual - signedExceptional - rowCorrection + aggregateGuard := by
  rfl

/-- Four-term triangle inequality with the paper's signs left visible. -/
theorem abs_roughCanonicalCompleteSignedResidual_le
    (rawResidual signedExceptional rowCorrection aggregateGuard : Real) :
    abs (roughCanonicalCompleteSignedResidual rawResidual signedExceptional
      rowCorrection aggregateGuard) <=
      abs rawResidual + abs signedExceptional + abs rowCorrection +
        abs aggregateGuard := by
  unfold roughCanonicalCompleteSignedResidual
  have houter := abs_add_le
    (rawResidual - signedExceptional - rowCorrection) aggregateGuard
  have hrow := abs_sub (rawResidual - signedExceptional) rowCorrection
  have hexceptional := abs_sub rawResidual signedExceptional
  calc
    abs (rawResidual - signedExceptional - rowCorrection + aggregateGuard) ≤
        abs (rawResidual - signedExceptional - rowCorrection) +
          abs aggregateGuard :=
      houter
    _ ≤ (abs (rawResidual - signedExceptional) + abs rowCorrection) +
          abs aggregateGuard :=
      add_le_add hrow le_rfl
    _ ≤ ((abs rawResidual + abs signedExceptional) + abs rowCorrection) +
          abs aggregateGuard :=
      add_le_add (add_le_add hexceptional le_rfl) le_rfl

/-- The missing signed exceptional estimate, stated independently of the
nonnegative factor charge. -/
def RoughCanonicalSignedExceptionalResidualBound
    (n h K : Nat) (deltaStar : Real) (rawWeight : Nat -> Real)
    (p : Nat) (bound : Real) : Prop :=
  abs (roughCanonicalSignedExceptionalResidual n h K deltaStar
    rawWeight p) <= bound

/-- A transparent wrapper for a quantitative aggregate guard-profile
estimate.  Unlike the signed-exceptional wrapper, its paper-scale bound is
proved below from the literal guard census. -/
def RoughCanonicalAggregateGuardResidualBound
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K : Nat) (rawWeight : Nat -> Real)
    (p : Nat) (bound : Real) : Prop :=
  abs (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
    rawWeight p) <= bound

/-- Public predicate for an exact aggregate row-correction estimate. -/
def RoughCanonicalAggregateRawRowCorrectionBound
    (W n h K : Nat) (deltaStar alpha beta logScale : Real)
    (p : Nat) (bound : Real) : Prop :=
  abs (roughCanonicalAggregateRawRowCorrection W n h K deltaStar
    alpha beta logScale p) ≤ bound

/-- The smallest remaining analytic row-correction input: a uniform bound
for the literal constant correction density on every active attained row.
By `roughCanonicalRawCorrectionDensityAtLabel_eq_quotaError_div`, this is
exactly a uniform quota-error-over-pool-cardinality estimate. -/
def RoughCanonicalUniformRawRowCorrectionDensityBound
    (W n h K : Nat) (deltaStar alpha beta logScale densityBound : Real) :
    Prop :=
  ∀ label ∈ roughCanonicalActiveRawCorrectionLabels n h K deltaStar,
    abs (roughCanonicalRawCorrectionDensityAtLabel
      W n h K alpha beta logScale label) ≤ densityBound

/-- A positive-parts bound is a valid, though generally non-sharp, signed
exceptional bound. -/
theorem roughCanonicalSignedExceptionalResidualBound_of_positive_parts
    {n h K p : Nat} {deltaStar bound : Real}
    {rawWeight : Nat → Real}
    (hweight : ∀ a ∈
      roughCanonicalExceptionalRawLowerSet n h K deltaStar,
        0 ≤ rawWeight a)
    (hparts :
      (∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
          (a.factorization p : Real)) +
        (∑ a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar,
          rawWeight a * (a.factorization p : Real)) ≤ bound) :
    RoughCanonicalSignedExceptionalResidualBound n h K deltaStar
      rawWeight p bound := by
  exact (abs_roughCanonicalSignedExceptionalResidual_le_positive_parts
    hweight).trans hparts

/-- Package the proved finite guard majorant in the public bound predicate. -/
theorem roughCanonicalAggregateGuardResidualBound_of_majorant
    {c : Real} {depth n h W K p : Nat} {left right : Nat → Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (rawWeight : Nat → Real)
    (hweight : ∀ a ∈ roughRawCandidateSet n h K,
      0 ≤ rawWeight a ∧ rawWeight a ≤ 1)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWp : W < p) (hpY : p ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hp : p.Prime) (hendpoint : upperEndpoint n h ≤ 3 * n) :
    RoughCanonicalAggregateGuardResidualBound R certificate deltaStar K
      rawWeight p (roughCanonicalAggregateGuardResidualMajorant n) := by
  exact abs_roughCanonicalAggregateGuardResidual_le_majorant
    R certificate deltaStar rawWeight hweight hTwoW hPrefix hWp hpY
      hyCutoff hp hendpoint

/-- The rowwise valuation-census expression is a sufficient and exact
input for the aggregate correction bound. -/
theorem roughCanonicalAggregateRawRowCorrectionBound_of_rowwise
    {W n h K p : Nat} {deltaStar alpha beta logScale bound : Real}
    (hrowwise :
      (∑ label ∈ roughCanonicalActiveRawCorrectionLabels n h K deltaStar,
        abs (roughCanonicalRawCorrectionDensityAtLabel
          W n h K alpha beta logScale label) *
          (∑ a ∈ roughCanonicalBroadCorrectionPool
              W n h K (yNat n) label,
            (a.factorization p : Real))) ≤ bound) :
    RoughCanonicalAggregateRawRowCorrectionBound W n h K deltaStar
      alpha beta logScale p bound := by
  exact (abs_roughCanonicalAggregateRawRowCorrection_le_rowwise
    W n h K deltaStar alpha beta logScale p).trans hrowwise

/-- A uniform density estimate implies the aggregate correction bound using
the proved global `4n/p` valuation census. -/
theorem roughCanonicalAggregateRawRowCorrectionBound_of_uniformDensity
    {W n h K p : Nat}
    {deltaStar alpha beta logScale densityBound : Real}
    (hp : p.Prime) (hdensityNonneg : 0 ≤ densityBound)
    (hdensity : RoughCanonicalUniformRawRowCorrectionDensityBound
      W n h K deltaStar alpha beta logScale densityBound) :
    RoughCanonicalAggregateRawRowCorrectionBound W n h K deltaStar
      alpha beta logScale p
        (densityBound * (4 * (n : Real) / (p : Real))) := by
  exact abs_roughCanonicalAggregateRawRowCorrection_le_uniformDensity hp
    hdensityNonneg hdensity

/-- At density scale `C/(4L²)`, the named uniform-density input implies the
strict aggregate correction rate `C*N/(pL)`. -/
theorem roughCanonicalAggregateRawRowCorrectionBound_strictScale_of_uniformDensity
    {W n h K p : Nat} {deltaStar alpha beta densityConstant : Real}
    (hn : 1 < n) (hp : p.Prime) (hdensityConstant : 0 ≤ densityConstant)
    (hdensity : RoughCanonicalUniformRawRowCorrectionDensityBound
      W n h K deltaStar alpha beta (L n)
        (densityConstant / (4 * L n ^ 2))) :
    RoughCanonicalAggregateRawRowCorrectionBound W n h K deltaStar
      alpha beta (L n) p
        (densityConstant * secondOrderScale n / ((p : Real) * L n)) := by
  exact abs_roughCanonicalAggregateRawRowCorrection_le_strictScale_of_density
    hn hp hdensityConstant hdensity

/-- The literal paper raw weight gives an eventual strict-rate guard bound,
uniformly over every realization, guard certificate, cutoff, row parameter,
and medium prime.  The only numerical premises are feasibility of the two
raw levels. -/
theorem eventually_roughCanonicalAggregateGuardResidualBound
    {c epsilon : Real} (hc : 0 < c) (hepsilon : 0 < epsilon)
    (depth W : Nat) (hTwoW : 2 ≤ W)
    (hPrefix : 2 * depth + 1 ≤ W) :
    ∀ᶠ n : Nat in atTop,
      ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (left right : Nat → Nat) (changed : Finset Nat)
        (certificate : GuardedCentralAnchorCertificate c depth n
          left right changed)
        (deltaStar alpha beta : Real) (K p : Nat),
      (0 ≤ alpha ∧ alpha ≤ 1) →
      (0 ≤ beta / L n ∧ beta / L n ≤ 1) →
      p.Prime → W < p → p ≤ yNat n →
      RoughCanonicalAggregateGuardResidualBound R certificate deltaStar K
        (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
          alpha beta (L n)) p
        (epsilon * secondOrderScale n / ((p : Real) * L n)) := by
  filter_upwards [eventually_upperTailLength_le hc,
    eventually_yNat_lt_centralAnchorCutoff depth,
    eventually_roughCanonicalAggregateGuardResidualMajorant_le_strictScale
      hepsilon]
      with n htail hyCutoff hstrict
  intro R left right changed certificate deltaStar alpha beta K p
    halpha hbeta hp hWp hpY
  have hweight : ∀ a ∈
      roughRawCandidateSet n (upperTailLength c n) K,
      0 ≤ roughHeadCompatibleRawWeight W n (upperTailLength c n) K
          alpha beta (L n) a ∧
        roughHeadCompatibleRawWeight W n (upperTailLength c n) K
          alpha beta (L n) a ≤ 1 := by
    intro a _ha
    exact roughHeadCompatibleRawWeight_mem_unitInterval halpha hbeta a
  exact (abs_roughCanonicalAggregateGuardResidual_le_majorant
    R certificate deltaStar
      (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
        alpha beta (L n))
      hweight hTwoW hPrefix hWp hpY hyCutoff hp
      (upperEndpoint_le_three_mul htail)).trans
    (hstrict p hp hpY)

/-- Combining the four component estimates gives the strict residual rate
with the sum of their constants. -/
theorem abs_roughCanonicalCompleteSignedResidual_le_scale
    {scale C_raw C_exceptional C_row C_guard : Real}
    {rawResidual signedExceptional rowCorrection aggregateGuard : Real}
    (_hscale : 0 <= scale)
    (hraw : abs rawResidual <= C_raw * scale)
    (hexceptional : abs signedExceptional <= C_exceptional * scale)
    (hrow : abs rowCorrection <= C_row * scale)
    (hguard : abs aggregateGuard <= C_guard * scale) :
    abs (roughCanonicalCompleteSignedResidual rawResidual signedExceptional
      rowCorrection aggregateGuard) <=
        (C_raw + C_exceptional + C_row + C_guard) * scale := by
  calc
    abs (roughCanonicalCompleteSignedResidual rawResidual signedExceptional
        rowCorrection aggregateGuard) <=
      abs rawResidual + abs signedExceptional + abs rowCorrection +
        abs aggregateGuard :=
      abs_roughCanonicalCompleteSignedResidual_le _ _ _ _
    _ <= C_raw * scale + C_exceptional * scale + C_row * scale +
        C_guard * scale := by linarith
    _ = (C_raw + C_exceptional + C_row + C_guard) * scale := by ring

end BankPaperRealization

end

end Erdos390.WholePaper
