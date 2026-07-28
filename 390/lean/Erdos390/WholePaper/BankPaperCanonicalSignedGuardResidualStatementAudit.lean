import Erdos390.WholePaper.BankPaperCanonicalSignedGuardResidual

/-! # Statement audit for the signed exceptional/guard residual ledger -/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace BankPaperRealization

#check sum_factorization_cast_le_card_mul_log_two
#check abs_sum_weight_mul_factorization_le_sum_factorization
#check sum_factorization_union_le
#check roughCanonicalExceptionalRawLowerSet
#check mem_roughCanonicalExceptionalRawLowerSet
#check roughCanonicalSignedExceptionalResidual

example (n h K : Nat) (deltaStar : Real) :
    roughCanonicalExceptionalRawLowerSet n h K deltaStar =
      (roughRawCandidateSet n h K).filter (fun a =>
        RoughCanonicalExceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) a)) := by
  classical
  rfl

example {n h K a : Nat} {deltaStar : Real} :
    a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar ↔
      a ∈ roughRawCandidateSet n h K ∧
        RoughCanonicalExceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) a) :=
  mem_roughCanonicalExceptionalRawLowerSet

example (n h K : Nat) (deltaStar : Real)
    (rawWeight : Nat -> Real) (p : Nat) :
    roughCanonicalSignedExceptionalResidual n h K deltaStar rawWeight p =
      (∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
        (a.factorization p : Real)) -
      ∑ a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar,
        rawWeight a * (a.factorization p : Real) := by
  rfl

#check sum_paperExceptionalUpperFactors_factorization_eq_prod
#check abs_roughCanonicalSignedExceptionalResidual_le_positive_parts
#check roughCanonicalNonexceptionalGuardDeletedSet
#check mem_roughCanonicalNonexceptionalGuardDeletedSet
#check roughCanonicalExceptionalDonorSet
#check mem_roughCanonicalExceptionalDonorSet

example
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K : Nat) :
    R.roughCanonicalNonexceptionalGuardDeletedSet certificate deltaStar K =
      ((roughRawCandidateSet n h K) ∩
        R.roughCanonicalGuardSet certificate deltaStar).filter (fun a =>
          ¬ RoughCanonicalExceptionalLabel n deltaStar
            (completeRoughLabel (yNat n) a)) := by
  classical
  rfl

example
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
          (completeRoughLabel (yNat n) a) :=
  R.mem_roughCanonicalNonexceptionalGuardDeletedSet certificate deltaStar

example {n h : Nat} (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : Real) :
    R.roughCanonicalExceptionalDonorSet deltaStar =
      R.prechargeDonorSet.filter (fun a =>
        RoughCanonicalExceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) a)) := by
  classical
  rfl

example {n h a : Nat} (R : BankPaperRealization n (upperEndpoint n h))
    {deltaStar : Real} :
    a ∈ R.roughCanonicalExceptionalDonorSet deltaStar ↔
      a ∈ R.prechargeDonorSet ∧
        RoughCanonicalExceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) a) :=
  R.mem_roughCanonicalExceptionalDonorSet

#check roughCanonicalExceptionalDonorSet_subset_prechargeDonorSet
#check roughCanonicalNonexceptionalGuardDeletedSet_subset_support
#check roughCanonicalAggregateGuardResidual
#check abs_roughCanonicalAggregateGuardResidual_le_components

example
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K : Nat) (rawWeight : Nat -> Real)
    (p : Nat) :
    R.roughCanonicalAggregateGuardResidual certificate deltaStar K
        rawWeight p =
      (∑ a ∈ R.roughCanonicalNonexceptionalGuardDeletedSet certificate
            deltaStar K,
        rawWeight a * (a.factorization p : Real)) +
      (∑ a ∈ R.roughCanonicalExceptionalDonorSet deltaStar,
        (a.factorization p : Real)) -
      ∑ a ∈ R.prechargeBaseState, (a.factorization p : Real) := by
  rfl

example
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
        (a.factorization p : Real)) :=
  R.abs_roughCanonicalAggregateGuardResidual_le_components certificate
    deltaStar K rawWeight p

#check sum_guardedCentralAnchors_factorization_le_two_mul_log_two
#check precharge_guard_state_factorization_bounds
#check roughCanonicalAggregateGuardResidualMajorant

example (n : Nat) :
    roughCanonicalAggregateGuardResidualMajorant n =
      (2 + 4 * (bankPaperAnchorMarkerBudget n : Real)) *
        (Nat.log 2 (3 * n) : Real) := by
  rfl

#check roughCanonicalAggregateGuardResidualMajorant_nonneg
#check abs_roughCanonicalAggregateGuardResidual_le_majorant
#check bankPaperGuardCubicNormalizedCost

example (n : Nat) :
    bankPaperGuardCubicNormalizedCost n =
      y n ^ 3 * L n ^ 2 / secondOrderScale n := by
  rfl

#check bankPaperGuardCubicNormalizedCost_eq
#check bankPaperGuardCubicNormalizedCost_tendsto_zero
#check y_cubed_mul_L_sq_isLittleO_secondOrderScale
#check roughCanonicalAggregateGuardResidualMajorant_scaled_isLittleO
#check roughCanonicalAggregateGuardResidualMajorant_scaled_tendsto_zero
#check eventually_roughCanonicalAggregateGuardResidualMajorant_le_strictScale
#check roughCanonicalActiveRawCorrectionLabels

example (n h K : Nat) (deltaStar : Real) :
    roughCanonicalActiveRawCorrectionLabels n h K deltaStar =
      (completeRoughLabelSet (yNat n)
        (roughRawCandidateSet n h K)).filter
          (RoughCanonicalActiveNonexceptionalLabel n deltaStar) := by
  classical
  rfl

#check mem_roughCanonicalActiveRawCorrectionLabels
#check roughCanonicalRawCorrectionDensityAtLabel
#check roughCanonicalAggregateRawRowCorrection

example (W n h K : Nat) (alpha beta logScale : Real) (label : Nat) :
    roughCanonicalRawCorrectionDensityAtLabel W n h K
        alpha beta logScale label =
      bankPaperConstantPoolCorrectionDensity
        (completeRoughRowFiber (yNat n)
          (roughRawCandidateSet n h K) label)
        (roughCanonicalBroadCorrectionPool W n h K (yNat n) label)
        (roughHeadCompatibleRawWeight W n h K alpha beta logScale)
        (roughUpperCompleteRoughRowTarget n h (yNat n) label : Real) := by
  rfl

example (W n h K : Nat) (deltaStar alpha beta logScale : Real)
    (p : Nat) :
    roughCanonicalAggregateRawRowCorrection W n h K deltaStar
        alpha beta logScale p =
      ∑ label ∈ roughCanonicalActiveRawCorrectionLabels n h K deltaStar,
        ∑ a ∈ roughCanonicalBroadCorrectionPool
            W n h K (yNat n) label,
          roughCanonicalRawCorrectionDensityAtLabel
              W n h K alpha beta logScale label *
            (a.factorization p : Real) := by
  rfl

#check roughCanonicalRawCorrectionDensityAtLabel_eq_quotaError_div
#check roughCanonicalAggregateRawRowCorrection_eq_density_mul_valuationSum
#check abs_roughCanonicalAggregateRawRowCorrection_le_rowwise
#check sum_activeRawCorrectionPool_factorization_le_four_mul_div_prime
#check abs_roughCanonicalAggregateRawRowCorrection_le_uniformDensity
#check abs_roughCanonicalAggregateRawRowCorrection_le_strictScale_of_density
#check roughCanonicalCompleteSignedResidual
#check roughCanonicalCompleteSignedResidual_eq
#check abs_roughCanonicalCompleteSignedResidual_le

example (rawResidual signedExceptional rowCorrection aggregateGuard : Real) :
    roughCanonicalCompleteSignedResidual rawResidual signedExceptional
        rowCorrection aggregateGuard =
      rawResidual - signedExceptional - rowCorrection + aggregateGuard := by
  rfl

example (rawResidual signedExceptional rowCorrection aggregateGuard : Real) :
    roughCanonicalCompleteSignedResidual rawResidual signedExceptional
        rowCorrection aggregateGuard =
      rawResidual - signedExceptional - rowCorrection + aggregateGuard :=
  roughCanonicalCompleteSignedResidual_eq _ _ _ _

example (rawResidual signedExceptional rowCorrection aggregateGuard : Real) :
    abs (roughCanonicalCompleteSignedResidual rawResidual signedExceptional
      rowCorrection aggregateGuard) <=
      abs rawResidual + abs signedExceptional + abs rowCorrection +
        abs aggregateGuard :=
  abs_roughCanonicalCompleteSignedResidual_le _ _ _ _

example (n h K : Nat) (deltaStar : Real)
    (rawWeight : Nat -> Real) (p : Nat) (bound : Real) :
    RoughCanonicalSignedExceptionalResidualBound n h K deltaStar
        rawWeight p bound ↔
      abs (roughCanonicalSignedExceptionalResidual n h K deltaStar
        rawWeight p) <= bound := by
  rfl

example
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K : Nat) (rawWeight : Nat -> Real)
    (p : Nat) (bound : Real) :
    RoughCanonicalAggregateGuardResidualBound R certificate deltaStar K
        rawWeight p bound ↔
      abs (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
        rawWeight p) <= bound := by
  rfl

example (W n h K p : Nat) (deltaStar alpha beta logScale bound : Real) :
    RoughCanonicalAggregateRawRowCorrectionBound W n h K deltaStar
        alpha beta logScale p bound ↔
      abs (roughCanonicalAggregateRawRowCorrection W n h K deltaStar
        alpha beta logScale p) ≤ bound := by
  rfl

example (W n h K : Nat)
    (deltaStar alpha beta logScale densityBound : Real) :
    RoughCanonicalUniformRawRowCorrectionDensityBound W n h K deltaStar
        alpha beta logScale densityBound ↔
      ∀ label ∈ roughCanonicalActiveRawCorrectionLabels n h K deltaStar,
        abs (roughCanonicalRawCorrectionDensityAtLabel
          W n h K alpha beta logScale label) ≤ densityBound := by
  rfl

#check RoughCanonicalSignedExceptionalResidualBound
#check RoughCanonicalAggregateGuardResidualBound
#check RoughCanonicalAggregateRawRowCorrectionBound
#check RoughCanonicalUniformRawRowCorrectionDensityBound
#check roughCanonicalSignedExceptionalResidualBound_of_positive_parts
#check roughCanonicalAggregateGuardResidualBound_of_majorant
#check roughCanonicalAggregateRawRowCorrectionBound_of_rowwise
#check roughCanonicalAggregateRawRowCorrectionBound_of_uniformDensity
#check roughCanonicalAggregateRawRowCorrectionBound_strictScale_of_uniformDensity
#check eventually_roughCanonicalAggregateGuardResidualBound
#check abs_roughCanonicalCompleteSignedResidual_le_scale

example
    {scale C_raw C_exceptional C_row C_guard : Real}
    {rawResidual signedExceptional rowCorrection aggregateGuard : Real}
    (hscale : 0 <= scale)
    (hraw : abs rawResidual <= C_raw * scale)
    (hexceptional : abs signedExceptional <= C_exceptional * scale)
    (hrow : abs rowCorrection <= C_row * scale)
    (hguard : abs aggregateGuard <= C_guard * scale) :
    abs (roughCanonicalCompleteSignedResidual rawResidual signedExceptional
      rowCorrection aggregateGuard) <=
        (C_raw + C_exceptional + C_row + C_guard) * scale :=
  abs_roughCanonicalCompleteSignedResidual_le_scale hscale hraw
    hexceptional hrow hguard

end BankPaperRealization

end

end Erdos390.WholePaper
