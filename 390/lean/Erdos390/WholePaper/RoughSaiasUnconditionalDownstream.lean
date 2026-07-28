import Erdos390.WholePaper.RoughCompactBVTranslation
import Erdos390.WholePaper.BankPaperCanonicalSaiasUpperReduction

/-!
# Unconditional downstream Saias wrappers

`RoughCompactBVTranslation.lean` proves the pure compact bounded-variation
principle that the weighted Saias and canonical-row developments previously
accepted as their first argument.  This module exposes the principal
downstream theorems with that argument discharged.

Every declaration below is a literal partial application of the existing
theorem to `roughCompactBVTranslationPrinciple`.  Consequently no other
hypothesis is changed: the HT--Saias endpoint approximation, deterministic
and transition ledgers, fixed-head allowance, and selector/tangent-flow
handoff remain exactly where they occurred in the original signatures.

Here `unconditional` means only that the pure BV premise has been discharged.
These wrappers do not select the closed coarse rate `(K+1)/log y`, and they do
not claim an `O(X/log(y)^2)` endpoint error.  A paper-absorbable endpoint rate
must instead come from the distinct sharp defect reduction in
`RoughSaiasEndpointApproximation.lean`.
-/

namespace Erdos390.WholePaper

noncomputable section

/-! ## Weighted transition wrappers -/

def roughFriableResidual_difference_abs_le_of_saiasEndpointApproximation_unconditional :=
  @roughFriableResidual_difference_abs_le_of_saiasEndpointApproximation
    roughCompactBVTranslationPrinciple

def roughPhysicalResidualTransition_abs_le_of_saiasEndpointApproximation_unconditional :=
  @roughPhysicalResidualTransition_abs_le_of_saiasEndpointApproximation
    roughCompactBVTranslationPrinciple

def roughPhysicalFriableCombination_abs_le_of_saiasEndpointApproximation_unconditional :=
  @roughPhysicalFriableCombination_abs_le_of_saiasEndpointApproximation
    roughCompactBVTranslationPrinciple

def roughPhysicalFriableCombination_abs_le_of_saiasPaperScale_unconditional :=
  @roughPhysicalFriableCombination_abs_le_of_saiasPaperScale
    roughCompactBVTranslationPrinciple

def roughPhysicalFriableCombination_abs_le_two_mul_of_saiasPaperScale_unconditional :=
  @roughPhysicalFriableCombination_abs_le_two_mul_of_saiasPaperScale
    roughCompactBVTranslationPrinciple

/-! ## Canonical-row wrappers -/

def roughCanonicalRawRowQuotaError_abs_le_of_saiasPaperScale_unconditional :=
  @roughCanonicalRawRowQuotaError_abs_le_of_saiasPaperScale
    roughCompactBVTranslationPrinciple

def roughCanonicalRawRowQuotaError_abs_le_of_literalSaiasPaperScale_unconditional :=
  @roughCanonicalRawRowQuotaError_abs_le_of_literalSaiasPaperScale
    roughCompactBVTranslationPrinciple

def roughCanonicalRawRowQuotaError_abs_le_of_literalSaiasAndHeadLedger_unconditional :=
  @roughCanonicalRawRowQuotaError_abs_le_of_literalSaiasAndHeadLedger
    roughCompactBVTranslationPrinciple

def roughCanonicalRawRowQuotaError_abs_le_three_mul_paperAllowance_unconditional :=
  @roughCanonicalRawRowQuotaError_abs_le_three_mul_paperAllowance
    roughCompactBVTranslationPrinciple

/-! ## Forward selector-handoff wrapper -/

def bankPaper_activeRoughRowQuota_and_isAdmissibleEndpoint_of_canonicalSaiasHandoff_unconditional :=
  @bankPaper_activeRoughRowQuota_and_isAdmissibleEndpoint_of_canonicalSaiasHandoff
    roughCompactBVTranslationPrinciple

end

end Erdos390.WholePaper
