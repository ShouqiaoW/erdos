import Erdos390.Full.GuardSquarefreeErrorRate

/-!
# Axiom audit for the squarefree guard-error rate

The declarations below must use only Lean's standard classical/quotient
axioms.  In particular, the moving-low logarithmic rate is proved rather
than supplied as an asymptotic contract.
-/

open Erdos390.Full.GuardSquarefreeErrorRate

#print axioms tendsto_censusRatioMajorant_mul_y_sq_zero
#print axioms tendsto_censusRatioMajorant_zero
#print axioms tendsto_censusRatioMajorant_mul_y_sq_mul_logL_zero
#print axioms tendsto_guardRateMajorant_zero
#print axioms tendsto_guardRateMajorant_mul_logL_zero
#print axioms guardSquarefreeError_rawCell_le_rateMajorant
#print axioms eventually_exp_two_mul_guardRatio_rawCell_le_half
#print axioms eventually_guarded_rawCell_density
#print axioms eventually_guarded_rawCell_endpoint_density
#print axioms canonicalGuardSquarefreeError_nonneg
#print axioms tendsto_canonicalGuardSquarefreeError_zero
#print axioms tendsto_canonicalGuardSquarefreeError_mul_logL_zero
