import Erdos390.Full.PaperExactTwoStageTargetSolve

/-!
# Statement-shape audit for the exact two-stage target solve

The terminal theorem below visibly assumes the literal actual-band
equivalence and its sharp inverse estimate; the literal projected target,
compensated variance and target, compensated prime coefficients, and the
two actual nuisance coefficients are the only quantitative inputs.  It does
not assume a Schur solution bound, effective velocity, or any of the three
`hprime`/`hnuisance`/`hslow` conclusions used by the older assembly layer.
-/

#check Erdos390.Full.PaperBridgeFit.BridgeData.projectedNormalizedTargetBand
#check Erdos390.Full.PaperBridgeFit.BridgeData.compensatedNormalizedTarget
#check Erdos390.Full.PaperBridgeFit.BridgeData.compensatedNormalizedTarget_eq_slow_sub_bandDPairing
#check Erdos390.Full.PaperBridgeFit.BridgeData.twoStageCompensatedTargetBound
#check Erdos390.Full.PaperBridgeFit.BridgeData.abs_compensatedNormalizedTarget_le_of_regression_target
#check Erdos390.Full.PaperBridgeFit.BridgeData.actualTwoStageCompensatedVariance
#check Erdos390.Full.PaperBridgeFit.BridgeData.targetFastNuisanceCoefficient
#check Erdos390.Full.PaperBridgeFit.BridgeData.targetFastNuisanceCoefficient_norm_le_of_covarianceVector
#check Erdos390.Full.PaperBridgeFit.BridgeData.actualTwoStageNuisanceCoefficient_norm_le_of_covarianceVector
#check Erdos390.Full.PaperBridgeFit.BridgeData.exactSchur_solution_component_bounds_of_twoStageTargets
