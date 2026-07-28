import Erdos390.Full.PaperCanonicalHeadPhysicalTarget

/-!
# Statement audit for the canonical head and physical target

This census covers all twenty explicit public declarations in the source
module: the two paper-data structures, their public definitions and elementary
identities, and the three exported `BridgeData` consequences.  The four
finite-mean helpers marked `private` in the source are intentionally excluded.
-/

#check Erdos390.Full.PaperGuardCensus.HeadSimplexReserve
#check Erdos390.Full.PaperGuardCensus.HeadSimplexReserve.zeroCoefficient
#check Erdos390.Full.PaperGuardCensus.HeadSimplexReserve.beta
#check Erdos390.Full.PaperGuardCensus.HeadSimplexReserve.zeroCoefficient_margin
#check Erdos390.Full.PaperGuardCensus.HeadSimplexReserve.beta_margin
#check Erdos390.Full.PaperGuardCensus.HeadSimplexReserve.beta_pos
#check Erdos390.Full.PaperGuardCensus.HeadSimplexReserve.beta_sum
#check Erdos390.Full.PaperGuardCensus.HeadSimplexReserve.exponent_cast_pos
#check Erdos390.Full.PaperGuardCensus.HeadSimplexReserve.exponent_activeMass_ne
#check Erdos390.Full.PaperGuardCensus.HeadSimplexReserve.beta_exponent_moment

#check Erdos390.Full.PaperGuardCensus.PhysicalInterpolationTarget
#check Erdos390.Full.PaperGuardCensus.PhysicalInterpolationTarget.physicalSpan
#check Erdos390.Full.PaperGuardCensus.PhysicalInterpolationTarget.lower_minus_lt_upper_plus
#check Erdos390.Full.PaperGuardCensus.PhysicalInterpolationTarget.physicalSpan_pos
#check Erdos390.Full.PaperGuardCensus.PhysicalInterpolationTarget.tau
#check Erdos390.Full.PaperGuardCensus.PhysicalInterpolationTarget.tau_pos

#check Erdos390.Full.PaperBridgeFit.BridgeData.barycentricTargetOfPaperData
#check Erdos390.Full.PaperBridgeFit.BridgeData.barycentricTargetOfPaperData_headExponentMoment
#check Erdos390.Full.PaperBridgeFit.BridgeData.barycentricTargetOfPaperData_cellMassMargin
#check Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment_physicalScore_zero_eq_mu_ofPaperData
