import Erdos390.Full.PaperBridgeCanonicalGuardPowerCorrection

/-!
# Statement audit for the canonical guard prime-power row

These checks expose the complete elaborated public interfaces.  In
particular, the terminal theorem visibly quantifies the exact
`canonicalSampleData` equality and the genuine coefficient box; it has no
raw-cell density, half-mass, score, or valuation-envelope hypothesis.
-/

#check Erdos390.Full.PaperBridgeFit.BridgeData.canonicalRawMediumReferenceLaw
#check Erdos390.Full.PaperBridgeFit.BridgeData.canonicalGuardedMediumReferenceLaw
#check Erdos390.Full.PaperBridgeFit.BridgeData.sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le
#check Erdos390.Full.PaperBridgeFit.BridgeData.weighted_sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le
#check Erdos390.Full.PaperBridgeFit.BridgeData.exists_eventually_canonicalGuardPowerCorrection_reference_bound
#check Erdos390.Full.PaperBridgeFit.BridgeData.tendsto_guardPowerCorrectionWeightedMajorant_div_lowCenter_zero
