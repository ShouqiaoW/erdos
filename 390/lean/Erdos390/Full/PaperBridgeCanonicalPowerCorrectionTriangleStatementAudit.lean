import Erdos390.Full.PaperBridgeCanonicalPowerCorrectionTriangle

/-!
# Statement audit for the terminal canonical prime-power triangle

The final check visibly has neither a Lemma 7.5 certificate nor an
actual/reference power-row hypothesis: both are constructed internally.
Only the genuine residual-physical cell and box inputs remain explicit.
-/

#check Erdos390.Full.PaperBridgeFit.BridgeData.actual_powerCorrection_reference_weightedRow_le_of_two_sides
#check Erdos390.Full.PaperBridgeFit.BridgeData.actual_powerCorrection_canonicalRaw_weightedRow_le
#check Erdos390.Full.PaperBridgeFit.BridgeData.abs_actual_fullSharpRow_sub_squarefreeSharpRow_le_of_canonicalRaw
#check Erdos390.Full.PaperBridgeFit.BridgeData.exists_boxIndependent_canonicalRaw_fullSharp_of_physicalInputs
#check Erdos390.Full.PaperBridgeFit.BridgeData.boxIndependent_canonicalRaw_fullSharp
