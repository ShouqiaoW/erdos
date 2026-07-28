import Erdos390.Full.PaperActualFullProjectedInverseEventually

/-!
# Statement audit for the eventual literal full-projected inverse

The terminal theorem visibly chooses the uniform inverse constant and mesh
tolerance before the prime cutoff, and the cutoff before the ambient limit.
After the threshold it assumes only exact canonical constructor equalities
and the two fixed coefficient-box bounds.  There is no reference inverse,
squarefree row bound, Lemma 7.5 package, or full-power row bound among its
hypotheses.
-/

#check Erdos390.Full.PaperBridgeFit.BridgeData.canonical_varyingInverseConstant_le
#check Erdos390.Full.PaperBridgeFit.BridgeData.abs_actual_squarefreeSharpRow_sub_equalPartitionArithmetic_le
#check Erdos390.Full.PaperBridgeFit.BridgeData.exists_actualFullProjectedEquiv_of_equal_referencePartition
#check Erdos390.Full.PaperBridgeFit.BridgeData.exists_meshTolerance_cutoff_eventually_canonical_actualFullProjected_inverse
