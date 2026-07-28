import Erdos390.Full.PaperCompensatedCoefficientBounds

/-!
# Statement-shape audit for the literal raw-gauge geometric gap

The terminal consumes only the actual finite arithmetic partition, a raw
gauge vector, and the explicit moment comparison `variance ≤ centerEnergy`.
It has no continuum-centre, covariance-gap, or asymptotic-transfer input.
-/

#check Erdos390.Full.ArithmeticBandGeometry.Partition.centerEnergy_pos
#check Erdos390.Full.ArithmeticBandGeometry.Partition.rawGauge_inGauge
#check Erdos390.Full.ArithmeticBandGeometry.Partition.half_variance_le_physicalSq_rawGauge
