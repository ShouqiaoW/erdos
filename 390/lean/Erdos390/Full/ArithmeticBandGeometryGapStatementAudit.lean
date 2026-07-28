import Erdos390.Full.ArithmeticBandGeometry

/-!
# Statement-shape audit for the finite arithmetic quotient gap

The two conclusions use only the literal arithmetic partition, its exact
gauge identity, and positivity/comparison of its two finite quadratic
moments.  No continuum centre, limit operator, or asymptotic transfer is an
input.
-/

#check Erdos390.Full.ArithmeticBandGeometry.Partition.physicalSq_ge_gauge_add_harmonic_gap
#check Erdos390.Full.ArithmeticBandGeometry.Partition.half_variance_le_physicalSq
