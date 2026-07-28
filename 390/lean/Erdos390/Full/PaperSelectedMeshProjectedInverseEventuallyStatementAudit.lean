import Erdos390.Full.PaperSelectedMeshProjectedInverseEventually

/-!
# Statement-shape audit for the nonvacuous selected-mesh inverse

The elaborated statement visibly chooses a universal continuum constant and
tolerance first, then exhibits an explicit dyadic regular mesh and its
nonempty anchor block, and only afterward chooses the arithmetic cutoff and
ambient threshold.  The conclusion constructs the literal projected
arithmetic equivalence and inverse bound; neither is an input.
-/

#check Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.exists_selectedDyadicMesh_eventually_canonical_projected_inverse
