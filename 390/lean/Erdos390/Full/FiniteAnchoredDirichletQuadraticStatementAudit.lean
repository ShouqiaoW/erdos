import Erdos390.Full.FiniteAnchoredDirichletQuadratic

/-!
# Statement audit for the finite multi-anchor Dirichlet algebra

The printed types expose the symmetry, sign, anchor-edge, and literal finite
centering hypotheses.  In particular there is no assumed spectral gap or
continuum convergence theorem.
-/

#check Erdos390.Full.FiniteAnchoredDirichletQuadratic.referenceQuadratic_eq_dirichletEnergy_add_rowResidual
#check Erdos390.Full.FiniteAnchoredDirichletQuadratic.anchorMass_mul_weightedDistance_le_anchorPairVariation
#check Erdos390.Full.FiniteAnchoredDirichletQuadratic.half_kappa_anchorMass_mul_weightedDistance_le_dirichletEnergy
