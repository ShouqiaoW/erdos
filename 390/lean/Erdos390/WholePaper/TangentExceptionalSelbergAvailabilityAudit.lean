import Erdos390.WholePaper.TangentExceptionalCanonicalBounds

/-!
# Availability audit for the Section 9 exceptional-row sieve

The paper's required analytic chain is

1. construct Lambda-squared upper-sieve coefficients supported at level
   `R=y^2`;
2. diagonalize their main term and prove the sieve-density lower bound
   `L_P(R) \gg log y`;
3. use `[d,e] <= y^4` and the constant-one interval remainder to obtain
   `H / log y + y^4 / (log y)^2`;
4. sum over `b < X0/u` and use `delta_* < 1/18`.

The current `Mathlib.NumberTheory.SelbergSieve` file ends after the abstract
upper-Moebius inequality checked below.  It defines `BoundingSieve`,
`IsUpperMoebius`, `mainSum`, and `errSum`; it has no public construction of
the Lambda-squared coefficients, no diagonalized `L_P(R)` theorem, and no
specialization with a logarithmic main term.  The prime-number-theorem and
Chebyshev modules available in this repository estimate prime counting and
theta functions, but do not supply the missing sieve-density lower bound.

The project-local continuation now also closes the analytic boundary.  It
uses the verified interval Mertens theorem to prove
`G(P_y,y^2) >= exp(-K) log y / 10`, and a squarefree Euler-product mean
estimate to prove `||lambda||_1 <= exp(4) y^2 / G`.  The named constants
`tangentSelbergCanonicalMainConstant` and
`tangentSelbergCanonicalLambdaConstant` therefore give the two hypotheses
of the canonical paper-shape theorem eventually, without assumptions.  The
finite exceptional factorization and common-list ledger substitutions
remain checked in
`TangentExceptionalSelbergReductionStatementAudit`.
-/

#check BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius
#check Erdos390.WholePaper.reducedResidueIoc_card_le_abstractSelberg_l1
#check Erdos390.WholePaper.tangentSelbergLambdaSquareCoefficient_isUpperMoebius
#check Erdos390.WholePaper.tangentSelbergLambdaSquare_quadraticDiagonalization
#check Erdos390.WholePaper.tangentSelbergCanonicalLambda_quadratic_eq_invDensity
#check Erdos390.WholePaper.reducedResidueIoc_card_le_canonicalLambdaSquare_paperShape
#check Erdos390.WholePaper.eventually_tangentSelbergCanonical_invDensity_le
#check Erdos390.WholePaper.eventually_tangentSelbergCanonical_l1_le
#check Erdos390.WholePaper.eventually_reducedResidueIoc_card_le_canonicalLambdaSquare_roughHead
#check Erdos390.WholePaper.card_tangentExceptionalMultipliers_le_sieveSum
#check Erdos390.WholePaper.tangentExceptionalMultipliers_card_cast_le_abstractSelbergL1Majorant
#check Erdos390.WholePaper.tangentCommonMultiplier_abstractSelberg_finite_deletion_ledger
