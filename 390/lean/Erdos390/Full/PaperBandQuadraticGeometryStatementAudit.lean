import Erdos390.Full.PaperBandQuadraticGeometry

/-!
# Expanded statement audit for the full arithmetic band quotient geometry

The terminal below deliberately repeats every quantifier and displayed
coefficient.  In particular it exposes the exact minimizing physical
coefficient, the relative row hypothesis, and the structural arithmetic
`D`-distance rather than checking only a theorem name.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperBandQuadraticGeometryStatementAudit

open Erdos390.Full
open ArithmeticModel ArithmeticBandGeometry
open ArithmeticBandGeometry.Partition
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]

example [Nonempty Band]
    (P : Partition n W Band) (hn : 1 < n)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2)
    (anchor : Finset (PrimeIndex n W))
    (hinterior : ∀ p ∈ anchor,
      tPrime n p.1 ∈ Icc epsilon (1 - epsilon))
    (hmass : 0 < anchorMass (primeWeight n) anchor)
    {rowError : ℝ}
    (hrow : ∀ p : PrimeIndex n W,
      |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
        rowError * tPrime n p.1) :
    ∃ kappa : ℝ, 0 < kappa ∧
      (rowError ≤ (kappa / 2) * anchorMass (primeWeight n) anchor →
        ∀ b : Band → ℝ,
          ((kappa / 2) * anchorMass (primeWeight n) anchor - rowError) *
              P.data.bandNormSq (P.data.gaugePart b) ≤
            primeReferenceQuadratic n
              (P.data.residual b (P.data.physicalMinimizer b))) := by
  exact
    Erdos390.Full.PaperBandQuadraticGeometry.exists_primeReference_fullQuotient_lower
      P hn hepsilon hhalf anchor hinterior hmass hrow

end Erdos390.Full.PaperBandQuadraticGeometryStatementAudit
