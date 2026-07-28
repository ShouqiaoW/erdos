import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstMassAlgebra

/-!
# Pre-mesh numerical data for the source-first post-height construction

This file isolates the numerical choices which genuinely precede the
regular mesh:

* lower and upper paper-scale coefficients for the guarded source mass;
* a positive head exponent already large enough for the retained quarter
  of the source coefficient; and
* the fixed source cell margin obtained from that head margin and the
  fixed physical interpolation target.

There is no mesh, mesh width, analytic ledger, bridge, or downstream input
package in the theorem statement.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-- Choose all numerical data needed before any regular mesh is selected.

The displayed equality records the literal definition of
`sourceCellMargin`; the remaining conclusions are only positivity, the
explicit exponent inequality, and the two-sided guarded-source mass
envelope. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshNumericalData
    {c betaAct : Real} {N : Nat}
    (depth W K0 : Nat)
    (hc : C0 < c)
    (hW : 0 < W)
    (hbetaAct : 0 < betaAct)
    (deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) :
    ∃ cSource cUpper : Real, ∃ E : Nat, ∃ sourceCellMargin : Real,
      0 < cSource ∧
        0 < cUpper ∧
        0 < E ∧
        sourceCellMargin =
          bankPaperCanonicalSectionNinePostHeightHeadMargin E
              (fun _ : {p : Nat // p ∈ primesUpTo W} =>
                bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W)
              cUpper *
            bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.tau ∧
        0 < sourceCellMargin ∧
        2 *
              (∑ p : {p : Nat // p ∈ primesUpTo W},
                bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
                  c p.1) ≤
            (E : Real) * (cSource / 4) ∧
        ∀ᶠ n : Nat in atTop,
          cSource * secondOrderScale n ≤
              F.extendedGuardedSmoothBaseMass
                W (K0 + 1) betaAct deltaStar n ∧
            F.extendedGuardedSmoothBaseMass
                W (K0 + 1) betaAct deltaStar n ≤
              cUpper * secondOrderScale n := by
  have hC0Pos : (0 : Real) < C0 := by
    norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
  obtain
      ⟨cSource, cUpper, E, hcSource, hcUpper, hE, hElarge, Hmass⟩ :=
    exists_eventually_bankPaperCanonicalSectionNinePostHeight_preledgerSourceMassExponent
      depth W (K0 + 1) hcPos hbetaAct deltaStar F
  let sourceCellMargin : Real :=
    bankPaperCanonicalSectionNinePostHeightHeadMargin E
        (fun _ : {p : Nat // p ∈ primesUpTo W} =>
          bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W)
        cUpper *
      bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.tau
  have hsourceCellMarginPos : 0 < sourceCellMargin := by
    apply mul_pos
    · exact
        bankPaperCanonicalSectionNinePostHeightHeadMargin_pos
          E _ cUpper hE
            (fun _ =>
              bankPaperCanonicalSectionNinePostHeightHeadLinearFloor_pos
                hc hW)
            hcUpper
    · exact
        bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.tau_pos
  exact
    ⟨cSource, cUpper, E, sourceCellMargin,
      hcSource, hcUpper, hE, rfl, hsourceCellMarginPos,
      hElarge, Hmass⟩

end

end Erdos390.WholePaper
