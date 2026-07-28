import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshNumericalData

/-!
# Statement audit for the source-first pre-mesh numerical data

This audit freezes the fully expanded mesh-free interface: the four
numerical witnesses, the literal source-cell-margin definition, the
exponent budget, and the eventual two-sided guarded-source mass envelope.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

example
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
  exact
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshNumericalData
      depth W K0 hc hW hbetaAct deltaStar F

#check
  exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshNumericalData

end

end Erdos390.WholePaper
