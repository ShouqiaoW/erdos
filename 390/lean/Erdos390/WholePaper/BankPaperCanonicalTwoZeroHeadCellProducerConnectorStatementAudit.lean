import Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellProducerConnector

/-! # Statement audit for the two-zero-head-cell producer connector -/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-- Expanded scalar audit: the symmetric height choice changes total mass
by exactly `-d`, while each zero-cell coordinate is the changed total cell
mass divided by the actual cell cardinality. -/
example
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (T : BarycentricTarget D) (q0 : Real) (d : Int)
    (m : D.Sample) (sigma : PhysicalSign)
    (hcell : D.cellOf m = (none, sigma)) :
    bankPaperCanonicalLiteralActiveMass D
        (bankPaperCanonicalTwoZeroHeadCellRebalance D
          (bankPaperCanonicalScaledActiveSeed T q0)
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d)) =
        q0 - (d : Real) ∧
      bankPaperCanonicalTwoZeroHeadCellRebalance D
          (bankPaperCanonicalScaledActiveSeed T q0)
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d) m =
        (q0 * T.baseline.cellMass (none, sigma) - (d : Real) / 2) /
          Fintype.card (D.SampleAt (none, sigma)) := by
  exact ⟨
    bankPaperCanonicalLiteralActiveMass_symmetricHeightRebalance
      D T q0 d,
    bankPaperCanonicalSymmetricHeightRebalance_apply_of_zeroHeadCell
      D T q0 d m sigma hcell⟩

/-! ## Complete public declaration census -/

#check eventually_physicalBound_le_two_mul_sub_upperTailLength
#check eventually_physicalIntervals_upperBound_le_two_mul_sub_upperTailLength
#check bankPaperCanonicalZeroHeadValue_coprime_roughHeadModulus
#check bankPaperCanonicalZeroHeadValue_mem_guardedBroadCorrectionPool
#check bankPaperCanonicalZeroHeadValue_mem_guardedBroadCorrectionPool_of_physicalIntervals
#check bankPaperCanonicalTwoZeroHeadCells_subset_guardedBroadCorrectionPool_of_physicalIntervals
#check bankPaperCanonicalSymmetricHeightCellMass
#check bankPaperCanonicalSymmetricHeightCellMass_add_self
#check bankPaperCanonicalLiteralActiveMass_symmetricHeightRebalance
#check bankPaperCanonicalSymmetricInitialAndHeightCellMass
#check bankPaperCanonicalSymmetricInitialAndHeightCellMass_add_self
#check bankPaperCanonicalLiteralActiveMass_symmetricInitialAndHeightRebalance
#check bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_symmetricHeight
#check bankPaperCanonicalSymmetricRebalance_apply_of_zeroHeadCell
#check bankPaperCanonicalSymmetricHeightRebalance_apply_of_zeroHeadCell
#check bankPaperCanonicalSymmetricInitialAndHeightRebalance_apply_of_zeroHeadCell
#check bankPaperCanonicalSymmetricHeightRebalance_nonneg_of_cellMass
#check bankPaperCanonicalSymmetricHeightRebalance_protected_le_one_of_cellMass
#check bankPaperCanonicalSymmetricInitialAndHeightRebalance_nonneg_of_cellMass
#check bankPaperCanonicalSymmetricInitialAndHeightRebalance_protected_le_one_of_cellMass

end BankPaperRealization

end

end Erdos390.WholePaper
