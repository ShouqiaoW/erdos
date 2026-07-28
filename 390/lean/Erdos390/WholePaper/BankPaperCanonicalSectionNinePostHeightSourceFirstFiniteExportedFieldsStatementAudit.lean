import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstFiniteExportedFields

/-!
# Statement audit for the source-first finite exported fields

This audit restates the complete signatures of the five finite exports:

* exact identification of the rounded frozen remainder with the protected
  layer;
* the pointwise rounded frozen-ledger bound;
* nonemptiness of the guarded broad correction pool;
* exact synchronization of the local `q0`; and
* exact synchronization of the local integer height.

Each expanded statement is assigned directly from the corresponding
production theorem.
-/

open Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularRelativeMesh
open BankPaperRealization

noncomputable section

section FiniteSourceFields

variable
    {delta eta : Real} {M : RegularRelativeMesh.Mesh delta eta}
    {P : Finset Nat}
    {Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M)}
    {c : Real} {depth K0 : Nat}
    {R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n))}
    {certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {I : PhysicalIntervals} {deltaStar : Real} {hdelta : 0 < delta}
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta)
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J)

include S

/-! ## Rounded frozen remainder and ledger -/

example
    (m : J.postHeightBridge.sampleData.Sample) :
    BridgeData.frozenAmbientWeight
        (bankPaperCanonicalActualFrozenValue
          (candidates :=
            R.roughCanonicalGuardedCandidateSet certificate
              deltaStar (K0 + 1)))
        (bankPaperCanonicalActualFrozenWeight
          J.postHeightBridge.sampleData
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          J.roundedSourceSelector J.roundedActiveSeed)
        (J.postHeightBridge.sampleData.value m) =
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K0 + 1)
        J.postHeightBridge R certificate deltaStar J.betaProt
          (J.postHeightBridge.sampleData.value m) := by
  exact
    BankPaperRealization.bankPaperCanonicalSectionNinePostHeight_roundedFrozenAmbientWeight_eq_protectedLayer
      J S m

example
    (m : J.postHeightBridge.sampleData.Sample) :
    BridgeData.frozenAmbientWeight
        (bankPaperCanonicalActualFrozenValue
          (candidates :=
            R.roughCanonicalGuardedCandidateSet certificate
              deltaStar (K0 + 1)))
        (bankPaperCanonicalActualFrozenWeight
          J.postHeightBridge.sampleData
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          J.roundedSourceSelector J.roundedActiveSeed)
        (J.postHeightBridge.sampleData.value m) ≤
      (J.betaProt + S.Cmass / S.density) /
        J.postHeightBridge.L := by
  exact
    BankPaperRealization.bankPaperCanonicalSectionNinePostHeight_roundedFrozenLedger_of_sourceInputs
      J S m

/-! ## Broad correction pool -/

example :
    (R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar J.postHeightBridge.sampleData.W (K0 + 1) 1).Nonempty := by
  exact
    BankPaperRealization.bankPaperCanonicalSectionNinePostHeight_guardedBroadCorrectionPool_nonempty_of_sourceInputs
      J S

/-! ## Analytic-family synchronization -/

variable
    {E : Nat}
    {mu sourceMarginFloor headMarginFloor physicalEtaFloor
      postMarginFloor : Real}
    {logY Lambda0 mFrozen qTilde : Nat → Real}
    (Hgap : BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt
      M Bsource R certificate I E deltaStar mu sourceMarginFloor
        headMarginFloor physicalEtaFloor postMarginFloor
        logY Lambda0 mFrozen qTilde hdelta J S)

include Hgap

example :
    J.q0 =
      bankPaperCanonicalSmoothQ0Family
        mFrozen qTilde Bsource.sampleData.n := by
  exact
    BankPaperRealization.bankPaperCanonicalSectionNinePostHeight_q0_eq_smoothQ0Family_of_primitiveGaps
      J S Hgap

example :
    (J.d : Real) =
      bankPaperCanonicalSmoothDRealFamily
        mu logY Lambda0 mFrozen qTilde
          J.postHeightBridge.sampleData.n := by
  exact
    BankPaperRealization.bankPaperCanonicalSectionNinePostHeight_d_eq_smoothDRealFamily_of_primitiveGaps
      J S Hgap

end FiniteSourceFields

#check
  BankPaperRealization.bankPaperCanonicalSectionNinePostHeight_roundedFrozenAmbientWeight_eq_protectedLayer
#check
  BankPaperRealization.bankPaperCanonicalSectionNinePostHeight_roundedFrozenLedger_of_sourceInputs
#check
  BankPaperRealization.bankPaperCanonicalSectionNinePostHeight_guardedBroadCorrectionPool_nonempty_of_sourceInputs
#check
  BankPaperRealization.bankPaperCanonicalSectionNinePostHeight_q0_eq_smoothQ0Family_of_primitiveGaps
#check
  BankPaperRealization.bankPaperCanonicalSectionNinePostHeight_d_eq_smoothDRealFamily_of_primitiveGaps

end

end Erdos390.WholePaper
