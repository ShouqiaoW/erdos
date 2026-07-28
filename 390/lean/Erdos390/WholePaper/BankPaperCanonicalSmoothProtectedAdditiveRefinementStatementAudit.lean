import Erdos390.WholePaper.BankPaperCanonicalSmoothProtectedAdditiveRefinement

/-!
# Statement audit for the smooth protected additive refinement

The public inventory consists of two definitions and eighteen theorems.
The expanded example records the pointwise identity which closes the
protected-remainder socket; the remaining declarations are checked at their
fully elaborated public types.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BankPaperRealization

#check bankPaperCanonicalGuardedSmoothProtectedLayer
#check bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
#check bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
#check bankPaperCanonicalGuardedSmoothProtectedLayer_pos_of_mem
#check bankPaperCanonicalGuardedSmoothProtectedLayer_eq_rawWeight_of_mem
#check roughHeadCompatibleRawWeight_eq_protected_add_active_of_mem_guardedSmoothPool
#check bankPaperCanonicalGuardedSmoothAdditiveRefinement
#check bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
#check bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_not_mem
#check bankPaperCanonicalGuardedSmoothAdditiveRefinement_sub_base
#check sum_guardedSmoothRow_additiveRefinement_sub_base_eq_pool
#check bankPaperCanonicalGuardedSmoothFlexibleQuota_additiveRefinement_of_rowChange
#check bankPaperCanonicalGuardedSmoothAdditiveRefinement_eq_base_on_nonsmoothPool
#check bankPaperCanonicalActiveSeedAmbientWeight_le_of_headPatternsSeparated
#check bankPaperCanonicalGuardedSmoothAdditiveRefinement_le_div_log
#check bankPaperCanonicalGuardedSmoothAdditiveRefinement_le_of_cellDensity
#check bankPaperCanonicalGuardedSmoothAdditiveRefinement_protectedReserve
#check bankPaperCanonicalGuardedSmoothAdditiveRefinement_frozenAmbientWeight_eq
#check bankPaperCanonicalGuardedSmoothAdditiveRefinement_protectedWindow
#check exists_bankPaperCanonicalGuardedSmoothAdditiveRefinement_endpointSlackLayers

example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
      B R certificate
        deltaStar betaProt baseSelector activeSeed a =
      betaProt / B.L +
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData activeSeed a :=
  bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
    B R certificate baseSelector activeSeed ha

end BankPaperRealization

end

end Erdos390.WholePaper
