import Erdos390.WholePaper.BankPaperCanonicalSmoothAdditiveRefinementTangentTransport

/-!
# Statement audit for smooth additive refinement tangent transport

The public inventory consists of two definitions and sixteen theorems.  The
expanded example records the exact pointwise residual transport identity;
the remaining declarations are checked at their elaborated public types.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BankPaperRealization

#check bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment
#check BankPaperCanonicalGuardedSmoothAdditiveRefinementZeroMomentLedger
#check bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment_eq_zero_of_not_prime
#check bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment_eq_zero_of_yNat_lt
#check bankPaperCanonicalGuardedSmoothAdditiveRefinement_sub_base_at_scaledActiveValue
#check sum_guardedCandidates_additiveRefinement_factorization_sub_base_eq_moment
#check bankPaperCanonicalSelectorValuationDeficit_additiveRefinement_eq_sub_moment
#check bankPaperCanonicalTangentResidual_additiveRefinement_eq_sub_moment
#check sum_tangentResidual_additiveRefinement_eq_sub_moment
#check tangentRatioCellPrefixMass_additiveRefinement_eq_sub_moment
#check bankPaperCanonicalGuardedSmoothAdditiveRefinement_eq_base_on_guardedRow
#check sum_guardedRow_additiveRefinement_eq_base_of_label_ne_one
#check sum_guardedSmoothRow_additiveRefinement_eq_base_of_zeroMomentLedger
#check bankPaperCanonicalGuardedSmoothFlexibleQuota_additiveRefinement_of_zeroMomentLedger
#check bankPaperCanonicalSelectorValuationDeficit_additiveRefinement_eq_base_of_zeroMomentLedger
#check bankPaperCanonicalTangentResidual_additiveRefinement_eq_base_of_zeroMomentLedger
#check bankPaperCanonicalSelectorRowIntegral_additiveRefinement_of_zeroMomentLedger
#check bankPaperCanonicalRoundedSelectorTangentInput_additiveRefinement_of_zeroMomentLedger

example
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (p : BankPaperCanonicalTangentPrime B.sampleData.n B.sampleData.W) :
    bankPaperCanonicalTangentResidual R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
          B R certificate
          deltaStar betaProt baseSelector activeSeed) p =
      bankPaperCanonicalTangentResidual R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          baseSelector p -
        bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment (K := K)
          B R certificate deltaStar betaProt baseSelector activeSeed p.1 :=
  bankPaperCanonicalTangentResidual_additiveRefinement_eq_sub_moment
    (K := K) B R certificate fixed baseSelector activeSeed p

end BankPaperRealization

end

end Erdos390.WholePaper
