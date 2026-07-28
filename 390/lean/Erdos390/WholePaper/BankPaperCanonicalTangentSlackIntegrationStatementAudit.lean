import Erdos390.WholePaper.BankPaperCanonicalTangentSlackIntegration

/-! # Statement audit for the canonical tangent-slack integration

The checks below cover all five public definitions and all ten public
theorems.  The examples restate the parameter choice and the two quantitative
correction statements; the remaining (long, request-parametric) declarations
are checked at their fully elaborated public types.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! Complete declaration inventory: five definitions and ten theorems. -/

#check IsPaperCombinedTangentDeltaStar
#check paperCombinedTangentDeltaStar
#check paperCombinedTangentDeltaStar_spec
#check paperCombinedTangentDeltaStar_chargeSpec
#check paperCombinedTangentDeltaStar_cleanListInputs
#check exists_eventually_bankPaperCombinedChargeTerminal_for_tangentChoice

example (c : Real) (W : Nat) (r0 deltaStar : Real) :
    IsPaperCombinedTangentDeltaStar c W r0 deltaStar ↔
      IsPaperCombinedChargeDeltaStar c deltaStar ∧
        80 * tangentSelbergCanonicalMainConstant * deltaStar <
          tangentPaperHeadGap W r0 := by
  rfl

example (c : Real) (W : Nat) (r0 : Real) :
    paperCombinedTangentDeltaStar c W r0 =
      min (paperCombinedChargeDeltaStar c)
        (tangentPaperHeadGap W r0 /
          (160 * tangentSelbergCanonicalMainConstant)) := by
  rfl

example {c r0 : Real} (W : Nat) (hc : C0 < c) (hr0 : r0 < 2) :
    IsPaperCombinedTangentDeltaStar c W r0
      (paperCombinedTangentDeltaStar c W r0) :=
  paperCombinedTangentDeltaStar_spec W hc hr0

example {c r0 : Real} (W : Nat) (hc : C0 < c) (hr0 : r0 < 2) :
    IsPaperCombinedChargeDeltaStar c
      (paperCombinedTangentDeltaStar c W r0) :=
  paperCombinedTangentDeltaStar_chargeSpec W hc hr0

example {c r0 : Real} (W : Nat) (hc : C0 < c) (hr0 : r0 < 2) :
    0 < paperCombinedTangentDeltaStar c W r0 ∧
      paperCombinedTangentDeltaStar c W r0 < 1 / 18 ∧
      80 * tangentSelbergCanonicalMainConstant *
          paperCombinedTangentDeltaStar c W r0 <
        tangentPaperHeadGap W r0 :=
  paperCombinedTangentDeltaStar_cleanListInputs W hc hr0

namespace BankPaperRealization

#check roughCanonicalGuardedPostchargeCorrectionDensity
#check roughCanonicalGuardedPostchargeRowCorrectedWeight
#check roughCanonicalGuardedPostchargeRowCorrectedWeight_apply_of_mem
#check roughCanonicalGuardedPostchargeRowCorrectedWeight_twoSidedSlack
#check canonicalDistributedCleanMultiplier_guardedBroadEndpoints
#check BankPaperCanonicalGuardedEndpointSlackConstruction
#check guardedEndpointSlackConstruction_twoSidedSlack_of_mem
#check guardedEndpointSlackConstruction_cleanMultiplierSlack
#check guardedEndpointSlackConstruction_candidateSetEndpointInputs

example
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K label : Nat) (alpha beta L : Real) :
    R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
        deltaStar W K label alpha beta L =
      bankPaperConstantPoolCorrectionDensity
        (R.roughCanonicalGuardedRow certificate deltaStar K label)
        (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
          W K label)
        (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
          alpha beta L)
        (R.roughCanonicalPostchargeRowTarget deltaStar label) := by
  rfl

example
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K label : Nat) (alpha beta L : Real) (a : Nat) :
    R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
        deltaStar W K label alpha beta L a =
      bankPaperConstantPoolCorrection
        (R.roughCanonicalGuardedRow certificate deltaStar K label)
        (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
          W K label)
        (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
          alpha beta L)
        (R.roughCanonicalPostchargeRowTarget deltaStar label) a := by
  rfl

example
    {c : Real} {depth n W K label : Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {deltaStar alpha beta L : Real} {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar W K label) :
    R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
        deltaStar W K label alpha beta L a =
      beta / L +
        R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
          deltaStar W K label alpha beta L :=
  R.roughCanonicalGuardedPostchargeRowCorrectedWeight_apply_of_mem ha

example
    {c : Real} {depth n W K label : Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {deltaStar alpha beta L sigma : Real} {a : Nat}
    (hfloor :
      sigma / L +
          |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W K label alpha beta L| ≤ beta / L)
    (hceiling :
      beta / L +
          |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W K label alpha beta L| ≤ 1 - sigma / L)
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar W K label) :
    sigma / L ≤
        R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
          deltaStar W K label alpha beta L a ∧
      R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
          deltaStar W K label alpha beta L a ≤ 1 - sigma / L :=
  R.roughCanonicalGuardedPostchargeRowCorrectedWeight_twoSidedSlack
    hfloor hceiling ha

end BankPaperRealization

end


end Erdos390.WholePaper
