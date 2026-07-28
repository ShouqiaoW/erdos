import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightLocalInputConnector

/-!
# Statement audit for the paper-faithful post-height finite input

The declarations below expose the complete fixed-witness route:

* certificate-dependent `logY`, rounded `Lambda0`, and `A0`;
* the fresh active-mass bridge of mass `q0-d`;
* source and dependent finite input packages;
* derived ordinary-log, frozen-ledger, target-envelope, and reserve facts;
* the guarded-slack producer and synchronized-input adapter.

No legacy symmetric-height core occurs in any checked declaration.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization

#check bankPaperCanonicalSectionNinePostHeightLogY
#check bankPaperCanonicalSectionNinePostHeightRoundedQ0
#check bankPaperCanonicalSectionNinePostHeightRoundedLambda0
#check bankPaperCanonicalSectionNinePostHeightA0
#check bankPaperCanonicalSectionNinePostHeightActiveHeadTarget

#check BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
#check BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
#check
  BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_q
#check
  BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightTarget_eq_scaffoldTarget
#check
  BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_baseWeight
#check
  BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.roundedQ0_eq_postHeightBridge
#check
  BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.roundedLambda0_eq_postHeightBridge

#check BankPaperCanonicalSectionNinePostHeightSourceInputsAt
#check
  BankPaperCanonicalSectionNinePostHeightSourceInputsAt.sourceToPostHeight
#check
  BankPaperCanonicalSectionNinePostHeightSourceInputsAt.activeSeedUpper

#check BankPaperCanonicalSectionNinePostHeightDependentInputsAt
#check
  BankPaperCanonicalSectionNinePostHeightDependentInputsAt.ordinaryLogCompatible
#check
  BankPaperCanonicalSectionNinePostHeightDependentInputsAt.placedFrozenLedger
#check
  BankPaperCanonicalSectionNinePostHeightDependentInputsAt.targetEnvelopes
#check
  BankPaperCanonicalSectionNinePostHeightDependentInputsAt.protectedReserve

#check bankPaperCanonicalSectionNinePostHeightPlacedSelectorDeficit_eq
#check
  exists_bankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage_of_postHeightInputs
#check
  bankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt_of_postHeightInputs

end BankPaperRealization

end

end Erdos390.WholePaper
