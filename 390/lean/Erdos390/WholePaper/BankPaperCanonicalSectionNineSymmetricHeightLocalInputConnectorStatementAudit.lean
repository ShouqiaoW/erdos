import Erdos390.WholePaper.BankPaperCanonicalSectionNineSymmetricHeightLocalInputConnector

/-!
# Statement audit for the symmetric-height local-input connector

The audit exposes both the legacy three-package rounded-source path and the
primary weak source-state path.  It verifies the exact compatibility-builder
and finite-assembly signatures and that both paths stop at their corresponding
generic finite Post-Hfit interfaces.  It does not conclude a Post-Hfit
package, Section 9 output, final payload, collision statement, or asymptotic
budget.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Weak source-state path -/

example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (S : BankPaperCanonicalSectionNineSymmetricHeightSourceInputsAt
      B R certificate K0 deltaStar) :
    BankPaperCanonicalSectionNineSymmetricHeightCoreInputsAt
      B R certificate K0 deltaStar :=
  bankPaperCanonicalSectionNineSymmetricHeightCoreInputsAt_of_sourceInputs
    B R certificate K0 deltaStar S

example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (S : BankPaperCanonicalSectionNineSymmetricHeightSourceInputsAt
      B R certificate K0 deltaStar) :
    BankPaperCanonicalSectionNineSymmetricHeightSourceStateInputsAt
      B R certificate K0 deltaStar :=
  bankPaperCanonicalSectionNineSymmetricHeightSourceStateInputsAt_of_sourceInputs
    B R certificate K0 deltaStar S

example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar sigma Cpost : Real)
    (S : BankPaperCanonicalSectionNineSymmetricHeightSourceInputsAt
      B R certificate K0 deltaStar)
    (A : BankPaperCanonicalSectionNineSymmetricHeightP87InputsAt
      B R certificate K0 deltaStar Cpost S)
    (N : BankPaperCanonicalSectionNineSymmetricHeightSlackInputsAt
      B R certificate K0 deltaStar sigma Cpost S A) :
    BankPaperCanonicalSectionNineSymmetricHeightDependentInputsAt
      B R certificate K0 deltaStar sigma Cpost
        (bankPaperCanonicalSectionNineSymmetricHeightSourceStateInputsAt_of_sourceInputs
          B R certificate K0 deltaStar S) :=
  bankPaperCanonicalSectionNineSymmetricHeightDependentInputsAt_of_p87_slack
    B R certificate K0 deltaStar sigma Cpost S A N

example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar sigma Cpost : Real)
    (S :
      BankPaperCanonicalSectionNineSymmetricHeightSourceStateInputsAt
        B R certificate K0 deltaStar)
    (A : BankPaperCanonicalSectionNineSymmetricHeightDependentInputsAt
      B R certificate K0 deltaStar sigma Cpost S) :
    BankPaperCanonicalSectionNinePostHfitSourceStateLocalInputsAt
      (K0 := K0) B R certificate deltaStar sigma Cpost :=
  bankPaperCanonicalSectionNinePostHfitSourceStateLocalInputsAt_of_symmetricHeight
    (K0 := K0) B R certificate deltaStar sigma Cpost S A

/-! ## Legacy rounded-source path -/

example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar sigma Cpost : Real)
    (S : BankPaperCanonicalSectionNineSymmetricHeightSourceInputsAt
      B R certificate K0 deltaStar)
    (A : BankPaperCanonicalSectionNineSymmetricHeightP87InputsAt
      B R certificate K0 deltaStar Cpost S)
    (N : BankPaperCanonicalSectionNineSymmetricHeightSlackInputsAt
      B R certificate K0 deltaStar sigma Cpost S A) :
    BankPaperCanonicalSectionNinePostHfitLocalInputsAt
      (K0 := K0) B R certificate deltaStar sigma Cpost :=
  bankPaperCanonicalSectionNinePostHfitLocalInputsAt_of_symmetricHeight
    (K0 := K0) B R certificate deltaStar sigma Cpost S A N

#check BankPaperCanonicalSectionNineSymmetricHeightSourceInputsAt
#check BankPaperCanonicalSectionNineSymmetricHeightP87InputsAt
#check BankPaperCanonicalSectionNineSymmetricHeightSlackInputsAt
#check BankPaperCanonicalSectionNineSymmetricHeightCoreInputsAt
#check BankPaperCanonicalSectionNineSymmetricHeightSourceStateInputsAt
#check BankPaperCanonicalSectionNineSymmetricHeightDependentInputsAt
#check
  bankPaperCanonicalSectionNineSymmetricHeightCoreInputsAt_of_sourceInputs
#check
  bankPaperCanonicalSectionNineSymmetricHeightSourceStateInputsAt_of_sourceInputs
#check
  bankPaperCanonicalSectionNineSymmetricHeightDependentInputsAt_of_p87_slack
#check bankPaperCanonicalSymmetricHeightRebalance_le_div_log
#check
  bankPaperCanonicalSectionNinePostHfitSourceStateLocalInputsAt_of_symmetricHeight
#check bankPaperCanonicalSectionNinePostHfitLocalInputsAt_of_symmetricHeight

end BankPaperRealization

end

end Erdos390.WholePaper
