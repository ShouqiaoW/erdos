import Erdos390.WholePaper.BankPaperCanonicalSectionNineTopFrozenSymmetricHeightLocalInputConnector

/-!
# Statement audit for the frozen-top symmetric-height finite input

The example below exposes the exact finite output.  Its source is the
literal frozen-top selector and no equality with the legacy global source
selector occurs in the signature.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

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
      BankPaperCanonicalSectionNineTopFrozenSymmetricHeightSourceInputsAt
        B R certificate K0 deltaStar)
    (A :
      BankPaperCanonicalSectionNineTopFrozenSymmetricHeightDependentInputsAt
        B R certificate K0 deltaStar sigma Cpost S) :
    ∃ quota : Int, ∃ path : Real → B.ParamSpace,
      ∃ endpoint : Nat → Real,
        BankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage
          (K := K0 + 1) B R certificate
          (R.paperFixedExceptionalFactors deltaStar) S.Tsource
          deltaStar S.core.betaProt S.alpha S.beta S.qTilde sigma
          S.placementSeed S.activeSeed A.radius Cpost A.cellIndex
          quota path endpoint :=
  exists_bankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage_of_symmetricHeightInputs
    (K0 := K0) B R certificate deltaStar sigma Cpost S A

#check BankPaperCanonicalSectionNineTopFrozenSymmetricHeightSourceInputsAt
#check BankPaperCanonicalSectionNineTopFrozenSymmetricHeightDependentInputsAt
#check
  exists_bankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage_of_symmetricHeightInputs

end BankPaperRealization

end

end Erdos390.WholePaper
