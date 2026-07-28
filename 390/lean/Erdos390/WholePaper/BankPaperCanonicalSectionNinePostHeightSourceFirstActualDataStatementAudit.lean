import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstActualData

/-!
# Statement audit for the source-first actual-data identities
-/

open Filter Topology Set

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.Scale
open BankPaperRealization

noncomputable section

example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (hqTilde : 1 ≤ qTilde)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (halpha : 0 ≤ alpha ∧ alpha ≤ 1)
    (hbetaProtBox :
      0 ≤ betaProt / B.L ∧ betaProt / B.L ≤ 1)
    (hselectorNonneg : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 ≤
        R.bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde) a) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (R.bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B certificate deltaStar betaProt alpha betaTotal
          (bankPaperCanonicalScaledActiveSeed T qTilde))
      (bankPaperCanonicalScaledActiveSeed T qTilde) :=
  R.bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_actualActiveMeasureConstructor
    B certificate T deltaStar betaProt alpha betaTotal qTilde
      hqTilde hsep hactiveSmooth halpha hbetaProtBox hselectorNonneg

example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed bankBase : Finset Nat)
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1) :
    bankPaperCanonicalActualFrozenLogMass B.sampleData fixed bankBase
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde)
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate T deltaStar betaProt alpha qTilde) =
      bankPaperCanonicalActualFrozenLogMass B.sampleData fixed bankBase
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (R.bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde))
        (bankPaperCanonicalScaledActiveSeed T qTilde) :=
  R.bankPaperCanonicalTopFrozenRounded_actualFrozenLogMass_eq_qTildeSource
    B certificate fixed bankBase T deltaStar betaProt alpha betaTotal
      qTilde hactiveSmooth

#check BankPaperRealization.bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_actualActiveMeasureConstructor
#check BankPaperRealization.bankPaperCanonicalTopFrozenRounded_actualFrozenLogMass_eq_qTildeSource

end

end Erdos390.WholePaper
