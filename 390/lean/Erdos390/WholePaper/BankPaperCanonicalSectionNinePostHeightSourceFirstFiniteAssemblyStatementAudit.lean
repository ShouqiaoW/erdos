import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstFiniteAssembly

/-!
# Statement audit for finite source-first post-height assembly

The source reserve and target are explicit inputs.  The only margin selected
by this theorem is the independent post-height margin.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale
open BankPaperRealization

noncomputable section

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (hdelta : 0 < delta)
    (hW : Bsource.sampleData.W ≠ 0)
    (S : ScaleSeparation M Bsource.sampleData.n Bsource.sampleData.W)
    (hlo : ∀ sigma, Bsource.sampleData.lo sigma =
      physicalBound
        (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower sigma)
        Bsource.sampleData.n)
    (hhi : ∀ sigma, Bsource.sampleData.hi sigma =
      physicalBound
        (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper sigma)
        Bsource.sampleData.n)
    (Rhead : HeadSimplexReserve P)
    (Kphysical : PhysicalInterpolationTarget
      bankPaperCanonicalSectionNinePostHeightPhysicalIntervals)
    (Tsource : BarycentricTarget Bsource.sampleData)
    (hTsource :
      Tsource =
        Bsource.barycentricTargetOfPaperData
          bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
          hlo hhi Rhead Kphysical)
    (deltaStar betaProt betaAct qTilde q0 A0 qn : Real)
    (d : Int) (postMargin : Real)
    (hqTilde : qTilde = Rhead.activeMass)
    (hqn : 0 < qn)
    (hpostMargin : 0 < postMargin)
    (hpostVertex :
      ∀ p : {p : Nat // p ∈ P},
        postMargin ≤
          ((certificate.selectorTailTarget R
            (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
              Real) /
            ((Rhead.exponent : Real) * qn))
    (hpostZero :
      postMargin ≤
        1 - ∑ p : {p : Nat // p ∈ P},
          ((certificate.selectorTailTarget R
            (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
              Real) /
            ((Rhead.exponent : Real) * qn))
    (hqnEq : qn = q0 - (d : Real))
    (hphysical :
      Real.log
          (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
            .minus) ≤
        (A0 + (d : Real) * L Bsource.sampleData.n) / qn -
          bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ∧
      (A0 + (d : Real) * L Bsource.sampleData.n) / qn +
            bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ≤
        Real.log
          (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
            .plus))
    (hq0Sync :
      bankPaperCanonicalSectionNinePostHeightRoundedQ0
          (K0 + 1) Bsource R certificate deltaStar betaProt
          (bankPaperCanonicalPostHfitBalancedAlpha
            Bsource c K0 betaProt betaAct) qTilde =
        q0)
    (hA0Sync :
      bankPaperCanonicalSectionNinePostHeightA0
          (K0 + 1) Bsource R certificate Tsource deltaStar betaProt
          (bankPaperCanonicalPostHfitBalancedAlpha
            Bsource c K0 betaProt betaAct)
          (betaProt + betaAct) qTilde =
        A0) :
    ∃ J : BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
        (K0 := K0) M Bsource R certificate
          bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
          deltaStar hdelta,
      J.Tsource =
          J.postHeightBridge.barycentricTargetOfPaperData
            bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
            J.postHeightHlo J.postHeightHhi Rhead Kphysical ∧
        J.qTilde = Rhead.activeMass ∧
        J.exponent = Rhead.exponent ∧
        J.d = d ∧
        J.betaProt = betaProt ∧
        J.betaAct = betaAct ∧
        J.q0 = q0 ∧
        J.A0 = A0 ∧
        J.qn = qn ∧
        J.targetInputs.headMargin = postMargin ∧
        J.targetInputs.physicalEta =
          bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 := by
  exact
    BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeightBridgeInputsAt_of_preconstructedSource_and_postMargin
      M Bsource R certificate hdelta hW S hlo hhi Rhead Kphysical
        Tsource hTsource deltaStar betaProt betaAct qTilde q0 A0 qn
        d postMargin hqTilde hqn hpostMargin hpostVertex hpostZero
        hqnEq hphysical hq0Sync hA0Sync

#check
  BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeightBridgeInputsAt_of_preconstructedSource_and_postMargin

end

end Erdos390.WholePaper
