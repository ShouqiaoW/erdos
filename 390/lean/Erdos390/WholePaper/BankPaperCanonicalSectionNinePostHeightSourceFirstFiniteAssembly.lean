import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstMassAlgebra

/-!
# Finite source-first assembly of the post-height bridge

The source head reserve and source barycentric bridge are constructed before
the exact Section 8 ledger.  The ledger then supplies the final mass and
physical mean, from which a potentially different positive post-height head
margin is chosen.

`BankPaperCanonicalSectionNinePostHeightBridgeInputsAt` stores the source
target and the post-height target inputs separately, so there is no
mathematical reason for the source and post margins to be the same number.
This finite helper exposes that separation directly.
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

noncomputable section

namespace BankPaperRealization

/-- Assemble the fresh post-height bridge from an already constructed source
bridge and source reserve.  Only the post-height margin is supplied here;
the source margin remains encapsulated in the honest preconstructed
`Rhead`. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeightBridgeInputsAt_of_preconstructedSource_and_postMargin
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
    ∃ J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
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
  have hactiveMass :
      0 <
        bankPaperCanonicalSectionNinePostHeightActiveMass
          (bankPaperCanonicalSectionNinePostHeightRoundedQ0
            (K0 + 1) Bsource R certificate deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                Bsource c K0 betaProt betaAct)
              qTilde)
          d := by
    rw [bankPaperCanonicalSectionNinePostHeightActiveMass_eq, hq0Sync,
      ← hqnEq]
    exact hqn
  have hmean :
      bankPaperCanonicalSectionNinePostHeightPhysicalMean
          Bsource
          (bankPaperCanonicalSectionNinePostHeightRoundedQ0
            (K0 + 1) Bsource R certificate deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                Bsource c K0 betaProt betaAct)
              qTilde)
          (bankPaperCanonicalSectionNinePostHeightA0
            (K0 + 1) Bsource R certificate Tsource deltaStar
              betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                Bsource c K0 betaProt betaAct)
              (betaProt + betaAct) qTilde)
          d =
        (A0 + (d : Real) * L Bsource.sampleData.n) / qn := by
    unfold bankPaperCanonicalSectionNinePostHeightPhysicalMean
      bankPaperCanonicalSectionNinePostHeightPhysicalLogMean
      bankPaperCanonicalSectionNinePostHeightActiveHeight
      bankPaperCanonicalSectionNinePostHeightActiveMass
    rw [hq0Sync, hA0Sync, ← hqnEq]
    rfl
  let Htarget :
      BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
        Bsource bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
        (bankPaperCanonicalSectionNinePostHeightRoundedQ0
          (K0 + 1) Bsource R certificate deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              Bsource c K0 betaProt betaAct)
            qTilde)
        (bankPaperCanonicalSectionNinePostHeightA0
          (K0 + 1) Bsource R certificate Tsource deltaStar
            betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              Bsource c K0 betaProt betaAct)
            (betaProt + betaAct) qTilde)
        d Rhead.exponent
        (bankPaperCanonicalSectionNinePostHeightActiveHeadTarget
          Bsource R certificate deltaStar) :=
    { exponent_pos := Rhead.exponent_pos
      activeMass_pos := hactiveMass
      headMargin := postMargin
      headMargin_pos := hpostMargin
      vertex_margin := by
        intro p
        simpa only [
          bankPaperCanonicalSectionNinePostHeightActiveHeadTarget,
          bankPaperCanonicalSectionNinePostHeightActiveMass_eq,
          hq0Sync, ← hqnEq] using hpostVertex p
      zero_margin := by
        simpa only [
          bankPaperCanonicalSectionNinePostHeightActiveHeadTarget,
          bankPaperCanonicalSectionNinePostHeightActiveMass_eq,
          hq0Sync, ← hqnEq] using hpostZero
      physicalEta :=
        bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2
      physicalEta_pos := by
        exact half_pos
          bankPaperCanonicalSectionNinePostHeightPhysicalEta_pos
      minus_below := by
        rw [hmean]
        exact hphysical.1
      plus_above := by
        rw [hmean]
        exact hphysical.2 }
  let J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate
        bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
        deltaStar hdelta :=
    { Tsource := Tsource
      betaProt := betaProt
      betaAct := betaAct
      qTilde := qTilde
      d := d
      exponent := Rhead.exponent
      hW := hW
      scaleSeparation := S
      hlo := hlo
      hhi := hhi
      targetInputs := Htarget }
  refine ⟨J, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [J] using hTsource
  · exact hqTilde
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hq0Sync
  · exact hA0Sync
  · change
      bankPaperCanonicalSectionNinePostHeightRoundedQ0
            (K0 + 1) Bsource R certificate deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                Bsource c K0 betaProt betaAct)
              qTilde -
          (d : Real) =
        qn
    rw [hq0Sync]
    exact hqnEq.symm
  · rfl
  · rfl

end BankPaperRealization

end

end Erdos390.WholePaper
