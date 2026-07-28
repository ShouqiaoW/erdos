import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceInputAssemblyConnector

/-!
# Statement audit: mechanical fresh post-height source-input assembly

The audited wrapper chooses its numerical constants before the mesh, then
chooses the eventual threshold after the mesh-dependent exponent-band type is
available.  It remains universally quantified over the coherent bridge and
its target/residual facts; it is not a completed eventual supplier.
-/

open Filter

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization

#check
  exists_bankPaperCanonicalSectionNinePostHeight_sourceInputsAndPrimitiveGapsAt_of_canonical
#check
  exists_eventually_bankPaperCanonicalSectionNinePostHeight_sourceInputsAndPrimitiveGapsAt_of_targetResidual

/-! ## Literal quantifier-order audit -/

example
    (P : Finset Nat)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat) (hE : 0 < E)
    (I : PhysicalIntervals)
    (hlowerOne : ∀ sign, 1 ≤ I.lower sign)
    (hupperStrict : ∀ sign, I.upper sign < 2)
    {c : Real} (depth W K0 Ntail : Nat)
    (F : BankPaperCanonicalGuardedTailFamily c depth Ntail)
    {deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
      physicalEtaFloor postMarginFloor : Real}
    (hc : 0 < c) (hbetaAct : 0 < betaAct) (hmu : 0 < mu)
    (hbetaProt : 0 ≤ betaProt)
    (hsourceMarginFloor : 0 < sourceMarginFloor)
    (hheadMarginFloor : 0 < headMarginFloor)
    (hphysicalEtaFloor : 0 < physicalEtaFloor)
    (hpostMarginFloor : 0 < postMarginFloor)
    (hhead : primesUpTo W ⊆ P)
    (logY Lambda0 mFrozen : Nat → Real)
    (Hledger :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n => bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) (K0 + 1) betaAct)
        (F.extendedGuardedSmoothBaseMass
          W (K0 + 1) betaAct deltaStar)
        (bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen
          (F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar))) :
    ∃ Cmass density : Real,
      0 < Cmass ∧
      0 < density ∧
      ∀ {delta eta : Real}
        (M : RegularRelativeMesh.Mesh delta eta),
        ∀ᶠ n : Nat in atTop,
          ∀ (hdelta : 0 < delta)
          (Bsource : BridgeData (PaperHeadSimplex.Tag P)
            (BankPaperCanonicalExponentBand M)),
          Bsource.sampleData.n = n →
          Bsource.sampleData.W = W →
          ∀ (hnTail : Ntail ≤ Bsource.sampleData.n),
            let R := F.realization Bsource.sampleData.n hnTail
            let certificate := F.certificate Bsource.sampleData.n hnTail
            ∀ (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
                (K0 := K0) M Bsource R certificate I deltaStar hdelta),
              J.exponent = E →
              J.betaProt = betaProt →
              J.betaAct = betaAct →
              (∀
                (hsep :
                  physicalBound (I.upper .minus)
                      J.postHeightBridge.sampleData.n <
                    physicalBound (I.lower .plus)
                      J.postHeightBridge.sampleData.n)
                (hremaining : ∀ cell : Cell (PaperHeadSimplex.Tag P),
                  (rawCell (PaperHeadSimplex.pattern P hprime E) I
                      J.postHeightBridge.sampleData.n cell \
                    (roughCanonicalBridgeRelevantLedgerFamily depth
                      J.postHeightBridge.sampleData.n).guards).Nonempty),
                J.postHeightBridge.sampleData =
                    canonicalSampleData
                      (W := J.postHeightBridge.sampleData.W)
                      (PaperHeadSimplex.pattern P hprime E) I
                      (roughCanonicalBridgeRelevantLedgerFamily depth
                        J.postHeightBridge.sampleData.n)
                      hsep hremaining →
                J.qTilde =
                    bankPaperCanonicalGuardedSmoothBaseMass
                      R certificate deltaStar
                        J.postHeightBridge.sampleData.W
                        (K0 + 1) J.betaAct →
                sourceMarginFloor ≤ J.Tsource.cellMassMargin →
                headMarginFloor ≤ J.targetInputs.headMargin →
                physicalEtaFloor ≤ J.targetInputs.physicalEta →
                postMarginFloor ≤ J.postHeightTarget.cellMassMargin →
                mFrozen Bsource.sampleData.n =
                    bankPaperCanonicalTopFrozenSmoothFrozenMass
                      (K := K0 + 1) J.postHeightBridge R certificate
                      deltaStar J.betaProt J.alpha →
                J.qn =
                    bankPaperCanonicalSmoothFinalActiveMassFamily
                      mu logY Lambda0 mFrozen
                        (F.extendedGuardedSmoothBaseMass
                          W (K0 + 1) betaAct deltaStar)
                        Bsource.sampleData.n →
                BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
                    (K := K0 + 1) J.postHeightBridge R certificate
                      (R.paperFixedExceptionalFactors deltaStar)
                      J.Tsource deltaStar J.betaProt J.alpha J.beta
                        J.qTilde →
                (centralAnchorDivisor J.postHeightBridge.sampleData.n
                        (centralAnchorCutoff depth
                          J.postHeightBridge.sampleData.n)
                        certificate.q * R.prechargeBaseStateProduct ∣
                    centralTailProduct J.postHeightBridge.sampleData.n
                      (upperTailLength c
                        J.postHeightBridge.sampleData.n)) ∧
                  R.selectorTailCharge
                        (R.paperFixedExceptionalFactors deltaStar) ∣
                    certificate.prechargedTailTarget →
                ∃ S :
                    BankPaperCanonicalSectionNinePostHeightSourceInputsAt
                      M Bsource R certificate I deltaStar hdelta J,
                  ∃ _Hgap :
                      BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt
                        M Bsource R certificate I E deltaStar mu
                          sourceMarginFloor headMarginFloor physicalEtaFloor
                          postMarginFloor logY Lambda0 mFrozen
                          (F.extendedGuardedSmoothBaseMass
                            W (K0 + 1) betaAct deltaStar)
                          hdelta J S,
                    S.Cmass = Cmass ∧ S.density = density) := by
  exact
    exists_eventually_bankPaperCanonicalSectionNinePostHeight_sourceInputsAndPrimitiveGapsAt_of_targetResidual
      P hprime E hE I hlowerOne hupperStrict depth W K0 Ntail F
        hc hbetaAct hmu hbetaProt hsourceMarginFloor hheadMarginFloor
        hphysicalEtaFloor hpostMarginFloor hhead logY Lambda0 mFrozen Hledger

/-! The exact records constructed by the finite theorem. -/

#check BankPaperCanonicalSectionNinePostHeightSourceInputsAt
#check BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt

/-! Existing mechanical producers used by the eventual wrapper. -/

#check eventually_bankPaperCanonicalTopFrozenRoundedSelectorSourceState_of_residualInputs
#check bankPaperCanonicalGuardedCellDensityFloor
#check bankPaperCanonicalGuardedCellDensityFloor_pos
#check bankPaperCanonicalGuardedCellDensityFloor_le
#check eventually_roughCanonicalBridgeRelevantLedgerFamily_agreement
#check structuredSample_value_not_fullGuard_of_agreement
#check GuardedCentralAnchorCertificate.baseExactificationBank_prod_dvd_prechargedTailTarget
#check GuardedCentralAnchorCertificate.prechargedTailTarget_mul_centralAnchorDivisor

end BankPaperRealization

#check bankPaperCanonicalSectionEight_d_isBigO
#check eventually_one_le_bankPaperCanonicalSectionEight_finalActiveMass
#check secondOrderScale_div_L_isLittleO_secondOrderScale
#check Erdos390.Full.GuardSquarefreeErrorRate.eventually_guarded_rawCell_density

end

end Erdos390.WholePaper
