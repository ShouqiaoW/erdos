import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceObligationPublicSyncConnector

/-!
# Expanded statement audit: public synchronization from the source obligation

This audit unfolds the complete eventual coherent bridge/source obligation
in the hypothesis.  In particular, the source bridge, guarded-tail
realization, post-height bridge inputs, rounded-source inputs, primitive
gaps, canonical sample identity, guarded smooth mass identity, and fixed
source constants are all still explicit assumptions.

The conclusion is also written out literally.  It exports only the three
public equalities already carried by that obligation: the ambient index,
the fixed prime width, and the Section 8 final-active-mass family.
-/

open Filter

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization

example
    (P : Finset Nat)
    (Patterns : PaperHeadSimplex.Tag P → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    {c : Real} (depth W K0 E Ntail : Nat)
    (F : BankPaperCanonicalGuardedTailFamily c depth Ntail)
    (deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
      physicalEtaFloor postMarginFloor Cmass density : Real)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (hdelta : 0 < delta)
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (Hsource :
      ∀ᶠ n : Nat in atTop,
        ∃ Bsource : BridgeData (PaperHeadSimplex.Tag P)
            (BankPaperCanonicalExponentBand M),
          ∃ hnTail : Ntail ≤ Bsource.sampleData.n,
            let R := F.realization Bsource.sampleData.n hnTail
            let certificate := F.certificate Bsource.sampleData.n hnTail
            ∃ J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
                (K0 := K0) M Bsource R certificate I deltaStar hdelta,
              ∃ S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
                  M Bsource R certificate I deltaStar hdelta J,
                ∃ _Hgap :
                    BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt
                      M Bsource R certificate I E deltaStar mu
                        sourceMarginFloor headMarginFloor physicalEtaFloor
                        postMarginFloor logY Lambda0 mFrozen qTilde
                        hdelta J S,
                  ∃ hsep :
                      physicalBound (I.upper .minus)
                          J.postHeightBridge.sampleData.n <
                        physicalBound (I.lower .plus)
                          J.postHeightBridge.sampleData.n,
                    ∃ hremaining :
                        ∀ cell : Cell (PaperHeadSimplex.Tag P),
                          (rawCell Patterns I
                              J.postHeightBridge.sampleData.n cell \
                            (G J.postHeightBridge.sampleData.n).guards).Nonempty,
                      B n = J.postHeightBridge ∧
                        Bsource.sampleData.n = n ∧
                        Bsource.sampleData.W = W ∧
                        J.betaProt = betaProt ∧
                        J.betaAct = betaAct ∧
                        J.postHeightBridge.sampleData =
                          canonicalSampleData
                            (W := J.postHeightBridge.sampleData.W)
                            Patterns I
                              (G J.postHeightBridge.sampleData.n)
                              hsep hremaining ∧
                        J.qTilde =
                          bankPaperCanonicalGuardedSmoothBaseMass
                            R certificate deltaStar
                              J.postHeightBridge.sampleData.W
                              (K0 + 1) J.betaAct ∧
                        S.Cmass = Cmass ∧
                        S.density = density) :
    ∀ᶠ n : Nat in atTop,
      (B n).sampleData.n = n ∧
        (B n).sampleData.W = W ∧
        (B n).q =
          bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde n := by
  exact
    eventually_bankPaperCanonicalSectionNinePostHeight_coherentBridgeSourceObligation_publicSync
      P Patterns I Cprom Cbank G depth W K0 E Ntail F
        deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
        physicalEtaFloor postMarginFloor Cmass density
        logY Lambda0 mFrozen qTilde M hdelta B Hsource

/-! ## Public declaration census -/

#check
  eventually_bankPaperCanonicalSectionNinePostHeight_coherentBridgeSourceObligation_publicSync

end BankPaperRealization

end

end Erdos390.WholePaper
