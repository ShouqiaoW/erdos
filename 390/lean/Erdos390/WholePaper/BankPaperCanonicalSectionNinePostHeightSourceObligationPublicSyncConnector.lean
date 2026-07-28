import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightEventualSupplierConnector

/-!
# Public synchronization from the post-height source obligation

This connector projects the three public family equalities carried by the
eventual coherent bridge/source obligation.  It introduces no new
construction or analytic assumption: the public bridge has the ambient
index and fixed width, and its mass is the Section 8 final-active-mass
family.
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

/-- The bridge family exported by the coherent source obligation is
eventually synchronized with the ambient index, the fixed prime width, and
the final active-mass family. -/
theorem
    eventually_bankPaperCanonicalSectionNinePostHeight_coherentBridgeSourceObligation_publicSync
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
      BankPaperCanonicalSectionNinePostHeightEventualCoherentBridgeSourceObligation
        P Patterns I Cprom Cbank G (c := c) depth W K0 E Ntail F
        deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
        physicalEtaFloor postMarginFloor Cmass density
        logY Lambda0 mFrozen qTilde M hdelta B) :
    ∀ᶠ n : Nat in atTop,
      (B n).sampleData.n = n ∧
        (B n).sampleData.W = W ∧
        (B n).q =
          bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde n := by
  simp only
    [BankPaperCanonicalSectionNinePostHeightEventualCoherentBridgeSourceObligation]
    at Hsource
  filter_upwards [Hsource] with n hsourceN
  rcases hsourceN with
    ⟨Bsource, _hnTail, J, _S, Hgap, _hsep, _hremaining,
      hbridge, hBn, hBW, _hbetaProtSync, _hbetaActSync,
      _hcanonical, _hqTilde, _hCmassSync, _hdensitySync⟩
  refine ⟨?_, ?_, ?_⟩
  · calc
      (B n).sampleData.n = J.postHeightBridge.sampleData.n := by
        rw [hbridge]
      _ = Bsource.sampleData.n := by
        rw [J.postHeightBridge_sampleData]
      _ = n := hBn
  · calc
      (B n).sampleData.W = J.postHeightBridge.sampleData.W := by
        rw [hbridge]
      _ = Bsource.sampleData.W := by
        rw [J.postHeightBridge_sampleData]
      _ = W := hBW
  · calc
      (B n).q = J.postHeightBridge.q := by
        rw [hbridge]
      _ = J.qn := J.postHeightBridge_q
      _ =
          bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n :=
        Hgap.finalActiveMass_family
      _ =
          bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde n := by
        rw [hBn]

end BankPaperRealization

end

end Erdos390.WholePaper
