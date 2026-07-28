import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstCrossMeshScalarTransport
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstLedgerFamilies

/-!
# A common source-first scalar ledger chosen before the final mesh

The rich source geometry is necessarily constructed after a regular
relative mesh has been supplied.  The scalar Section 8 ledger, however,
must precede the final mesh in the global parameter order.

We resolve this order exactly.  A harmless reference mesh with parameters
`delta = 1 / 2` and `eta = 1` supplies one fixed-rich source and hence the
three total scalar families.  For every later mesh, the fixed-numerical
rich-source constructor supplies a second witness.  Cross-mesh scalar
transport then identifies its literal frozen mass, precharged logarithm,
and rounded logarithmic mass with the reference formulas on a common tail.

Thus the displayed existential quantifiers for `logY`, `Lambda0`, and
`mFrozen` occur strictly before the universally quantified final mesh.
There is no post-height bridge, final-mass estimate, P87 input, or terminal
conclusion in this module.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000 in
/-- Choose the exact Section 8 scalar ledger before the final regular mesh.

The fixed source coefficients, exponent, and source-cell margin are inputs
which have already been selected by the pre-mesh numerical theorem.  The
conclusion first returns the three total scalar families and their exact
analytic ledger.  Only afterwards does it quantify over a final mesh and
return a genuine fixed-rich source whose three literal local formulas are
synchronized with those same families. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCommonLedgerBeforeMesh
    {c deltaStar betaProt betaAct : Real}
    {depth N W K0 : Nat}
    (hc : C0 < c)
    (hdeltaStar : IsPaperCombinedChargeDeltaStar c deltaStar)
    (hW : 0 < W)
    (hbetaProt : 0 ≤ betaProt)
    (hbetaAct : 0 < betaAct)
    (hbetaUpper :
      betaProt + betaAct ≤ c / roughHeadDensity W)
    (hKlarge :
      1 / roughHeadDensity W ≤ (((K0 + 1 : Nat) : Real)))
    (hprefix : 2 * depth + 1 ≤ W)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (hterminal :
      ∀ n (hn : N ≤ n),
        let R := F.realization n hn
        let certificate := F.certificate n hn
        centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q * R.prechargeBaseStateProduct ∣
            centralTailProduct n (upperTailLength c n) ∧
          (baseBankFactors R.exactificationState).prod id ∣
            certificate.prechargedTailTarget ∧
          R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget ∧
          (∀ p ∈ primesUpTo (2 * depth + 1),
            (c - C0) / (24 * (((p - 1 : Nat) : Real))) *
                  secondOrderScale n +
                (R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar)).factorization p ≤
              certificate.prechargedTailTarget.factorization p) ∧
          certificate.selectorTailTarget R
                (R.paperFixedExceptionalFactors deltaStar) *
              R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) =
            certificate.prechargedTailTarget ∧
          certificate.prechargedTailTarget *
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q =
            centralTailProduct n (upperTailLength c n))
    (cSource cUpper : Real) (E : Nat) (sourceCellMargin : Real)
    (hcSource : 0 < cSource)
    (hcUpper : 0 < cUpper)
    (hE : 0 < E)
    (hsourceCellMarginEq :
      sourceCellMargin =
        bankPaperCanonicalSectionNinePostHeightHeadMargin E
            (fun _ : {p : Nat // p ∈ primesUpTo W} =>
              bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W)
            cUpper *
          bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.tau)
    (hElarge :
      2 *
            (∑ p : {p : Nat // p ∈ primesUpTo W},
              bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
                c p.1) ≤
          (E : Real) * (cSource / 4))
    (Hmass :
      ∀ᶠ n : Nat in atTop,
        cSource * secondOrderScale n ≤
            F.extendedGuardedSmoothBaseMass
              W (K0 + 1) betaAct deltaStar n ∧
          F.extendedGuardedSmoothBaseMass
              W (K0 + 1) betaAct deltaStar n ≤
            cUpper * secondOrderScale n) :
    ∃ logY Lambda0 mFrozen : Nat → Real,
      logY = F.extendedPrechargedTailLogTarget ∧
        BankPaperCanonicalSectionEightAnalyticLedger
          (fun n =>
            bankPaperCanonicalRawSmoothBaseMass W n
              (upperTailLength c n) (K0 + 1) betaAct)
          (F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar)
          (bankPaperCanonicalSmoothA0Family
            logY Lambda0 mFrozen
            (F.extendedGuardedSmoothBaseMass
              W (K0 + 1) betaAct deltaStar)) ∧
        ∀ {delta eta : Real}
            (M : RegularRelativeMesh.Mesh delta eta)
            (hdelta : 0 < delta),
          ∃ X :
              BankPaperCanonicalSectionNinePostHeightFixedRichSourceWitness
                M (c := c) (deltaStar := deltaStar)
                  (betaProt := betaProt) (betaAct := betaAct)
                  (sourceCellMargin := sourceCellMargin)
                  (depth := depth) (N := N) (W := W)
                  (K0 := K0) (E := E) hdelta F,
            ∀ᶠ n : Nat in atTop,
              ∀ hn : N ≤ n,
                let Y := X.source n hn
                let B := Y.1
                let R := Y.2.1.1
                let certificate := Y.2.1.2
                let T := Y.2.2
                let alpha :=
                  bankPaperCanonicalPostHfitBalancedAlpha
                    B c K0 betaProt betaAct
                let qTilde :=
                  F.extendedGuardedSmoothBaseMass
                    W (K0 + 1) betaAct deltaStar n
                mFrozen n =
                    bankPaperCanonicalTopFrozenSmoothFrozenMass
                      (K := K0 + 1) B R certificate
                        deltaStar betaProt alpha ∧
                  logY n =
                    bankPaperCanonicalSectionNinePostHeightLogY
                      B R certificate ∧
                  Lambda0 n =
                    bankPaperCanonicalSectionNinePostHeightRoundedLambda0
                      (K0 + 1) B R certificate T
                        deltaStar betaProt alpha
                          (betaProt + betaAct) qTilde := by
  have hdeltaStarUpper : deltaStar < 1 :=
    hdeltaStar.2.1.trans (by norm_num)
  have hcPos : 0 < c :=
    (show (0 : Real) < C0 by norm_num [C0]).trans hc
  have hrich :
      ∀ {delta eta : Real}
          (M : RegularRelativeMesh.Mesh delta eta)
          (hdelta : 0 < delta),
        Nonempty
          (BankPaperCanonicalSectionNinePostHeightFixedRichSourceWitness
            M (c := c) (deltaStar := deltaStar)
              (betaProt := betaProt) (betaAct := betaAct)
              (sourceCellMargin := sourceCellMargin)
              (depth := depth) (N := N) (W := W)
              (K0 := K0) (E := E) hdelta F) := by
    intro delta eta M hdelta
    obtain
        ⟨sourceGeom, source, hprojection,
          Hsource, Hready, Hcanonical⟩ :=
      exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstRichSourceWithFixedNumericalData
        hc hdeltaStar hW hbetaProt hbetaAct hbetaUpper hKlarge hprefix
          F hterminal cSource cUpper E sourceCellMargin
          hcSource hcUpper hE hsourceCellMarginEq hElarge Hmass M hdelta
    refine ⟨{
      sourceGeom := sourceGeom
      source := source
      projection := ?_
      source_event := Hsource
      ready_event := Hready
      canonical_event := Hcanonical
    }⟩
    intro n hn
    simpa only [
      bankPaperCanonicalSectionNinePostHeight_fixedRichThinOfRich] using
        hprojection n hn
  let Mref : RegularRelativeMesh.Mesh (1 / 2 : Real) 1 :=
    Classical.choice
      (RegularRelativeMesh.exists_mesh
        (by norm_num) (by norm_num) (by norm_num))
  have hdeltaRef : (0 : Real) < 1 / 2 := by
    norm_num
  let Xref :
      BankPaperCanonicalSectionNinePostHeightFixedRichSourceWitness
        Mref (c := c) (deltaStar := deltaStar)
          (betaProt := betaProt) (betaAct := betaAct)
          (sourceCellMargin := sourceCellMargin)
          (depth := depth) (N := N) (W := W)
          (K0 := K0) (E := E) hdeltaRef F :=
    Classical.choice (hrich Mref hdeltaRef)
  obtain ⟨logY, Lambda0, mFrozen, hlogY, Hledger, HsyncRef⟩ :=
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstLedgerFamilies
      (P := primesUpTo W)
      (Band := BankPaperCanonicalExponentBand Mref)
      hcPos hdeltaStar.1 hdeltaStarUpper F
        Xref.source Xref.source_event
  refine ⟨logY, Lambda0, mFrozen, hlogY, Hledger, ?_⟩
  intro delta eta M hdelta
  let X :
      BankPaperCanonicalSectionNinePostHeightFixedRichSourceWitness
        M (c := c) (deltaStar := deltaStar)
          (betaProt := betaProt) (betaAct := betaAct)
          (sourceCellMargin := sourceCellMargin)
          (depth := depth) (N := N) (W := W)
          (K0 := K0) (E := E) hdelta F :=
    Classical.choice (hrich M hdelta)
  have Hcross :=
    eventually_bankPaperCanonicalSectionNinePostHeight_fixedRichSource_crossMeshScalarTransport
      Mref M hdeltaRef hdelta F Xref X
  refine ⟨X, ?_⟩
  filter_upwards [HsyncRef, Hcross] with n hsyncRefN hcrossN
  intro hn
  have hsyncRef := hsyncRefN hn
  have hcross := hcrossN hn
  dsimp only at hsyncRef hcross ⊢
  exact
    ⟨hsyncRef.1.trans hcross.1,
      hsyncRef.2.1.trans hcross.2.1,
      hsyncRef.2.2.trans hcross.2.2⟩

end BankPaperRealization

end

end Erdos390.WholePaper
