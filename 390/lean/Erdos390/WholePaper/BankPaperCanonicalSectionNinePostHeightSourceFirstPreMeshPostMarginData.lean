import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPostLedgerConnector

/-!
# Post-height numerical data chosen before the final mesh

Once the exact Section 8 ledger families have been fixed, all analytic
constants used to protect the post-height head and physical coordinates can
be chosen without mentioning a regular mesh.  This module isolates precisely
that choice.

The eventual conclusion retains the literal lower and upper bounds for the
final active mass and the fixed physical-mean margin.  A later mesh-dependent
constructor may therefore consume these facts without choosing `Cpost` or
`postMargin` after the mesh.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-- Choose the post-height upper coefficient and head margin after the common
Section 8 ledger, but before any final regular mesh.

The theorem contains no mesh, source bridge, or mesh-dependent callback in
its statement. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshPostMarginData
    {c deltaStar betaAct : Real}
    {depth N W K0 : Nat}
    (hc : C0 < c)
    (hW : 0 < W)
    (hbetaAct : 0 < betaAct)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (cSource : Real)
    (E : Nat)
    (hcSource : 0 < cSource)
    (hE : 0 < E)
    (hsourceLower :
      ∀ᶠ n : Nat in atTop,
        cSource * secondOrderScale n ≤
          F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar n)
    (logY Lambda0 mFrozen : Nat → Real)
    (Hledger :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n =>
          bankPaperCanonicalRawSmoothBaseMass W n
            (upperTailLength c n) (K0 + 1) betaAct)
        (F.extendedGuardedSmoothBaseMass
          W (K0 + 1) betaAct deltaStar)
        (bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen
          (F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar))) :
    ∃ Cpost postMargin : Real,
      0 < Cpost ∧
        postMargin =
          bankPaperCanonicalSectionNinePostHeightHeadMargin
            E
            (fun _ : {p : Nat // p ∈ primesUpTo W} =>
              bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W)
            Cpost ∧
        0 < postMargin ∧
        ∀ᶠ n : Nat in atTop,
          (cSource / 4) * secondOrderScale n ≤
              bankPaperCanonicalSmoothFinalActiveMassFamily
                bankPaperCanonicalSectionNinePostHeightPhysicalMu
                logY Lambda0 mFrozen
                (F.extendedGuardedSmoothBaseMass
                  W (K0 + 1) betaAct deltaStar) n ∧
            ‖bankPaperCanonicalSmoothFinalActiveMassFamily
                bankPaperCanonicalSectionNinePostHeightPhysicalMu
                logY Lambda0 mFrozen
                (F.extendedGuardedSmoothBaseMass
                  W (K0 + 1) betaAct deltaStar) n‖ ≤
              Cpost * ‖secondOrderScale n‖ ∧
            Real.log
                  (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
                    .minus) ≤
                bankPaperCanonicalSmoothFinalActiveHeightFamily
                      bankPaperCanonicalSectionNinePostHeightPhysicalMu
                      logY Lambda0 mFrozen
                      (F.extendedGuardedSmoothBaseMass
                        W (K0 + 1) betaAct deltaStar) n /
                    bankPaperCanonicalSmoothFinalActiveMassFamily
                      bankPaperCanonicalSectionNinePostHeightPhysicalMu
                      logY Lambda0 mFrozen
                      (F.extendedGuardedSmoothBaseMass
                        W (K0 + 1) betaAct deltaStar) n -
                  bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ∧
              bankPaperCanonicalSmoothFinalActiveHeightFamily
                      bankPaperCanonicalSectionNinePostHeightPhysicalMu
                      logY Lambda0 mFrozen
                      (F.extendedGuardedSmoothBaseMass
                        W (K0 + 1) betaAct deltaStar) n /
                    bankPaperCanonicalSmoothFinalActiveMassFamily
                      bankPaperCanonicalSectionNinePostHeightPhysicalMu
                      logY Lambda0 mFrozen
                      (F.extendedGuardedSmoothBaseMass
                        W (K0 + 1) betaAct deltaStar) n +
                  bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ≤
                Real.log
                  (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
                    .plus) := by
  let qTilde : Nat → Real :=
    F.extendedGuardedSmoothBaseMass
      W (K0 + 1) betaAct deltaStar
  let a : {p : Nat // p ∈ primesUpTo W} → Real :=
    fun _ =>
      bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W
  have hC0Pos : (0 : Real) < C0 := by
    norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
  have ha : ∀ p, 0 < a p := by
    intro p
    simpa only [a] using
      bankPaperCanonicalSectionNinePostHeightHeadLinearFloor_pos hc hW
  have Hledger' :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n =>
          bankPaperCanonicalRawSmoothBaseMass W n
            (upperTailLength c n) (K0 + 1) betaAct)
        qTilde
        (bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen qTilde) := by
    simpa only [qTilde] using Hledger
  have hsourceLower' :
      ∀ᶠ n : Nat in atTop,
        cSource * secondOrderScale n ≤ qTilde n := by
    simpa only [qTilde] using hsourceLower
  have hfinalLower :=
    eventually_bankPaperCanonicalSectionNinePostHeight_finalActiveMass_ge_quarter_sourceCoefficient
      (c := c) (betaAct := betaAct)
      (mu := bankPaperCanonicalSectionNinePostHeightPhysicalMu)
      W (K0 + 1)
      bankPaperCanonicalSectionNinePostHeightPhysicalMu_pos
      hcSource qTilde hsourceLower' logY Lambda0 mFrozen Hledger'
  have hfinalUpperBigO :=
    bankPaperCanonicalSectionNinePostHeight_finalActiveMass_isBigO
      W (K0 + 1) c betaAct
      bankPaperCanonicalSectionNinePostHeightPhysicalMu_pos
      logY Lambda0 mFrozen qTilde Hledger'
  obtain ⟨Cpost, hCpost, hfinalUpper⟩ :=
    hfinalUpperBigO.exists_pos
  let postMargin : Real :=
    bankPaperCanonicalSectionNinePostHeightHeadMargin E a Cpost
  have hpostMarginPos : 0 < postMargin := by
    simpa only [postMargin] using
      bankPaperCanonicalSectionNinePostHeightHeadMargin_pos
        E a Cpost hE ha hCpost
  have hphysical :=
    eventually_bankPaperCanonicalSectionNinePostHeight_smoothPhysicalMean_has_fixed_margin_of_analyticLedger
      W (K0 + 1) hcPos hbetaAct
      logY Lambda0 mFrozen qTilde Hledger'
  refine ⟨Cpost, postMargin, hCpost, rfl, hpostMarginPos, ?_⟩
  filter_upwards [
    hfinalLower,
    hfinalUpper.bound,
    hphysical] with n hfinalLowerN hfinalUpperN hphysicalN
  simpa only [qTilde] using
    And.intro hfinalLowerN (And.intro hfinalUpperN hphysicalN)

end BankPaperRealization

end

end Erdos390.WholePaper
