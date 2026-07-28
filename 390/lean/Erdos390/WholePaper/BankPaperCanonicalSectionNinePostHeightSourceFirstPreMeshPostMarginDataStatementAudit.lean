import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshPostMarginData

/-!
# Expanded statement audit: pre-mesh post-height numerical data
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

example
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
                    .plus) :=
  exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshPostMarginData
    hc hW hbetaAct F cSource E hcSource hE hsourceLower
      logY Lambda0 mFrozen Hledger

#check
  exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshPostMarginData

end BankPaperRealization

end

end Erdos390.WholePaper
