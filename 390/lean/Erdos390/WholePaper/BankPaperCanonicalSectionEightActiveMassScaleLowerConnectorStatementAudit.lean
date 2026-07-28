import Erdos390.WholePaper.BankPaperCanonicalSectionEightActiveMassScaleLowerConnector

/-!
# Statement audit for the guarded Section 8 active-mass lower connector
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

example
    {c : Real} {N : Nat} (depth W K : Nat) (deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) :
    BankPaperCanonicalSmoothGuardDeletionCensus
      (F.extendedSmoothBaseGuardDeletionCard W K deltaStar) :=
  bankPaperCanonicalGuardedTailSmoothBaseDeletionCensus
    depth W K deltaStar F

example
    {c betaAct : Real} {N : Nat} (depth W K : Nat)
    (hc : 0 < c) (hbeta : 0 < betaAct) (deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar) :=
  bankPaperCanonicalExtendedGuardedSmoothBaseMass_paperScaleLower
    depth W K hc hbeta deltaStar F

example
    {c betaAct : Real} {N : Nat} (depth W K : Nat)
    (hc : 0 < c) (hbeta : 0 < betaAct) (deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (mFrozen : Nat -> Real) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (bankPaperCanonicalSmoothQ0Family mFrozen
        (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)) :=
  bankPaperCanonicalGuardedTailSmoothQ0Family_paperScaleLower
    depth W K hc hbeta deltaStar F mFrozen

#check bankPaperCanonicalGuardedTailSmoothBaseDeletionCensus
#check bankPaperCanonicalRawSmoothBase_sub_extendedGuardedSmoothBase_isLittleO
#check bankPaperCanonicalExtendedGuardedSmoothBaseMass_paperScaleLower
#check bankPaperCanonicalGuardedTailSmoothQ0Family_paperScaleLower

end

end Erdos390.WholePaper
