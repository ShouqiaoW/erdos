import Erdos390.WholePaper.BankPaperCanonicalSectionEightPrechargedLogConnector

/-!
# Statement audit for the Section 8 precharged-log connector
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

example
    {c : Real} {depth N n : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (hn : N <= n) :
    F.extendedPrechargedTailLogTarget n =
        Real.log ((F.certificate n hn).prechargedTailTarget : Real) ∧
      F.extendedCentralAnchorDivisorLog n =
        Real.log
          (centralAnchorDivisor n (centralAnchorCutoff depth n)
            (F.certificate n hn).q : Real) ∧
      F.extendedPrechargedTailLogTarget n +
          F.extendedCentralAnchorDivisorLog n =
        bankPaperCanonicalCentralTailLogTarget c n :=
  ⟨F.extendedPrechargedTailLogTarget_eq hn,
    F.extendedCentralAnchorDivisorLog_eq hn,
    F.extendedPrechargedTailLogTarget_add_anchorLog_of_tail hn⟩

example
    {c : Real} {depth N : Nat} (hc : 0 < c)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) :
    F.extendedCentralAnchorDivisorLog =O[atTop] secondOrderScale ∧
      (fun n => F.extendedPrechargedTailLogTarget n -
        bankPaperCanonicalUpperTailHeight c n * Scale.L n) =O[atTop]
          secondOrderScale :=
  ⟨F.extendedCentralAnchorDivisorLog_isBigO_secondOrderScale hc,
    F.extendedPrechargedTailLogTarget_sub_height_mul_L_isBigO hc⟩

example
    {c : Real} {depth N : Nat} (hc : 0 < c)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (rawBase qTilde Lambda0 mFrozen : Nat -> Real)
    (Hcentral : BankPaperCanonicalSectionEightAnalyticLedger
      rawBase qTilde
      (bankPaperCanonicalSmoothA0Family
        (bankPaperCanonicalCentralTailLogTarget c)
        Lambda0 mFrozen qTilde)) :
    BankPaperCanonicalSectionEightAnalyticLedger
      rawBase qTilde
      (bankPaperCanonicalSmoothA0Family
        F.extendedPrechargedTailLogTarget
        Lambda0 mFrozen qTilde) :=
  bankPaperCanonicalSectionEightAnalyticLedger_precharged_of_centralTail
    hc F rawBase qTilde Lambda0 mFrozen Hcentral

#check BankPaperCanonicalGuardedTailFamily.extendedPrechargedTailLogTarget
#check BankPaperCanonicalGuardedTailFamily.extendedCentralAnchorDivisorLog
#check BankPaperCanonicalGuardedTailFamily.extendedPrechargedTailLogTarget_add_anchorLog_of_tail
#check BankPaperCanonicalGuardedTailFamily.extendedPrechargedTailLogTarget_add_extendedCentralAnchorDivisorLog
#check GuardedCentralAnchorCertificate.centralAnchorDivisor_factorization_le_upperTailValuation
#check GuardedCentralAnchorCertificate.centralAnchorDivisorLog_eq_sum_primesUpTo
#check eventually_upperTailValuation_le_add_one_mul_secondOrderScale_on_primesUpTo
#check BankPaperCanonicalGuardedTailFamily.extendedCentralAnchorDivisorLog_isBigO_secondOrderScale
#check BankPaperCanonicalGuardedTailFamily.extendedPrechargedTailLogTarget_sub_height_mul_L_isBigO
#check bankPaperCanonicalSectionEightAnalyticLedger_precharged_of_centralTail

end

end Erdos390.WholePaper
