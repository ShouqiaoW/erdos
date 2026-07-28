import Erdos390.WholePaper.BankPaperCanonicalActualBridgeMassUpperConnector

/-!
# Statement audit for the actual bridge active-mass upper bound

The expanded checks expose the exact baseline compatibility premise, the
Section 8 ledger, and the fixed eventual constant consumed by Section 9.
-/

open Filter Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

/-! ## Complete public declaration census -/

#check BridgeData.q_eq_of_baseWeight_eq_scaledActiveSeed
#check bankPaperCanonical_actualBridge_q_isBigO_of_sectionEightLedger_scaledSeed
#check exists_bankPaperCanonical_actualBridge_q_upper_of_sectionEightLedger_scaledSeed

/-! ## Exact finite identification -/

example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band) (T : BarycentricTarget B.sampleData)
    (q : Real)
    (hseed : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m =
        bankPaperCanonicalScaledActiveSeed T q m) :
    B.q = q :=
  BridgeData.q_eq_of_baseWeight_eq_scaledActiveSeed B T q hseed

/-! ## Exact eventual interface -/

example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : Nat -> BridgeData Head Band)
    (W K : Nat) (c betaAct : Real)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde))
    (hseed : ∀ᶠ n : Nat in atTop,
      exists T : BarycentricTarget (B n).sampleData,
        forall m : (B n).sampleData.Sample,
          (B n).baseline.baseWeight m =
            bankPaperCanonicalScaledActiveSeed T
              (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n) m) :
    (fun n => (B n).q) =O[atTop] secondOrderScale :=
  bankPaperCanonical_actualBridge_q_isBigO_of_sectionEightLedger_scaledSeed
    B W K c betaAct logY Lambda0 mFrozen qTilde Hledger hseed

example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : Nat -> BridgeData Head Band)
    (W K : Nat) (c betaAct : Real)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde))
    (hseed : ∀ᶠ n : Nat in atTop,
      exists T : BarycentricTarget (B n).sampleData,
        forall m : (B n).sampleData.Sample,
          (B n).baseline.baseWeight m =
            bankPaperCanonicalScaledActiveSeed T
              (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n) m) :
    exists Cq : Real, 0 < Cq ∧
      ∀ᶠ n : Nat in atTop,
        (B n).q <= Cq * secondOrderScale n :=
  exists_bankPaperCanonical_actualBridge_q_upper_of_sectionEightLedger_scaledSeed
    B W K c betaAct logY Lambda0 mFrozen qTilde Hledger hseed

end

end Erdos390.WholePaper
