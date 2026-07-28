import Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightAsymptotic
import Erdos390.WholePaper.BankPaperCanonicalActualActiveMeasureConstruction

/-!
# Actual bridge active-mass upper bound

The Proposition 8.7 and actual-moment modules use `BridgeData.q` as an
input scale; they do not themselves estimate it.  For the literal Section 8
bridge, however, the baseline is the canonical scaled seed of mass `q0`.
This identifies the bridge mass exactly with `q0`.

The Section 8 analytic ledger already proves that the post-guard mass is
`O(secondOrderScale)`, and nearest-integer initialization preserves that
bound.  This connector records the resulting upper bound on the actual
bridge mass.  Its only compatibility premise is the baseline/seed equality
already required by the actual Proposition 8.7 endpoint construction.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale

noncomputable section

/-! ## Exact bridge-mass identification -/

/-- If the bridge baseline is the canonical scaled seed of mass `q`, then
the actual bridge mass is exactly `q`. -/
theorem BridgeData.q_eq_of_baseWeight_eq_scaledActiveSeed
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band) (T : BarycentricTarget B.sampleData)
    (q : Real)
    (hseed : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m =
        bankPaperCanonicalScaledActiveSeed T q m) :
    B.q = q := by
  calc
    B.q =
        bankPaperCanonicalLiteralActiveMass B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q) :=
      Erdos390.WholePaper.BridgeData.q_eq_literalActiveMass_of_baseWeight_eq_seed
        B (bankPaperCanonicalScaledActiveSeed T q) hseed
    _ = q :=
      bankPaperCanonicalLiteralActiveMass_scaledActiveSeed T q

/-! ## Section 8 asymptotic transport -/

/-- The actual bridge-mass family is `O(secondOrderScale)` once its baseline
is the initialized Section 8 scaled seed. -/
theorem
    bankPaperCanonical_actualBridge_q_isBigO_of_sectionEightLedger_scaledSeed
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
    (fun n => (B n).q) =O[atTop] secondOrderScale := by
  let rawBase : Nat -> Real := fun n =>
    bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct
  have Hraw : rawBase =O[atTop] secondOrderScale := by
    simpa only [rawBase] using
      bankPaperCanonicalRawSmoothBaseMass_isBigO W K c betaAct
  have HqTilde : qTilde =O[atTop] secondOrderScale :=
    bankPaperCanonicalPostGuardSmoothMass_isBigO
      rawBase qTilde Hraw (by simpa only [rawBase] using Hledger.1)
  have Hq0 :
      bankPaperCanonicalSmoothQ0Family mFrozen qTilde =O[atTop]
        secondOrderScale :=
    bankPaperCanonicalSmoothQ0Family_isBigO
      mFrozen qTilde HqTilde
  apply Hq0.congr' ?_ EventuallyEq.rfl
  filter_upwards [hseed] with n hseedN
  rcases hseedN with ⟨Tn, hseedN⟩
  exact (
    BridgeData.q_eq_of_baseWeight_eq_scaledActiveSeed
      (B n) Tn
        (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)
        hseedN).symm

/-- Pointwise form used by the Section 9 budget closure: one fixed positive
constant dominates the actual bridge mass on the paper scale eventually. -/
theorem
    exists_bankPaperCanonical_actualBridge_q_upper_of_sectionEightLedger_scaledSeed
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
        (B n).q <= Cq * secondOrderScale n := by
  have Hq :=
    bankPaperCanonical_actualBridge_q_isBigO_of_sectionEightLedger_scaledSeed
      B W K c betaAct logY Lambda0 mFrozen qTilde Hledger hseed
  rcases (isBigO_iff').mp Hq with ⟨Cq, hCq, hbound⟩
  refine ⟨Cq, hCq, ?_⟩
  filter_upwards [hbound, eventually_secondOrderScale_pos] with
    n hboundN hscaleN
  have habs :
      |(B n).q| <= Cq * secondOrderScale n := by
    simpa only [Real.norm_eq_abs, abs_of_pos hscaleN] using hboundN
  exact (le_abs_self ((B n).q)).trans habs

end

end Erdos390.WholePaper
