import Erdos390.WholePaper.BankPaperCanonicalSectionNineActiveLedgerConnector

/-!
# Statement audit for the Section 9 active-ledger density connector

The checks expose the positive finite density floor, the finite
mass/cardinality calculation, and the eventual constant with the exact
`Cactive / B.L` conclusion consumed by the weak local input.
-/

open Filter Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

#check bankPaperCanonicalGuardedCellDensityFloor
#check bankPaperCanonicalGuardedCellDensityFloor_pos
#check bankPaperCanonicalGuardedCellDensityFloor_le
#check bankPaperCanonical_activeLedger_of_scaledSeed_cellDensity
#check exists_eventually_bankPaperCanonical_activeLedger_of_q0_isBigO

/-- Expanded finite audit: no coordinate ceiling is assumed. -/
example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (T : BarycentricTarget B.sampleData)
    (q Cq density : Real)
    (hCq : 0 ≤ Cq) (hdensity : 0 < density)
    (hq : |q| ≤ Cq * secondOrderScale B.sampleData.n)
    (hcard : ∀ cell : Cell Head,
      density * (B.sampleData.n : Real) ≤
        (Fintype.card (B.sampleData.SampleAt cell) : Real))
    (hseed : ∀ m : B.sampleData.Sample,
      B.baseline.baseWeight m =
        bankPaperCanonicalScaledActiveSeed T q m) :
    ∀ m : B.sampleData.Sample,
      B.baseline.baseWeight m ≤ (Cq / density) / B.L :=
  bankPaperCanonical_activeLedger_of_scaledSeed_cellDensity
    B T q Cq density hCq hdensity hq hcard hseed

/-- Expanded eventual audit: the constant is outside `n`, `B`, and `T`,
while the canonical-data proof terms remain inside the selected index. -/
example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (Phead : Head → HeadPattern.Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (ledger : ∀ n, Ledger n Cprom Cbank)
    (q0 : Nat → Real)
    (Hq0 : q0 =O[atTop] secondOrderScale) :
    ∃ Cactive : Real, 0 ≤ Cactive ∧
      ∀ᶠ n : Nat in atTop,
        ∀ (B : BridgeData Head Band),
          B.sampleData.n = n →
          ∀
            (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ cell : Cell Head,
              (rawCell Phead I B.sampleData.n cell \
                (ledger B.sampleData.n).guards).Nonempty),
            B.sampleData =
                canonicalSampleData (W := B.sampleData.W)
                  Phead I (ledger B.sampleData.n) hsep hremaining →
            ∀ (T : BarycentricTarget B.sampleData),
              (∀ m : B.sampleData.Sample,
                B.baseline.baseWeight m =
                  bankPaperCanonicalScaledActiveSeed T (q0 n) m) →
              ∀ m : B.sampleData.Sample,
                B.baseline.baseWeight m ≤ Cactive / B.L :=
  exists_eventually_bankPaperCanonical_activeLedger_of_q0_isBigO
    Phead I Cprom Cbank ledger q0 Hq0

end BankPaperRealization

end

end Erdos390.WholePaper
