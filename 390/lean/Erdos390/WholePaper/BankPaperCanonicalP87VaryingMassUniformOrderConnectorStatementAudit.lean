import Erdos390.WholePaper.BankPaperCanonicalP87VaryingMassUniformOrderConnector

/-!
# Statement audit for uniform-order varying-mass Proposition 8.7

The first example unfolds the production proposition literally.  The second
assigns the production theorem directly to the same expanded statement, so
the audited order is visible without relying on the proposition's name:
`meshTol` and `W0` precede both the final width and `qMass`.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperPermittedRegularMesh
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

#check BankPaperCanonicalP87VaryingMassUniformOrderStatement
#check
  bankPaperCanonicalP87VaryingActiveMassLiteralBandBalance_uniformOrder

/-! ## Literal definition expansion -/

universe uHead uFixed

example
    (cMesh : Real)
    (I : PhysicalIntervals) (U : Real)
    (Cprom Cbank : Nat) (ledger : ∀ n, Ledger n Cprom Cbank) :
    BankPaperCanonicalP87VaryingMassUniformOrderStatement.{uHead, uFixed}
        cMesh I U Cprom Cbank ledger ↔
      (0 < cMesh →
        1 ≤ U →
        (∀ sigma, 1 ≤ I.lower sigma) →
        (∀ sigma, I.upper sigma ≤ U) →
        ∃ meshTol : Real, 0 < meshTol ∧
        ∃ W0 : Nat, ∀ W : Nat, W0 ≤ W →
          ∀ (qMass : Nat → Real),
            (∀ᶠ n : Nat in atTop, 1 ≤ qMass n) →
          ∀ {Head : Type uHead}
            [Fintype Head] [DecidableEq Head] [Nonempty Head]
            (Phead : Head → HeadPattern.Pattern),
          (∀ h : Head, ∀ p : Nat,
            p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
          ∀ (Ctarget Cinitial Cmass Cfixed Cactive
              marginFloor : Real),
            0 ≤ Ctarget → 0 ≤ Cinitial → 0 ≤ Cmass →
            0 ≤ Cfixed → 0 ≤ Cactive → 0 < marginFloor →
          ∃ radius : NNReal, 0 < (radius : Real) ∧
          ∃ Cpost : Real, 0 ≤ Cpost ∧
          ∀ {delta eta : Real}
            (M : RegularRelativeMesh.Mesh delta eta)
            (hdelta : 0 < delta)
            (_hPermitted : IsPermitted (cMesh := cMesh) M),
            delta + eta ≤ meshTol →
            ∀ᶠ n : Nat in atTop,
              ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
                B.sampleData.n = n →
                B.sampleData.W = W →
                ∀
                  (hsep :
                    physicalBound (I.upper .minus) B.sampleData.n <
                      physicalBound (I.lower .plus) B.sampleData.n)
                  (hremaining : ∀ c : Cell Head,
                    (rawCell Phead I B.sampleData.n c \
                      (ledger B.sampleData.n).guards).Nonempty),
                  (hcanonical :
                    B.sampleData =
                      canonicalSampleData
                        (W := B.sampleData.W) Phead I
                          (ledger B.sampleData.n) hsep hremaining) →
                  (hpartition :
                    ∃ (hWne : B.sampleData.W ≠ 0)
                      (S : ScaleSeparation
                        M B.sampleData.n B.sampleData.W),
                      B.partition =
                        RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                          M hdelta B.n_gt_one hWne S) →
                  (hscale : B.w = delta + eta) →
                  ∀ (T : BarycentricTarget B.sampleData)
                    (hq : 0 < qMass B.sampleData.n),
                    marginFloor ≤ T.cellMassMargin →
                    B.baseline =
                      T.activeMassBaseline
                        (qMass B.sampleData.n) hq →
                  ∀ (Delta : Fin (M.cellCount + 1) → Real),
                    B.HasTargetEnvelopes Ctarget Delta →
                  ∀ (markedTarget : Nat → Real) (N : Real),
                    0 ≤ N →
                    B.q ≤ Cmass * N →
                    (∀ p ∈
                        primeBand B.sampleData.n B.sampleData.W,
                      abs (markedTarget p -
                        B.paperMoment
                          (B.markedValuation p) 0) ≤
                        Cinitial * N / ((p : Real) * B.L)) →
                    (∀ j,
                      Delta j =
                        B.markedBandResidual markedTarget 0 j) →
                  ∀ {Fixed : Type uFixed} [Fintype Fixed]
                    (fixedValue : Fixed → Nat)
                    (fixedWeight : Fixed → Real)
                    (quota : Int),
                    (quota : Real) =
                      (∑ f, fixedWeight f) + B.q →
                    B.sampleData.HeadPatternsSeparated →
                    (∀ x,
                      BridgeData.frozenAmbientWeight
                          fixedValue fixedWeight x ∈
                        Set.Icc (0 : Real) 1) →
                    (∀ m : B.sampleData.Sample,
                      BridgeData.frozenAmbientWeight
                          fixedValue fixedWeight
                          (B.sampleData.value m) ≤
                        Cfixed / B.L) →
                    (∀ m : B.sampleData.Sample,
                      B.baseline.baseWeight m ≤
                        Cactive / B.L) →
                    B.HasPaperProposition87Conclusion
                      Delta radius markedTarget N Cpost
                        fixedValue fixedWeight quota) := by
  rfl

/-! ## Expanded theorem assignment -/

example
    (cMesh : Real)
    (I : PhysicalIntervals) (U : Real)
    (Cprom Cbank : Nat) (ledger : ∀ n, Ledger n Cprom Cbank) :
    0 < cMesh →
    1 ≤ U →
    (∀ sigma, 1 ≤ I.lower sigma) →
    (∀ sigma, I.upper sigma ≤ U) →
    ∃ meshTol : Real, 0 < meshTol ∧
    ∃ W0 : Nat, ∀ W : Nat, W0 ≤ W →
      ∀ (qMass : Nat → Real),
        (∀ᶠ n : Nat in atTop, 1 ≤ qMass n) →
      ∀ {Head : Type uHead}
        [Fintype Head] [DecidableEq Head] [Nonempty Head]
        (Phead : Head → HeadPattern.Pattern),
      (∀ h : Head, ∀ p : Nat,
        p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
      ∀ (Ctarget Cinitial Cmass Cfixed Cactive
          marginFloor : Real),
        0 ≤ Ctarget → 0 ≤ Cinitial → 0 ≤ Cmass →
        0 ≤ Cfixed → 0 ≤ Cactive → 0 < marginFloor →
      ∃ radius : NNReal, 0 < (radius : Real) ∧
      ∃ Cpost : Real, 0 ≤ Cpost ∧
      ∀ {delta eta : Real}
        (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta)
        (_hPermitted : IsPermitted (cMesh := cMesh) M),
        delta + eta ≤ meshTol →
        ∀ᶠ n : Nat in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n →
            B.sampleData.W = W →
            ∀
              (hsep :
                physicalBound (I.upper .minus) B.sampleData.n <
                  physicalBound (I.lower .plus) B.sampleData.n)
              (hremaining : ∀ c : Cell Head,
                (rawCell Phead I B.sampleData.n c \
                  (ledger B.sampleData.n).guards).Nonempty),
              (hcanonical :
                B.sampleData =
                  canonicalSampleData
                    (W := B.sampleData.W) Phead I
                      (ledger B.sampleData.n) hsep hremaining) →
              (hpartition :
                ∃ (hWne : B.sampleData.W ≠ 0)
                  (S : ScaleSeparation
                    M B.sampleData.n B.sampleData.W),
                  B.partition =
                    RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                      M hdelta B.n_gt_one hWne S) →
              (hscale : B.w = delta + eta) →
              ∀ (T : BarycentricTarget B.sampleData)
                (hq : 0 < qMass B.sampleData.n),
                marginFloor ≤ T.cellMassMargin →
                B.baseline =
                  T.activeMassBaseline
                    (qMass B.sampleData.n) hq →
              ∀ (Delta : Fin (M.cellCount + 1) → Real),
                B.HasTargetEnvelopes Ctarget Delta →
              ∀ (markedTarget : Nat → Real) (N : Real),
                0 ≤ N →
                B.q ≤ Cmass * N →
                (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
                  abs (markedTarget p -
                    B.paperMoment (B.markedValuation p) 0) ≤
                      Cinitial * N / ((p : Real) * B.L)) →
                (∀ j,
                  Delta j =
                    B.markedBandResidual markedTarget 0 j) →
              ∀ {Fixed : Type uFixed} [Fintype Fixed]
                (fixedValue : Fixed → Nat)
                (fixedWeight : Fixed → Real)
                (quota : Int),
                (quota : Real) =
                  (∑ f, fixedWeight f) + B.q →
                B.sampleData.HeadPatternsSeparated →
                (∀ x,
                  BridgeData.frozenAmbientWeight
                      fixedValue fixedWeight x ∈
                    Set.Icc (0 : Real) 1) →
                (∀ m : B.sampleData.Sample,
                  BridgeData.frozenAmbientWeight
                      fixedValue fixedWeight
                      (B.sampleData.value m) ≤
                    Cfixed / B.L) →
                (∀ m : B.sampleData.Sample,
                  B.baseline.baseWeight m ≤ Cactive / B.L) →
                B.HasPaperProposition87Conclusion
                  Delta radius markedTarget N Cpost
                    fixedValue fixedWeight quota := by
  exact
    bankPaperCanonicalP87VaryingActiveMassLiteralBandBalance_uniformOrder.{uHead, uFixed}
      cMesh I U Cprom Cbank ledger

end

end Erdos390.WholePaper
