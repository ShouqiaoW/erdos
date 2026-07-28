import Erdos390.WholePaper.BankPaperCanonicalTopFrozenRoundedSourceStateConnector
import Erdos390.WholePaper.BankPaperCanonicalRawBroadSurplusAsymptotic

/-!
# Charged nonsmooth rows for the frozen-top source

The frozen-top `qTilde` source now vanishes pointwise on every exceptional
nonsmooth row.  On an active nonexceptional row it is the literal guarded
constant-pool correction.  Consequently a one-coordinate lower bound for
each guarded broad correction pool is enough to manufacture the complete
charged-row realization.

The finite theorem below keeps that capacity hypothesis explicit.  The
eventual wrapper supplies it from the intrinsic raw broad-pool surplus and
the canonical three-coordinate guard census.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Finite charged-row producer -/

/-- The literal frozen-top `qTilde` source realizes every charged nonsmooth
row once each active nonexceptional complete label has a nonempty guarded
broad correction pool.

The active-row identity is the generic constant-pool correction sum.
Exceptional rows are pointwise zero by construction. -/
theorem
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_chargedNonsmoothRows_of_activeCapacity
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (hcapacity : ∀ label,
      IsCompleteRoughLabel (yNat B.sampleData.n) label ->
        RoughCanonicalActiveNonexceptionalLabel
            B.sampleData.n deltaStar label ->
          RoughCanonicalGuardedBroadPoolCapacity R certificate deltaStar
            B.sampleData.W K label 1) :
    BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K) R certificate deltaStar
        (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde)) := by
  constructor
  · intro label hlabelMem hactive
    have hcomplete : IsCompleteRoughLabel
        (yNat B.sampleData.n) label :=
      isCompleteRoughLabel_of_canonicalCompleteRoughRow
        (⟨label, hlabelMem⟩ :
          CanonicalCompleteRoughRow (yNat B.sampleData.n)
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K))
    have hpoolCapacity := hcapacity label hcomplete hactive
    have hpoolNonempty :
        (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
          B.sampleData.W K label).Nonempty := by
      apply Finset.card_pos.mp
      exact hpoolCapacity
    calc
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha betaTotal
              (bankPaperCanonicalScaledActiveSeed T qTilde) a) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
            deltaStar B.sampleData.W K label alpha betaTotal B.L a := by
          apply Finset.sum_congr rfl
          intro a ha
          exact
            bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_nonsmoothRow
              (K := K) B R certificate deltaStar betaProt alpha betaTotal
                (bankPaperCanonicalScaledActiveSeed T qTilde) hactive ha
      _ = R.roughCanonicalPostchargeRowTarget deltaStar label := by
        simpa only [roughCanonicalGuardedPostchargeRowCorrectedWeight] using
          (sum_bankPaperConstantPoolCorrection_eq_target
            (x := roughHeadCompatibleRawWeight B.sampleData.W
              B.sampleData.n (upperTailLength c B.sampleData.n) K
                alpha betaTotal B.L)
            (target := R.roughCanonicalPostchargeRowTarget deltaStar label)
            (R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
              certificate deltaStar B.sampleData.W K label)
            hpoolNonempty)
  · intro label _hlabelMem hlabel hexceptional
    apply Finset.sum_eq_zero
    intro a ha
    exact
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_exceptionalNonsmoothRow
        (K := K) B R certificate deltaStar betaProt alpha betaTotal
          (bankPaperCanonicalScaledActiveSeed T qTilde)
          hlabel hexceptional ha

/-! ## Eventual capacity supplier -/

/-- Eventually the intrinsic guarded broad-pool capacity supplies the
charged nonsmooth rows of every literal frozen-top `qTilde` source with the
displayed physical index and head cutoff. -/
theorem
    eventually_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_chargedNonsmoothRows
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (depth W K : Nat) {c deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        B.sampleData.W = W ->
        forall
          (R : BankPaperRealization B.sampleData.n
            (upperEndpoint B.sampleData.n
              (upperTailLength c B.sampleData.n)))
          (certificate : GuardedCentralAnchorCertificate c depth
            B.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
            (R.centralChangedMarkers depth))
          (T : BarycentricTarget B.sampleData)
          (betaProt alpha betaTotal qTilde : Real),
          BankPaperCanonicalChargedNonsmoothRowRealization
            (K := K) R certificate deltaStar
              (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
                (K := K) B R certificate deltaStar betaProt alpha betaTotal
                  (bankPaperCanonicalScaledActiveSeed T qTilde)) := by
  have Hcapacity :=
    BankPaperRealization.eventually_roughCanonical_active_intrinsic_guard_capacity_inputs
      W K 1 hc hdelta
  filter_upwards [Hcapacity,
      eventually_ge_atTop (centralAnchorCutoffThreshold depth),
      eventually_yNat_lt_centralAnchorCutoff depth]
      with n hcapacityN hnCutoff hyCutoff
  intro B hBn hBW R certificate T betaProt alpha betaTotal qTilde
  subst n
  refine
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_chargedNonsmoothRows_of_activeCapacity
      (K := K) B R certificate T deltaStar betaProt alpha betaTotal
        qTilde ?_
  intro label hcomplete hactive
  simpa only [hBW] using
    (hcapacityN depth R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth) R certificate hnCutoff hyCutoff
        label hcomplete hactive).2.1

end BankPaperRealization

end

end Erdos390.WholePaper
