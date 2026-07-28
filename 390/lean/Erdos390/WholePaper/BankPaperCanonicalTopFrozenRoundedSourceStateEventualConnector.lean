import Erdos390.WholePaper.BankPaperCanonicalArbitrarySourcePostHfitConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionEightTwoZeroOneShotConnector

/-!
# Eventual construction of the frozen-top rounded source state

The finite nearest-integer connector reduces the frozen-top source state to
three kinds of input:

* canonical sample geometry and the capacities of the two zero-head cells;
* feasibility of the literal `qTilde` source and its charged nonsmooth rows;
* exact selector-tail agreement outside the medium-prime band.

The first group is already asymptotic.  Canonical sample geometry is
provided by
`bankPaperCanonicalSectionEight_twoZeroHeadCell_geometryInputs`.  The
generic two-cell scalar-capacity theorem also supplies the initialization
capacity once it is applied to the uniformly bounded change
`(q0 - qTilde) / 2`.

This file packages that reuse.  The remaining residual input records only
the three facts for which the repository has no source-specific producer:
literal `qTilde` feasibility, charged nonsmooth rows, and literal `qTilde`
selector-tail support.  The zero-head correction is proved below to preserve
that support.  The equality identifying the analytic family `mFrozen` with
the concrete frozen-top row mass is also kept explicit at the eventual
synchronization boundary.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## The initial-only cell change and its capacity -/

/-- The nearest-integer change placed in one zero-head cell, as an
asymptotic family. -/
def bankPaperCanonicalSymmetricInitialCellMassFamily
    (mFrozen qTilde : Nat -> Real) (n : Nat) : Real :=
  bankPaperCanonicalSymmetricInitialAndHeightCellMass
    (mFrozen n) (qTilde n) 0

/-- The nearest-integer change in one zero-head cell is little-o of the
paper active-mass scale. -/
theorem bankPaperCanonicalSymmetricInitialCellMassFamily_isLittleO
    (mFrozen qTilde : Nat -> Real) :
    bankPaperCanonicalSymmetricInitialCellMassFamily mFrozen qTilde
        =o[atTop]
      secondOrderScale := by
  have hround :=
    bankPaperCanonicalSmoothQ0Family_sub_qTilde_isLittleO
      mFrozen qTilde
  have hhalf := hround.const_mul_left ((1 : Real) / 2)
  exact hhalf.congr_left fun n => by
    unfold bankPaperCanonicalSymmetricInitialCellMassFamily
    unfold bankPaperCanonicalSymmetricInitialAndHeightCellMass
    unfold bankPaperCanonicalSmoothActiveMassAt
    unfold bankPaperCanonicalSmoothQ0Family
    ring

/-- The Section 8 analytic ledger supplies pointwise capacity for the
nearest-integer initialization itself.  Existing exported corollaries cover
height-only and combined initial-plus-height changes; this is the missing
`d = 0` specialization needed by the frozen-top source state. -/
theorem
    eventually_bankPaperCanonicalSymmetricInitial_twoZeroHeadCell_rebalance_capacity
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    (W K : Nat) {c betaAct marginFloor : Real}
    (hc : 0 < c) (hbeta : 0 < betaAct)
    (hmarginFloor : 0 < marginFloor)
    (mFrozen qTilde A0 : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde A0)
    (betaProt : Real) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        forall
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell :
              Cell (PaperHeadSimplex.Tag P),
            (rawCell Phead I B.sampleData.n cell \
              (ledger B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Phead I (ledger B.sampleData.n) hsep hremaining ->
          forall (T : BarycentricTarget B.sampleData),
            marginFloor <= T.cellMassMargin ->
            forall (sigma : PhysicalSign)
              (m : B.sampleData.Sample),
              B.sampleData.cellOf m = (none, sigma) ->
              0 <=
                  bankPaperCanonicalTwoZeroHeadCellRebalance
                    B.sampleData
                    (bankPaperCanonicalScaledActiveSeed T (qTilde n))
                    (bankPaperCanonicalSymmetricInitialCellMassFamily
                      mFrozen qTilde n)
                    (bankPaperCanonicalSymmetricInitialCellMassFamily
                      mFrozen qTilde n) m ∧
              betaProt / B.L +
                  bankPaperCanonicalTwoZeroHeadCellRebalance
                    B.sampleData
                    (bankPaperCanonicalScaledActiveSeed T (qTilde n))
                    (bankPaperCanonicalSymmetricInitialCellMassFamily
                      mFrozen qTilde n)
                    (bankPaperCanonicalSymmetricInitialCellMassFamily
                      mFrozen qTilde n) m <= 1 := by
  let rawBase : Nat -> Real := fun n =>
    bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct
  have HrawLower :
      BankPaperCanonicalActiveMassPaperScaleLower rawBase := by
    simpa only [rawBase] using
      bankPaperCanonicalRawSmoothBaseMass_paperScaleLower
        W K hc hbeta
  have HqTildeLower :
      BankPaperCanonicalActiveMassPaperScaleLower qTilde :=
    bankPaperCanonicalPostGuardSmoothMass_paperScaleLower
      rawBase qTilde HrawLower Hledger.1
  have HrawBigO : rawBase =O[atTop] secondOrderScale := by
    simpa only [rawBase] using
      bankPaperCanonicalRawSmoothBaseMass_isBigO W K c betaAct
  have HqTildeBigO : qTilde =O[atTop] secondOrderScale :=
    bankPaperCanonicalPostGuardSmoothMass_isBigO
      rawBase qTilde HrawBigO Hledger.1
  have Hchange :
      bankPaperCanonicalSymmetricInitialCellMassFamily mFrozen qTilde
          =o[atTop]
        secondOrderScale :=
    bankPaperCanonicalSymmetricInitialCellMassFamily_isLittleO
      mFrozen qTilde
  have hcapacity :=
    eventually_bankPaperCanonicalTwoZeroHeadCell_scalarCapacity_of_asymptoticMass
      (P := P) (Band := Band)
      Phead I Cprom Cbank ledger qTilde
        (bankPaperCanonicalSymmetricInitialCellMassFamily mFrozen qTilde)
        HqTildeLower HqTildeBigO Hchange hmarginFloor betaProt
  filter_upwards [hcapacity] with n hcapacityN
  intro B hBn hsep hremaining hcanonical T hTmargin sigma m hcell
  have hscalar :=
    hcapacityN B hBn hsep hremaining hcanonical T hTmargin sigma
  exact
    ⟨bankPaperCanonicalSymmetricInitialAndHeightRebalance_nonneg_of_cellMass
        B.sampleData T (mFrozen n) (qTilde n) 0
          m sigma hcell hscalar.1,
      bankPaperCanonicalSymmetricInitialAndHeightRebalance_protected_le_one_of_cellMass
        B T (mFrozen n) (qTilde n) 0 betaProt
          m sigma hcell hscalar.2⟩

/-! ## Selector-tail support transport -/

/-- On the guarded candidate set, replacing `qTilde` by the nearest-integer
seed changes the frozen-top source by exactly the corresponding ambient seed
change.  On the smooth row the frozen raw layer cancels; on every nonsmooth
row both sources agree and both active ambient weights vanish. -/
theorem
    bankPaperCanonicalTopFrozenRoundedSourceSelector_sub_qTildeSource_eq_ambient_sub
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
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    {a : Nat}
    (ha : a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K) :
    bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde a -
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde) a =
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
          (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde) a -
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
          (bankPaperCanonicalScaledActiveSeed T qTilde) a := by
  by_cases hlabel :
      completeRoughLabel (yNat B.sampleData.n) a = 1
  · have haSmooth :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
      simpa only [BankPaperRealization.roughCanonicalGuardedRow] using
        (mem_completeRoughRowFiber.mpr ⟨ha, hlabel⟩)
    rw [bankPaperCanonicalTopFrozenRoundedSourceSelector,
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
        B R certificate
          (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde)
          haSmooth,
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
        B R certificate (bankPaperCanonicalScaledActiveSeed T qTilde)
          haSmooth]
    ring
  · have haRow :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K
          (completeRoughLabel (yNat B.sampleData.n) a) := by
      simpa only [BankPaperRealization.roughCanonicalGuardedRow] using
        (mem_completeRoughRowFiber.mpr ⟨ha, rfl⟩)
    have hsourceEq :=
      bankPaperCanonicalTopFrozenRoundedSourceSelector_eq_qTildeSource_of_mem_nonsmoothRow
        (K := K) B R certificate T deltaStar betaProt alpha betaTotal
          qTilde hlabel haRow
    have hnewZero :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate T deltaStar betaProt alpha qTilde) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      have hmSmooth :=
        hactiveSmooth
          (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
      have hmLabel := (mem_completeRoughRowFiber.mp hmSmooth).2
      exact hlabel hmLabel
    have holdZero :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalScaledActiveSeed T qTilde) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      have hmSmooth :=
        hactiveSmooth
          (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
      have hmLabel := (mem_completeRoughRowFiber.mp hmSmooth).2
      exact hlabel hmLabel
    rw [hsourceEq, hnewZero, holdZero]
    ring

/-- The nearest-integer zero-head correction preserves the complete
frozen-top source moment at every prime represented by the head simplex. -/
theorem
    sum_bankPaperCanonicalTopFrozenRoundedSourceSelector_mul_headValuation_eq_qTilde
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
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime E)
    (p : {p : Nat // p ∈ P}) :
    (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate T deltaStar betaProt alpha betaTotal qTilde a *
          valuation p.1 a) =
      ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha betaTotal
              (bankPaperCanonicalScaledActiveSeed T qTilde) a *
          valuation p.1 a := by
  have hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedCandidateSet certificate deltaStar K := by
    intro m
    exact (mem_completeRoughRowFiber.mp
      (hactiveSmooth
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩))).1
  have hambient :=
    sum_bankPaperCanonicalTopFrozenRoundedAmbient_mul_headValuation_eq_qTilde
      (K := K) B R certificate T deltaStar betaProt alpha qTilde
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        hvalues hprime E hpattern p
  apply sub_eq_zero.mp
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
              B R certificate T deltaStar betaProt alpha betaTotal
                qTilde a *
            valuation p.1 a -
          bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
              B R certificate deltaStar betaProt alpha betaTotal
                (bankPaperCanonicalScaledActiveSeed T qTilde) a *
            valuation p.1 a)) =
      ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        (bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
                B R certificate T deltaStar betaProt alpha qTilde) a -
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalScaledActiveSeed T qTilde) a) *
            valuation p.1 a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← sub_mul,
        bankPaperCanonicalTopFrozenRoundedSourceSelector_sub_qTildeSource_eq_ambient_sub
          (K := K) B R certificate T deltaStar betaProt alpha betaTotal
            qTilde hactiveSmooth ha]
    _ =
      (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
                B R certificate T deltaStar betaProt alpha qTilde) a *
            valuation p.1 a) -
        ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalScaledActiveSeed T qTilde) a *
            valuation p.1 a := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ = 0 := by
      rw [hambient, sub_self]

/-- Above `y`, the rounded and literal `qTilde` frozen-top sources have the
same valuation moment: nonsmooth rows agree pointwise, while the complete
smooth row has zero valuation at such a prime. -/
theorem
    sum_bankPaperCanonicalTopFrozenRoundedSourceSelector_mul_factorization_eq_qTilde_of_yNat_lt
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
    (q : Nat) (hyq : yNat B.sampleData.n < q) :
    (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate T deltaStar betaProt alpha betaTotal qTilde a *
          (a.factorization q : Real)) =
      ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha betaTotal
              (bankPaperCanonicalScaledActiveSeed T qTilde) a *
          (a.factorization q : Real) := by
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hlabel :
      completeRoughLabel (yNat B.sampleData.n) a = 1
  · have hfactorization : a.factorization q = 0 := by
      have hrough :
          (completeRoughLabel (yNat B.sampleData.n) a).factorization q =
            0 := by
        rw [hlabel]
        simp
      rw [completeRoughLabel_factorization_apply, if_pos hyq] at hrough
      exact hrough
    rw [hfactorization]
    ring
  · have haRow :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K
          (completeRoughLabel (yNat B.sampleData.n) a) := by
      simpa only [BankPaperRealization.roughCanonicalGuardedRow] using
        (mem_completeRoughRowFiber.mpr ⟨ha, rfl⟩)
    rw [
      bankPaperCanonicalTopFrozenRoundedSourceSelector_eq_qTildeSource_of_mem_nonsmoothRow
        (K := K) B R certificate T deltaStar betaProt alpha betaTotal
          qTilde hlabel haRow]

/-- The zero-head nearest-integer correction transports selector-tail
support from the literal `qTilde` frozen-top source to the rounded source. -/
theorem
    bankPaperCanonicalTopFrozenRoundedSourceSelector_deficitSupportedOnPrimeBand_of_qTilde
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
    (fixed : Finset Nat)
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime E)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (hsource : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal
          (bankPaperCanonicalScaledActiveSeed T qTilde))) :
    BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha betaTotal qTilde) := by
  intro q hqPrime hqNotBand
  have hsum :
      (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
          bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
              B R certificate T deltaStar betaProt alpha betaTotal
                qTilde a *
            (a.factorization q : Real)) =
        ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
          bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
              B R certificate deltaStar betaProt alpha betaTotal
                (bankPaperCanonicalScaledActiveSeed T qTilde) a *
            (a.factorization q : Real) := by
    by_cases hqHead : q <= B.sampleData.W
    · have hqMem : q ∈ primesUpTo B.sampleData.W :=
        mem_primesUpTo.mpr ⟨hqPrime, hqHead⟩
      let p : {p : Nat // p ∈ P} := ⟨q, hhead hqMem⟩
      simpa only [p, valuation] using
        (sum_bankPaperCanonicalTopFrozenRoundedSourceSelector_mul_headValuation_eq_qTilde
          (K := K) B R certificate T deltaStar betaProt alpha betaTotal
            qTilde hactiveSmooth hprime E hpattern p)
    · have hWq : B.sampleData.W < q := Nat.lt_of_not_ge hqHead
      have hyq : yNat B.sampleData.n < q := by
        by_contra hnotY
        have hqy : q <= yNat B.sampleData.n := Nat.le_of_not_gt hnotY
        exact hqNotBand (mem_primeBand.mpr ⟨hqPrime, hWq, hqy⟩)
      exact
        sum_bankPaperCanonicalTopFrozenRoundedSourceSelector_mul_factorization_eq_qTilde_of_yNat_lt
          (K := K) B R certificate T deltaStar betaProt alpha betaTotal
            qTilde q hyq
  simpa only [bankPaperCanonicalSelectorValuationDeficit, hsum] using
    hsource q hqPrime hqNotBand

/-! ## Exact residual input -/

/-- The source-specific facts not supplied by canonical geometry or the
Section 8 analytic capacity argument.

The first conjunct is feasibility before nearest-integer rounding.  The
second is the charged nonsmooth-row realization already used by the
frozen-top initial-mass theorem.  The third is the exact selector-tail
support identity for that same literal source; it transports to the rounded
source by the preceding theorem. -/
def BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
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
    (fixed : Finset Nat)
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real) : Prop :=
  (∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde) a ∧
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde) a <= 1) ∧
    BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K) R certificate deltaStar
        (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde)) ∧
    BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal
          (bankPaperCanonicalScaledActiveSeed T qTilde))

/-! ## Finite assembly -/

/-- Canonical geometry, two-cell initialization capacity, and the residual
source-specific inputs construct the exact nearest-integer source state. -/
theorem bankPaperCanonicalTopFrozenRoundedSelectorSourceState_of_qTildeSource
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
    (fixed : Finset Nat)
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime E)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (hbetaProt : 0 <= betaProt)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hminus : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hplus : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hminusCapacity : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        0 <= bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde m ∧
          betaProt / B.L +
              bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
                B R certificate T deltaStar betaProt alpha qTilde m <= 1)
    (hplusCapacity : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        0 <= bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde m ∧
          betaProt / B.L +
              bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
                B R certificate T deltaStar betaProt alpha qTilde m <= 1)
    (Hresidual : BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
      (K := K) B R certificate fixed T deltaStar betaProt alpha betaTotal
        qTilde) :
    BankPaperCanonicalSelectorSourceState (W := B.sampleData.W)
      R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha betaTotal qTilde) := by
  have hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
    intro m
    exact hactiveSmooth
      (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩)
  have hfeasible :=
    bankPaperCanonicalTopFrozenRoundedSourceSelector_feasible_of_qTildeSource
      (K := K) B R certificate T deltaStar betaProt alpha betaTotal
        qTilde hbetaProt hsep hactiveSmooth Hresidual.1 hminus hplus
        hminusCapacity hplusCapacity
  have hsupport :=
    bankPaperCanonicalTopFrozenRoundedSourceSelector_deficitSupportedOnPrimeBand_of_qTilde
      (K := K) B R certificate fixed T deltaStar betaProt alpha betaTotal
        qTilde hactiveSmooth hprime E hpattern hhead Hresidual.2.2
  exact
    bankPaperCanonicalTopFrozenRoundedSelectorSourceState
      (K := K) B R certificate fixed T deltaStar betaProt alpha betaTotal
        qTilde hvalues Hresidual.2.1 hfeasible hsupport

/-! ## Eventual canonical supplier -/

/-- The narrow eventual `qTilde -> q0 -> SourceState` supplier.

Canonical-data geometry and initial two-cell capacity are discharged
internally.  At the synchronized finite index, the caller supplies only:

* the equality between the analytic `mFrozen` family and the concrete
  frozen-top smooth mass; and
* `BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt`.

Those are precisely the source-specific identities not proved by the
current Section 8/9 eventual infrastructure. -/
theorem
    eventually_bankPaperCanonicalTopFrozenRoundedSelectorSourceState_of_residualInputs
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat) (hE : 0 < E)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperStrict : forall sigma, I.upper sigma < 2)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    (depth W K : Nat)
    {c betaAct marginFloor deltaStar betaProt : Real}
    (hc : 0 < c) (hbeta : 0 < betaAct)
    (hmarginFloor : 0 < marginFloor)
    (hbetaProt : 0 <= betaProt)
    (hhead : primesUpTo W ⊆ P)
    (mFrozen qTilde A0 : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde A0) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        B.sampleData.W = W ->
        forall
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell :
              Cell (PaperHeadSimplex.Tag P),
            (rawCell (PaperHeadSimplex.pattern P hprime E) I
                B.sampleData.n cell \
              (ledger B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                (PaperHeadSimplex.pattern P hprime E) I
                (ledger B.sampleData.n) hsep hremaining ->
          forall
            (R : BankPaperRealization B.sampleData.n
              (upperEndpoint B.sampleData.n
                (upperTailLength c B.sampleData.n)))
            (certificate : GuardedCentralAnchorCertificate c depth
              B.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
              (R.centralChangedMarkers depth))
            (_hguardAgreement : BankPaperCanonicalBridgeGuardAgreement
              (ledger B.sampleData.n) R certificate deltaStar)
            (T : BarycentricTarget B.sampleData),
              marginFloor <= T.cellMassMargin ->
              forall (fixed : Finset Nat) (alpha betaTotal : Real),
                mFrozen n =
                    bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K)
                      B R certificate deltaStar betaProt alpha ->
                BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
                    (K := K) B R certificate fixed T deltaStar betaProt
                      alpha betaTotal (qTilde n) ->
                BankPaperCanonicalSelectorSourceState
                  (W := B.sampleData.W) R certificate fixed
                  (R.roughCanonicalGuardedCandidateSet certificate
                    deltaStar K)
                  (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
                    B R certificate T deltaStar betaProt alpha betaTotal
                      (qTilde n)) := by
  have hcapacity :=
    eventually_bankPaperCanonicalSymmetricInitial_twoZeroHeadCell_rebalance_capacity
      (P := P) (Band := Band)
      (PaperHeadSimplex.pattern P hprime E)
      I Cprom Cbank ledger W K hc hbeta hmarginFloor
        mFrozen qTilde A0 Hledger betaProt
  have hupperBroad :=
    eventually_physicalIntervals_upperBound_le_two_mul_sub_upperTailLength
      I K hc hupperStrict
  have hKh := eventually_mul_upperTailLength_le_self K hc
  filter_upwards [hcapacity, hupperBroad, hKh] with
    n hcapacityN hupperBroadN hKhN
  intro B hBn hBW hsep hremaining hcanonical
    R certificate hguardAgreement T hTmargin
    fixed alpha betaTotal hmFrozen Hresidual
  have hheadB : primesUpTo B.sampleData.W ⊆ P := by
    simpa only [hBW] using hhead
  have hKhB :
      K * upperTailLength c B.sampleData.n <= B.sampleData.n := by
    simpa only [hBn] using hKhN
  have hupperBroadB : forall sigma,
      physicalBound (I.upper sigma) B.sampleData.n <=
        2 * B.sampleData.n -
          K * upperTailLength c B.sampleData.n := by
    intro sigma
    simpa only [hBn] using hupperBroadN sigma
  have hupperTwo : forall sigma, I.upper sigma <= 2 :=
    fun sigma => (hupperStrict sigma).le
  have hpattern :
      B.sampleData.pattern =
        PaperHeadSimplex.pattern P hprime E := by
    calc
      B.sampleData.pattern =
          (canonicalSampleData (W := B.sampleData.W)
            (PaperHeadSimplex.pattern P hprime E) I
            (ledger B.sampleData.n) hsep hremaining).pattern :=
        congrArg
          (fun D : StructuredSampleData (PaperHeadSimplex.Tag P) =>
            D.pattern)
          hcanonical
      _ = PaperHeadSimplex.pattern P hprime E :=
        canonicalSampleData_pattern
          (PaperHeadSimplex.pattern P hprime E) I
          (ledger B.sampleData.n) hsep hremaining
  have hgeometry :=
    bankPaperCanonicalSectionEight_twoZeroHeadCell_geometryInputs
      (P := P) (Band := Band) (c := c) (depth := depth) (K := K)
      hprime E hE I hlowerOne hupperTwo Cprom Cbank ledger
      B hheadB hsep hremaining hcanonical R certificate deltaStar
      hguardAgreement hKhB hupperBroadB
  have hcellMass :
      bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
          B R certificate deltaStar betaProt alpha (qTilde n) =
        bankPaperCanonicalSymmetricInitialCellMassFamily
          mFrozen qTilde n := by
    rw [
      bankPaperCanonicalTopFrozenNearestIntegerCellMass_eq_symmetricInitial,
      bankPaperCanonicalSymmetricInitialCellMassFamily,
      hmFrozen]
  have hminusCapacity : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        0 <= bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha (qTilde n) m ∧
          betaProt / B.L +
              bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
                B R certificate T deltaStar betaProt alpha (qTilde n) m <=
            1 := by
    intro m hm
    simpa only [bankPaperCanonicalTopFrozenRoundedActiveSeed,
      hcellMass] using
      (hcapacityN B hBn hsep hremaining hcanonical T hTmargin
        .minus m hm)
  have hplusCapacity : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        0 <= bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha (qTilde n) m ∧
          betaProt / B.L +
              bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
                B R certificate T deltaStar betaProt alpha (qTilde n) m <=
            1 := by
    intro m hm
    simpa only [bankPaperCanonicalTopFrozenRoundedActiveSeed,
      hcellMass] using
      (hcapacityN B hBn hsep hremaining hcanonical T hTmargin
        .plus m hm)
  exact
    bankPaperCanonicalTopFrozenRoundedSelectorSourceState_of_qTildeSource
      (K := K) B R certificate fixed T deltaStar betaProt alpha betaTotal
        (qTilde n) hprime E hpattern hheadB
        hbetaProt hgeometry.1 hgeometry.2.1
        hgeometry.2.2.1 hgeometry.2.2.2
        hminusCapacity hplusCapacity Hresidual

end BankPaperRealization

end

end Erdos390.WholePaper
