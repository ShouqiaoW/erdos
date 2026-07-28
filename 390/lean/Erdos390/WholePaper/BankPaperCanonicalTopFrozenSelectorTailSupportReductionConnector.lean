import Erdos390.WholePaper.BankPaperCanonicalTopFrozenChargedRowsConnector
import Erdos390.WholePaper.BankPaperCanonicalTopFrozenRoundedSourceStateEventualConnector
import Erdos390.WholePaper.BankPaperCanonicalSignedResidualSelectorIdentification

/-!
# Selector-tail support reduction for the frozen-top sources

Outside the medium-prime band there are two disjoint finite mechanisms.

* At a head prime `q ≤ W`, every raw or constant-pool correction term has
  zero `q`-valuation.  The source moment is therefore exactly the moment of
  the scaled structured seed, hence `Rhead.target`.
* At a high prime `yNat n < q`, factorization is constant on each complete
  rough row.  Charged nonsmooth-row totals, together with postcharge row
  capacity for unattained active rows, identify the source moment with the
  selector-tail target ledger.

Thus the only extra low-prime datum is the literal compatibility

`Rhead.target p =
  (certificate.selectorTailTarget R fixed).factorization p`.

The finite theorems below first expose the low/high reductions separately,
then package selector-tail support for both the literal `qTilde` source and
its nearest-integer rounded counterpart.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Head-prime vanishing -/

/-- A head-compatible raw coordinate has zero weighted valuation at every
prime in the complete head product. -/
theorem
    roughHeadCompatibleRawWeight_mul_factorization_eq_zero_of_headPrime
    {W n h K q a : Nat} {alpha beta ell : Real}
    (hqPrime : q.Prime) (hqW : q <= W) :
    roughHeadCompatibleRawWeight W n h K alpha beta ell a *
        (a.factorization q : Real) = 0 := by
  by_cases hcop : Nat.Coprime a (roughHeadModulus W)
  · have hqHead : q ∈ primesUpTo W :=
      mem_primesUpTo.mpr ⟨hqPrime, hqW⟩
    have hqDvd : q ∣ roughHeadModulus W := by
      unfold roughHeadModulus
      exact Finset.dvd_prod_of_mem (fun r : Nat => r) hqHead
    have haq : Nat.Coprime a q :=
      Nat.Coprime.of_dvd_right hqDvd hcop
    have hfactorization : a.factorization q = 0 :=
      Nat.factorization_eq_zero_of_not_dvd
        (hqPrime.coprime_iff_not_dvd.mp haq.symm)
    rw [hfactorization]
    ring
  · simp [roughHeadCompatibleRawWeight, hcop]

/-- Every coordinate in any guarded broad correction row—not only the
smooth row—has zero valuation at a head prime. -/
theorem factorization_eq_zero_of_mem_guardedBroadCorrectionPool_of_headPrime_label
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K label : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar : Real} {q a : Nat}
    (hqPrime : q.Prime) (hqW : q <= B.sampleData.W)
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K label) :
    a.factorization q = 0 := by
  have haRaw :=
    R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
      certificate deltaStar B.sampleData.W K label ha
  have haData := mem_completeRoughRowFiber.mp haRaw
  have haHeadFree := mem_roughHeadFree.mp haData.1
  have hqHead : q ∈ primesUpTo B.sampleData.W :=
    mem_primesUpTo.mpr ⟨hqPrime, hqW⟩
  have hqDvd : q ∣ roughHeadModulus B.sampleData.W := by
    unfold roughHeadModulus
    exact Finset.dvd_prod_of_mem (fun r : Nat => r) hqHead
  have haq : Nat.Coprime a q :=
    Nat.Coprime.of_dvd_right hqDvd haHeadFree.2
  exact Nat.factorization_eq_zero_of_not_dvd
    (hqPrime.coprime_iff_not_dvd.mp haq.symm)

/-- The literal guarded postcharge correction has zero weighted valuation
at every head prime, independently of its row target and density. -/
theorem
    roughCanonicalGuardedPostchargeRowCorrectedWeight_mul_factorization_eq_zero_of_headPrime
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K label : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar alpha beta : Real} {q a : Nat}
    (hqPrime : q.Prime) (hqW : q <= B.sampleData.W) :
    R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
          deltaStar B.sampleData.W K label alpha beta B.L a *
        (a.factorization q : Real) = 0 := by
  unfold roughCanonicalGuardedPostchargeRowCorrectedWeight
  unfold bankPaperConstantPoolCorrection
  by_cases haPool :
      a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K label
  · rw [if_pos haPool,
      factorization_eq_zero_of_mem_guardedBroadCorrectionPool_of_headPrime_label
        B R certificate hqPrime hqW haPool]
    ring
  · rw [if_neg haPool]
    simpa using
      (roughHeadCompatibleRawWeight_mul_factorization_eq_zero_of_headPrime
        (W := B.sampleData.W) (n := B.sampleData.n)
        (h := upperTailLength c B.sampleData.n) (K := K)
        (alpha := alpha) (beta := beta) (ell := B.L)
        (q := q) (a := a) hqPrime hqW)

/-- On the guarded candidate set, the complete frozen-top source has the
same head-prime moment pointwise as its ambient structured seed. -/
theorem
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_mul_factorization_eq_ambient_of_headPrime
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
    (deltaStar betaProt alpha beta : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    {q a : Nat} (hqPrime : q.Prime) (hqW : q <= B.sampleData.W)
    (ha : a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K) :
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a *
        (a.factorization q : Real) =
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData oldSeed a *
        (a.factorization q : Real) := by
  classical
  by_cases hlabel :
      completeRoughLabel (yNat B.sampleData.n) a = 1
  · have haSmooth :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
      simpa only [BankPaperRealization.roughCanonicalGuardedRow] using
        (mem_completeRoughRowFiber.mpr ⟨ha, hlabel⟩)
    rw [
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
        B R certificate oldSeed haSmooth]
    have hraw :=
      roughHeadCompatibleRawWeight_mul_factorization_eq_zero_of_headPrime
        (W := B.sampleData.W) (n := B.sampleData.n)
        (h := upperTailLength c B.sampleData.n) (K := K)
        (alpha := alpha) (beta := betaProt) (ell := B.L)
        (q := q) (a := a) hqPrime hqW
    calc
      (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha betaProt B.L a +
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a) *
          (a.factorization q : Real) =
        roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
              (upperTailLength c B.sampleData.n) K alpha betaProt B.L a *
            (a.factorization q : Real) +
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData oldSeed a *
            (a.factorization q : Real) := by ring
      _ = bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a * (a.factorization q : Real) := by
        rw [hraw]
        ring
  · have hnotSmoothPool :
        a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1 := by
      intro haPool
      have haSmooth :
          a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
        R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
          certificate deltaStar B.sampleData.W K 1 haPool
      exact hlabel (mem_completeRoughRowFiber.mp haSmooth).2
    have hambientZero :
        bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      have hmSmooth :=
        hactiveSmooth
          (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
      exact hlabel (mem_completeRoughRowFiber.mp hmSmooth).2
    rw [bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
      bankPaperCanonicalTwoZeroHeadCellSourceSelector,
      if_neg hnotSmoothPool,
      bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop,
      if_neg hlabel]
    by_cases hexceptional :
        RoughCanonicalExceptionalLabel B.sampleData.n deltaStar
          (completeRoughLabel (yNat B.sampleData.n) a)
    · rw [if_pos hexceptional, hambientZero]
    · rw [if_neg hexceptional, hambientZero,
        roughCanonicalGuardedPostchargeRowCorrectedWeight_mul_factorization_eq_zero_of_headPrime
          B R certificate hqPrime hqW]
      ring

/-- The whole literal frozen-top source moment at a head prime is exactly
the corresponding reserve target. -/
theorem
    sum_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_mul_factorization_eq_headTarget
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (hprime : ∀ p ∈ P, p.Prime)
    (Rhead : HeadSimplexReserve P)
    (I : PhysicalIntervals)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (Kphysical : PhysicalInterpolationTarget I)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime Rhead.exponent)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (p : {p : Nat // p ∈ P}) (hpW : p.1 <= B.sampleData.W) :
    let T := B.barycentricTargetOfPaperData
      I hlo hhi Rhead Kphysical
    (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha beta
              (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass) a *
          (a.factorization p.1 : Real)) =
      Rhead.target p := by
  dsimp only
  let T :=
    B.barycentricTargetOfPaperData I hlo hhi Rhead Kphysical
  have hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedCandidateSet certificate deltaStar K := by
    intro m
    exact (mem_completeRoughRowFiber.mp
      (hactiveSmooth
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩))).1
  calc
    (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha beta
              (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass) a *
          (a.factorization p.1 : Real)) =
      ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass) a *
          (a.factorization p.1 : Real) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_mul_factorization_eq_ambient_of_headPrime
          (K := K) B R certificate deltaStar betaProt alpha beta
            (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass)
            hactiveSmooth (hprime p.1 p.2) hpW ha
    _ = Rhead.target p := by
      simpa only [T, valuation] using
        (sum_bankPaperCanonicalScaledActiveSeedAmbient_mul_paperHeadValuation
          B hprime Rhead I hlo hhi Kphysical hpattern
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            hvalues p)

/-- Low-prime selector-tail closure.  The displayed reserve/target
compatibility is the only premise not supplied by the finite head
realization itself. -/
theorem
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_selectorValuationDeficit_eq_zero_of_headPrime
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (hprime : ∀ p ∈ P, p.Prime)
    (Rhead : HeadSimplexReserve P)
    (I : PhysicalIntervals)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (Kphysical : PhysicalInterpolationTarget I)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime Rhead.exponent)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    (deltaStar betaProt alpha beta : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (p : {p : Nat // p ∈ P}) (hpW : p.1 <= B.sampleData.W)
    (hcompatibility :
      Rhead.target p =
        ((certificate.selectorTailTarget R fixed).factorization p.1 :
          Real)) :
    let T := B.barycentricTargetOfPaperData
      I hlo hhi Rhead Kphysical
    bankPaperCanonicalSelectorValuationDeficit R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta
            (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass))
        p.1 = 0 := by
  dsimp only
  have hmoment :=
    sum_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_mul_factorization_eq_headTarget
      (K := K) B hprime Rhead I hlo hhi Kphysical hpattern
        R certificate deltaStar betaProt alpha beta hactiveSmooth p hpW
  unfold bankPaperCanonicalSelectorValuationDeficit
  rw [← hcompatibility, hmoment, sub_self]

/-! ## High-prime row reindexing -/

/-- A weighted high-prime moment can be reindexed over any finite superset
of the attained complete rough labels. -/
theorem
    sum_mul_factorization_eq_sum_rowSum_mul_labelFactorization_of_labelSet_subset
    (y p : Nat) (A labels : Finset Nat) (weight : Nat -> Real)
    (hyp : y < p) (hlabels : completeRoughLabelSet y A ⊆ labels) :
    (∑ a ∈ A, weight a * (a.factorization p : Real)) =
      ∑ label ∈ labels,
        (∑ a ∈ completeRoughRowFiber y A label, weight a) *
          (label.factorization p : Real) := by
  rw [sum_eq_sum_completeRoughRowFibers_of_labelSet_subset
    y A labels (fun a => weight a * (a.factorization p : Real)) hlabels]
  apply Finset.sum_congr rfl
  intro label _hlabel
  calc
    (∑ a ∈ completeRoughRowFiber y A label,
        weight a * (a.factorization p : Real)) =
      ∑ a ∈ completeRoughRowFiber y A label,
        weight a * (label.factorization p : Real) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [factorization_eq_label_factorization_of_mem_rowFiber hyp ha]
    _ = (∑ a ∈ completeRoughRowFiber y A label, weight a) *
          (label.factorization p : Real) := by
      rw [Finset.sum_mul]

/-- Cast-valued specialization of the preceding weighted partition. -/
theorem
    sum_factorization_cast_eq_sum_completeLabelMultiplicity_mul_of_labelSet_subset
    (y p : Nat) (A labels : Finset Nat)
    (hyp : y < p) (hlabels : completeRoughLabelSet y A ⊆ labels) :
    (∑ a ∈ A, (a.factorization p : Real)) =
      ∑ label ∈ labels,
        (completeLabelMultiplicity y A label : Real) *
          (label.factorization p : Real) := by
  simpa [completeLabelMultiplicity, completeRoughRowFiber] using
    (sum_mul_factorization_eq_sum_rowSum_mul_labelFactorization_of_labelSet_subset
      y p A labels (fun _a => (1 : Real)) hyp hlabels)

/-- Charged nonsmooth rows and global postcharge capacity determine the
target total on every non-smooth label in the finite charged universe,
including labels not attained by guarded candidates. -/
theorem
    sum_chargedSelector_eq_postchargeRowTarget_of_mem_labelSet_of_ne_one
    {c : Real} {depth n h K : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (selector : Nat -> Real)
    (hrows : BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K) R certificate deltaStar selector)
    (hcapacity : forall label, IsCompleteRoughLabel (yNat n) label ->
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        RoughCanonicalPostchargeRowCapacity R certificate deltaStar K label)
    {label : Nat}
    (hlabel : label ∈
      bankPaperCanonicalChargedLabelSet (K := K)
        R certificate deltaStar)
    (hlabelNeOne : label ≠ 1) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
        selector a) =
      R.roughCanonicalPostchargeRowTarget deltaStar label := by
  by_cases hlabelCandidate :
      label ∈ completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
  · rcases roughCanonical_activeNonexceptional_or_exceptional
        (n := n) (deltaStar := deltaStar) hlabelNeOne with
      hactive | hexceptional
    · exact hrows.1 label hlabelCandidate hactive
    · have hzero :=
        hrows.2 label hlabelCandidate hlabelNeOne hexceptional
      have htargetZero :=
        R.roughCanonicalPostchargeRowTarget_eq_zero_of_exceptional
          deltaStar label hexceptional
      simpa only [htargetZero] using hzero
  · have hempty :
        R.roughCanonicalGuardedRow certificate deltaStar K label = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact hlabelCandidate
        (mem_completeRoughLabelSet.mpr
          ⟨a, (mem_completeRoughRowFiber.mp ha).1,
            (mem_completeRoughRowFiber.mp ha).2⟩)
    have hcomplete : IsCompleteRoughLabel (yNat n) label := by
      simp only [bankPaperCanonicalChargedLabelSet,
        Finset.mem_insert, Finset.mem_union] at hlabel
      rcases hlabel with hlabelOne |
        (((hlabelUpper | hlabelFixed) | hlabelBase) | hlabelCandidates)
      · exact (hlabelNeOne hlabelOne).elim
      · exact isCompleteRoughLabel_of_canonicalCompleteRoughRow
          (⟨label, hlabelUpper⟩ :
            CanonicalCompleteRoughRow (yNat n) (roughUpperBlock n h))
      · exact isCompleteRoughLabel_of_canonicalCompleteRoughRow
          (⟨label, hlabelFixed⟩ :
            CanonicalCompleteRoughRow (yNat n)
              (R.paperFixedExceptionalFactors deltaStar))
      · exact isCompleteRoughLabel_of_canonicalCompleteRoughRow
          (⟨label, hlabelBase⟩ :
            CanonicalCompleteRoughRow (yNat n) R.prechargeBaseState)
      · exact isCompleteRoughLabel_of_canonicalCompleteRoughRow
          (⟨label, hlabelCandidates⟩ :
            CanonicalCompleteRoughRow (yNat n)
              (R.roughCanonicalGuardedCandidateSet certificate
                deltaStar K))
    rcases roughCanonical_activeNonexceptional_or_exceptional
        (n := n) (deltaStar := deltaStar) hlabelNeOne with
      hactive | hexceptional
    · have hcap := hcapacity label hcomplete hactive
      unfold RoughCanonicalPostchargeRowCapacity at hcap
      rw [hempty] at hcap
      have htargetZero :
          R.roughCanonicalPostchargeRowTarget deltaStar label = 0 := by
        apply le_antisymm
        · simpa only [Finset.card_empty, Nat.cast_zero] using hcap
        · exact
            R.roughCanonicalPostchargeRowTarget_nonneg deltaStar label
      simp only [hempty, Finset.sum_empty, htargetZero]
    · have htargetZero :=
        R.roughCanonicalPostchargeRowTarget_eq_zero_of_exceptional
          deltaStar label hexceptional
      simp only [hempty, Finset.sum_empty, htargetZero]

/-- The signed target ledger is equivalent, after cancelling designated
exceptional donors, to the three charged row families used by the
postcharge target. -/
theorem
    selectorTailTarget_factorization_eq_upper_sub_fixed_sub_base_of_signedTargetLedger
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (p : Nat)
    (htarget : BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p) :
    ((certificate.selectorTailTarget R
        (R.paperFixedExceptionalFactors deltaStar)).factorization p :
      Real) =
      (∑ a ∈ roughUpperBlock n (upperTailLength c n),
        (a.factorization p : Real)) -
      (∑ a ∈ R.paperFixedExceptionalFactors deltaStar,
        (a.factorization p : Real)) -
      ∑ a ∈ R.prechargeBaseState, (a.factorization p : Real) := by
  have hdisjoint :
      Disjoint (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalExceptionalDonorSet deltaStar) := by
    rw [Finset.disjoint_left]
    intro a hfixed hdonor
    have hdonor' :=
      ((R.mem_roughCanonicalExceptionalDonorSet).1 hdonor).1
    exact (Finset.disjoint_left.mp
      (R.paperFixedExceptionalFactors_disjoint_prechargeDonorSet
        deltaStar)) hfixed hdonor'
  have hexceptionalSum :
      (∑ a ∈ paperExceptionalUpperFactors n
          (upperTailLength c n) deltaStar,
        (a.factorization p : Real)) =
      (∑ a ∈ R.paperFixedExceptionalFactors deltaStar,
        (a.factorization p : Real)) +
      ∑ a ∈ R.roughCanonicalExceptionalDonorSet deltaStar,
        (a.factorization p : Real) := by
    rw [paperExceptionalUpperFactors_eq_fixed_union_exceptionalDonors
      R deltaStar, Finset.sum_union hdisjoint]
  unfold BankPaperCanonicalSignedResidualTargetLedger at htarget
  rw [hexceptionalSum] at htarget
  linarith only [htarget]

/-- High-prime selector-tail closure from charged row totals. -/
theorem
    bankPaperCanonicalSelectorValuationDeficit_eq_zero_of_chargedRows_of_yNat_lt
    {c : Real} {depth n K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (selector : Nat -> Real)
    (p : Nat) (hyp : yNat n < p)
    (hrows : BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K) R certificate deltaStar selector)
    (hcapacity : forall label, IsCompleteRoughLabel (yNat n) label ->
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        RoughCanonicalPostchargeRowCapacity R certificate deltaStar K label)
    (htarget : BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p) :
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        selector p = 0 := by
  classical
  let candidates :=
    R.roughCanonicalGuardedCandidateSet certificate deltaStar K
  let labels :=
    bankPaperCanonicalChargedLabelSet (K := K) R certificate deltaStar
  have hupperLabels :
      completeRoughLabelSet (yNat n)
          (roughUpperBlock n (upperTailLength c n)) ⊆ labels := by
    intro label hlabel
    simp [labels, bankPaperCanonicalChargedLabelSet, hlabel]
  have hfixedLabels :
      completeRoughLabelSet (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) ⊆ labels := by
    intro label hlabel
    simp [labels, bankPaperCanonicalChargedLabelSet, hlabel]
  have hbaseLabels :
      completeRoughLabelSet (yNat n) R.prechargeBaseState ⊆ labels := by
    intro label hlabel
    simp [labels, bankPaperCanonicalChargedLabelSet, hlabel]
  have hcandidateLabels :
      completeRoughLabelSet (yNat n) candidates ⊆ labels := by
    intro label hlabel
    simp [labels, candidates, bankPaperCanonicalChargedLabelSet, hlabel]
  have hcandidatesPartition :
      (∑ a ∈ candidates, selector a * (a.factorization p : Real)) =
        ∑ label ∈ labels,
          (∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
              selector a) *
            (label.factorization p : Real) :=
    sum_mul_factorization_eq_sum_rowSum_mul_labelFactorization_of_labelSet_subset
      (yNat n) p candidates labels selector hyp hcandidateLabels
  have hupperPartition :
      (∑ a ∈ roughUpperBlock n (upperTailLength c n),
          (a.factorization p : Real)) =
        ∑ label ∈ labels,
          (roughUpperCompleteRoughRowTarget n
              (upperTailLength c n) (yNat n) label : Real) *
            (label.factorization p : Real) := by
    simpa [roughUpperCompleteRoughRowTarget, completeLabelMultiplicity,
      completeRoughRowFiber] using
      (sum_factorization_cast_eq_sum_completeLabelMultiplicity_mul_of_labelSet_subset
        (yNat n) p (roughUpperBlock n (upperTailLength c n))
          labels hyp hupperLabels)
  have hfixedPartition :
      (∑ a ∈ R.paperFixedExceptionalFactors deltaStar,
          (a.factorization p : Real)) =
        ∑ label ∈ labels,
          (completeLabelMultiplicity (yNat n)
              (R.paperFixedExceptionalFactors deltaStar) label : Real) *
            (label.factorization p : Real) :=
    sum_factorization_cast_eq_sum_completeLabelMultiplicity_mul_of_labelSet_subset
      (yNat n) p (R.paperFixedExceptionalFactors deltaStar)
        labels hyp hfixedLabels
  have hbasePartition :
      (∑ a ∈ R.prechargeBaseState, (a.factorization p : Real)) =
        ∑ label ∈ labels,
          (completeLabelMultiplicity (yNat n)
              R.prechargeBaseState label : Real) *
            (label.factorization p : Real) :=
    sum_factorization_cast_eq_sum_completeLabelMultiplicity_mul_of_labelSet_subset
      (yNat n) p R.prechargeBaseState labels hyp hbaseLabels
  have hrowMoment :
      (∑ label ∈ labels,
          (∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
              selector a) *
            (label.factorization p : Real)) =
        ∑ label ∈ labels,
          R.roughCanonicalPostchargeRowTarget deltaStar label *
            (label.factorization p : Real) := by
    apply Finset.sum_congr rfl
    intro label hlabel
    by_cases hlabelOne : label = 1
    · subst label
      simp
    · have hrow :=
        sum_chargedSelector_eq_postchargeRowTarget_of_mem_labelSet_of_ne_one
          R certificate deltaStar selector hrows hcapacity
            (by simpa only [labels] using hlabel) hlabelOne
      exact
        (by
          simpa only [BankPaperRealization.roughCanonicalGuardedRow] using
            congrArg
              (fun x : Real => x * (label.factorization p : Real)) hrow)
  have htargetPartition :
      (∑ label ∈ labels,
          R.roughCanonicalPostchargeRowTarget deltaStar label *
            (label.factorization p : Real)) =
        (∑ a ∈ roughUpperBlock n (upperTailLength c n),
            (a.factorization p : Real)) -
          (∑ a ∈ R.paperFixedExceptionalFactors deltaStar,
            (a.factorization p : Real)) -
          ∑ a ∈ R.prechargeBaseState,
            (a.factorization p : Real) := by
    calc
      (∑ label ∈ labels,
          R.roughCanonicalPostchargeRowTarget deltaStar label *
            (label.factorization p : Real)) =
        (∑ label ∈ labels,
            (roughUpperCompleteRoughRowTarget n
                (upperTailLength c n) (yNat n) label : Real) *
              (label.factorization p : Real)) -
          (∑ label ∈ labels,
            (completeLabelMultiplicity (yNat n)
                (R.paperFixedExceptionalFactors deltaStar) label : Real) *
              (label.factorization p : Real)) -
          ∑ label ∈ labels,
            (completeLabelMultiplicity (yNat n)
                R.prechargeBaseState label : Real) *
              (label.factorization p : Real) := by
          simp only [roughCanonicalPostchargeRowTarget, sub_mul,
            Finset.sum_sub_distrib]
      _ = (∑ a ∈ roughUpperBlock n (upperTailLength c n),
              (a.factorization p : Real)) -
            (∑ a ∈ R.paperFixedExceptionalFactors deltaStar,
              (a.factorization p : Real)) -
            ∑ a ∈ R.prechargeBaseState,
              (a.factorization p : Real) := by
          rw [← hupperPartition, ← hfixedPartition, ← hbasePartition]
  have hselectorMoment :
      (∑ a ∈ candidates, selector a * (a.factorization p : Real)) =
        (∑ a ∈ roughUpperBlock n (upperTailLength c n),
            (a.factorization p : Real)) -
          (∑ a ∈ R.paperFixedExceptionalFactors deltaStar,
            (a.factorization p : Real)) -
          ∑ a ∈ R.prechargeBaseState,
            (a.factorization p : Real) := by
    rw [hcandidatesPartition, hrowMoment, htargetPartition]
  have htargetSimple :=
    selectorTailTarget_factorization_eq_upper_sub_fixed_sub_base_of_signedTargetLedger
      R certificate deltaStar p htarget
  unfold bankPaperCanonicalSelectorValuationDeficit
  simpa only [candidates] using
    sub_eq_zero.mpr (htargetSimple.trans hselectorMoment.symm)

/-! ## WithTop and rounded support wrappers -/

/-- Finite selector-tail support for the literal frozen-top source.  All
high-prime coordinates come from charged row totals.  The only low-prime
compatibility is the displayed reserve/selector-target equality. -/
theorem
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_deficitSupportedOnPrimeBand
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (hprime : ∀ p ∈ P, p.Prime)
    (Rhead : HeadSimplexReserve P)
    (I : PhysicalIntervals)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (Kphysical : PhysicalInterpolationTarget I)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime Rhead.exponent)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (hcompatibility : ∀ p : {p : Nat // p ∈ P},
      p.1 <= B.sampleData.W ->
        Rhead.target p =
          ((certificate.selectorTailTarget R
            (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
              Real))
    (hprefix : 2 * depth + 1 <= B.sampleData.W)
    (hchargeDvd :
      R.selectorTailCharge (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget)
    (hrows :
      let T := B.barycentricTargetOfPaperData
        I hlo hhi Rhead Kphysical
      BankPaperCanonicalChargedNonsmoothRowRealization
        (K := K) R certificate deltaStar
          (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha beta
              (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass)))
    (hcapacity : forall label,
      IsCompleteRoughLabel (yNat B.sampleData.n) label ->
        RoughCanonicalActiveNonexceptionalLabel
            B.sampleData.n deltaStar label ->
          RoughCanonicalPostchargeRowCapacity
            R certificate deltaStar K label) :
    let T := B.barycentricTargetOfPaperData
      I hlo hhi Rhead Kphysical
    BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha beta
          (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass)) := by
  dsimp only at hrows ⊢
  intro q hqPrime hqNotBand
  by_cases hqW : q <= B.sampleData.W
  · have hqHead : q ∈ primesUpTo B.sampleData.W :=
      mem_primesUpTo.mpr ⟨hqPrime, hqW⟩
    let p : {p : Nat // p ∈ P} := ⟨q, hhead hqHead⟩
    simpa only [p] using
      (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_selectorValuationDeficit_eq_zero_of_headPrime
        (K := K) B hprime Rhead I hlo hhi Kphysical hpattern
          R certificate (R.paperFixedExceptionalFactors deltaStar)
          deltaStar betaProt alpha beta hactiveSmooth p hqW
            (hcompatibility p hqW))
  · have hWq : B.sampleData.W < q := Nat.lt_of_not_ge hqW
    have hyq : yNat B.sampleData.n < q := by
      by_contra hnotY
      have hqy : q <= yNat B.sampleData.n := Nat.le_of_not_gt hnotY
      exact hqNotBand (mem_primeBand.mpr ⟨hqPrime, hWq, hqy⟩)
    exact
      bankPaperCanonicalSelectorValuationDeficit_eq_zero_of_chargedRows_of_yNat_lt
        (K := K) R certificate deltaStar
          (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha beta
              (bankPaperCanonicalScaledActiveSeed
                (B.barycentricTargetOfPaperData
                  I hlo hhi Rhead Kphysical)
                Rhead.activeMass))
          q hyq hrows hcapacity
            (bankPaperCanonicalSignedResidualTargetLedger_of_chargeDvd
              (W := B.sampleData.W) R certificate deltaStar
                hprefix hqPrime hWq hchargeDvd)

/-- The same finite support theorem after the nearest-integer zero-head
rounding.  The existing zero-head transport consumes the literal source
support proved immediately above. -/
theorem
    bankPaperCanonicalTopFrozenRoundedSourceSelector_deficitSupportedOnPrimeBand
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (hprime : ∀ p ∈ P, p.Prime)
    (Rhead : HeadSimplexReserve P)
    (I : PhysicalIntervals)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (Kphysical : PhysicalInterpolationTarget I)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime Rhead.exponent)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (hcompatibility : ∀ p : {p : Nat // p ∈ P},
      p.1 <= B.sampleData.W ->
        Rhead.target p =
          ((certificate.selectorTailTarget R
            (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
              Real))
    (hprefix : 2 * depth + 1 <= B.sampleData.W)
    (hchargeDvd :
      R.selectorTailCharge (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget)
    (hrows :
      let T := B.barycentricTargetOfPaperData
        I hlo hhi Rhead Kphysical
      BankPaperCanonicalChargedNonsmoothRowRealization
        (K := K) R certificate deltaStar
          (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha beta
              (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass)))
    (hcapacity : forall label,
      IsCompleteRoughLabel (yNat B.sampleData.n) label ->
        RoughCanonicalActiveNonexceptionalLabel
            B.sampleData.n deltaStar label ->
          RoughCanonicalPostchargeRowCapacity
            R certificate deltaStar K label) :
    let T := B.barycentricTargetOfPaperData
      I hlo hhi Rhead Kphysical
    BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha beta
          Rhead.activeMass) := by
  dsimp only at hrows ⊢
  let T :=
    B.barycentricTargetOfPaperData I hlo hhi Rhead Kphysical
  have hsource :
      BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
        (W := B.sampleData.W) R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta
            (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass)) :=
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_deficitSupportedOnPrimeBand
      (K := K) B hprime Rhead I hlo hhi Kphysical hpattern
        R certificate deltaStar betaProt alpha beta hactiveSmooth hhead
          hcompatibility hprefix hchargeDvd hrows hcapacity
  exact
    bankPaperCanonicalTopFrozenRoundedSourceSelector_deficitSupportedOnPrimeBand_of_qTilde
      (K := K) B R certificate
        (R.paperFixedExceptionalFactors deltaStar) T deltaStar betaProt
          alpha beta Rhead.activeMass hactiveSmooth hprime Rhead.exponent
            hpattern hhead hsource

end BankPaperRealization

end

end Erdos390.WholePaper
