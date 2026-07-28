import Erdos390.WholePaper.BankPaperCanonicalStructuredPrebridgeLedgerConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionEightActualDataConnector

/-!
# Concrete producer and mass choice for the two zero-head cells

This file isolates the two finite facts needed by the structured
prebridge producer.

First, a sample in the zero head cell is coprime to the complete head
modulus.  Hence it belongs to the guarded broad correction pool as soon as
its physical interval lies below the literal broad cutoff and every sample
value is known pointwise to avoid the canonical guard set.  In particular, no
cardinality surplus theorem is used to prove membership.

Second, the height adjustment has a canonical symmetric realization: put
`-d / 2` in each of the two physical zero-head cells.  Its total change is
the integer `-d`, and the exact lower and upper coordinate-capacity
conditions reduce to two scalar inequalities involving the old total cell
mass and the guard-deleted cell cardinality.

The nearest-integer normalization from `qTilde` to `q0` is recorded
separately.  That first change is generally real rather than integral; the
integer prebridge ledger applies to the subsequent height change from
`q0` to `q0 - d`.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeSums

noncomputable section

namespace BankPaperRealization

/-! ## The fixed physical intervals eventually lie below the broad cutoff -/

/-- A fixed endpoint strictly below `2` eventually leaves enough room for
the whole `K * upperTailLength` top strip.  This is the literal numerical
inequality used in the paper to put the upper physical pool below
`2n-Kh`. -/
theorem eventually_physicalBound_le_two_mul_sub_upperTailLength
    (K : Nat) {c b : Real} (hc : 0 < c) (hb0 : 0 <= b) (hbTwo : b < 2) :
    ∀ᶠ n : Nat in atTop,
      physicalBound b n <= 2 * n - K * upperTailLength c n := by
  have htailEvent : ∀ᶠ n : Nat in atTop,
      (((K * upperTailLength c n : Nat) : Real) / (n : Real)) < 2 - b := by
    have hT := (upperTailLength_ratio_tendsto_zero hc).const_mul (K : Real)
    have hzeroLt : (K : Real) * 0 < 2 - b := by
      simpa using sub_pos.mpr hbTwo
    have hsmall := hT.eventually
      (eventually_lt_nhds hzeroLt)
    filter_upwards [hsmall] with n hn
    have hn' :
        (K : Real) *
            ((upperTailLength c n : Real) / (n : Real)) < 2 - b := hn
    simpa [Nat.cast_mul, mul_div_assoc] using hn'
  filter_upwards [htailEvent, eventually_gt_atTop 0] with n htail hn
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have htailCross :
      ((K * upperTailLength c n : Nat) : Real) <
        (2 - b) * (n : Real) :=
    (div_lt_iff₀ hnReal).mp htail
  have hfloor :
      (physicalBound b n : Real) <= b * (n : Real) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hb0 (by positivity))
  have hsumReal :
      (physicalBound b n : Real) +
          (K * upperTailLength c n : Nat) < 2 * (n : Real) := by
    calc
      (physicalBound b n : Real) +
          (K * upperTailLength c n : Nat) <=
        b * (n : Real) + (K * upperTailLength c n : Nat) :=
          add_le_add hfloor le_rfl
      _ < 2 * (n : Real) := by nlinarith
  have hsumNat :
      physicalBound b n + K * upperTailLength c n <= 2 * n := by
    exact_mod_cast hsumReal.le
  omega

/-- Simultaneous two-sign form for the paper's fixed physical intervals. -/
theorem eventually_physicalIntervals_upperBound_le_two_mul_sub_upperTailLength
    (I : PhysicalIntervals) (K : Nat) {c : Real} (hc : 0 < c)
    (hupperStrict : forall sigma, I.upper sigma < 2) :
    ∀ᶠ n : Nat in atTop, forall sigma,
      physicalBound (I.upper sigma) n <=
        2 * n - K * upperTailLength c n := by
  have hminus :=
    eventually_physicalBound_le_two_mul_sub_upperTailLength K hc
      (le_of_lt ((I.lower_pos .minus).trans (I.lower_lt_upper .minus)))
      (hupperStrict .minus)
  have hplus :=
    eventually_physicalBound_le_two_mul_sub_upperTailLength K hc
      (le_of_lt ((I.lower_pos .plus).trans (I.lower_lt_upper .plus)))
      (hupperStrict .plus)
  filter_upwards [hminus, hplus] with n hnMinus hnPlus
  intro sigma
  cases sigma with
  | minus => exact hnMinus
  | plus => exact hnPlus

/-! ## The zero head pattern produces head-freeness -/

/-- A structured sample carrying the zero simplex tag is coprime to the
product of every prime at most its head cutoff, provided those primes occur
in the concrete head pattern. -/
theorem bankPaperCanonicalZeroHeadValue_coprime_roughHeadModulus
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : D.pattern = PaperHeadSimplex.pattern P hprime E)
    (hhead : primesUpTo D.W ⊆ P)
    (m : D.Sample) (sigma : PhysicalSign)
    (hcell : D.cellOf m = (none, sigma)) :
    Nat.Coprime (D.value m) (roughHeadModulus D.W) := by
  rw [roughHeadModulus, Nat.coprime_prod_right_iff]
  intro p hp
  have hpP : p ∈ P := hhead hp
  have hpPattern : p ∈ (D.pattern (D.cellOf m).1).primes := by
    rw [hpattern]
    exact hpP
  have hmatch := D.value_matches_head m p hpPattern
  have hzero : (D.value m).factorization p = 0 := by
    simpa [hpattern, hcell, PaperHeadSimplex.pattern] using hmatch
  apply Nat.Coprime.symm
  apply ((mem_primesUpTo.mp hp).1.coprime_iff_not_dvd).mpr
  intro hpDvd
  have hpos := (mem_primesUpTo.mp hp).1.factorization_pos_of_dvd
    (Nat.ne_of_gt (D.value_pos m)) hpDvd
  omega

/-- The exact finite producer for membership in the guarded broad pool.
The two numerical premises are precisely membership in `(n,2n-Kh]`; head
freeness and smooth label `1` are derived, while guard exclusion is supplied
pointwise. -/
theorem bankPaperCanonicalZeroHeadValue_mem_guardedBroadCorrectionPool
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
    (deltaStar : Real)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime E)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (m : B.sampleData.Sample) (sigma : PhysicalSign)
    (hcell : B.sampleData.cellOf m = (none, sigma))
    (hlower : B.sampleData.n < B.sampleData.value m)
    (hupper : B.sampleData.value m <=
      2 * B.sampleData.n -
        K * upperTailLength c B.sampleData.n) :
    B.sampleData.value m ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 := by
  rw [BankPaperRealization.roughCanonicalGuardedBroadCorrectionPool,
    Finset.mem_sdiff]
  constructor
  · apply mem_completeRoughRowFiber.mpr
    constructor
    · apply mem_roughHeadFree.mpr
      constructor
      · rw [roughBroadLowerBlock, Finset.mem_Ioc]
        exact ⟨hlower, hupper⟩
      · exact bankPaperCanonicalZeroHeadValue_coprime_roughHeadModulus
          B.sampleData hprime E hpattern hhead m sigma hcell
    · exact (completeRoughLabel_eq_one_iff_mem_smoothNumbers
        (B.sampleData.value_pos m)).mpr
          (B.sampleData.value_mem_smoothNumbers m)
  · exact hnotGuard m

/-- Fixed physical intervals discharge the lower broad inequality.  The
only extra endpoint condition beyond the existing structured-support
theorem is the literal upper gap
`floor (b_sigma n) <= 2n-Kh`. -/
theorem bankPaperCanonicalZeroHeadValue_mem_guardedBroadCorrectionPool_of_physicalIntervals
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
    (deltaStar : Real)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime E)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hupperBroad : forall sigma,
      physicalBound (I.upper sigma) B.sampleData.n <=
        2 * B.sampleData.n -
          K * upperTailLength c B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (m : B.sampleData.Sample) (sigma : PhysicalSign)
    (hcell : B.sampleData.cellOf m = (none, sigma)) :
    B.sampleData.value m ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 := by
  have hbounds :=
    bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
      B I hlowerOne hupperTwo hlo hhi
  apply bankPaperCanonicalZeroHeadValue_mem_guardedBroadCorrectionPool
    B R certificate deltaStar hprime E hpattern hhead hnotGuard
      m sigma hcell (hbounds.1 m)
  calc
    B.sampleData.value m <=
        B.sampleData.hi (B.sampleData.cellOf m).2 :=
      B.sampleData.value_le_hi m
    _ = physicalBound (I.upper sigma) B.sampleData.n := by
      rw [hcell, hhi]
    _ <= 2 * B.sampleData.n -
        K * upperTailLength c B.sampleData.n := hupperBroad sigma

/-- Both literal zero-head physical cells are therefore produced at once.
This is the exact pair of hypotheses consumed by the two-cell prebridge
connector. -/
theorem bankPaperCanonicalTwoZeroHeadCells_subset_guardedBroadCorrectionPool_of_physicalIntervals
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
    (deltaStar : Real)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime E)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hupperBroad : forall sigma,
      physicalBound (I.upper sigma) B.sampleData.n <=
        2 * B.sampleData.n -
          K * upperTailLength c B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar) :
    (forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1) ∧
      forall m : B.sampleData.Sample,
        B.sampleData.cellOf m = (none, .plus) ->
          B.sampleData.value m ∈
            R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar B.sampleData.W K 1 := by
  constructor
  · intro m hm
    exact
      bankPaperCanonicalZeroHeadValue_mem_guardedBroadCorrectionPool_of_physicalIntervals
        B R certificate deltaStar hprime E hpattern hhead I
          hlowerOne hupperTwo hlo hhi hupperBroad hnotGuard
          m .minus hm
  · intro m hm
    exact
      bankPaperCanonicalZeroHeadValue_mem_guardedBroadCorrectionPool_of_physicalIntervals
        B R certificate deltaStar hprime E hpattern hhead I
          hlowerOne hupperTwo hlo hhi hupperBroad hnotGuard
          m .plus hm

/-! ## Canonical symmetric mass choices -/

/-- Half of the integer height change, assigned to each physical copy of
the zero head cell. -/
def bankPaperCanonicalSymmetricHeightCellMass (d : Int) : Real :=
  -(d : Real) / 2

@[simp] theorem bankPaperCanonicalSymmetricHeightCellMass_add_self
    (d : Int) :
    bankPaperCanonicalSymmetricHeightCellMass d +
        bankPaperCanonicalSymmetricHeightCellMass d =
      ((-d : Int) : Real) := by
  unfold bankPaperCanonicalSymmetricHeightCellMass
  push_cast
  ring

/-- Starting from the initialized active mass `q0`, the symmetric height
rebalance has literal active mass `q0-d`. -/
theorem bankPaperCanonicalLiteralActiveMass_symmetricHeightRebalance
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (T : BarycentricTarget D) (q0 : Real) (d : Int) :
    bankPaperCanonicalLiteralActiveMass D
        (bankPaperCanonicalTwoZeroHeadCellRebalance D
          (bankPaperCanonicalScaledActiveSeed T q0)
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d)) =
      q0 - (d : Real) := by
  rw [bankPaperCanonicalLiteralActiveMass_rebalancedScaledActiveSeed]
  unfold bankPaperCanonicalSymmetricHeightCellMass
  ring

/-- The symmetric normalization-and-height change relative to the actual
post-guard mass `qTilde`.  Unlike the height-only change, this quantity is
not asserted to be an integer. -/
def bankPaperCanonicalSymmetricInitialAndHeightCellMass
    (mFrozen qTilde : Real) (d : Int) : Real :=
  (bankPaperCanonicalSmoothActiveMassAt mFrozen qTilde d - qTilde) / 2

@[simp] theorem bankPaperCanonicalSymmetricInitialAndHeightCellMass_add_self
    (mFrozen qTilde : Real) (d : Int) :
    bankPaperCanonicalSymmetricInitialAndHeightCellMass
          mFrozen qTilde d +
        bankPaperCanonicalSymmetricInitialAndHeightCellMass
          mFrozen qTilde d =
      bankPaperCanonicalSmoothActiveMassAt mFrozen qTilde d - qTilde := by
  unfold bankPaperCanonicalSymmetricInitialAndHeightCellMass
  ring

/-- Applying the preceding combined change to a `qTilde`-scaled seed gives
the exact final Section 8 active mass. -/
theorem bankPaperCanonicalLiteralActiveMass_symmetricInitialAndHeightRebalance
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (T : BarycentricTarget D) (mFrozen qTilde : Real) (d : Int) :
    bankPaperCanonicalLiteralActiveMass D
        (bankPaperCanonicalTwoZeroHeadCellRebalance D
          (bankPaperCanonicalScaledActiveSeed T qTilde)
          (bankPaperCanonicalSymmetricInitialAndHeightCellMass
            mFrozen qTilde d)
          (bankPaperCanonicalSymmetricInitialAndHeightCellMass
            mFrozen qTilde d)) =
      bankPaperCanonicalSmoothActiveMassAt mFrozen qTilde d := by
  rw [bankPaperCanonicalLiteralActiveMass_rebalancedScaledActiveSeed,
    add_assoc,
    bankPaperCanonicalSymmetricInitialAndHeightCellMass_add_self]
  ring

/-- The existing whole-row prebridge producer now has a canonical mass
choice: the integer row change is exactly `-d`. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_symmetricHeight
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
    (deltaStar betaProt : Real)
    (oldSeed : B.sampleData.Sample -> Real) (d : Int)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hminus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hplus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1) :
    BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger (K := K)
      B R certificate deltaStar betaProt
        (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed)
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d)) := by
  apply
    bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_twoZeroHeadCells
      (K := K) B R certificate deltaStar betaProt oldSeed
        (bankPaperCanonicalSymmetricHeightCellMass d)
        (bankPaperCanonicalSymmetricHeightCellMass d) (-d)
        hactiveSmooth hminus hplus
  exact bankPaperCanonicalSymmetricHeightCellMass_add_self d

/-! ## Exact finite coordinate capacity -/

/-- A symmetric change of arbitrary real total-cell mass has the expected
pointwise formula on either zero-head cell.  This is the common finite
algebra behind both the nearest-integer normalization and the integer
height adjustment. -/
theorem bankPaperCanonicalSymmetricRebalance_apply_of_zeroHeadCell
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (T : BarycentricTarget D) (q mass : Real)
    (m : D.Sample) (sigma : PhysicalSign)
    (hcell : D.cellOf m = (none, sigma)) :
    bankPaperCanonicalTwoZeroHeadCellRebalance D
        (bankPaperCanonicalScaledActiveSeed T q) mass mass m =
      (q * T.baseline.cellMass (none, sigma) + mass) /
        Fintype.card (D.SampleAt (none, sigma)) := by
  cases sigma <;>
    simp [bankPaperCanonicalTwoZeroHeadCellRebalance,
      bankPaperCanonicalUniformCellIncrement,
      bankPaperCanonicalScaledActiveSeed,
      BaselineAllocation.baseWeight, hcell] <;>
    ring

/-- On either zero-head cell the symmetric height rebalance is the old
total cell mass minus `d/2`, divided by the literal guard-deleted cell
cardinality. -/
theorem bankPaperCanonicalSymmetricHeightRebalance_apply_of_zeroHeadCell
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (T : BarycentricTarget D) (q0 : Real) (d : Int)
    (m : D.Sample) (sigma : PhysicalSign)
    (hcell : D.cellOf m = (none, sigma)) :
    bankPaperCanonicalTwoZeroHeadCellRebalance D
        (bankPaperCanonicalScaledActiveSeed T q0)
        (bankPaperCanonicalSymmetricHeightCellMass d)
        (bankPaperCanonicalSymmetricHeightCellMass d) m =
      (q0 * T.baseline.cellMass (none, sigma) - (d : Real) / 2) /
        Fintype.card (D.SampleAt (none, sigma)) := by
  rw [bankPaperCanonicalSymmetricRebalance_apply_of_zeroHeadCell
    D T q0 (bankPaperCanonicalSymmetricHeightCellMass d) m sigma hcell]
  unfold bankPaperCanonicalSymmetricHeightCellMass
  ring

/-- Pointwise form of the combined normalization-and-height change from
the actual post-guard mass `qTilde`. -/
theorem bankPaperCanonicalSymmetricInitialAndHeightRebalance_apply_of_zeroHeadCell
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (T : BarycentricTarget D) (mFrozen qTilde : Real) (d : Int)
    (m : D.Sample) (sigma : PhysicalSign)
    (hcell : D.cellOf m = (none, sigma)) :
    bankPaperCanonicalTwoZeroHeadCellRebalance D
        (bankPaperCanonicalScaledActiveSeed T qTilde)
        (bankPaperCanonicalSymmetricInitialAndHeightCellMass
          mFrozen qTilde d)
        (bankPaperCanonicalSymmetricInitialAndHeightCellMass
          mFrozen qTilde d) m =
      (qTilde * T.baseline.cellMass (none, sigma) +
          bankPaperCanonicalSymmetricInitialAndHeightCellMass
            mFrozen qTilde d) /
        Fintype.card (D.SampleAt (none, sigma)) := by
  exact bankPaperCanonicalSymmetricRebalance_apply_of_zeroHeadCell
    D T qTilde
      (bankPaperCanonicalSymmetricInitialAndHeightCellMass
        mFrozen qTilde d) m sigma hcell

/-- Exact removal-capacity criterion for either symmetric zero-head cell.
It is a total-mass inequality, before division by the cell cardinality. -/
theorem bankPaperCanonicalSymmetricHeightRebalance_nonneg_of_cellMass
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (T : BarycentricTarget D) (q0 : Real) (d : Int)
    (m : D.Sample) (sigma : PhysicalSign)
    (hcell : D.cellOf m = (none, sigma))
    (hremove : (d : Real) / 2 <=
      q0 * T.baseline.cellMass (none, sigma)) :
    0 <= bankPaperCanonicalTwoZeroHeadCellRebalance D
      (bankPaperCanonicalScaledActiveSeed T q0)
      (bankPaperCanonicalSymmetricHeightCellMass d)
      (bankPaperCanonicalSymmetricHeightCellMass d) m := by
  rw [bankPaperCanonicalSymmetricHeightRebalance_apply_of_zeroHeadCell
    D T q0 d m sigma hcell]
  exact div_nonneg (sub_nonneg.mpr hremove) (by positivity)

/-- Exact addition-capacity criterion for either symmetric zero-head cell.
The right side is the total room below the selector ceiling after reserving
the protected weight `betaProt/L`. -/
theorem bankPaperCanonicalSymmetricHeightRebalance_protected_le_one_of_cellMass
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (T : BarycentricTarget B.sampleData) (q0 : Real) (d : Int)
    (betaProt : Real) (m : B.sampleData.Sample) (sigma : PhysicalSign)
    (hcell : B.sampleData.cellOf m = (none, sigma))
    (hadd : q0 * T.baseline.cellMass (none, sigma) - (d : Real) / 2 <=
      (Fintype.card (B.sampleData.SampleAt (none, sigma)) : Real) *
        (1 - betaProt / B.L)) :
    betaProt / B.L +
        bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q0)
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d) m <= 1 := by
  rw [bankPaperCanonicalSymmetricHeightRebalance_apply_of_zeroHeadCell
    B.sampleData T q0 d m sigma hcell]
  have hcard : 0 <
      (Fintype.card (B.sampleData.SampleAt (none, sigma)) : Real) := by
    exact_mod_cast B.sampleData.sampleAt_card_pos (none, sigma)
  have hquot :
      (q0 * T.baseline.cellMass (none, sigma) - (d : Real) / 2) /
          Fintype.card (B.sampleData.SampleAt (none, sigma)) <=
        1 - betaProt / B.L := by
    apply (div_le_iff₀ hcard).2
    simpa only [mul_comm] using hadd
  linarith

/-- Exact removal criterion for the combined nearest-integer and height
change.  The displayed numerator is the final total mass assigned to this
one zero-head physical cell. -/
theorem bankPaperCanonicalSymmetricInitialAndHeightRebalance_nonneg_of_cellMass
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (T : BarycentricTarget D) (mFrozen qTilde : Real) (d : Int)
    (m : D.Sample) (sigma : PhysicalSign)
    (hcell : D.cellOf m = (none, sigma))
    (hremove : 0 <= qTilde * T.baseline.cellMass (none, sigma) +
      bankPaperCanonicalSymmetricInitialAndHeightCellMass
        mFrozen qTilde d) :
    0 <= bankPaperCanonicalTwoZeroHeadCellRebalance D
      (bankPaperCanonicalScaledActiveSeed T qTilde)
      (bankPaperCanonicalSymmetricInitialAndHeightCellMass
        mFrozen qTilde d)
      (bankPaperCanonicalSymmetricInitialAndHeightCellMass
        mFrozen qTilde d) m := by
  rw [bankPaperCanonicalSymmetricInitialAndHeightRebalance_apply_of_zeroHeadCell
    D T mFrozen qTilde d m sigma hcell]
  exact div_nonneg hremove (by positivity)

/-- Exact addition criterion for the same combined change.  Together with
the preceding theorem this is the literal finite `[0,1]` capacity problem
left to the Section 8 asymptotic estimates. -/
theorem bankPaperCanonicalSymmetricInitialAndHeightRebalance_protected_le_one_of_cellMass
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (T : BarycentricTarget B.sampleData)
    (mFrozen qTilde : Real) (d : Int) (betaProt : Real)
    (m : B.sampleData.Sample) (sigma : PhysicalSign)
    (hcell : B.sampleData.cellOf m = (none, sigma))
    (hadd : qTilde * T.baseline.cellMass (none, sigma) +
        bankPaperCanonicalSymmetricInitialAndHeightCellMass
          mFrozen qTilde d <=
      (Fintype.card (B.sampleData.SampleAt (none, sigma)) : Real) *
        (1 - betaProt / B.L)) :
    betaProt / B.L +
        bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T qTilde)
          (bankPaperCanonicalSymmetricInitialAndHeightCellMass
            mFrozen qTilde d)
          (bankPaperCanonicalSymmetricInitialAndHeightCellMass
            mFrozen qTilde d) m <= 1 := by
  rw [bankPaperCanonicalSymmetricInitialAndHeightRebalance_apply_of_zeroHeadCell
    B.sampleData T mFrozen qTilde d m sigma hcell]
  have hcard : 0 <
      (Fintype.card (B.sampleData.SampleAt (none, sigma)) : Real) := by
    exact_mod_cast B.sampleData.sampleAt_card_pos (none, sigma)
  have hquot :
      (qTilde * T.baseline.cellMass (none, sigma) +
          bankPaperCanonicalSymmetricInitialAndHeightCellMass
            mFrozen qTilde d) /
          Fintype.card (B.sampleData.SampleAt (none, sigma)) <=
        1 - betaProt / B.L := by
    apply (div_le_iff₀ hcard).2
    simpa only [mul_comm] using hadd
  linarith

end BankPaperRealization

end

end Erdos390.WholePaper
