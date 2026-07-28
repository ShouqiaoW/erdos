import Erdos390.WholePaper.BankPaperCanonicalSectionEightTopFrozenInitialMassConnector
import Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellProducerConnector

/-!
# Nearest-integer source state for the frozen-top selector

The finite frozen-top source at mass `qTilde` has the paper's literal
smooth-row mass, but that mass need not be an integer.  The initialization
step replaces `qTilde` by

`q0 = nearestInteger(mFrozen + qTilde) - mFrozen`.

This connector proves the exact part of that handoff:

* changing the scaled seed from `qTilde` to `q0` changes no nonsmooth row;
* the new smooth-row total is the declared nearest integer;
* the charged nonsmooth-row equations therefore imply integrality of every
  complete rough row; and
* feasibility and exact target agreement outside the tangent prime band
  then package the result as `BankPaperCanonicalSelectorSourceState`.

The last two properties are retained as explicit premises.  They are not
consequences of row-mass rounding: feasibility is pointwise, while target
agreement is a prime-valuation identity.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## The exact frozen mass and nearest-integer source -/

/-- The part of the guarded smooth-row mass which is unchanged when the
active seed mass is replaced by its nearest-integer normalization. -/
def bankPaperCanonicalTopFrozenSmoothFrozenMass
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
    (deltaStar betaProt alpha : Real) : Real :=
  ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
    roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
      (upperTailLength c B.sampleData.n) K alpha betaProt B.L a

/-- The paper's normalized active mass `q0`, specialized to the literal
frozen-top guarded smooth row. -/
def bankPaperCanonicalTopFrozenRoundedActiveMass
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
    (deltaStar betaProt alpha qTilde : Real) : Real :=
  bankPaperCanonicalSmoothInitialActiveMass
    (bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K)
      B R certificate deltaStar betaProt alpha)
    qTilde

/-- Half of the nearest-integer mass correction.  The paper puts one copy
in each physical realization of the zero head cell, so no nonzero head
moment is changed. -/
def bankPaperCanonicalTopFrozenNearestIntegerCellMass
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
    (deltaStar betaProt alpha qTilde : Real) : Real :=
  (bankPaperCanonicalTopFrozenRoundedActiveMass (K := K)
      B R certificate deltaStar betaProt alpha qTilde - qTilde) / 2

/-- Identification with the already audited combined
normalization-and-height cell mass at height `d = 0`.  This is the form
consumed by the existing zero-cell capacity estimates. -/
theorem bankPaperCanonicalTopFrozenNearestIntegerCellMass_eq_symmetricInitial
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
    (deltaStar betaProt alpha qTilde : Real) :
    bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
        B R certificate deltaStar betaProt alpha qTilde =
      bankPaperCanonicalSymmetricInitialAndHeightCellMass
        (bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K)
          B R certificate deltaStar betaProt alpha)
        qTilde 0 := by
  unfold bankPaperCanonicalTopFrozenNearestIntegerCellMass
  unfold bankPaperCanonicalTopFrozenRoundedActiveMass
  unfold bankPaperCanonicalSymmetricInitialAndHeightCellMass
  unfold bankPaperCanonicalSmoothActiveMassAt
  norm_num

/-- The actual nearest-integer seed.  It starts from the literal
`qTilde`-scaled barycentric seed and changes only the two zero-head cells. -/
def bankPaperCanonicalTopFrozenRoundedActiveSeed
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
    (deltaStar betaProt alpha qTilde : Real) :
    B.sampleData.Sample -> Real :=
  bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
    (bankPaperCanonicalScaledActiveSeed T qTilde)
    (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
      B R certificate deltaStar betaProt alpha qTilde)
    (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
      B R certificate deltaStar betaProt alpha qTilde)

/-- The frozen-top source after replacing the literal post-guard active
mass `qTilde` by the two-zero-cell nearest-integer correction. -/
def bankPaperCanonicalTopFrozenRoundedSourceSelector
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
    (deltaStar betaProt alpha betaTotal qTilde : Real) : Nat -> Real :=
  bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
    B R certificate deltaStar betaProt alpha betaTotal
      (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
        B R certificate T deltaStar betaProt alpha qTilde)

/-! ## Nonsmooth rows are independent of the active seed -/

/-- On every nonsmooth guarded row, changing the structured active seed is
pointwise invisible.  Active nonexceptional rows use the same corrected
weight for both seeds, while exceptional rows are zero for both seeds. -/
theorem bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_eq_of_mem_nonsmoothRow
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
    (deltaStar betaProt alpha betaTotal : Real)
    (oldSeed₁ oldSeed₂ : B.sampleData.Sample -> Real) {a : Nat}
    (hlabel : label ≠ 1)
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label) :
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal oldSeed₁ a =
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal oldSeed₂ a := by
  have haLabel :
      completeRoughLabel (yNat B.sampleData.n) a = label :=
    (mem_completeRoughRowFiber.mp ha).2
  have hnotSmoothPool :
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 := by
    intro haSmooth
    have haSmoothRow :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
      R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar B.sampleData.W K 1 haSmooth
    have haSmoothLabel :
        completeRoughLabel (yNat B.sampleData.n) a = 1 :=
      (mem_completeRoughRowFiber.mp haSmoothRow).2
    exact hlabel (haLabel.symm.trans haSmoothLabel)
  simp only [bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
    bankPaperCanonicalTwoZeroHeadCellSourceSelector, hnotSmoothPool,
    if_false, bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop,
    haLabel, hlabel]

/-- On an active nonexceptional nonsmooth guarded row, the frozen-top source
is the explicit postcharge corrected row weight. -/
theorem bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_nonsmoothRow
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
    (deltaStar betaProt alpha betaTotal : Real)
    (oldSeed : B.sampleData.Sample -> Real) {a : Nat}
    (hactive :
      RoughCanonicalActiveNonexceptionalLabel
        B.sampleData.n deltaStar label)
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label) :
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal oldSeed a =
      R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
        deltaStar B.sampleData.W K label alpha betaTotal B.L a := by
  have haLabel :
      completeRoughLabel (yNat B.sampleData.n) a = label :=
    (mem_completeRoughRowFiber.mp ha).2
  have hnotSmoothPool :
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 := by
    intro haSmooth
    have haSmoothRow :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
      R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar B.sampleData.W K 1 haSmooth
    have haSmoothLabel :
        completeRoughLabel (yNat B.sampleData.n) a = 1 :=
      (mem_completeRoughRowFiber.mp haSmoothRow).2
    exact hactive.1 (haLabel.symm.trans haSmoothLabel)
  have haNotOne :
      completeRoughLabel (yNat B.sampleData.n) a ≠ 1 := by
    intro haOne
    exact hactive.1 (haLabel.symm.trans haOne)
  have hnonexceptional :
      ¬ RoughCanonicalExceptionalLabel
        B.sampleData.n deltaStar label :=
    not_lt_of_ge hactive.2
  unfold bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
  unfold bankPaperCanonicalTwoZeroHeadCellSourceSelector
  rw [if_neg hnotSmoothPool]
  unfold bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop
  rw [if_neg haNotOne, haLabel, if_neg hnonexceptional]

/-- On an exceptional nonsmooth guarded row, the frozen-top source is
pointwise zero. -/
theorem bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_exceptionalNonsmoothRow
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
    (deltaStar betaProt alpha betaTotal : Real)
    (oldSeed : B.sampleData.Sample -> Real) {a : Nat}
    (hlabel : label ≠ 1)
    (hexceptional :
      RoughCanonicalExceptionalLabel B.sampleData.n deltaStar label)
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label) :
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal oldSeed a = 0 := by
  have haLabel :
      completeRoughLabel (yNat B.sampleData.n) a = label :=
    (mem_completeRoughRowFiber.mp ha).2
  have hnotSmoothPool :
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 := by
    intro haSmooth
    have haSmoothRow :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
      R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar B.sampleData.W K 1 haSmooth
    have haSmoothLabel :
        completeRoughLabel (yNat B.sampleData.n) a = 1 :=
      (mem_completeRoughRowFiber.mp haSmoothRow).2
    exact hlabel (haLabel.symm.trans haSmoothLabel)
  have haNotOne :
      completeRoughLabel (yNat B.sampleData.n) a ≠ 1 := by
    intro haOne
    exact hlabel (haLabel.symm.trans haOne)
  unfold bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
  unfold bankPaperCanonicalTwoZeroHeadCellSourceSelector
  rw [if_neg hnotSmoothPool]
  unfold bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop
  rw [if_neg haNotOne, haLabel, if_pos hexceptional]

/-- Replacing `qTilde` by `q0` is pointwise invisible on every nonsmooth
guarded row. -/
theorem bankPaperCanonicalTopFrozenRoundedSourceSelector_eq_qTildeSource_of_mem_nonsmoothRow
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
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    {a : Nat} (hlabel : label ≠ 1)
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label) :
    bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha betaTotal qTilde a =
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal
          (bankPaperCanonicalScaledActiveSeed T qTilde) a := by
  unfold bankPaperCanonicalTopFrozenRoundedSourceSelector
  exact
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_eq_of_mem_nonsmoothRow
      (K := K) B R certificate deltaStar betaProt alpha betaTotal
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate T deltaStar betaProt alpha qTilde)
        (bankPaperCanonicalScaledActiveSeed T qTilde) hlabel ha

/-! ## Exact smooth and nonsmooth row ledgers -/

/-- The two zero-head corrections replace the literal active mass
`qTilde` by exactly `q0`. -/
theorem bankPaperCanonicalLiteralActiveMass_topFrozenRoundedActiveSeed
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
    (deltaStar betaProt alpha qTilde : Real) :
    bankPaperCanonicalLiteralActiveMass B.sampleData
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate T deltaStar betaProt alpha qTilde) =
      bankPaperCanonicalTopFrozenRoundedActiveMass (K := K)
        B R certificate deltaStar betaProt alpha qTilde := by
  unfold bankPaperCanonicalTopFrozenRoundedActiveSeed
  rw [bankPaperCanonicalLiteralActiveMass_rebalancedScaledActiveSeed]
  unfold bankPaperCanonicalTopFrozenNearestIntegerCellMass
  ring

/-- The nearest-integer correction preserves every head-simplex valuation
moment because both increments are placed in the zero head cell. -/
theorem sum_bankPaperCanonicalTopFrozenRoundedActiveSeed_mul_headValuation_eq_qTilde
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
    (deltaStar betaProt alpha qTilde : Real)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime E)
    (p : {p : Nat // p ∈ P}) :
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde m *
          valuation p.1 (B.sampleData.value m)) =
      ∑ m : B.sampleData.Sample,
        bankPaperCanonicalScaledActiveSeed T qTilde m *
          valuation p.1 (B.sampleData.value m) := by
  unfold bankPaperCanonicalTopFrozenRoundedActiveSeed
  exact
    sum_bankPaperCanonicalTwoZeroHeadCellRebalance_mul_valuation_eq
      B.sampleData hprime E hpattern
        (bankPaperCanonicalScaledActiveSeed T qTilde)
        (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
          B R certificate deltaStar betaProt alpha qTilde)
        (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
          B R certificate deltaStar betaProt alpha qTilde)
        p

/-- Ambient form of the same head-moment preservation on any finite support
containing every structured active value. -/
theorem sum_bankPaperCanonicalTopFrozenRoundedAmbient_mul_headValuation_eq_qTilde
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
    (deltaStar betaProt alpha qTilde : Real)
    (support : Finset Nat)
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈ support)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime E)
    (p : {p : Nat // p ∈ P}) :
    (∑ a ∈ support,
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate T deltaStar betaProt alpha qTilde) a *
          valuation p.1 a) =
      ∑ a ∈ support,
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalScaledActiveSeed T qTilde) a *
          valuation p.1 a := by
  rw [
    sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
      B.sampleData
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate T deltaStar betaProt alpha qTilde)
        support hvalues p.1,
    sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
      B.sampleData (bankPaperCanonicalScaledActiveSeed T qTilde)
        support hvalues p.1]
  exact
    sum_bankPaperCanonicalTopFrozenRoundedActiveSeed_mul_headValuation_eq_qTilde
      (K := K) B R certificate T deltaStar betaProt alpha qTilde
        hprime E hpattern p

/-- The rounded frozen-top smooth row has exactly the nearest-integer total
used to define `q0`. -/
theorem sum_bankPaperCanonicalTopFrozenRoundedSourceSelector_smoothRow
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
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha betaTotal qTilde a) =
      (bankPaperCanonicalSmoothInitialQuota
        (bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K)
          B R certificate deltaStar betaProt alpha)
        qTilde : Real) := by
  have hsum :=
    sum_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_smoothRow_eq_frozenRaw_add_activeMass
      (K := K) (deltaStar := deltaStar) (betaProt := betaProt)
      (alpha := alpha) (beta := betaTotal) B R certificate
      (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
        B R certificate T deltaStar betaProt alpha qTilde)
      hvalues
  calc
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha betaTotal qTilde a) =
        bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K)
            B R certificate deltaStar betaProt alpha +
          bankPaperCanonicalLiteralActiveMass B.sampleData
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate T deltaStar betaProt alpha qTilde) := by
      simpa only [bankPaperCanonicalTopFrozenRoundedSourceSelector,
        bankPaperCanonicalTopFrozenSmoothFrozenMass] using hsum
    _ = bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K)
          B R certificate deltaStar betaProt alpha +
        bankPaperCanonicalTopFrozenRoundedActiveMass (K := K)
          B R certificate deltaStar betaProt alpha qTilde := by
      rw [bankPaperCanonicalLiteralActiveMass_topFrozenRoundedActiveSeed]
    _ = (bankPaperCanonicalSmoothInitialQuota
          (bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K)
            B R certificate deltaStar betaProt alpha)
          qTilde : Real) := by
      unfold bankPaperCanonicalTopFrozenRoundedActiveMass
      unfold bankPaperCanonicalSmoothInitialActiveMass
      ring

/-- The charged nonsmooth-row realization at `qTilde` transports unchanged
to the nearest-integer normalized source. -/
theorem bankPaperCanonicalChargedNonsmoothRowRealization_topFrozenRounded_of_qTilde
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
    (hrows : BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K) R certificate deltaStar
        (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde))) :
    BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K) R certificate deltaStar
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde) := by
  constructor
  · intro label hlabelMem hactive
    calc
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate T deltaStar betaProt alpha betaTotal
              qTilde a) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha betaTotal
              (bankPaperCanonicalScaledActiveSeed T qTilde) a := by
          apply Finset.sum_congr rfl
          intro a ha
          exact
            bankPaperCanonicalTopFrozenRoundedSourceSelector_eq_qTildeSource_of_mem_nonsmoothRow
              (K := K) B R certificate T deltaStar betaProt alpha
                betaTotal qTilde hactive.1 ha
      _ = R.roughCanonicalPostchargeRowTarget deltaStar label :=
        hrows.1 label hlabelMem hactive
  · intro label hlabelMem hlabel hexceptional
    calc
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate T deltaStar betaProt alpha betaTotal
              qTilde a) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha betaTotal
              (bankPaperCanonicalScaledActiveSeed T qTilde) a := by
          apply Finset.sum_congr rfl
          intro a ha
          exact
            bankPaperCanonicalTopFrozenRoundedSourceSelector_eq_qTildeSource_of_mem_nonsmoothRow
              (K := K) B R certificate T deltaStar betaProt alpha
                betaTotal qTilde hlabel ha
      _ = 0 := hrows.2 label hlabelMem hlabel hexceptional

/-! ## Exact feasibility transport through the two zero cells -/

/-- Feasibility of the literal `qTilde` frozen-top source transports to the
nearest-integer source once the two changed zero-head cells satisfy their
literal capacities.  All other structured coordinates are unchanged, and
coordinates outside the structured image have zero old and new ambient
seed weight. -/
theorem bankPaperCanonicalTopFrozenRoundedSourceSelector_feasible_of_qTildeSource
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
    (hbetaProt : 0 <= betaProt)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hsource : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde) a ∧
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde) a <= 1)
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
                B R certificate T deltaStar betaProt alpha qTilde m <= 1) :
    ∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde a ∧
        bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde a <= 1 := by
  intro a haCandidate
  by_cases hactive :
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData
  · obtain ⟨m, rfl⟩ :=
      mem_bankPaperCanonicalStructuredActiveValues.mp hactive
    have hnewAmbient :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate T deltaStar betaProt alpha qTilde)
            (B.sampleData.value m) =
          bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde m :=
      bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value_of_headPatternsSeparated
        B.sampleData
          (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde)
          hsep m
    have holdAmbient :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalScaledActiveSeed T qTilde)
            (B.sampleData.value m) =
          bankPaperCanonicalScaledActiveSeed T qTilde m :=
      bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value_of_headPatternsSeparated
        B.sampleData (bankPaperCanonicalScaledActiveSeed T qTilde) hsep m
    by_cases hmMinus :
        B.sampleData.cellOf m = (none, .minus)
    · have hmPool := hminus m hmMinus
      rw [bankPaperCanonicalTopFrozenRoundedSourceSelector,
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
        bankPaperCanonicalTwoZeroHeadCellSourceSelector, if_pos hmPool,
        hnewAmbient]
      have hcap := hminusCapacity m hmMinus
      exact
        ⟨add_nonneg (div_nonneg hbetaProt B.L_pos.le) hcap.1,
          hcap.2⟩
    · by_cases hmPlus :
          B.sampleData.cellOf m = (none, .plus)
      · have hmPool := hplus m hmPlus
        rw [bankPaperCanonicalTopFrozenRoundedSourceSelector,
          bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
          bankPaperCanonicalTwoZeroHeadCellSourceSelector, if_pos hmPool,
          hnewAmbient]
        have hcap := hplusCapacity m hmPlus
        exact
          ⟨add_nonneg (div_nonneg hbetaProt B.L_pos.le) hcap.1,
            hcap.2⟩
      · have hsame :
          bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate T deltaStar betaProt alpha qTilde m =
            bankPaperCanonicalScaledActiveSeed T qTilde m := by
          simp [bankPaperCanonicalTopFrozenRoundedActiveSeed,
            bankPaperCanonicalTwoZeroHeadCellRebalance,
            bankPaperCanonicalUniformCellIncrement, hmMinus, hmPlus]
        have hsourceEq :
            bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
                B R certificate T deltaStar betaProt alpha betaTotal
                  qTilde (B.sampleData.value m) =
              bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
                B R certificate deltaStar betaProt alpha betaTotal
                  (bankPaperCanonicalScaledActiveSeed T qTilde)
                    (B.sampleData.value m) := by
          have hmSmooth :=
            hactiveSmooth
              (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩)
          have hmLabel :
              completeRoughLabel (yNat B.sampleData.n)
                  (B.sampleData.value m) = 1 :=
            (mem_completeRoughRowFiber.mp hmSmooth).2
          by_cases hmPool :
              B.sampleData.value m ∈
                R.roughCanonicalGuardedBroadCorrectionPool certificate
                  deltaStar B.sampleData.W K 1
          · simp only [bankPaperCanonicalTopFrozenRoundedSourceSelector,
              bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
              bankPaperCanonicalTwoZeroHeadCellSourceSelector, hmPool,
              if_true, hnewAmbient, holdAmbient, hsame]
          · simp only [bankPaperCanonicalTopFrozenRoundedSourceSelector,
              bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
              bankPaperCanonicalTwoZeroHeadCellSourceSelector, hmPool,
              if_false,
              bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop,
              hmLabel, if_true, hnewAmbient, holdAmbient, hsame]
        rw [hsourceEq]
        exact hsource (B.sampleData.value m) haCandidate
  · have hnewZero :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate T deltaStar betaProt alpha qTilde) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
    have holdZero :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalScaledActiveSeed T qTilde) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
    have hsourceEq :
        bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate T deltaStar betaProt alpha betaTotal qTilde a =
          bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha betaTotal
              (bankPaperCanonicalScaledActiveSeed T qTilde) a := by
      by_cases haPool :
          a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1
      · simp only [bankPaperCanonicalTopFrozenRoundedSourceSelector,
          bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
          bankPaperCanonicalTwoZeroHeadCellSourceSelector, haPool, if_true,
          hnewZero, holdZero]
      · by_cases haLabel :
          completeRoughLabel (yNat B.sampleData.n) a = 1
        · simp only [bankPaperCanonicalTopFrozenRoundedSourceSelector,
            bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
            bankPaperCanonicalTwoZeroHeadCellSourceSelector, haPool, if_false,
            bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop,
            haLabel, if_true, hnewZero, holdZero]
        · simp only [bankPaperCanonicalTopFrozenRoundedSourceSelector,
            bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
            bankPaperCanonicalTwoZeroHeadCellSourceSelector, haPool, if_false,
            bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop,
            haLabel, if_false]
    rw [hsourceEq]
    exact hsource a haCandidate

/-! ## Complete-row integrality and the source-state handoff -/

/-- A selector with the charged nonsmooth row equations and one explicitly
integer smooth-row quota has integral mass in every complete rough row. -/
theorem bankPaperCanonicalSelectorRowIntegral_of_chargedNonsmoothRows_of_smoothQuota
    {c deltaStar : Real} {depth n K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (selector : Nat -> Real)
    (smoothQuota : Int)
    (hrows : BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K) R certificate deltaStar selector)
    (hsmooth :
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        selector a) = (smoothQuota : Real)) :
    BankPaperCanonicalSelectorRowIntegral n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      selector := by
  intro label hlabelMem
  by_cases hlabel : label = 1
  · subst label
    refine ⟨smoothQuota, ?_⟩
    simpa only [BankPaperRealization.roughCanonicalGuardedRow] using hsmooth
  · rcases roughCanonical_activeNonexceptional_or_exceptional
      (n := n) (deltaStar := deltaStar) hlabel with
      hactive | hexceptional
    · refine
        ⟨R.roughCanonicalPostchargeRowTargetInt deltaStar label, ?_⟩
      have hrow := hrows.1 label hlabelMem hactive
      rw [R.roughCanonicalPostchargeRowTarget_eq_intCast
        deltaStar label] at hrow
      simpa only [BankPaperRealization.roughCanonicalGuardedRow] using hrow
    · refine ⟨0, ?_⟩
      have hrow := hrows.2 label hlabelMem hlabel hexceptional
      simpa only [BankPaperRealization.roughCanonicalGuardedRow,
        Int.cast_zero] using hrow

/-- Nearest-integer normalization internally supplies the complete-row
integrality field for the frozen-top source. -/
theorem bankPaperCanonicalTopFrozenRoundedSourceSelector_rowIntegral
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
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hrows : BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K) R certificate deltaStar
        (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde))) :
    BankPaperCanonicalSelectorRowIntegral B.sampleData.n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha betaTotal qTilde) := by
  apply
    bankPaperCanonicalSelectorRowIntegral_of_chargedNonsmoothRows_of_smoothQuota
      R certificate
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha betaTotal qTilde)
      (bankPaperCanonicalSmoothInitialQuota
        (bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K)
          B R certificate deltaStar betaProt alpha)
        qTilde)
  · exact
      bankPaperCanonicalChargedNonsmoothRowRealization_topFrozenRounded_of_qTilde
        (K := K) B R certificate T deltaStar betaProt alpha betaTotal
          qTilde hrows
  · exact
      sum_bankPaperCanonicalTopFrozenRoundedSourceSelector_smoothRow
        (K := K) B R certificate T deltaStar betaProt alpha betaTotal
          qTilde hvalues

/-- Exact `qTilde -> q0 -> SourceState` handoff.

Row integrality is now a conclusion.  The two remaining premises are
precisely the properties which nearest-integer row-mass normalization does
not imply: pointwise feasibility and selector-tail target agreement away
from the medium-prime band. -/
theorem bankPaperCanonicalTopFrozenRoundedSelectorSourceState
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
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hrows : BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K) R certificate deltaStar
        (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde)))
    (hfeasible : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde a ∧
        bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde a <= 1)
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha betaTotal qTilde)) :
    BankPaperCanonicalSelectorSourceState (W := B.sampleData.W)
      R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha betaTotal qTilde) := by
  exact
    { feasible := hfeasible
      rowIntegral :=
        bankPaperCanonicalTopFrozenRoundedSourceSelector_rowIntegral
          (K := K) B R certificate T deltaStar betaProt alpha betaTotal
            qTilde hvalues hrows
      deficitSupportedOnPrimeBand := hsupport }

end BankPaperRealization

end

end Erdos390.WholePaper
