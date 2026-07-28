import Erdos390.WholePaper.BankPaperCanonicalSectionEightAnalyticLedgerReduction
import Erdos390.WholePaper.BankPaperProposition87ActualDataConnector
import Erdos390.WholePaper.BankPaperFixedExceptionalChargeAsymptotic
import Erdos390.WholePaper.BankPaperCanonicalRawBroadSurplusAsymptotic
import Erdos390.WholePaper.UpperProductAssembly

/-!
# Actual-data connector for the Section 8 analytic ledger

The reduced Section 8 ledger still names the actual post-guard active mass
and the exact frozen mass/logarithmic ledgers.  The Proposition 8.7 actual-
data connector already supplies the finite decomposition needed to make
those objects literal: every guarded candidate is split into its active
seed and its frozen remainder.

This file adjoins the frozen integral factors, defines the resulting exact
total frozen mass and logarithmic contribution, and proves

`m0 + qTilde = #fixed + sum candidates preSelector`

whenever the actual active-measure constructor holds.  Consequently the
first frozen-baseline estimate reduces to the rough selector's literal
total-mass estimate.  For the canonical scaled seed, its active mass is
exactly the guarded smooth base.  Exact interval support then centers the
frozen logarithmic contribution, while the complete central-tail product
satisfies `logY = h * L + O(secondOrderScale)` by elementary factor bounds.
The generic interval-geometry theorem exposes the selector total-mass
estimate, and the final constructed-quota theorem proves that estimate from
the rough-stage frozen baseline ledger, nearest-integer construction, and
the existing `d = O(secondOrderScale / L)` theorem.

No abstract `qTilde`, `m0`, or `Lambda0` remains in the final theorem.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open BankPaperRealization

noncomputable section

/-! ## Literal frozen mass and logarithmic contribution -/

/-- Exact total frozen mass: integral frozen factors have weight one, and
every guarded fractional candidate contributes its actual protected
remainder after subtracting the active seed. -/
def bankPaperCanonicalActualFrozenTotalMass
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head)
    (fixed bankBase candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real) : Real :=
  (fixed.card : Real) + (bankBase.card : Real) +
    ∑ a : BankPaperCanonicalActualFrozenIndex candidates,
      bankPaperCanonicalActualFrozenWeight
        D candidates preSelector activeSeed a

/-- Exact ordinary logarithmic contribution of the same frozen data. -/
def bankPaperCanonicalActualFrozenLogMass
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head)
    (fixed bankBase candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real) : Real :=
  (∑ a ∈ fixed, Real.log (a : Real)) +
    (∑ a ∈ bankBase, Real.log (a : Real)) +
    ∑ a : BankPaperCanonicalActualFrozenIndex candidates,
      bankPaperCanonicalActualFrozenWeight
          D candidates preSelector activeSeed a *
        Real.log (bankPaperCanonicalActualFrozenValue a : Real)

/-- The actual-data split identifies the total frozen mass with the fixed
integral count plus candidate selector mass minus literal active mass. -/
theorem bankPaperCanonicalActualFrozenTotalMass_eq
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (fixed bankBase candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    bankPaperCanonicalActualFrozenTotalMass
        D fixed bankBase candidates preSelector activeSeed =
      (fixed.card : Real) + (bankBase.card : Real) +
        (∑ a ∈ candidates, preSelector a) -
        bankPaperCanonicalLiteralActiveMass D activeSeed := by
  unfold bankPaperCanonicalActualFrozenTotalMass
  rw [sum_bankPaperCanonicalActualFrozenWeight H]
  ring

/-- Equivalently, adjoining the literal active mass recovers the complete
fixed-plus-selector mass with no error term. -/
theorem bankPaperCanonicalActualFrozenTotalMass_add_literalActiveMass_eq
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (fixed bankBase candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    bankPaperCanonicalActualFrozenTotalMass
          D fixed bankBase candidates preSelector activeSeed +
        bankPaperCanonicalLiteralActiveMass D activeSeed =
      (fixed.card : Real) + (bankBase.card : Real) +
        ∑ a ∈ candidates, preSelector a := by
  rw [bankPaperCanonicalActualFrozenTotalMass_eq
    D T fixed bankBase candidates preSelector activeSeed H]
  ring

/-! ## Families of literal actual data -/

/-- Varying exact total frozen mass. -/
def bankPaperCanonicalActualFrozenTotalMassFamily
    {Head : Type*} [Fintype Head]
    (D : Nat -> StructuredSampleData Head)
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (n : Nat) : Real :=
  bankPaperCanonicalActualFrozenTotalMass
    (D n) (fixed n) (bankBase n) (candidates n) (preSelector n)
      (activeSeed n)

/-- Varying exact frozen logarithmic contribution. -/
def bankPaperCanonicalActualFrozenLogMassFamily
    {Head : Type*} [Fintype Head]
    (D : Nat -> StructuredSampleData Head)
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (n : Nat) : Real :=
  bankPaperCanonicalActualFrozenLogMass
    (D n) (fixed n) (bankBase n) (candidates n) (preSelector n)
      (activeSeed n)

/-! ## Elementary logarithmic geometry of the literal upper tail -/

/-- The paper's literal real-valued upper-tail height. -/
def bankPaperCanonicalUpperTailHeight (c : Real) (n : Nat) : Real :=
  (upperTailLength c n : Real)

/-- The logarithm of the complete central tail product. -/
def bankPaperCanonicalCentralTailLogTarget (c : Real) (n : Nat) : Real :=
  Real.log (centralTailProduct n (upperTailLength c n) : Real)

/-- The logarithm of the central tail product is the sum of the logarithms
of its literal factors. -/
theorem bankPaperCanonicalCentralTailLog_eq_sum (n h : Nat) :
    Real.log (centralTailProduct n h : Real) =
      ∑ a ∈ factorInterval (2 * n) (2 * n + h),
        Real.log (a : Real) := by
  unfold centralTailProduct
  rw [Nat.cast_prod]
  apply Real.log_prod
  intro a ha
  have haPos : 0 < a := by
    have haBounds := Finset.mem_Ioc.mp ha
    omega
  exact_mod_cast haPos.ne'

/-- Exact centered-log identity for the complete central tail. -/
theorem bankPaperCanonicalCentralTailLog_sub_height_mul_L_eq_sum
    (n h : Nat) :
    Real.log (centralTailProduct n h : Real) - (h : Real) * L n =
      ∑ a ∈ factorInterval (2 * n) (2 * n + h),
        (Real.log (a : Real) - L n) := by
  rw [bankPaperCanonicalCentralTailLog_eq_sum,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hcard : (factorInterval (2 * n) (2 * n + h)).card = h := by
    simp only [factorInterval, Nat.card_Ioc]
    omega
  rw [hcard]

/-- Every factor in `(n,2n+h]`, when `h <= n`, has logarithmic displacement
from `log n` between zero and `log 3`. -/
theorem bankPaperCanonicalFactorLog_sub_L_mem_Icc
    {n h a : Nat} (hn : 0 < n) (hh : h <= n)
    (ha : a ∈ factorInterval n (upperEndpoint n h)) :
    Real.log (a : Real) - L n ∈ Set.Icc (0 : Real) (Real.log 3) := by
  have haBounds := Finset.mem_Ioc.mp ha
  have hnLeA : n <= a := haBounds.1.le
  have haLeThree : a <= 3 * n :=
    haBounds.2.trans (upperEndpoint_le_three_mul hh)
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have haReal : 0 < (a : Real) := by
    exact_mod_cast (hn.trans_le hnLeA)
  have hlower : L n <= Real.log (a : Real) := by
    rw [L]
    exact Real.log_le_log hnReal (by exact_mod_cast hnLeA)
  have hupper : Real.log (a : Real) <= Real.log 3 + L n := by
    calc
      Real.log (a : Real) <= Real.log (3 * (n : Real)) :=
        Real.log_le_log haReal (by exact_mod_cast haLeThree)
      _ = Real.log 3 + L n := by
        rw [L, Real.log_mul (by norm_num : (3 : Real) ≠ 0) hnReal.ne']
  exact ⟨sub_nonneg.mpr hlower, by linarith⟩

/-- The literal upper-tail height is `O(secondOrderScale)`. -/
theorem bankPaperCanonicalUpperTailHeight_isBigO
    {c : Real} (hc : 0 < c) :
    bankPaperCanonicalUpperTailHeight c =O[atTop] secondOrderScale := by
  apply IsBigO.of_bound (2 * c)
  filter_upwards [
      eventually_upperTailLength_cast_le_two_mul_secondOrderScale hc,
      eventually_secondOrderScale_pos] with n htail hscale
  rw [bankPaperCanonicalUpperTailHeight, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _), Real.norm_eq_abs,
    abs_of_pos hscale]
  exact htail

/-- The complete central-tail logarithm differs from `h log n` by only
`O(secondOrderScale)`.  This is elementary: there are exactly `h` factors,
and each lies between `n` and `3n`. -/
theorem bankPaperCanonicalCentralTailLogTarget_sub_height_mul_L_isBigO
    {c : Real} (hc : 0 < c) :
    (fun n => bankPaperCanonicalCentralTailLogTarget c n -
      bankPaperCanonicalUpperTailHeight c n * L n) =O[atTop]
        secondOrderScale := by
  apply IsBigO.of_bound (2 * c * Real.log 3)
  filter_upwards [eventually_gt_atTop 0, eventually_upperTailLength_le hc,
      eventually_upperTailLength_cast_le_two_mul_secondOrderScale hc,
      eventually_secondOrderScale_pos]
      with n hn htail htailScale hscale
  let h := upperTailLength c n
  have hlogThree : 0 <= Real.log 3 := Real.log_nonneg (by norm_num)
  have hpoint : ∀ a ∈ factorInterval (2 * n) (2 * n + h),
      Real.log (a : Real) - L n ∈ Set.Icc (0 : Real) (Real.log 3) := by
    intro a ha
    apply bankPaperCanonicalFactorLog_sub_L_mem_Icc hn htail
    rw [factorInterval] at ha ⊢
    rw [Finset.mem_Ioc] at ha ⊢
    constructor
    · omega
    · simpa only [upperEndpoint] using ha.2
  have hsumNonneg : 0 <=
      ∑ a ∈ factorInterval (2 * n) (2 * n + h),
        (Real.log (a : Real) - L n) := by
    apply Finset.sum_nonneg
    intro a ha
    exact (hpoint a ha).1
  have hcard : (factorInterval (2 * n) (2 * n + h)).card = h := by
    simp only [factorInterval, Nat.card_Ioc]
    omega
  rw [bankPaperCanonicalCentralTailLogTarget,
    bankPaperCanonicalUpperTailHeight,
    bankPaperCanonicalCentralTailLog_sub_height_mul_L_eq_sum,
    Real.norm_eq_abs, abs_of_nonneg hsumNonneg,
    Real.norm_eq_abs, abs_of_pos hscale]
  calc
    (∑ a ∈ factorInterval (2 * n) (2 * n + h),
        (Real.log (a : Real) - L n)) <=
        ∑ _a ∈ factorInterval (2 * n) (2 * n + h),
          Real.log 3 := by
      apply Finset.sum_le_sum
      intro a ha
      exact (hpoint a ha).2
    _ = (h : Real) * Real.log 3 := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ <= (2 * c * secondOrderScale n) * Real.log 3 :=
      mul_le_mul_of_nonneg_right htailScale hlogThree
    _ = (2 * c * Real.log 3) * secondOrderScale n := by ring

/-! ## Centering the literal frozen logarithmic ledger -/

/-- The constructor's coordinatewise dominance makes every literal frozen
remainder nonnegative. -/
theorem bankPaperCanonicalActualFrozenWeight_nonneg
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (a : BankPaperCanonicalActualFrozenIndex candidates) :
    0 <= bankPaperCanonicalActualFrozenWeight
      D candidates preSelector activeSeed a := by
  exact sub_nonneg.mpr
    (bankPaperCanonicalActiveSeedAmbientWeight_le_preSelector H a.2)

/-- Hence the exact total frozen mass is nonnegative. -/
theorem bankPaperCanonicalActualFrozenTotalMass_nonneg
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    (fixed bankBase candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    0 <= bankPaperCanonicalActualFrozenTotalMass
      D fixed bankBase candidates preSelector activeSeed := by
  unfold bankPaperCanonicalActualFrozenTotalMass
  exact add_nonneg
    (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun a _ha =>
        bankPaperCanonicalActualFrozenWeight_nonneg H a)

/-- Exact centering identity for the literal frozen logarithmic data, valid
at an arbitrary reference logarithm `ell`. -/
theorem bankPaperCanonicalActualFrozenLogMass_sub_total_mul
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head)
    (fixed bankBase candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real) (ell : Real) :
    bankPaperCanonicalActualFrozenLogMass
          D fixed bankBase candidates preSelector activeSeed -
        bankPaperCanonicalActualFrozenTotalMass
            D fixed bankBase candidates preSelector activeSeed * ell =
      (∑ a ∈ fixed, (Real.log (a : Real) - ell)) +
        (∑ a ∈ bankBase, (Real.log (a : Real) - ell)) +
        ∑ a : BankPaperCanonicalActualFrozenIndex candidates,
          bankPaperCanonicalActualFrozenWeight
              D candidates preSelector activeSeed a *
            (Real.log (bankPaperCanonicalActualFrozenValue a : Real) - ell) := by
  unfold bankPaperCanonicalActualFrozenLogMass
    bankPaperCanonicalActualFrozenTotalMass
  simp only [add_mul, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, mul_sub, Finset.sum_mul]
  ring

/-- Exact finite geometry needed to center the frozen ledger: every fixed or
fractional candidate is an actual factor in the paper interval `(n,2n+h]`.
This is structural data, not an asymptotic estimate. -/
def BankPaperCanonicalActualFrozenIntervalGeometry
    {c : Real} (fixed bankBase candidates : Nat -> Finset Nat) : Prop :=
  ∀ᶠ n : Nat in atTop,
    fixed n ⊆ factorInterval n
        (upperEndpoint n (upperTailLength c n)) ∧
      bankBase n ⊆ factorInterval n
        (upperEndpoint n (upperTailLength c n)) ∧
      candidates n ⊆ factorInterval n
        (upperEndpoint n (upperTailLength c n))

/-- The selector-mass interface used by the generic interval-geometry
adapter.  The constructed smooth-quota theorem below derives it from the
rough-stage frozen baseline source. -/
def BankPaperCanonicalActualSelectorMassEstimate
    (c : Real) (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real) : Prop :=
  (fun n => ((fixed n).card : Real) +
      ((bankBase n).card : Real) + (∑ a ∈ candidates n, preSelector n a) -
        bankPaperCanonicalUpperTailHeight c n) =O[atTop]
    (fun n => secondOrderScale n / L n)

/-- The paper's frozen baseline mass relation already is the literal
pre-initial selector mass estimate once the exact active/frozen split is
used.  This adapter is the noncircular entry point for the constructed
smooth-quota theorem below: its premise is the rough-stage baseline ledger,
not an estimate for the final selector. -/
theorem bankPaperCanonicalActualSelectorMassEstimate_of_frozenBaselineSource
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {c : Real}
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (initialSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (qTilde logY : Nat -> Real)
    (Hconstructor : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (initialSelector n) (activeSeed n))
    (HqTilde : ∀ᶠ n : Nat in atTop,
      qTilde n = bankPaperCanonicalLiteralQMass D activeSeed n)
    (Hbaseline : BankPaperCanonicalFrozenBaselineSourceLedger
      (bankPaperCanonicalUpperTailHeight c) logY
      (bankPaperCanonicalActualFrozenLogMassFamily
        D fixed bankBase candidates initialSelector activeSeed)
      (bankPaperCanonicalActualFrozenTotalMassFamily
        D fixed bankBase candidates initialSelector activeSeed)
      qTilde) :
    BankPaperCanonicalActualSelectorMassEstimate
      c fixed bankBase candidates initialSelector := by
  unfold BankPaperCanonicalActualSelectorMassEstimate
  apply Hbaseline.1.congr'
  · filter_upwards [Hconstructor, HqTilde] with n hconstructor hqTilde
    unfold bankPaperCanonicalActualFrozenTotalMassFamily
    rw [hqTilde, bankPaperCanonicalLiteralQMass,
      bankPaperCanonicalActualFrozenTotalMass_add_literalActiveMass_eq
        (D n) (T n) (fixed n) (bankBase n) (candidates n)
          (initialSelector n) (activeSeed n) hconstructor]
  · exact EventuallyEq.rfl

/-- Exact nonsmooth-row state consumed by the charged finite ledger.  This
packages only construction equations; it contains no estimate. -/
def BankPaperCanonicalChargedNonsmoothRowRealization
    {c : Real} {depth n h K : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (selector : Nat -> Real) : Prop :=
  (∀ label ∈ completeRoughLabelSet (yNat n)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
    RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          selector a) =
        R.roughCanonicalPostchargeRowTarget deltaStar label) ∧
  ∀ label ∈ completeRoughLabelSet (yNat n)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
    label ≠ 1 -> RoughCanonicalExceptionalLabel n deltaStar label ->
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          selector a) = 0

/-! ## Exact charged-selector row ledger -/

/-- Extend the complete-rough-row partition of `A` by zero across any
finite superset of its attained labels. -/
theorem sum_eq_sum_completeRoughRowFibers_of_labelSet_subset
    {M : Type*} [AddCommMonoid M]
    (y : Nat) (A labels : Finset Nat) (weight : Nat -> M)
    (hlabels : completeRoughLabelSet y A ⊆ labels) :
    (∑ a ∈ A, weight a) =
      ∑ label ∈ labels,
        ∑ a ∈ completeRoughRowFiber y A label, weight a := by
  classical
  rw [sum_eq_sum_completeRoughRowFibers]
  refine Finset.sum_subset hlabels ?_
  intro label _hlabel hlabelNotAttained
  have hempty : completeRoughRowFiber y A label = ∅ := by
    ext a
    simp only [Finset.notMem_empty, iff_false]
    intro ha
    exact hlabelNotAttained (mem_completeRoughLabelSet.mpr
      ⟨a, (mem_completeRoughRowFiber.mp ha).1,
        (mem_completeRoughRowFiber.mp ha).2⟩)
  rw [hempty]
  simp

/-- The cardinality of a finite set is the sum of its complete-label
multiplicities over any finite label set containing all attained labels. -/
theorem card_cast_eq_sum_completeLabelMultiplicity_of_labelSet_subset
    (y : Nat) (A labels : Finset Nat)
    (hlabels : completeRoughLabelSet y A ⊆ labels) :
    (A.card : Real) =
      ∑ label ∈ labels,
        (completeLabelMultiplicity y A label : Real) := by
  simpa [completeLabelMultiplicity, completeRoughRowFiber] using
    (sum_eq_sum_completeRoughRowFibers_of_labelSet_subset
      (M := Real) y A labels (fun _a => (1 : Real)) hlabels)

/-- The finite universe of complete rough labels needed to compare the
literal upper row, fixed exceptional charge, precharge base state, and
guarded flexible selector.  The smooth label is inserted even when all four
finite sets happen to be empty. -/
def bankPaperCanonicalChargedLabelSet
    {c : Real} {depth n h K : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) : Finset Nat :=
  insert 1
    (((completeRoughLabelSet (yNat n) (roughUpperBlock n h) ∪
        completeRoughLabelSet (yNat n)
          (R.paperFixedExceptionalFactors deltaStar)) ∪
      completeRoughLabelSet (yNat n) R.prechargeBaseState) ∪
      completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K))

/-- Exact finite charged-product identity.  Once every nonsmooth attained
row has its postcharge mass, global active-row capacity rules out a missing
positive row.  Consequently the full mass error is exactly the negative of
the one remaining smooth-row postcharge discrepancy.

This identity includes both charged integral layers: the fixed exceptional
factors and `prechargeBaseState`.  It has no asymptotic premise. -/
theorem bankPaperCanonical_chargedSelectorMass_sub_height_eq_neg_smoothDiscrepancy
    {c : Real} {depth n h K : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (selector : Nat -> Real)
    (hactiveRows : ∀ label ∈ completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
            selector a) =
          R.roughCanonicalPostchargeRowTarget deltaStar label)
    (hexceptionalRows : ∀ label ∈ completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
      label ≠ 1 -> RoughCanonicalExceptionalLabel n deltaStar label ->
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
            selector a) = 0)
    (hcapacity : forall label, IsCompleteRoughLabel (yNat n) label ->
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        RoughCanonicalPostchargeRowCapacity R certificate deltaStar K label) :
    ((R.paperFixedExceptionalFactors deltaStar).card : Real) +
        (R.prechargeBaseState.card : Real) +
        (∑ a ∈ R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K, selector a) - (h : Real) =
      -R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar K
        1 selector := by
  classical
  let candidates :=
    R.roughCanonicalGuardedCandidateSet certificate deltaStar K
  let labels := bankPaperCanonicalChargedLabelSet
    (K := K) R certificate deltaStar
  have hupperLabels :
      completeRoughLabelSet (yNat n) (roughUpperBlock n h) ⊆ labels := by
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
  have hone : 1 ∈ labels := by
    simp [labels, bankPaperCanonicalChargedLabelSet]
  have hcandidatesPartition :
      (∑ a ∈ candidates, selector a) =
        ∑ label ∈ labels,
          ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
            selector a :=
    sum_eq_sum_completeRoughRowFibers_of_labelSet_subset
      (yNat n) candidates labels selector hcandidateLabels
  have hupperPartition :
      ((roughUpperBlock n h).card : Real) =
        ∑ label ∈ labels,
          (roughUpperCompleteRoughRowTarget n h (yNat n) label : Real) := by
    simpa only [roughUpperCompleteRoughRowTarget] using
      card_cast_eq_sum_completeLabelMultiplicity_of_labelSet_subset
        (yNat n) (roughUpperBlock n h) labels hupperLabels
  have hfixedPartition :
      ((R.paperFixedExceptionalFactors deltaStar).card : Real) =
        ∑ label ∈ labels,
          (completeLabelMultiplicity (yNat n)
            (R.paperFixedExceptionalFactors deltaStar) label : Real) :=
    card_cast_eq_sum_completeLabelMultiplicity_of_labelSet_subset
      (yNat n) (R.paperFixedExceptionalFactors deltaStar) labels hfixedLabels
  have hbasePartition :
      (R.prechargeBaseState.card : Real) =
        ∑ label ∈ labels,
          (completeLabelMultiplicity (yNat n) R.prechargeBaseState
            label : Real) :=
    card_cast_eq_sum_completeLabelMultiplicity_of_labelSet_subset
      (yNat n) R.prechargeBaseState labels hbaseLabels
  have hrow : ∀ label ∈ labels, label ≠ 1 ->
      (∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
          selector a) =
        R.roughCanonicalPostchargeRowTarget deltaStar label := by
    intro label hlabel hlabelNeOne
    by_cases hlabelCandidate :
        label ∈ completeRoughLabelSet (yNat n) candidates
    · rcases roughCanonical_activeNonexceptional_or_exceptional
          (n := n) (deltaStar := deltaStar) hlabelNeOne with
        hactive | hexceptional
      · simpa only [candidates, BankPaperRealization.roughCanonicalGuardedRow]
          using hactiveRows label (by simpa only [candidates] using
            hlabelCandidate) hactive
      · have hzero := hexceptionalRows label
          (by simpa only [candidates] using hlabelCandidate)
          hlabelNeOne hexceptional
        have htargetZero :=
          R.roughCanonicalPostchargeRowTarget_eq_zero_of_exceptional
            deltaStar label hexceptional
        simpa only [candidates, BankPaperRealization.roughCanonicalGuardedRow,
          htargetZero] using hzero
    · have hempty :
          completeRoughRowFiber (yNat n) candidates label = ∅ := by
        ext a
        simp only [Finset.notMem_empty, iff_false]
        intro ha
        exact hlabelCandidate (mem_completeRoughLabelSet.mpr
          ⟨a, (mem_completeRoughRowFiber.mp ha).1,
            (mem_completeRoughRowFiber.mp ha).2⟩)
      have hcomplete : IsCompleteRoughLabel (yNat n) label := by
        simp only [labels, bankPaperCanonicalChargedLabelSet,
          Finset.mem_insert, Finset.mem_union] at hlabel
        rcases hlabel with hlabelOne |
          (((hlabelUpper | hlabelFixed) | hlabelBase) | hlabelCandidates)
        · exact (hlabelNeOne hlabelOne).elim
        · exact isCompleteRoughLabel_of_canonicalCompleteRoughRow
            (⟨label, hlabelUpper⟩ : CanonicalCompleteRoughRow (yNat n)
              (roughUpperBlock n h))
        · exact isCompleteRoughLabel_of_canonicalCompleteRoughRow
            (⟨label, hlabelFixed⟩ : CanonicalCompleteRoughRow (yNat n)
              (R.paperFixedExceptionalFactors deltaStar))
        · exact isCompleteRoughLabel_of_canonicalCompleteRoughRow
            (⟨label, hlabelBase⟩ : CanonicalCompleteRoughRow (yNat n)
              R.prechargeBaseState)
        · exact isCompleteRoughLabel_of_canonicalCompleteRoughRow
            (⟨label, hlabelCandidates⟩ : CanonicalCompleteRoughRow (yNat n)
              candidates)
      rcases roughCanonical_activeNonexceptional_or_exceptional
          (n := n) (deltaStar := deltaStar) hlabelNeOne with
        hactive | hexceptional
      · have hcap := hcapacity label hcomplete hactive
        unfold RoughCanonicalPostchargeRowCapacity at hcap
        have htargetZero :
            R.roughCanonicalPostchargeRowTarget deltaStar label = 0 := by
          rw [show R.roughCanonicalGuardedRow certificate deltaStar K label = ∅ by
            simpa only [candidates,
              BankPaperRealization.roughCanonicalGuardedRow] using hempty]
            at hcap
          apply le_antisymm
          · simpa only [Finset.card_empty, Nat.cast_zero] using hcap
          · exact
              R.roughCanonicalPostchargeRowTarget_nonneg deltaStar label
        simp only [hempty, Finset.sum_empty, htargetZero]
      · have htargetZero :=
          R.roughCanonicalPostchargeRowTarget_eq_zero_of_exceptional
            deltaStar label hexceptional
        simp only [hempty, Finset.sum_empty, htargetZero]
  have hrowDifference :
      (∑ label ∈ labels,
          ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
            selector a) -
          ∑ label ∈ labels,
            R.roughCanonicalPostchargeRowTarget deltaStar label =
        (∑ a ∈ completeRoughRowFiber (yNat n) candidates 1,
            selector a) -
          R.roughCanonicalPostchargeRowTarget deltaStar 1 := by
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ label ∈ labels,
          ((∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
              selector a) -
            R.roughCanonicalPostchargeRowTarget deltaStar label)) =
          ∑ label ∈ labels,
            if label = 1 then
              ((∑ a ∈ completeRoughRowFiber (yNat n) candidates 1,
                  selector a) -
                R.roughCanonicalPostchargeRowTarget deltaStar 1)
            else 0 := by
        apply Finset.sum_congr rfl
        intro label hlabel
        by_cases hlabelOne : label = 1
        · subst label
          simp
        · rw [if_neg hlabelOne, hrow label hlabel hlabelOne, sub_self]
      _ = (∑ a ∈ completeRoughRowFiber (yNat n) candidates 1,
              selector a) -
            R.roughCanonicalPostchargeRowTarget deltaStar 1 := by
        simp [hone]
  have htargetPartition :
      (∑ label ∈ labels,
          R.roughCanonicalPostchargeRowTarget deltaStar label) =
        ((roughUpperBlock n h).card : Real) -
          ((R.paperFixedExceptionalFactors deltaStar).card : Real) -
          (R.prechargeBaseState.card : Real) := by
    unfold BankPaperRealization.roughCanonicalPostchargeRowTarget
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← hupperPartition, ← hfixedPartition, ← hbasePartition]
  have htargetPartition' :
      (∑ label ∈ labels,
          R.roughCanonicalPostchargeRowTarget deltaStar label) =
        (h : Real) -
          ((R.paperFixedExceptionalFactors deltaStar).card : Real) -
          (R.prechargeBaseState.card : Real) := by
    simpa only [roughUpperBlock_card] using htargetPartition
  rw [hcandidatesPartition,
    BankPaperRealization.roughCanonicalPostchargeRowDiscrepancy]
  change ((R.paperFixedExceptionalFactors deltaStar).card : Real) +
      (R.prechargeBaseState.card : Real) +
      (∑ label ∈ labels,
        ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
          selector a) - (h : Real) =
    -(R.roughCanonicalPostchargeRowTarget deltaStar 1 -
      ∑ a ∈ completeRoughRowFiber (yNat n) candidates 1, selector a)
  calc
    ((R.paperFixedExceptionalFactors deltaStar).card : Real) +
          (R.prechargeBaseState.card : Real) +
          (∑ label ∈ labels,
            ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
              selector a) - (h : Real) =
        (∑ label ∈ labels,
            ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
              selector a) -
          ((h : Real) -
            ((R.paperFixedExceptionalFactors deltaStar).card : Real) -
            (R.prechargeBaseState.card : Real)) := by ring
    _ = (∑ label ∈ labels,
            ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
              selector a) -
          ∑ label ∈ labels,
            R.roughCanonicalPostchargeRowTarget deltaStar label := by
      rw [htargetPartition']
    _ = (∑ a ∈ completeRoughRowFiber (yNat n) candidates 1,
            selector a) -
          R.roughCanonicalPostchargeRowTarget deltaStar 1 := hrowDifference
    _ = -(R.roughCanonicalPostchargeRowTarget deltaStar 1 -
          ∑ a ∈ completeRoughRowFiber (yNat n) candidates 1,
            selector a) := by ring

/-- Expanded exact form of the same identity relative to any raw
pre-selector.  It displays, with signs fixed, all four sources left on the
smooth row: the raw row discrepancy, fixed and precharge-base tokens, the
guard-deleted raw mass, and the later smooth-row mass change. -/
theorem bankPaperCanonical_chargedSelectorMass_sub_height_eq_rawSmoothLedger
    {c : Real} {depth n h K : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (rawSelector selector : Nat -> Real)
    (hactiveRows : ∀ label ∈ completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
            selector a) =
          R.roughCanonicalPostchargeRowTarget deltaStar label)
    (hexceptionalRows : ∀ label ∈ completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
      label ≠ 1 -> RoughCanonicalExceptionalLabel n deltaStar label ->
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
            selector a) = 0)
    (hcapacity : forall label, IsCompleteRoughLabel (yNat n) label ->
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        RoughCanonicalPostchargeRowCapacity R certificate deltaStar K label) :
    ((R.paperFixedExceptionalFactors deltaStar).card : Real) +
        (R.prechargeBaseState.card : Real) +
        (∑ a ∈ R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K, selector a) - (h : Real) =
      -roughCanonicalRawRowDiscrepancy n h K 1 rawSelector +
        (completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) 1 : Real) +
        (completeLabelMultiplicity (yNat n) R.prechargeBaseState 1 : Real) -
        (∑ a ∈ R.roughCanonicalGuardDeletedRow certificate deltaStar
          K 1, rawSelector a) +
        ((∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            selector a) -
          ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            rawSelector a) := by
  have htotal :=
    bankPaperCanonical_chargedSelectorMass_sub_height_eq_neg_smoothDiscrepancy
      R certificate deltaStar selector hactiveRows hexceptionalRows hcapacity
  have hguard := R.roughCanonicalGuardLocalDiscrepancyLedger
    certificate deltaStar K 1 rawSelector
  rw [BankPaperRealization.roughCanonicalPostchargeRowDiscrepancy]
    at htotal hguard
  linarith

/-- Literal frozen mass in the initial smooth row.  It consists of the two
charged integral multiplicities and the guarded flexible row, after the
actual active mass `qTilde` is removed.  Unlike the global frozen mass this
is a row-local real quantity, and need not be integral. -/
def BankPaperRealization.bankPaperCanonicalInitialSmoothFrozenMass
    {c : Real} {depth n h K : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (initialSelector : Nat -> Real)
    (qTilde : Real) : Real :=
  (completeLabelMultiplicity (yNat n)
      (R.paperFixedExceptionalFactors deltaStar) 1 : Real) +
    (completeLabelMultiplicity (yNat n) R.prechargeBaseState 1 : Real) +
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      initialSelector a) - qTilde

/-- The pre-initialization smooth mismatch is exactly the negative global
baseline mass error.  This is the finite bridge behind the paper's sentence
that exact nonsmooth rows leave only the actual post-guard smooth raw mass.
No asymptotic estimate is used here. -/
theorem BankPaperRealization.roughCanonicalSmoothPreinitialMismatch_eq_neg_chargedMassError
    {c : Real} {depth n h K : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (initialSelector : Nat -> Real) (qTilde : Real)
    (hactiveRows : ∀ label ∈ completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
            initialSelector a) =
          R.roughCanonicalPostchargeRowTarget deltaStar label)
    (hexceptionalRows : ∀ label ∈ completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
      label ≠ 1 -> RoughCanonicalExceptionalLabel n deltaStar label ->
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
            initialSelector a) = 0)
    (hcapacity : forall label, IsCompleteRoughLabel (yNat n) label ->
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        RoughCanonicalPostchargeRowCapacity R certificate deltaStar K label) :
    ((roughUpperCompleteRoughRowTarget n h (yNat n) 1 : Nat) : Real) -
        (R.bankPaperCanonicalInitialSmoothFrozenMass (K := K)
          certificate deltaStar initialSelector qTilde + qTilde) =
      -(((R.paperFixedExceptionalFactors deltaStar).card : Real) +
        (R.prechargeBaseState.card : Real) +
        (∑ a ∈ R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K, initialSelector a) - (h : Real)) := by
  have htotal :=
    bankPaperCanonical_chargedSelectorMass_sub_height_eq_neg_smoothDiscrepancy
      R certificate deltaStar initialSelector hactiveRows hexceptionalRows
        hcapacity
  rw [BankPaperRealization.roughCanonicalPostchargeRowDiscrepancy,
    BankPaperRealization.roughCanonicalPostchargeRowTarget] at htotal
  unfold BankPaperRealization.bankPaperCanonicalInitialSmoothFrozenMass
  linarith

/-- The guarded continuation's actual selector therefore satisfies the
charged identity once the independently proved intrinsic active-row
capacity is supplied.  This projection also identifies the remaining error
with its literal integer smooth quota. -/
theorem BankPaperRealization.bankPaperCanonicalGuardedSectionNineContinuation_exists_chargedMassIdentity
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    {Band : Type*} [DecidableEq Band]
    (lastCell : Band -> Nat)
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (tailLower tailUpper : Band -> Nat -> Nat)
    (scale : Real) (guardBudget poolMinimum : Nat)
    (H : BankPaperCanonicalGuardedSectionNineContinuation
      (K := K) R certificate deltaStar lastCell bandOf cellIndex
        tailLower tailUpper scale guardBudget poolMinimum)
    (hcapacity : forall label, IsCompleteRoughLabel (yNat n) label ->
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        RoughCanonicalPostchargeRowCapacity R certificate deltaStar K label) :
    ∃ smoothFlexibleQuota : Int,
    ∃ selector : Nat -> Real,
      BankPaperCanonicalGuardedSmoothFlexibleQuota
          R certificate deltaStar K selector smoothFlexibleQuota ∧
        ((R.paperFixedExceptionalFactors deltaStar).card : Real) +
            (R.prechargeBaseState.card : Real) +
            (∑ a ∈ R.roughCanonicalGuardedCandidateSet
              certificate deltaStar K, selector a) -
              (upperTailLength c n : Real) =
          (smoothFlexibleQuota : Real) -
            R.roughCanonicalPostchargeRowTarget deltaStar 1 := by
  rcases H with ⟨_hguardCensus, _hpoolCapacity, _hattainedCapacity,
    _hscale, _hindex, _hoccupied, _hlowerCutoff, _hendpoints, _hgeometry,
    smoothFlexibleQuota, selector, _hselector, hsmoothTarget,
    hactiveRows, hexceptionalRows, _hprimeBandBalance,
    _hdeficitSupport, _hbalance, _hpointwise⟩
  refine ⟨smoothFlexibleQuota, selector, hsmoothTarget, ?_⟩
  have htotal :=
    Erdos390.WholePaper.bankPaperCanonical_chargedSelectorMass_sub_height_eq_neg_smoothDiscrepancy
      R certificate deltaStar selector hactiveRows hexceptionalRows hcapacity
  rw [BankPaperRealization.roughCanonicalPostchargeRowDiscrepancy] at htotal
  linarith

/-- If the smooth-row constructor uses the paper's literal nearest-integer
quota, its postcharge discrepancy has an exact three-term ledger: the raw
smooth-height mismatch, the bounded nearest-integer error, and the integer
height adjustment `d`.  The fixed integer removed from the flexible quota
is the literal label-one multiplicity of both charged layers, including
`prechargeBaseState`.

This is the algebraic quota-target bridge.  In particular, the arbitrary
integer exposed by `BankPaperCanonicalGuardedSectionNineContinuation` is
not enough for this conclusion: the selector construction must realize the
displayed `bankPaperCanonicalSmoothFlexibleQuotaAt`. -/
theorem BankPaperRealization.roughCanonicalPostchargeRowDiscrepancy_eq_constructedSmoothLedger
    {c : Real} {depth n K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar mFrozen qTilde : Real) (d : Int)
    (selector : Nat -> Real)
    (hquota : BankPaperCanonicalGuardedSmoothFlexibleQuota
      (c := c) (depth := depth) (n := n)
      R certificate deltaStar K selector
        (bankPaperCanonicalSmoothFlexibleQuotaAt mFrozen qTilde
          (Int.ofNat
            (completeLabelMultiplicity (yNat n)
                (R.paperFixedExceptionalFactors deltaStar) 1 +
              completeLabelMultiplicity (yNat n)
                R.prechargeBaseState 1)) d)) :
    R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar K
        1 selector =
      ((roughUpperCompleteRoughRowTarget n (upperTailLength c n)
          (yNat n) 1 : Nat) : Real) -
          (mFrozen + qTilde) -
        ((bankPaperCanonicalSmoothInitialQuota mFrozen qTilde : Real) -
          (mFrozen + qTilde)) +
        (d : Real) := by
  have hquotaEq :=
    Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalGuardedSmoothFlexibleQuota_eq_intCast
      (c := c) (depth := depth) (n := n) (K := K)
      (R := R) (certificate := certificate)
      (deltaStar := deltaStar) (selector := selector)
      (smoothFlexibleQuota :=
        bankPaperCanonicalSmoothFlexibleQuotaAt mFrozen qTilde
          (Int.ofNat
            (completeLabelMultiplicity (yNat n)
                (R.paperFixedExceptionalFactors deltaStar) 1 +
              completeLabelMultiplicity (yNat n)
                R.prechargeBaseState 1)) d)
      hquota
  rw [BankPaperRealization.roughCanonicalPostchargeRowDiscrepancy, hquotaEq]
  unfold BankPaperRealization.roughCanonicalPostchargeRowTarget
    bankPaperCanonicalSmoothFlexibleQuotaAt
    bankPaperCanonicalSmoothQuotaAt
  push_cast
  simp only [Int.ofNat_eq_natCast, Nat.cast_add, Int.cast_add,
    Int.cast_natCast]
  ring

/-- Quantitative finite form of the constructed smooth ledger.  The only
terms that can grow are the literal pre-initialization smooth-height error
and `d`; nearest-integer initialization costs at most one half. -/
theorem BankPaperRealization.abs_roughCanonicalPostchargeRowDiscrepancy_le_of_constructedSmoothQuota
    {c : Real} {depth n K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar mFrozen qTilde : Real) (d : Int)
    (selector : Nat -> Real)
    (hquota : BankPaperCanonicalGuardedSmoothFlexibleQuota
      (c := c) (depth := depth) (n := n)
      R certificate deltaStar K selector
        (bankPaperCanonicalSmoothFlexibleQuotaAt mFrozen qTilde
          (Int.ofNat
            (completeLabelMultiplicity (yNat n)
                (R.paperFixedExceptionalFactors deltaStar) 1 +
              completeLabelMultiplicity (yNat n)
                R.prechargeBaseState 1)) d)) :
    |R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar K
        1 selector| <=
      |((roughUpperCompleteRoughRowTarget n (upperTailLength c n)
          (yNat n) 1 : Nat) : Real) -
          (mFrozen + qTilde)| + 1 / 2 + |(d : Real)| := by
  rw [Erdos390.WholePaper.BankPaperRealization.roughCanonicalPostchargeRowDiscrepancy_eq_constructedSmoothLedger
    (c := c) (depth := depth) (n := n) (K := K)
    R certificate deltaStar mFrozen qTilde d selector hquota]
  have hround :=
    bankPaperNearestIntegerTieLower_abs_sub_le (mFrozen + qTilde)
  change
    |((roughUpperCompleteRoughRowTarget n (upperTailLength c n)
        (yNat n) 1 : Nat) : Real) -
          (mFrozen + qTilde) -
        ((bankPaperCanonicalSmoothInitialQuota mFrozen qTilde : Real) -
          (mFrozen + qTilde)) +
        (d : Real)| <= _
  have hround' :
      |(bankPaperCanonicalSmoothInitialQuota mFrozen qTilde : Real) -
          (mFrozen + qTilde)| <= 1 / 2 := by
    simpa only [bankPaperCanonicalSmoothInitialQuota] using hround
  calc
    |((roughUpperCompleteRoughRowTarget n (upperTailLength c n)
        (yNat n) 1 : Nat) : Real) -
          (mFrozen + qTilde) -
        ((bankPaperCanonicalSmoothInitialQuota mFrozen qTilde : Real) -
          (mFrozen + qTilde)) +
        (d : Real)| <=
        |((roughUpperCompleteRoughRowTarget n (upperTailLength c n)
            (yNat n) 1 : Nat) : Real) -
            (mFrozen + qTilde) -
          ((bankPaperCanonicalSmoothInitialQuota mFrozen qTilde : Real) -
            (mFrozen + qTilde))| + |(d : Real)| := abs_add_le _ _
    _ <=
        (|((roughUpperCompleteRoughRowTarget n (upperTailLength c n)
              (yNat n) 1 : Nat) : Real) -
            (mFrozen + qTilde)| +
          |(bankPaperCanonicalSmoothInitialQuota mFrozen qTilde : Real) -
            (mFrozen + qTilde)|) + |(d : Real)| := by
      exact add_le_add (abs_sub _ _) le_rfl
    _ <=
        |((roughUpperCompleteRoughRowTarget n (upperTailLength c n)
            (yNat n) 1 : Nat) : Real) -
          (mFrozen + qTilde)| + 1 / 2 + |(d : Real)| := by
      exact add_le_add (add_le_add le_rfl hround') le_rfl

/-- The paper's pre-initialization baseline mass estimate propagates through
the literal nearest-integer smooth construction to the final charged
selector.  The propagation is assumption-free at the analytic level:

* the pre-initial smooth mismatch is the exact negative baseline mass error;
* nearest-integer initialization contributes a bounded half unit;
* the existing Section 8 theorem gives `d = O(N/L)`;
* the charged all-row identity turns the resulting smooth discrepancy back
  into the final total selector mass error.

The remaining premise is one eventual shared witness containing the finite
construction equations (the two row states and the installed literal quota)
together with the identifications of the four observable sequences.  Global
row capacity is discharged internally by the intrinsic broad-surplus theorem.
-/
theorem BankPaperRealization.bankPaperCanonicalActualSelectorMassEstimate_of_constructedSmoothQuota
    (depth W K poolMinimum : Nat)
    {c betaAct deltaStar mu : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) (hmu : 0 < mu)
    (fixed bankBase candidates : Nat -> Finset Nat)
    (initialSelector finalSelector : Nat -> Nat -> Real)
    (mFrozen qTilde logY Lambda0 : Nat -> Real)
    (HbaselineMass : BankPaperCanonicalActualSelectorMassEstimate c
      fixed bankBase candidates initialSelector)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family logY Lambda0
        mFrozen qTilde))
    (Hconstructed : ∀ᶠ n : Nat in atTop,
      ∃ Rn : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)),
      ∃ certn : GuardedCentralAnchorCertificate c depth n
          Rn.anchorGuardLeftCore Rn.anchorGuardRightCore
          (Rn.centralChangedMarkers depth),
        fixed n = Rn.paperFixedExceptionalFactors deltaStar ∧
        bankBase n = Rn.prechargeBaseState ∧
        candidates n =
          Rn.roughCanonicalGuardedCandidateSet certn deltaStar K ∧
        mFrozen n =
          Rn.bankPaperCanonicalInitialSmoothFrozenMass
            (K := K) certn deltaStar (initialSelector n) (qTilde n) ∧
        BankPaperCanonicalChargedNonsmoothRowRealization
            (K := K) Rn certn deltaStar (initialSelector n) ∧
        BankPaperCanonicalChargedNonsmoothRowRealization
            (K := K) Rn certn deltaStar (finalSelector n) ∧
        BankPaperCanonicalGuardedSmoothFlexibleQuota
          Rn certn deltaStar K (finalSelector n)
          (bankPaperCanonicalSmoothFlexibleQuotaAt
            (mFrozen n) (qTilde n)
            (Int.ofNat
              (completeLabelMultiplicity (yNat n) (fixed n) 1 +
                completeLabelMultiplicity (yNat n) (bankBase n) 1))
            (bankPaperCanonicalSmoothDIntFamily
              mu logY Lambda0 mFrozen qTilde n))) :
    BankPaperCanonicalActualSelectorMassEstimate c
      fixed bankBase candidates finalSelector := by
  have HbaselineMass' := HbaselineMass
  unfold BankPaperCanonicalActualSelectorMassEstimate at HbaselineMass'
  have HcapacityRaw :=
    BankPaperRealization.eventually_roughCanonical_active_intrinsic_guard_capacity_inputs
      W K poolMinimum hc hdelta
  have Hthreshold :=
    eventually_ge_atTop (centralAnchorCutoffThreshold depth)
  have HyCutoff :=
    eventually_yNat_lt_centralAnchorCutoff depth
  have HpreMismatch :
      (fun n =>
        ((roughUpperCompleteRoughRowTarget n (upperTailLength c n)
            (yNat n) 1 : Nat) : Real) -
          (mFrozen n + qTilde n)) =O[atTop]
        (fun n => secondOrderScale n / L n) := by
    refine HbaselineMass'.neg_left.congr' ?_ EventuallyEq.rfl
    filter_upwards [Hconstructed, HcapacityRaw, Hthreshold, HyCutoff]
        with n hwitness hcapacityRaw hnCutoff hyCutoff
    rcases hwitness with
      ⟨Rn, certn, hfixed, hbankBase, hcandidates, hmFrozen,
        hinitialRows, _hfinalRows, _hquota⟩
    have hcapacity :
        forall label, IsCompleteRoughLabel (yNat n) label ->
          RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
            RoughCanonicalPostchargeRowCapacity
              Rn certn deltaStar K label := by
      intro label hcomplete hactive
      exact
        (hcapacityRaw depth Rn.anchorGuardLeftCore
          Rn.anchorGuardRightCore (Rn.centralChangedMarkers depth)
          Rn certn hnCutoff hyCutoff label hcomplete hactive).2.2
    symm
    simpa only [hfixed, hbankBase, hcandidates, hmFrozen,
        bankPaperCanonicalUpperTailHeight] using
      Rn.roughCanonicalSmoothPreinitialMismatch_eq_neg_chargedMassError
        (K := K) certn deltaStar (initialSelector n) (qTilde n)
        hinitialRows.1 hinitialRows.2 hcapacity
  have HroundOne :
      (fun n =>
        (bankPaperCanonicalSmoothInitialQuota (mFrozen n) (qTilde n) : Real) -
          (mFrozen n + qTilde n)) =O[atTop]
        (fun _n : Nat => (1 : Real)) := by
    apply IsBigO.of_bound (1 / 2)
    filter_upwards [] with n
    simpa only [Real.norm_eq_abs, norm_one, mul_one,
      bankPaperCanonicalSmoothInitialQuota] using
        bankPaperNearestIntegerTieLower_abs_sub_le
          (mFrozen n + qTilde n)
  have Hround := HroundOne.trans
    bankPaperCanonical_one_isBigO_secondOrderScale_div_L
  have Hd :
      bankPaperCanonicalSmoothDRealFamily mu logY Lambda0 mFrozen qTilde
        =O[atTop] (fun n => secondOrderScale n / L n) := by
    exact bankPaperCanonicalSectionEight_d_isBigO
      W K c betaAct hmu logY Lambda0 mFrozen qTilde
        Hledger
  have HpostExpression :
      (fun n =>
        (((roughUpperCompleteRoughRowTarget n (upperTailLength c n)
            (yNat n) 1 : Nat) : Real) -
              (mFrozen n + qTilde n) -
            ((bankPaperCanonicalSmoothInitialQuota
                (mFrozen n) (qTilde n) : Real) -
              (mFrozen n + qTilde n))) +
          bankPaperCanonicalSmoothDRealFamily
            mu logY Lambda0 mFrozen qTilde n) =O[atTop]
        (fun n => secondOrderScale n / L n) :=
    (HpreMismatch.sub Hround).add Hd
  unfold BankPaperCanonicalActualSelectorMassEstimate
  apply HpostExpression.neg_left.congr'
  · filter_upwards [Hconstructed, HcapacityRaw, Hthreshold, HyCutoff]
        with n hwitness hcapacityRaw hnCutoff hyCutoff
    rcases hwitness with
      ⟨Rn, certn, hfixed, hbankBase, hcandidates, _hmFrozen,
        _hinitialRows, hfinalRows, hquota⟩
    have hcapacity :
        forall label, IsCompleteRoughLabel (yNat n) label ->
          RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
            RoughCanonicalPostchargeRowCapacity
              Rn certn deltaStar K label := by
      intro label hcomplete hactive
      exact
        (hcapacityRaw depth Rn.anchorGuardLeftCore
          Rn.anchorGuardRightCore (Rn.centralChangedMarkers depth)
          Rn certn hnCutoff hyCutoff label hcomplete hactive).2.2
    have hpost :=
      Erdos390.WholePaper.BankPaperRealization.roughCanonicalPostchargeRowDiscrepancy_eq_constructedSmoothLedger
        (c := c) (depth := depth) (n := n)
        (K := K)
        Rn certn deltaStar (mFrozen n) (qTilde n)
        (bankPaperCanonicalSmoothDIntFamily
          mu logY Lambda0 mFrozen qTilde n)
        (finalSelector n)
        (by simpa only [hfixed, hbankBase] using hquota)
    have hmass :=
      bankPaperCanonical_chargedSelectorMass_sub_height_eq_neg_smoothDiscrepancy
        (K := K) Rn certn deltaStar (finalSelector n)
        hfinalRows.1 hfinalRows.2 hcapacity
    rw [hpost] at hmass
    symm
    simpa only [hfixed, hbankBase, hcandidates,
      bankPaperCanonicalUpperTailHeight,
      bankPaperCanonicalSmoothDRealFamily] using hmass
  · exact EventuallyEq.rfl

/-- Losing one further factor of `L` only decreases the paper scale up to an
absolute constant. -/
theorem bankPaperCanonical_secondOrderScale_div_L_isBigO_secondOrderScale :
    (fun n => secondOrderScale n / L n) =O[atTop] secondOrderScale := by
  apply IsBigO.of_bound (1 / Real.log 2)
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < L n := L_pos (by omega)
  have hscale : 0 < secondOrderScale n := secondOrderScale_pos hn
  have hlogTwoLe : Real.log 2 <= L n := by
    rw [L]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  rw [Real.norm_eq_abs, abs_of_pos (div_pos hscale hL),
    Real.norm_eq_abs, abs_of_pos hscale]
  calc
    secondOrderScale n / L n <=
        secondOrderScale n / Real.log 2 :=
      div_le_div_of_nonneg_left hscale.le hlogTwo hlogTwoLe
    _ = (1 / Real.log 2) * secondOrderScale n := by ring

/-- The coarse precharge marker budget is already absorbed by the sharper
`N / L = secondOrderScale / L` mass scale.  This is stronger than the
previous `o(N)` statement and is the growth estimate needed after the
precharge base state is restored to the frozen ledger. -/
theorem bankPaperAnchorMarkerBudget_isBigO_secondOrderScale_div_L :
    (fun n : Nat => (bankPaperAnchorMarkerBudget n : Real)) =O[atTop]
      (fun n => secondOrderScale n / L n) := by
  apply bankPaperAnchorMarkerBudget_isBigO_yNat_sq.trans
  apply IsBigO.of_bound 1
  have hratio := tendsto_endpointRatio_zero.eventually
    (eventually_lt_nhds (by norm_num : (0 : Real) < 1))
  filter_upwards [hratio, eventually_ge_atTop 2] with n hratioN hn
  have hnPos : 0 < n := by omega
  have hnReal : (0 : Real) < n := by exact_mod_cast hnPos
  have hL : 0 < L n := L_pos hn
  have hyNonneg : 0 <= y n := (y_pos hnPos).le
  have hyFloor : (yNat n : Real) <= y n := Nat.floor_le hyNonneg
  have hySq : (yNat n : Real) ^ 2 <= y n ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg _) hyNonneg).2 hyFloor
  have hratioNat :
      (yNat n : Real) ^ 2 * L n ^ 2 / (n : Real) <= 1 := by
    calc
      (yNat n : Real) ^ 2 * L n ^ 2 / (n : Real) <=
          y n ^ 2 * L n ^ 2 / (n : Real) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hySq (sq_nonneg _)) hnReal.le
      _ = endpointRatio n := by rfl
      _ <= 1 := hratioN.le
  have hySqScale :
      (yNat n : Real) ^ 2 <= (n : Real) / L n ^ 2 := by
    apply (le_div_iff₀ (pow_pos hL 2)).2
    have hcross := (div_le_iff₀ hnReal).1 hratioNat
    simpa only [one_mul] using hcross
  have htarget :
      (n : Real) / L n ^ 2 = secondOrderScale n / L n := by
    unfold secondOrderScale L
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs,
    abs_of_pos (div_pos (secondOrderScale_pos hn) hL), one_mul]
  exact hySqScale.trans_eq htarget

/-- Any sequence of bank bases whose cardinality is eventually bounded by the
anchor-marker budget has cardinality `O(N/L)`. -/
theorem BankPaperRealization.prechargeBaseState_card_family_isBigO_secondOrderScale_div_L
    (bankBase : Nat -> Finset Nat)
    (hcardBound : ∀ᶠ n : Nat in atTop,
      (bankBase n).card <= bankPaperAnchorMarkerBudget n) :
    (fun n => ((bankBase n).card : Real)) =O[atTop]
      (fun n => secondOrderScale n / L n) := by
  have hcard :
      (fun n => ((bankBase n).card : Real)) =O[atTop]
        (fun n => (bankPaperAnchorMarkerBudget n : Real)) := by
    apply IsBigO.of_bound 1
    filter_upwards [hcardBound] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), one_mul]
    exact_mod_cast hn
  exact hcard.trans
    bankPaperAnchorMarkerBudget_isBigO_secondOrderScale_div_L

/-- The ordinary logarithmic mass of any eventually supported bank-base
sequence is `O(N)`, provided its cardinality is eventually controlled by the
anchor-marker budget.  Equivalently, its `O(N/L)` cardinality absorbs the one
factor of `L` coming from the size of a legal factor. -/
theorem BankPaperRealization.prechargeBaseState_logMassFamily_isBigO_secondOrderScale
    {c : Real} (hc : 0 < c)
    (bankBase : Nat -> Finset Nat)
    (hcardBound : ∀ᶠ n : Nat in atTop,
      (bankBase n).card <= bankPaperAnchorMarkerBudget n)
    (hsupport : ∀ᶠ n : Nat in atTop,
      ∀ a ∈ bankBase n,
        n < a ∧ a <= upperEndpoint n (upperTailLength c n)) :
    (fun n => ∑ a ∈ bankBase n,
        Real.log (a : Real)) =O[atTop] secondOrderScale := by
  have hcard :=
    BankPaperRealization.prechargeBaseState_card_family_isBigO_secondOrderScale_div_L
      bankBase hcardBound
  have hcardMulLRaw := hcard.mul (isBigO_refl L atTop)
  have hcardMulL :
      (fun n => ((bankBase n).card : Real) * L n) =O[atTop]
        secondOrderScale := by
    apply hcardMulLRaw.congr'
    · exact EventuallyEq.rfl
    · filter_upwards [eventually_gt_atTop 1] with n hn
      exact div_mul_cancel₀ (secondOrderScale n) (L_pos hn).ne'
  have hlogByCard :
      (fun n => ∑ a ∈ bankBase n,
          Real.log (a : Real)) =O[atTop]
        (fun n => ((bankBase n).card : Real) * L n) := by
    apply IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop 3, eventually_upperTailLength_le hc,
      hsupport] with n hn htail hsupportN
    have hnPos : 0 < n := by omega
    have hL : 0 < L n := L_pos (by omega)
    have hpoint : ∀ a ∈ bankBase n,
        0 ≤ Real.log (a : Real) ∧ Real.log (a : Real) ≤ 2 * L n := by
      intro a ha
      have haBounds := hsupportN a ha
      have haPos : 0 < a := hnPos.trans haBounds.1
      have haLeSq : a ≤ n * n := by
        have haUpper : a ≤ 3 * n :=
          haBounds.2.trans (upperEndpoint_le_three_mul htail)
        nlinarith
      constructor
      · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ a by omega))
      · calc
          Real.log (a : Real) ≤ Real.log ((n * n : Nat) : Real) :=
            Real.log_le_log (by exact_mod_cast haPos)
              (by exact_mod_cast haLeSq)
          _ = 2 * L n := by
            rw [Nat.cast_mul, Real.log_mul
              (by exact_mod_cast hnPos.ne') (by exact_mod_cast hnPos.ne')]
            unfold L
            ring
    have hsumNonneg : 0 ≤
        ∑ a ∈ bankBase n, Real.log (a : Real) := by
      apply Finset.sum_nonneg
      intro a ha
      exact (hpoint a ha).1
    have hsumUpper :
        (∑ a ∈ bankBase n, Real.log (a : Real)) ≤
          2 * (((bankBase n).card : Real) * L n) := by
      calc
        (∑ a ∈ bankBase n, Real.log (a : Real)) ≤
            ∑ _a ∈ bankBase n, 2 * L n := by
          apply Finset.sum_le_sum
          intro a ha
          exact (hpoint a ha).2
        _ = 2 * (((bankBase n).card : Real) * L n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
    rw [Real.norm_eq_abs, abs_of_nonneg hsumNonneg,
      Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hL.le)]
    exact hsumUpper
  exact hlogByCard.trans hcardMulL

/-- The selector total-mass estimate already forces the literal frozen mass
to be `O(secondOrderScale)`: the frozen layer is nonnegative and is bounded
by the complete fixed-plus-selector mass. -/
theorem bankPaperCanonicalActualFrozenTotalMassFamily_isBigO
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {c : Real} (hc : 0 < c)
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (Hconstructor : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (preSelector n) (activeSeed n))
    (Hselector : BankPaperCanonicalActualSelectorMassEstimate
      c fixed bankBase candidates preSelector) :
    bankPaperCanonicalActualFrozenTotalMassFamily
        D fixed bankBase candidates preSelector activeSeed =O[atTop]
      secondOrderScale := by
  have HselectorError :
      (fun n => ((fixed n).card : Real) +
          ((bankBase n).card : Real) +
          (∑ a ∈ candidates n, preSelector n a) -
            bankPaperCanonicalUpperTailHeight c n) =O[atTop]
        secondOrderScale :=
    Hselector.trans
      bankPaperCanonical_secondOrderScale_div_L_isBigO_secondOrderScale
  have HselectorMass :
      (fun n => ((fixed n).card : Real) +
        ((bankBase n).card : Real) +
        ∑ a ∈ candidates n, preSelector n a) =O[atTop]
          secondOrderScale :=
    (HselectorError.add (bankPaperCanonicalUpperTailHeight_isBigO hc)).congr_left
      (fun n => by ring)
  have HfrozenLeSelector :
      bankPaperCanonicalActualFrozenTotalMassFamily
          D fixed bankBase candidates preSelector activeSeed =O[atTop]
        (fun n => ((fixed n).card : Real) +
          ((bankBase n).card : Real) +
          ∑ a ∈ candidates n, preSelector n a) := by
    apply IsBigO.of_bound 1
    filter_upwards [Hconstructor] with n hn
    have hm0 : 0 <= bankPaperCanonicalActualFrozenTotalMassFamily
        D fixed bankBase candidates preSelector activeSeed n := by
      unfold bankPaperCanonicalActualFrozenTotalMassFamily
      exact bankPaperCanonicalActualFrozenTotalMass_nonneg
        (D := D n) (T := T n) (fixed n) (bankBase n) (candidates n)
          (preSelector n) (activeSeed n) hn
    have hq : 0 <= bankPaperCanonicalLiteralActiveMass
        (D n) (activeSeed n) :=
      (bankPaperCanonicalLiteralActiveMass_pos hn).le
    rw [Real.norm_eq_abs, abs_of_nonneg hm0, one_mul]
    calc
      bankPaperCanonicalActualFrozenTotalMassFamily
            D fixed bankBase candidates preSelector activeSeed n <=
          bankPaperCanonicalActualFrozenTotalMassFamily
              D fixed bankBase candidates preSelector activeSeed n +
            bankPaperCanonicalLiteralActiveMass (D n) (activeSeed n) :=
        le_add_of_nonneg_right hq
      _ = ((fixed n).card : Real) +
          ((bankBase n).card : Real) +
          ∑ a ∈ candidates n, preSelector n a := by
        unfold bankPaperCanonicalActualFrozenTotalMassFamily
        exact bankPaperCanonicalActualFrozenTotalMass_add_literalActiveMass_eq
          (D n) (T n) (fixed n) (bankBase n) (candidates n) (preSelector n)
            (activeSeed n) hn
      _ <= |((fixed n).card : Real) +
          ((bankBase n).card : Real) +
          ∑ a ∈ candidates n, preSelector n a| := le_abs_self _
      _ = ‖((fixed n).card : Real) +
          ((bankBase n).card : Real) +
          ∑ a ∈ candidates n, preSelector n a‖ :=
        (Real.norm_eq_abs _).symm
  exact HfrozenLeSelector.trans HselectorMass

/-- Interval support and the selector mass estimate automatically center the
literal frozen logarithmic ledger at `m0 * L`. -/
theorem bankPaperCanonicalActualFrozenLogMassFamily_centered_isBigO
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {c : Real} (hc : 0 < c)
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (Hconstructor : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (preSelector n) (activeSeed n))
    (Hgeometry : BankPaperCanonicalActualFrozenIntervalGeometry
      (c := c) fixed bankBase candidates)
    (Hselector : BankPaperCanonicalActualSelectorMassEstimate
      c fixed bankBase candidates preSelector) :
    (fun n =>
      bankPaperCanonicalActualFrozenLogMassFamily
          D fixed bankBase candidates preSelector activeSeed n -
        bankPaperCanonicalActualFrozenTotalMassFamily
            D fixed bankBase candidates preSelector activeSeed n * L n) =O[atTop]
      secondOrderScale := by
  have Hm0 := bankPaperCanonicalActualFrozenTotalMassFamily_isBigO
    hc D T fixed bankBase candidates preSelector activeSeed Hconstructor Hselector
  have HcenterByMass :
      (fun n =>
        bankPaperCanonicalActualFrozenLogMassFamily
            D fixed bankBase candidates preSelector activeSeed n -
          bankPaperCanonicalActualFrozenTotalMassFamily
              D fixed bankBase candidates preSelector activeSeed n * L n) =O[atTop]
        (bankPaperCanonicalActualFrozenTotalMassFamily
          D fixed bankBase candidates preSelector activeSeed) := by
    apply IsBigO.of_bound (Real.log 3)
    filter_upwards [Hconstructor, Hgeometry, eventually_gt_atTop 0,
        eventually_upperTailLength_le hc]
        with n hn hgeometry hnPos htail
    have hweight : forall
        a : BankPaperCanonicalActualFrozenIndex (candidates n),
        0 <= bankPaperCanonicalActualFrozenWeight
          (D n) (candidates n) (preSelector n) (activeSeed n) a :=
      fun a => bankPaperCanonicalActualFrozenWeight_nonneg hn a
    have hfixedPoint : ∀ a ∈ fixed n,
        Real.log (a : Real) - L n ∈ Set.Icc (0 : Real) (Real.log 3) := by
      intro a ha
      exact bankPaperCanonicalFactorLog_sub_L_mem_Icc hnPos htail
        (hgeometry.1 ha)
    have hcandidatePoint : forall
        a : BankPaperCanonicalActualFrozenIndex (candidates n),
        Real.log (bankPaperCanonicalActualFrozenValue a : Real) - L n ∈
          Set.Icc (0 : Real) (Real.log 3) := by
      intro a
      simpa only [bankPaperCanonicalActualFrozenValue] using
        (bankPaperCanonicalFactorLog_sub_L_mem_Icc hnPos htail
          (hgeometry.2.2 a.2))
    have hbankBasePoint : ∀ a ∈ bankBase n,
        Real.log (a : Real) - L n ∈ Set.Icc (0 : Real) (Real.log 3) := by
      intro a ha
      exact bankPaperCanonicalFactorLog_sub_L_mem_Icc hnPos htail
        (hgeometry.2.1 ha)
    have hfixedNonneg : 0 <=
        ∑ a ∈ fixed n, (Real.log (a : Real) - L n) := by
      apply Finset.sum_nonneg
      intro a ha
      exact (hfixedPoint a ha).1
    have hbankBaseNonneg : 0 <=
        ∑ a ∈ bankBase n, (Real.log (a : Real) - L n) := by
      apply Finset.sum_nonneg
      intro a ha
      exact (hbankBasePoint a ha).1
    have hcandidateNonneg : 0 <=
        ∑ a : BankPaperCanonicalActualFrozenIndex (candidates n),
          bankPaperCanonicalActualFrozenWeight
              (D n) (candidates n) (preSelector n) (activeSeed n) a *
            (Real.log (bankPaperCanonicalActualFrozenValue a : Real) -
              L n) := by
      apply Finset.sum_nonneg
      intro a _ha
      exact mul_nonneg (hweight a) (hcandidatePoint a).1
    have hcenterNonneg : 0 <=
        bankPaperCanonicalActualFrozenLogMassFamily
            D fixed bankBase candidates preSelector activeSeed n -
          bankPaperCanonicalActualFrozenTotalMassFamily
              D fixed bankBase candidates preSelector activeSeed n * L n := by
      rw [bankPaperCanonicalActualFrozenLogMassFamily,
        bankPaperCanonicalActualFrozenTotalMassFamily,
        bankPaperCanonicalActualFrozenLogMass_sub_total_mul]
      exact add_nonneg (add_nonneg hfixedNonneg hbankBaseNonneg)
        hcandidateNonneg
    have hm0 : 0 <= bankPaperCanonicalActualFrozenTotalMassFamily
        D fixed bankBase candidates preSelector activeSeed n := by
      unfold bankPaperCanonicalActualFrozenTotalMassFamily
      exact bankPaperCanonicalActualFrozenTotalMass_nonneg
        (D := D n) (T := T n) (fixed n) (bankBase n) (candidates n)
          (preSelector n) (activeSeed n) hn
    rw [Real.norm_eq_abs, abs_of_nonneg hcenterNonneg,
      Real.norm_eq_abs, abs_of_nonneg hm0,
      bankPaperCanonicalActualFrozenLogMassFamily,
      bankPaperCanonicalActualFrozenTotalMassFamily,
      bankPaperCanonicalActualFrozenLogMass_sub_total_mul]
    calc
      (∑ a ∈ fixed n, (Real.log (a : Real) - L n)) +
          (∑ a ∈ bankBase n, (Real.log (a : Real) - L n)) +
          ∑ a : BankPaperCanonicalActualFrozenIndex (candidates n),
            bankPaperCanonicalActualFrozenWeight
                (D n) (candidates n) (preSelector n) (activeSeed n) a *
              (Real.log (bankPaperCanonicalActualFrozenValue a : Real) -
                L n) <=
        (∑ _a ∈ fixed n, Real.log 3) +
          (∑ _a ∈ bankBase n, Real.log 3) +
          ∑ a : BankPaperCanonicalActualFrozenIndex (candidates n),
            bankPaperCanonicalActualFrozenWeight
                (D n) (candidates n) (preSelector n) (activeSeed n) a *
              Real.log 3 := by
        apply add_le_add
        · apply add_le_add
          · apply Finset.sum_le_sum
            intro a ha
            exact (hfixedPoint a ha).2
          · apply Finset.sum_le_sum
            intro a ha
            exact (hbankBasePoint a ha).2
        · apply Finset.sum_le_sum
          intro a _ha
          exact mul_le_mul_of_nonneg_left (hcandidatePoint a).2 (hweight a)
      _ = bankPaperCanonicalActualFrozenTotalMass
          (D n) (fixed n) (bankBase n) (candidates n) (preSelector n)
            (activeSeed n) *
            Real.log 3 := by
        unfold bankPaperCanonicalActualFrozenTotalMass
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.sum_mul]
        ring
      _ = Real.log 3 * bankPaperCanonicalActualFrozenTotalMass
          (D n) (fixed n) (bankBase n) (candidates n) (preSelector n)
            (activeSeed n) := by
        ring
  exact HcenterByMass.trans Hm0

/-! ## The remaining actual analytic sources -/

/-- The exact missing identification for the active side, now tied to the
literal tagged active seed rather than to an abstract function `qTilde`. -/
def BankPaperCanonicalActualGuardedSmoothMassEstimate
    {Head : Type*} [Fintype Head]
    (D : Nat -> StructuredSampleData Head)
    (activeSeed : forall n, (D n).Sample -> Real)
    (guardedBase : Nat -> Real) : Prop :=
  (fun n => guardedBase n -
      bankPaperCanonicalLiteralQMass D activeSeed n) =o[atTop]
    secondOrderScale

/-- The actual-data estimate is exactly the generic guarded-correction
estimate with `qTilde` instantiated by the literal tagged seed mass. -/
theorem bankPaperCanonicalGuardedSmoothCorrectionEstimate_of_actualData
    {Head : Type*} [Fintype Head]
    (D : Nat -> StructuredSampleData Head)
    (activeSeed : forall n, (D n).Sample -> Real)
    (guardedBase : Nat -> Real)
    (H : BankPaperCanonicalActualGuardedSmoothMassEstimate
      D activeSeed guardedBase) :
    BankPaperCanonicalGuardedSmoothCorrectionEstimate guardedBase
      (bankPaperCanonicalLiteralQMass D activeSeed) :=
  H

/-- For the canonical scaled active seed, the active-mass identification is
exact: its literal mass is the chosen guarded-base mass.  Thus the first
analytic source estimate disappears entirely for this paper-facing choice. -/
theorem bankPaperCanonicalActualGuardedSmoothMassEstimate_scaledActiveSeed
    {Head : Type*} [Fintype Head]
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (guardedBase : Nat -> Real) :
    BankPaperCanonicalActualGuardedSmoothMassEstimate D
      (fun n => bankPaperCanonicalScaledActiveSeed (T n) (guardedBase n))
      guardedBase := by
  have hzero : (fun _n : Nat => (0 : Real)) =o[atTop]
      secondOrderScale := isLittleO_zero _ _
  exact hzero.congr_left fun n => by
    simp only [bankPaperCanonicalLiteralQMass,
      bankPaperCanonicalLiteralActiveMass_scaledActiveSeed, sub_self]

/-- The three remaining baseline estimates after using the exact
frozen-plus-active decomposition.  Every function here is literal data. -/
def BankPaperCanonicalActualFrozenBaselineEstimates
    {Head : Type*} [Fintype Head]
    (D : Nat -> StructuredSampleData Head)
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (h logY : Nat -> Real) : Prop :=
  (fun n => ((fixed n).card : Real) +
      ((bankBase n).card : Real) +
      (∑ a ∈ candidates n, preSelector n a) - h n) =O[atTop]
      (fun n => secondOrderScale n / L n) ∧
    (fun n =>
      bankPaperCanonicalActualFrozenLogMassFamily
          D fixed bankBase candidates preSelector activeSeed n -
        bankPaperCanonicalActualFrozenTotalMassFamily
            D fixed bankBase candidates preSelector activeSeed n * L n) =O[atTop]
      secondOrderScale ∧
    (fun n => logY n - h n * L n) =O[atTop]
      secondOrderScale

/-- For the literal central-tail target, interval geometry derives both
logarithmic fields of the baseline ledger.  This generic adapter accepts a
selector total-mass estimate; the constructed-quota closure below proves it. -/
theorem bankPaperCanonicalActualFrozenBaselineEstimates_of_intervalGeometry
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {c : Real} (hc : 0 < c)
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (Hconstructor : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (preSelector n) (activeSeed n))
    (Hgeometry : BankPaperCanonicalActualFrozenIntervalGeometry
      (c := c) fixed bankBase candidates)
    (Hselector : BankPaperCanonicalActualSelectorMassEstimate
      c fixed bankBase candidates preSelector) :
    BankPaperCanonicalActualFrozenBaselineEstimates
      D fixed bankBase candidates preSelector activeSeed
        (bankPaperCanonicalUpperTailHeight c)
        (bankPaperCanonicalCentralTailLogTarget c) := by
  exact ⟨Hselector,
    bankPaperCanonicalActualFrozenLogMassFamily_centered_isBigO
      hc D T fixed bankBase candidates preSelector activeSeed Hconstructor
        Hgeometry Hselector,
    bankPaperCanonicalCentralTailLogTarget_sub_height_mul_L_isBigO hc⟩

/-- Complete actual source package.  The constructor is retained because
it is exactly what makes the active/frozen decomposition valid eventually;
all other fields are genuine asymptotic estimates. -/
def BankPaperCanonicalSectionEightActualDataSourceLedger
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (guardedBase h logY : Nat -> Real) : Prop :=
  (∀ᶠ n : Nat in atTop,
    BankPaperCanonicalActualActiveMeasureConstructor
      (D n) (T n) (candidates n) (preSelector n) (activeSeed n)) ∧
    BankPaperCanonicalActualGuardedSmoothMassEstimate
      D activeSeed guardedBase ∧
    BankPaperCanonicalActualFrozenBaselineEstimates
      D fixed bankBase candidates preSelector activeSeed h logY

/-- Smaller source package for the canonical scaled active seed.  Its mass
identification is the unconditional theorem above, so only construction of
the actual placement and the three literal frozen-baseline estimates remain. -/
def BankPaperCanonicalSectionEightScaledActualDataSourceLedger
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (guardedBase h logY : Nat -> Real) : Prop :=
  (∀ᶠ n : Nat in atTop,
    BankPaperCanonicalActualActiveMeasureConstructor
      (D n) (T n) (candidates n) (preSelector n)
        (bankPaperCanonicalScaledActiveSeed (T n) (guardedBase n))) ∧
    BankPaperCanonicalActualFrozenBaselineEstimates
      D fixed bankBase candidates preSelector
        (fun n => bankPaperCanonicalScaledActiveSeed (T n) (guardedBase n))
      h logY

/-- Central-tail specialization of the actual source ledger.  Active mass is
exact for the scaled seed and both logarithmic estimates are theorems.  Its
generic selector-mass input is discharged by the constructed-quota closure. -/
theorem bankPaperCanonicalSectionEightScaledActualDataSourceLedger_of_intervalGeometry
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {c : Real} (hc : 0 < c)
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (guardedBase : Nat -> Real)
    (Hconstructor : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (preSelector n)
          (bankPaperCanonicalScaledActiveSeed (T n) (guardedBase n)))
    (Hgeometry : BankPaperCanonicalActualFrozenIntervalGeometry
      (c := c) fixed bankBase candidates)
    (Hselector : BankPaperCanonicalActualSelectorMassEstimate
      c fixed bankBase candidates preSelector) :
    BankPaperCanonicalSectionEightScaledActualDataSourceLedger
      D T fixed bankBase candidates preSelector guardedBase
        (bankPaperCanonicalUpperTailHeight c)
        (bankPaperCanonicalCentralTailLogTarget c) := by
  exact ⟨Hconstructor,
    bankPaperCanonicalActualFrozenBaselineEstimates_of_intervalGeometry
      hc D T fixed bankBase candidates preSelector
        (fun n => bankPaperCanonicalScaledActiveSeed (T n) (guardedBase n))
        Hconstructor Hgeometry Hselector⟩

/-! ## Construction of the old Section 8 ledger -/

/-- The literal actual estimates construct the frozen-baseline source
ledger.  Its first field is just the exact active/frozen decomposition
followed by the supplied total-selector estimate. -/
theorem bankPaperCanonicalFrozenBaselineSourceLedger_of_actualData
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (h logY : Nat -> Real)
    (Hconstructor : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (preSelector n) (activeSeed n))
    (Hestimates : BankPaperCanonicalActualFrozenBaselineEstimates
      D fixed bankBase candidates preSelector activeSeed h logY) :
    BankPaperCanonicalFrozenBaselineSourceLedger
      h logY
      (bankPaperCanonicalActualFrozenLogMassFamily
        D fixed bankBase candidates preSelector activeSeed)
      (bankPaperCanonicalActualFrozenTotalMassFamily
        D fixed bankBase candidates preSelector activeSeed)
      (bankPaperCanonicalLiteralQMass D activeSeed) := by
  refine ⟨?_, Hestimates.2.1, Hestimates.2.2⟩
  apply Hestimates.1.congr'
  · filter_upwards [Hconstructor] with n hn
    unfold bankPaperCanonicalActualFrozenTotalMassFamily
      bankPaperCanonicalLiteralQMass
    rw [bankPaperCanonicalActualFrozenTotalMass_add_literalActiveMass_eq
      (D n) (T n) (fixed n) (bankBase n) (candidates n) (preSelector n)
        (activeSeed n) hn]
  · exact EventuallyEq.rfl

/-- Final literal tail-family connector.  It produces the old analytic
ledger for the actual tagged active mass and the actual frozen logarithmic
data, using the honest total guarded-base extension on the finite prefix. -/
theorem bankPaperCanonicalSectionEightAnalyticLedger_of_actualData
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {c : Real} {N : Nat} (depth W K : Nat)
    (betaAct deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (mFrozen h logY : Nat -> Real)
    (Hsource : BankPaperCanonicalSectionEightActualDataSourceLedger
      D T fixed bankBase candidates preSelector activeSeed
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
      h logY) :
    BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      (bankPaperCanonicalLiteralQMass D activeSeed)
      (bankPaperCanonicalSmoothA0Family
        logY
        (bankPaperCanonicalActualFrozenLogMassFamily
          D fixed bankBase candidates preSelector activeSeed)
        mFrozen (bankPaperCanonicalLiteralQMass D activeSeed)) := by
  apply bankPaperCanonicalSectionEightAnalyticLedger_of_correctionAndBaseline
    depth W K betaAct deltaStar F
    (bankPaperCanonicalLiteralQMass D activeSeed) h logY
    (bankPaperCanonicalActualFrozenLogMassFamily
      D fixed bankBase candidates preSelector activeSeed)
    (bankPaperCanonicalActualFrozenTotalMassFamily
      D fixed bankBase candidates preSelector activeSeed)
    mFrozen
  · exact bankPaperCanonicalGuardedSmoothCorrectionEstimate_of_actualData
      D activeSeed
        (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
        Hsource.2.1
  · exact bankPaperCanonicalFrozenBaselineSourceLedger_of_actualData
      D T fixed bankBase candidates preSelector activeSeed h logY
        Hsource.1 Hsource.2.2

/-- Canonical scaled-seed specialization.  Here `qTilde` is the literal
guarded-base mass itself, because the constructed seed has exactly that
mass; no postulated active-mass comparison remains. -/
theorem bankPaperCanonicalSectionEightAnalyticLedger_of_scaledActualData
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {c : Real} {N : Nat} (depth W K : Nat)
    (betaAct deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (mFrozen h logY : Nat -> Real)
    (Hsource : BankPaperCanonicalSectionEightScaledActualDataSourceLedger
      D T fixed bankBase candidates preSelector
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
      h logY) :
    BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
      (bankPaperCanonicalSmoothA0Family
        logY
        (bankPaperCanonicalActualFrozenLogMassFamily
          D fixed bankBase candidates preSelector
            (fun n => bankPaperCanonicalScaledActiveSeed (T n)
              (F.extendedGuardedSmoothBaseMass
                W K betaAct deltaStar n)))
        mFrozen
        (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)) := by
  have Hactual : BankPaperCanonicalSectionEightActualDataSourceLedger
      D T fixed bankBase candidates preSelector
      (fun n => bankPaperCanonicalScaledActiveSeed (T n)
        (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar n))
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
      h logY :=
    ⟨Hsource.1,
      bankPaperCanonicalActualGuardedSmoothMassEstimate_scaledActiveSeed
        D T (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar),
      Hsource.2⟩
  have hqMass :
      bankPaperCanonicalLiteralQMass D
          (fun n => bankPaperCanonicalScaledActiveSeed (T n)
            (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar n)) =
        F.extendedGuardedSmoothBaseMass W K betaAct deltaStar := by
    funext n
    simp only [bankPaperCanonicalLiteralQMass,
      bankPaperCanonicalLiteralActiveMass_scaledActiveSeed]
  have hledger :=
    bankPaperCanonicalSectionEightAnalyticLedger_of_actualData
      depth W K betaAct deltaStar F D T fixed bankBase candidates
        preSelector
        (fun n => bankPaperCanonicalScaledActiveSeed (T n)
          (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar n))
        mFrozen h logY Hactual
  rw [hqMass] at hledger
  exact hledger

/-- Generic paper-facing central-tail adapter with an explicit selector-mass
interface.  See the following theorem for its construction from the
rough-stage baseline ledger. -/
theorem bankPaperCanonicalSectionEightAnalyticLedger_of_scaledActualData_intervalGeometry
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {c : Real} {N : Nat} (hc : 0 < c) (depth W K : Nat)
    (betaAct deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (mFrozen : Nat -> Real)
    (Hconstructor : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (preSelector n)
          (bankPaperCanonicalScaledActiveSeed (T n)
            (F.extendedGuardedSmoothBaseMass
              W K betaAct deltaStar n)))
    (Hgeometry : BankPaperCanonicalActualFrozenIntervalGeometry
      (c := c) fixed bankBase candidates)
    (Hselector : BankPaperCanonicalActualSelectorMassEstimate
      c fixed bankBase candidates preSelector) :
    BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
      (bankPaperCanonicalSmoothA0Family
        (bankPaperCanonicalCentralTailLogTarget c)
        (bankPaperCanonicalActualFrozenLogMassFamily
          D fixed bankBase candidates preSelector
            (fun n => bankPaperCanonicalScaledActiveSeed (T n)
              (F.extendedGuardedSmoothBaseMass
                W K betaAct deltaStar n)))
        mFrozen
        (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)) := by
  apply bankPaperCanonicalSectionEightAnalyticLedger_of_scaledActualData
    depth W K betaAct deltaStar F D T fixed bankBase candidates
      preSelector mFrozen (bankPaperCanonicalUpperTailHeight c)
        (bankPaperCanonicalCentralTailLogTarget c)
  exact
    bankPaperCanonicalSectionEightScaledActualDataSourceLedger_of_intervalGeometry
      hc D T fixed bankBase candidates preSelector
        (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
        Hconstructor Hgeometry Hselector

/-- Fully constructed central-tail closure from the single literal
pre-initial selector-mass estimate.  The scaled actual-data connector first
turns that estimate into the initial Section 8 ledger.  Exact row
construction and nearest-integer smooth placement then transport the
selector-mass estimate to the final selector, where the same actual-data
connector closes the final ledger.  In particular, no separate frozen
baseline source ledger is required. -/
theorem bankPaperCanonicalSectionEightAnalyticLedger_of_constructedSmoothQuota_selectorMass_intervalGeometry
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {c betaAct deltaStar mu : Real} {N : Nat}
    (hc : 0 < c) (hdelta : 0 < deltaStar) (hmu : 0 < mu)
    (depth W K poolMinimum : Nat)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (initialSelector finalSelector : Nat -> Nat -> Real)
    (mFrozen : Nat -> Real)
    (HinitialConstructor : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (initialSelector n)
        (bankPaperCanonicalScaledActiveSeed (T n)
          (F.extendedGuardedSmoothBaseMass
            W K betaAct deltaStar n)))
    (HfinalConstructor : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (finalSelector n)
        (bankPaperCanonicalScaledActiveSeed (T n)
          (F.extendedGuardedSmoothBaseMass
            W K betaAct deltaStar n)))
    (HinitialMass : BankPaperCanonicalActualSelectorMassEstimate
      c fixed bankBase candidates initialSelector)
    (Hconstructed : ∀ᶠ n : Nat in atTop,
      ∃ hn : N ≤ n,
        fixed n =
            (F.realization n hn).paperFixedExceptionalFactors deltaStar ∧
        bankBase n = (F.realization n hn).prechargeBaseState ∧
        candidates n =
          (F.realization n hn).roughCanonicalGuardedCandidateSet
            (F.certificate n hn) deltaStar K ∧
        mFrozen n =
          (F.realization n hn).bankPaperCanonicalInitialSmoothFrozenMass
            (K := K) (F.certificate n hn) deltaStar (initialSelector n)
              (F.extendedGuardedSmoothBaseMass
                W K betaAct deltaStar n) ∧
        BankPaperCanonicalChargedNonsmoothRowRealization
            (K := K) (F.realization n hn) (F.certificate n hn)
              deltaStar (initialSelector n) ∧
        BankPaperCanonicalChargedNonsmoothRowRealization
            (K := K) (F.realization n hn) (F.certificate n hn)
              deltaStar (finalSelector n) ∧
        BankPaperCanonicalGuardedSmoothFlexibleQuota
          (F.realization n hn) (F.certificate n hn) deltaStar K
          (finalSelector n)
          (bankPaperCanonicalSmoothFlexibleQuotaAt
            (mFrozen n)
            (F.extendedGuardedSmoothBaseMass
              W K betaAct deltaStar n)
            (Int.ofNat
              (completeLabelMultiplicity (yNat n) (fixed n) 1 +
                completeLabelMultiplicity (yNat n) (bankBase n) 1))
            (bankPaperCanonicalSmoothDIntFamily mu
              (bankPaperCanonicalCentralTailLogTarget c)
              (bankPaperCanonicalActualFrozenLogMassFamily D
                fixed bankBase candidates initialSelector
                (fun m => bankPaperCanonicalScaledActiveSeed (T m)
                  (F.extendedGuardedSmoothBaseMass
                    W K betaAct deltaStar m)))
              mFrozen
              (F.extendedGuardedSmoothBaseMass
                W K betaAct deltaStar) n)))
    (Hgeometry : BankPaperCanonicalActualFrozenIntervalGeometry
      (c := c) fixed bankBase candidates) :
    BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
      (bankPaperCanonicalSmoothA0Family
        (bankPaperCanonicalCentralTailLogTarget c)
        (bankPaperCanonicalActualFrozenLogMassFamily D
          fixed bankBase candidates finalSelector
          (fun n => bankPaperCanonicalScaledActiveSeed (T n)
            (F.extendedGuardedSmoothBaseMass
              W K betaAct deltaStar n)))
        mFrozen
        (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)) := by
  let guardedBase : Nat -> Real :=
    F.extendedGuardedSmoothBaseMass W K betaAct deltaStar
  let activeSeed : forall n, (D n).Sample -> Real := fun n =>
    bankPaperCanonicalScaledActiveSeed (T n) (guardedBase n)
  let initialLambda : Nat -> Real :=
    bankPaperCanonicalActualFrozenLogMassFamily
      D fixed bankBase candidates initialSelector activeSeed
  have Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      guardedBase
      (bankPaperCanonicalSmoothA0Family
        (bankPaperCanonicalCentralTailLogTarget c) initialLambda
          mFrozen guardedBase) := by
    simpa only [guardedBase, activeSeed, initialLambda] using
      (bankPaperCanonicalSectionEightAnalyticLedger_of_scaledActualData_intervalGeometry
        hc depth W K betaAct deltaStar F D T fixed bankBase candidates
          initialSelector mFrozen HinitialConstructor Hgeometry HinitialMass)
  have Hselector : BankPaperCanonicalActualSelectorMassEstimate
      c fixed bankBase candidates finalSelector := by
    apply
      BankPaperRealization.bankPaperCanonicalActualSelectorMassEstimate_of_constructedSmoothQuota
        depth W K poolMinimum hc hdelta hmu fixed bankBase candidates
          initialSelector finalSelector mFrozen guardedBase
          (bankPaperCanonicalCentralTailLogTarget c) initialLambda
    · exact HinitialMass
    · exact Hledger
    · filter_upwards [Hconstructed] with n hwitness
      rcases hwitness with
        ⟨hn, hfixed, hbankBase, hcandidates, hmFrozen,
          hinitialRows, hfinalRows, hquota⟩
      refine ⟨F.realization n hn, F.certificate n hn,
        hfixed, hbankBase, hcandidates, ?_, hinitialRows,
        hfinalRows, ?_⟩
      · simpa only [guardedBase] using hmFrozen
      · simpa only [guardedBase, activeSeed, initialLambda] using hquota
  apply
    bankPaperCanonicalSectionEightAnalyticLedger_of_scaledActualData_intervalGeometry
      hc depth W K betaAct deltaStar F D T fixed bankBase
        candidates finalSelector mFrozen
  · simpa only [activeSeed, guardedBase]
      using HfinalConstructor
  · exact Hgeometry
  · exact Hselector

/-- Fully constructed central-tail closure.  The rough-stage frozen
baseline ledger is attached to the pre-initial selector.  Exact row
construction, nearest-integer smooth placement, and the existing height
adjustment theorem then prove the final selector-mass estimate.  Therefore
the interval-geometry actual-data theorem can be invoked with no separate
selector-mass asymptotic premise.  All constructed row and quota data are
required to come from the same guarded tail-family realization used by the
analytic reduction. -/
theorem bankPaperCanonicalSectionEightAnalyticLedger_of_constructedSmoothQuota_intervalGeometry
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {c betaAct deltaStar mu : Real} {N : Nat}
    (hc : 0 < c) (hdelta : 0 < deltaStar) (hmu : 0 < mu)
    (depth W K poolMinimum : Nat)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (initialSelector finalSelector : Nat -> Nat -> Real)
    (mFrozen : Nat -> Real)
    (HinitialConstructor : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (initialSelector n)
        (bankPaperCanonicalScaledActiveSeed (T n)
          (F.extendedGuardedSmoothBaseMass
            W K betaAct deltaStar n)))
    (HfinalConstructor : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (finalSelector n)
        (bankPaperCanonicalScaledActiveSeed (T n)
          (F.extendedGuardedSmoothBaseMass
            W K betaAct deltaStar n)))
    (Hbaseline : BankPaperCanonicalFrozenBaselineSourceLedger
      (bankPaperCanonicalUpperTailHeight c)
      (bankPaperCanonicalCentralTailLogTarget c)
      (bankPaperCanonicalActualFrozenLogMassFamily D
        fixed bankBase candidates initialSelector
        (fun n => bankPaperCanonicalScaledActiveSeed (T n)
          (F.extendedGuardedSmoothBaseMass
            W K betaAct deltaStar n)))
      (bankPaperCanonicalActualFrozenTotalMassFamily D
        fixed bankBase candidates initialSelector
        (fun n => bankPaperCanonicalScaledActiveSeed (T n)
          (F.extendedGuardedSmoothBaseMass
            W K betaAct deltaStar n)))
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar))
    (Hconstructed : ∀ᶠ n : Nat in atTop,
      ∃ hn : N ≤ n,
        fixed n =
            (F.realization n hn).paperFixedExceptionalFactors deltaStar ∧
        bankBase n = (F.realization n hn).prechargeBaseState ∧
        candidates n =
          (F.realization n hn).roughCanonicalGuardedCandidateSet
            (F.certificate n hn) deltaStar K ∧
        mFrozen n =
          (F.realization n hn).bankPaperCanonicalInitialSmoothFrozenMass
            (K := K) (F.certificate n hn) deltaStar (initialSelector n)
              (F.extendedGuardedSmoothBaseMass
                W K betaAct deltaStar n) ∧
        BankPaperCanonicalChargedNonsmoothRowRealization
            (K := K) (F.realization n hn) (F.certificate n hn)
              deltaStar (initialSelector n) ∧
        BankPaperCanonicalChargedNonsmoothRowRealization
            (K := K) (F.realization n hn) (F.certificate n hn)
              deltaStar (finalSelector n) ∧
        BankPaperCanonicalGuardedSmoothFlexibleQuota
          (F.realization n hn) (F.certificate n hn) deltaStar K
          (finalSelector n)
          (bankPaperCanonicalSmoothFlexibleQuotaAt
            (mFrozen n)
            (F.extendedGuardedSmoothBaseMass
              W K betaAct deltaStar n)
            (Int.ofNat
              (completeLabelMultiplicity (yNat n) (fixed n) 1 +
                completeLabelMultiplicity (yNat n) (bankBase n) 1))
            (bankPaperCanonicalSmoothDIntFamily mu
              (bankPaperCanonicalCentralTailLogTarget c)
              (bankPaperCanonicalActualFrozenLogMassFamily D
                fixed bankBase candidates initialSelector
                (fun m => bankPaperCanonicalScaledActiveSeed (T m)
                  (F.extendedGuardedSmoothBaseMass
                    W K betaAct deltaStar m)))
              mFrozen
              (F.extendedGuardedSmoothBaseMass
                W K betaAct deltaStar) n)))
    (Hgeometry : BankPaperCanonicalActualFrozenIntervalGeometry
      (c := c) fixed bankBase candidates) :
    BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
      (bankPaperCanonicalSmoothA0Family
        (bankPaperCanonicalCentralTailLogTarget c)
        (bankPaperCanonicalActualFrozenLogMassFamily D
          fixed bankBase candidates finalSelector
          (fun n => bankPaperCanonicalScaledActiveSeed (T n)
            (F.extendedGuardedSmoothBaseMass
              W K betaAct deltaStar n)))
        mFrozen
        (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)) := by
  let guardedBase : Nat -> Real :=
    F.extendedGuardedSmoothBaseMass W K betaAct deltaStar
  let activeSeed : forall n, (D n).Sample -> Real := fun n =>
    bankPaperCanonicalScaledActiveSeed (T n) (guardedBase n)
  let initialLambda : Nat -> Real :=
    bankPaperCanonicalActualFrozenLogMassFamily
      D fixed bankBase candidates initialSelector activeSeed
  let initialM0 : Nat -> Real :=
    bankPaperCanonicalActualFrozenTotalMassFamily
      D fixed bankBase candidates initialSelector activeSeed
  have HqTilde : ∀ᶠ n : Nat in atTop,
      guardedBase n = bankPaperCanonicalLiteralQMass D activeSeed n := by
    filter_upwards [] with n
    simp only [guardedBase, activeSeed, bankPaperCanonicalLiteralQMass,
      bankPaperCanonicalLiteralActiveMass_scaledActiveSeed]
  have HinitialMass : BankPaperCanonicalActualSelectorMassEstimate
      c fixed bankBase candidates initialSelector := by
    apply bankPaperCanonicalActualSelectorMassEstimate_of_frozenBaselineSource
      D T fixed bankBase candidates initialSelector activeSeed guardedBase
        (bankPaperCanonicalCentralTailLogTarget c)
    · simpa only [activeSeed, guardedBase]
        using HinitialConstructor
    · exact HqTilde
    · simpa only [activeSeed, guardedBase, initialLambda, initialM0]
        using Hbaseline
  have Hcorrection : BankPaperCanonicalGuardedSmoothCorrectionEstimate
      guardedBase guardedBase := by
    have hzero : (fun _n : Nat => (0 : Real)) =o[atTop]
        secondOrderScale := isLittleO_zero _ _
    exact hzero.congr_left fun n => by ring
  have Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      guardedBase
      (bankPaperCanonicalSmoothA0Family
        (bankPaperCanonicalCentralTailLogTarget c) initialLambda
          mFrozen guardedBase) := by
    apply bankPaperCanonicalSectionEightAnalyticLedger_of_correctionAndBaseline
      depth W K betaAct deltaStar F guardedBase
        (bankPaperCanonicalUpperTailHeight c)
        (bankPaperCanonicalCentralTailLogTarget c)
        initialLambda initialM0 mFrozen Hcorrection
    simpa only [initialLambda, initialM0, activeSeed, guardedBase]
      using Hbaseline
  have Hselector : BankPaperCanonicalActualSelectorMassEstimate
      c fixed bankBase candidates finalSelector := by
    apply
      BankPaperRealization.bankPaperCanonicalActualSelectorMassEstimate_of_constructedSmoothQuota
        depth W K poolMinimum hc hdelta hmu fixed bankBase candidates
          initialSelector finalSelector mFrozen guardedBase
          (bankPaperCanonicalCentralTailLogTarget c) initialLambda
    · exact HinitialMass
    · exact Hledger
    · filter_upwards [Hconstructed] with n hwitness
      rcases hwitness with
        ⟨hn, hfixed, hbankBase, hcandidates, hmFrozen,
          hinitialRows, hfinalRows, hquota⟩
      refine ⟨F.realization n hn, F.certificate n hn,
        hfixed, hbankBase, hcandidates, ?_, hinitialRows,
        hfinalRows, ?_⟩
      · simpa only [guardedBase] using hmFrozen
      · simpa only [guardedBase, activeSeed, initialLambda] using hquota
  apply
    bankPaperCanonicalSectionEightAnalyticLedger_of_scaledActualData_intervalGeometry
      hc depth W K betaAct deltaStar F D T fixed bankBase
        candidates finalSelector mFrozen
  · simpa only [activeSeed, guardedBase]
      using HfinalConstructor
  · exact Hgeometry
  · exact Hselector

end

end Erdos390.WholePaper
