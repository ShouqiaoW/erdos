import Erdos390.WholePaper.BankPaperCanonicalTopFrozenImplementationRateReductionConnector

/-!
# Exact reduction of the smooth source-to-guarded rate

The literal frozen-top implementation defect has already been reduced to
complete rough label `1`.  This file exposes the finite algebra inside that
last row.

There are two points which are easy to conflate.

* The paper's `qTilde` is the mass of the guarded active broad layer.  When
  the canonical scaled seed is instantiated at that mass, its literal mass
  is *exactly* the guarded smooth base mass.  No asymptotic comparison is
  needed.
* The valuation moment is not determined by total mass.  After the exact
  mass synchronization, the remaining analytic term is the difference
  between the scaled barycentric valuation moment and the uniform guarded
  broad-pool valuation moment.  The nearest-integer normalization contributes
  only the two explicit zero-head-cell moments.

The declarations below prove only these exact reductions.  In particular,
no `O(1 / (p L))` valuation comparison is introduced as an assumption.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.StructuredCells

noncomputable section

namespace BankPaperRealization

/-! ## Exact moving structured-cell identification -/

/-- The raw label-one head-free broad pool is not merely equinumerous with
a structured cell: it is literally the moving-upper structured cell for
the zero head pattern. -/
theorem bankPaperCanonicalRawSmoothBasePool_eq_zeroHeadStructuredCell
    (W n h K : Nat) :
    bankPaperCanonicalRawSmoothBasePool W n h K =
      structuredCell (roughHeadZeroPattern W)
        n (2 * n - K * h) (yNat n) := by
  classical
  ext a
  constructor
  · intro ha
    have haData : a ∈
        roughCanonicalBroadCorrectionPool
          W n h K (yNat n) 1 := by
      simpa only [bankPaperCanonicalRawSmoothBasePool] using ha
    have haRow := mem_completeRoughRowFiber.mp haData
    have haHead := mem_roughHeadFree.mp haRow.1
    have haBroad : n < a ∧ a <= 2 * n - K * h := by
      simpa only [roughBroadLowerBlock, Finset.mem_Ioc] using haHead.1
    have haPos : 0 < a := by omega
    apply mem_structuredCell.mpr
    refine
      ⟨mem_smoothInterval.mpr
          ⟨haBroad.1, haBroad.2,
            (completeRoughLabel_eq_one_iff_mem_smoothNumbers
              haPos).mp haRow.2⟩,
        ?_⟩
    apply
      ((roughHeadZeroPattern W).matches_iff_factor_dvd_and_coprime
        haPos.ne').mpr
    simpa only [roughHeadZeroPattern_factor, one_dvd, Nat.div_one,
      roughHeadZeroPattern_modulus, true_and] using haHead.2
  · intro ha
    have haCell := mem_structuredCell.mp ha
    have haInterval := mem_smoothInterval.mp haCell.1
    have haPos := pos_of_mem_smoothInterval haCell.1
    have haMatch :=
      ((roughHeadZeroPattern W).matches_iff_factor_dvd_and_coprime
        haPos.ne').mp haCell.2
    have haCoprime : Nat.Coprime a (roughHeadModulus W) := by
      simpa only [roughHeadZeroPattern_factor, one_dvd, Nat.div_one,
        roughHeadZeroPattern_modulus, true_and] using haMatch
    unfold bankPaperCanonicalRawSmoothBasePool
    unfold roughCanonicalBroadCorrectionPool
    apply mem_completeRoughRowFiber.mpr
    refine
      ⟨mem_roughHeadFree.mpr
          ⟨by
            simpa only [roughBroadLowerBlock, Finset.mem_Ioc] using
              ⟨haInterval.1, haInterval.2.1⟩,
            haCoprime⟩,
        (completeRoughLabel_eq_one_iff_mem_smoothNumbers
          haPos).mpr haInterval.2.2⟩

/-- Consequently the guarded broad pool is exactly that moving structured
cell with the numerical guard set deleted. -/
theorem roughCanonicalGuardedSmoothBasePool_eq_zeroHeadStructuredCell_sdiff
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K : Nat) :
    R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar W K 1 =
      structuredCell (roughHeadZeroPattern W)
          n (2 * n - K * upperTailLength c n) (yNat n) \
        R.roughCanonicalGuardSet certificate deltaStar := by
  unfold roughCanonicalGuardedBroadCorrectionPool
  rw [← bankPaperCanonicalRawSmoothBasePool_eq_zeroHeadStructuredCell]
  rfl

/-! ## Exact guarded-mass synchronization -/

/-- If the canonical active seed is scaled by the literal guarded smooth
base mass, then its finite total mass is exactly that base mass.  This is
the canonical specialization of the paper's definition of `qTilde`; the
error is identically zero. -/
@[simp] theorem
    bankPaperCanonicalLiteralActiveMass_scaledGuardedSmoothBase_eq
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
    (deltaStar betaAct : Real) :
    bankPaperCanonicalLiteralActiveMass B.sampleData
        (bankPaperCanonicalScaledActiveSeed T
          (bankPaperCanonicalGuardedSmoothBaseMass R certificate
            deltaStar B.sampleData.W K betaAct)) =
      bankPaperCanonicalGuardedSmoothBaseMass R certificate
        deltaStar B.sampleData.W K betaAct := by
  exact bankPaperCanonicalLiteralActiveMass_scaledActiveSeed T _

/-! ## The three literal valuation moments -/

/-- The valuation moment of the scaled barycentric active seed. -/
def bankPaperCanonicalScaledActiveValuationMoment
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head}
    (T : BarycentricTarget D) (q : Real) (p : Nat) : Real :=
  ∑ m : D.Sample,
    bankPaperCanonicalScaledActiveSeed T q m *
      valuation p (D.value m)

/-- The valuation moment of the constant guarded active broad layer. -/
def bankPaperCanonicalGuardedSmoothBaseValuationMoment
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
    (deltaStar betaAct : Real) (p : Nat) : Real :=
  betaAct / B.L *
    ∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      valuation p a

/-- The valuation moment added by the two equal nearest-integer
increments in the physical copies of the zero head cell. -/
def bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
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
    (deltaStar betaProt alpha qTilde : Real) (p : Nat) : Real :=
  let cellMass :=
    bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
      B R certificate deltaStar betaProt alpha qTilde
  cellMass *
      (B.guardedCellProbability (none, .minus)).expect
        (fun m ↦ valuation p (m : Nat)) +
    cellMass *
      (B.guardedCellProbability (none, .plus)).expect
        (fun m ↦ valuation p (m : Nat))

/-- The rounded active valuation moment is exactly the scaled moment plus
the two displayed zero-cell moments. -/
theorem
    sum_bankPaperCanonicalTopFrozenRoundedActiveSeed_mul_valuation_eq_scaled_add_nearestInteger
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
    (deltaStar betaProt alpha qTilde : Real) (p : Nat) :
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde m *
          valuation p (B.sampleData.value m)) =
      bankPaperCanonicalScaledActiveValuationMoment T qTilde p +
        bankPaperCanonicalTopFrozenNearestIntegerValuationMoment (K := K)
          B R certificate deltaStar betaProt alpha qTilde p := by
  unfold bankPaperCanonicalScaledActiveValuationMoment
  unfold bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
  unfold bankPaperCanonicalTopFrozenRoundedActiveSeed
  calc
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
            (bankPaperCanonicalScaledActiveSeed T qTilde)
            (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
              B R certificate deltaStar betaProt alpha qTilde)
            (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
              B R certificate deltaStar betaProt alpha qTilde) m *
          valuation p (B.sampleData.value m)) =
      (∑ m : B.sampleData.Sample,
          bankPaperCanonicalScaledActiveSeed T qTilde m *
            valuation p (B.sampleData.value m)) +
        (∑ m : B.sampleData.Sample,
          bankPaperCanonicalUniformCellIncrement B.sampleData
              (none, .minus)
              (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
                B R certificate deltaStar betaProt alpha qTilde) m *
            valuation p (B.sampleData.value m)) +
        ∑ m : B.sampleData.Sample,
          bankPaperCanonicalUniformCellIncrement B.sampleData
              (none, .plus)
              (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
                B R certificate deltaStar betaProt alpha qTilde) m *
            valuation p (B.sampleData.value m) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m _hm
      unfold bankPaperCanonicalTwoZeroHeadCellRebalance
      ring
    _ =
      (∑ m : B.sampleData.Sample,
          bankPaperCanonicalScaledActiveSeed T qTilde m *
            valuation p (B.sampleData.value m)) +
        (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
              B R certificate deltaStar betaProt alpha qTilde *
            (B.guardedCellProbability (none, .minus)).expect
              (fun m ↦ valuation p (m : Nat)) +
          bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
              B R certificate deltaStar betaProt alpha qTilde *
            (B.guardedCellProbability (none, .plus)).expect
              (fun m ↦ valuation p (m : Nat))) := by
      rw [
        sum_bankPaperCanonicalUniformCellIncrement_mul_valuation_eq_mass_mul_guardedCellProbability_expect
          B (none, .minus)
            (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
              B R certificate deltaStar betaProt alpha qTilde) p,
        sum_bankPaperCanonicalUniformCellIncrement_mul_valuation_eq_mass_mul_guardedCellProbability_expect
          B (none, .plus)
            (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
              B R certificate deltaStar betaProt alpha qTilde) p]
      ring

/-! ## Exact label-one source decomposition -/

/-- Under the paper's range `deltaStar <= 1`, complete rough label `1` is
not exceptional. -/
theorem not_roughCanonicalExceptionalLabel_one
    {n : Nat} {deltaStar : Real}
    (hn : 1 <= n) (hdeltaUpper : deltaStar <= 1) :
    ¬ RoughCanonicalExceptionalLabel n deltaStar 1 := by
  have hnOne : (1 : Real) <= (n : Real) := by exact_mod_cast hn
  have hpow : (n : Real) ^ deltaStar <= (n : Real) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hnOne hdeltaUpper
  unfold RoughCanonicalExceptionalLabel
  norm_num
  nlinarith [show (0 : Real) <= (n : Real) by positivity]

/-- Exact content of the surviving label-one defect: the frozen raw
protected part cancels, leaving the rounded structured active valuation
moment minus the constant guarded broad-layer valuation moment. -/
theorem
    roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect_eq_roundedActive_sub_guardedBase
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat} (K0 : Nat)
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt betaAct qTilde : Real)
    (p : Nat)
    (hn : 1 <= B.sampleData.n) (hdeltaUpper : deltaStar <= 1)
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1) :
    roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect
        B K0 R certificate T deltaStar betaProt betaAct qTilde p =
      (∑ m : B.sampleData.Sample,
          bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K0 + 1)
              B R certificate T deltaStar betaProt
                (bankPaperCanonicalPostHfitBalancedAlpha
                  B c K0 betaProt betaAct)
                qTilde m *
            valuation p (B.sampleData.value m)) -
        bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K0 + 1)
          B R certificate deltaStar betaAct p := by
  classical
  let row :=
    R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1
  let pool :=
    R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
      B.sampleData.W (K0 + 1) 1
  let alpha :=
    bankPaperCanonicalPostHfitBalancedAlpha
      B c K0 betaProt betaAct
  let roundedSeed :=
    bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K0 + 1)
      B R certificate T deltaStar betaProt alpha qTilde
  let source :=
    bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K0 + 1)
      B R certificate T deltaStar betaProt alpha
        (betaProt + betaAct) qTilde
  let rawProt := roughHeadCompatibleRawWeight B.sampleData.W
    B.sampleData.n (upperTailLength c B.sampleData.n) (K0 + 1)
      alpha betaProt B.L
  let rawTotal := roughHeadCompatibleRawWeight B.sampleData.W
    B.sampleData.n (upperTailLength c B.sampleData.n) (K0 + 1)
      alpha (betaProt + betaAct) B.L
  have hnotExceptional :
      ¬ RoughCanonicalExceptionalLabel B.sampleData.n deltaStar 1 :=
    not_roughCanonicalExceptionalLabel_one hn hdeltaUpper
  have hnotActive :
      ¬ RoughCanonicalActiveNonexceptionalLabel
        B.sampleData.n deltaStar 1 := by
    intro hactive
    exact hactive.1 rfl
  have hsmoothLabel :
      1 ∈ completeRoughLabelSet (yNat B.sampleData.n)
        (roughRawCandidateSet B.sampleData.n
          (upperTailLength c B.sampleData.n) (K0 + 1)) := by
    obtain ⟨a, ha⟩ :=
      B.sampleData.cell_nonempty
        ((none : PaperHeadSimplex.Tag P), .minus)
    let m : B.sampleData.Sample :=
      ⟨((none : PaperHeadSimplex.Tag P), .minus), ⟨a, ha⟩⟩
    have hmRow := hvalues m
    have hmData := mem_completeRoughRowFiber.mp hmRow
    apply mem_completeRoughLabelSet.mpr
    exact
      ⟨B.sampleData.value m,
        R.roughCanonicalGuardedCandidateSet_subset_rawCandidateSet
          certificate deltaStar (K0 + 1) hmData.1,
        hmData.2⟩
  have hsource :
      (∑ a ∈ row, source a * valuation p a) =
        (∑ a ∈ row, rawProt a * valuation p a) +
          ∑ m : B.sampleData.Sample,
            roundedSeed m * valuation p (B.sampleData.value m) := by
    calc
      (∑ a ∈ row, source a * valuation p a) =
          ∑ a ∈ row,
            (rawProt a +
              bankPaperCanonicalActiveSeedAmbientWeight
                B.sampleData roundedSeed a) * valuation p a := by
        apply Finset.sum_congr rfl
        intro a ha
        have ha' :
            a ∈ R.roughCanonicalGuardedRow certificate deltaStar
              (K0 + 1) 1 := by
          simpa only [row] using ha
        have hpoint :=
          bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
            (K := K0 + 1) B R certificate
              (deltaStar := deltaStar) (betaProt := betaProt)
              (alpha := alpha) (beta := betaProt + betaAct)
              roundedSeed ha'
        simpa only [source, rawProt, roundedSeed, alpha,
          bankPaperCanonicalTopFrozenRoundedSourceSelector] using
          congrArg (fun x : Real ↦ x * valuation p a) hpoint
      _ =
          (∑ a ∈ row, rawProt a * valuation p a) +
            ∑ a ∈ row,
              bankPaperCanonicalActiveSeedAmbientWeight
                  B.sampleData roundedSeed a * valuation p a := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _ha
        ring
      _ =
          (∑ a ∈ row, rawProt a * valuation p a) +
            ∑ m : B.sampleData.Sample,
              roundedSeed m * valuation p (B.sampleData.value m) := by
        rw [
          sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
            B.sampleData roundedSeed row
              (by
                intro m
                simpa only [row] using hvalues m)
              p]
  have hfilter :
      row.filter (fun a ↦ a ∈ pool) = pool := by
    ext a
    simp only [Finset.mem_filter]
    constructor
    · exact fun ha ↦ ha.2
    · intro ha
      exact
        ⟨by
          simpa only [row, pool] using
            R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
              certificate deltaStar B.sampleData.W (K0 + 1) 1 ha,
          ha⟩
  have hactiveMoment :
      (∑ a ∈ row,
          (if a ∈ pool then betaAct / B.L else 0) * valuation p a) =
        betaAct / B.L * ∑ a ∈ pool, valuation p a := by
    calc
      (∑ a ∈ row,
          (if a ∈ pool then betaAct / B.L else 0) * valuation p a) =
          ∑ a ∈ row.filter (fun a ↦ a ∈ pool),
            betaAct / B.L * valuation p a := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a _ha
        by_cases haPool : a ∈ pool <;> simp [haPool]
      _ = ∑ a ∈ pool, betaAct / B.L * valuation p a := by
        rw [hfilter]
      _ = betaAct / B.L * ∑ a ∈ pool, valuation p a := by
        rw [Finset.mul_sum]
  have hraw :
      (∑ a ∈ row, rawTotal a * valuation p a) =
        (∑ a ∈ row, rawProt a * valuation p a) +
          betaAct / B.L * ∑ a ∈ pool, valuation p a := by
    calc
      (∑ a ∈ row, rawTotal a * valuation p a) =
          ∑ a ∈ row,
            (rawProt a +
              if a ∈ pool then betaAct / B.L else 0) *
                valuation p a := by
        apply Finset.sum_congr rfl
        intro a ha
        have ha' :
            a ∈ R.roughCanonicalGuardedRow certificate deltaStar
              (K0 + 1) 1 := by
          simpa only [row] using ha
        have hpoint :=
          roughHeadCompatibleRawWeight_split_protected_active_of_mem_guardedSmoothRow
            (K := K0 + 1) B R certificate
              (deltaStar := deltaStar) (betaProt := betaProt)
              (betaAct := betaAct) (alpha := alpha) ha'
        simpa only [rawTotal, rawProt, pool, alpha] using
          congrArg (fun x : Real ↦ x * valuation p a) hpoint
      _ =
          (∑ a ∈ row, rawProt a * valuation p a) +
            ∑ a ∈ row,
              (if a ∈ pool then betaAct / B.L else 0) *
                valuation p a := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _ha
        ring
      _ =
          (∑ a ∈ row, rawProt a * valuation p a) +
            betaAct / B.L * ∑ a ∈ pool, valuation p a := by
        rw [hactiveMoment]
  unfold
    roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect
  unfold roughCanonicalSmoothSourceToGuardedValuationDefect
  rw [if_pos hsmoothLabel]
  unfold roughCanonicalPostchargeSourceGuardedRowValuationDefectAtLabel
  unfold roughCanonicalSourceGuardedRowValuationDefectAtLabel
  rw [
    R.completeRoughRowFiber_nonexceptionalGuarded_eq_guardedRow
      certificate deltaStar hnotExceptional,
    if_neg hnotActive]
  unfold bankPaperCanonicalGuardedSmoothBaseValuationMoment
  change
    (∑ a ∈ row, source a * valuation p a) -
        (∑ a ∈ row, rawTotal a * valuation p a) - 0 =
      (∑ m : B.sampleData.Sample,
          roundedSeed m * valuation p (B.sampleData.value m)) -
        betaAct / B.L * ∑ a ∈ pool, valuation p a
  rw [hsource, hraw]
  ring

/-- Final exact decomposition.  Once the total mass has been synchronized,
the only large analytic comparison is the displayed scaled-active versus
guarded-broad moment; the nearest-integer contribution is already an
explicit two-cell term. -/
theorem
    roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect_eq_scaled_sub_guardedBase_add_nearestInteger
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat} (K0 : Nat)
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt betaAct qTilde : Real)
    (p : Nat)
    (hn : 1 <= B.sampleData.n) (hdeltaUpper : deltaStar <= 1)
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1) :
    roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect
        B K0 R certificate T deltaStar betaProt betaAct qTilde p =
      bankPaperCanonicalScaledActiveValuationMoment T qTilde p -
        bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K0 + 1)
          B R certificate deltaStar betaAct p +
        bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            qTilde p := by
  rw [
    roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect_eq_roundedActive_sub_guardedBase
      B K0 R certificate T deltaStar betaProt betaAct qTilde p
        hn hdeltaUpper hvalues,
    sum_bankPaperCanonicalTopFrozenRoundedActiveSeed_mul_valuation_eq_scaled_add_nearestInteger]
  ring

end BankPaperRealization

end

end Erdos390.WholePaper
