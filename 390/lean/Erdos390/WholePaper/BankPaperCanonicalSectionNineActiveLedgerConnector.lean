import Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellOuterCapacityConnector

/-!
# Density packaging for the Section 9 active ledger

The weak Section 9 local input asks for one fixed constant `Cactive` such
that every literal baseline coordinate is at most `Cactive / L`.  For the
canonical scaled seed this is already a consequence of three earlier facts:

* its mass family is `O(secondOrderScale)`;
* every guard-deleted canonical cell has a fixed positive linear density;
* every normalized barycentric cell mass is at most one.

This file packages those facts.  The finite lemma exposes the exact
mass/cardinality calculation.  The eventual theorem uses the proved
guarded raw-cell density and takes a genuine finite minimum over all fixed
head/physical cells.  No coordinate bound is assumed.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## A common density for every fixed canonical cell -/

/-- The smallest literal guard-deleted density among the finite family of
head/physical cells. -/
def bankPaperCanonicalGuardedCellDensityFloor
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (Phead : Head → HeadPattern.Pattern)
    (I : PhysicalIntervals) : Real :=
  let densities := (Finset.univ : Finset (Cell Head)).image
    (fun cell =>
      paperCellDensity (Phead cell.1)
        (I.lower cell.2) (I.upper cell.2) / 4)
  densities.min' (by
    exact Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- The finite density floor is strictly positive. -/
theorem bankPaperCanonicalGuardedCellDensityFloor_pos
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (Phead : Head → HeadPattern.Pattern)
    (I : PhysicalIntervals) :
    0 < bankPaperCanonicalGuardedCellDensityFloor Phead I := by
  classical
  let densities := (Finset.univ : Finset (Cell Head)).image
    (fun cell =>
      paperCellDensity (Phead cell.1)
        (I.lower cell.2) (I.upper cell.2) / 4)
  have hdensities : densities.Nonempty :=
    Finset.univ_nonempty.image _
  have hmem :
      bankPaperCanonicalGuardedCellDensityFloor Phead I ∈ densities := by
    exact Finset.min'_mem densities hdensities
  obtain ⟨cell, _hcell, hEq⟩ := Finset.mem_image.mp hmem
  rw [← hEq]
  exact div_pos
    (paperCellDensity_pos (Phead cell.1)
      (I.lower_lt_upper cell.2))
    (by norm_num)

/-- The density floor is below the proved guarded density of each cell. -/
theorem bankPaperCanonicalGuardedCellDensityFloor_le
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (Phead : Head → HeadPattern.Pattern)
    (I : PhysicalIntervals) (cell : Cell Head) :
    bankPaperCanonicalGuardedCellDensityFloor Phead I ≤
      paperCellDensity (Phead cell.1)
        (I.lower cell.2) (I.upper cell.2) / 4 := by
  classical
  unfold bankPaperCanonicalGuardedCellDensityFloor
  exact Finset.min'_le _ _
    (Finset.mem_image.mpr ⟨cell, Finset.mem_univ cell, rfl⟩)

/-! ## Finite coordinate packaging -/

/-- A paper-scale upper bound for the scaled mass and a linear lower bound
for every cell cardinality imply the exact active-ledger coordinate bound.

The only barycentric estimate used here is the already proved
`cellMass ≤ 1`; the bridge baseline enters solely through its pointwise
identification with the canonical scaled seed. -/
theorem bankPaperCanonical_activeLedger_of_scaledSeed_cellDensity
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
      B.baseline.baseWeight m ≤ (Cq / density) / B.L := by
  intro m
  let cell := B.sampleData.cellOf m
  have hcardPos :
      0 < (Fintype.card (B.sampleData.SampleAt cell) : Real) := by
    exact_mod_cast B.sampleData.sampleAt_card_pos cell
  have hcellPos : 0 < T.baseline.cellMass cell :=
    T.baseline.cellMass_pos cell
  have hcellOne : T.baseline.cellMass cell ≤ 1 :=
    bankPaperCanonical_baseline_cellMass_le_one T cell
  have hscaled :
      bankPaperCanonicalScaledActiveSeed T q m =
        (q * T.baseline.cellMass cell) /
          Fintype.card (B.sampleData.SampleAt cell) := by
    unfold bankPaperCanonicalScaledActiveSeed BaselineAllocation.baseWeight
    change
      q * (T.baseline.cellMass cell /
          Fintype.card (B.sampleData.SampleAt cell)) =
        (q * T.baseline.cellMass cell) /
          Fintype.card (B.sampleData.SampleAt cell)
    ring
  have hscaledUpper :
      B.baseline.baseWeight m ≤
        |q| / Fintype.card (B.sampleData.SampleAt cell) := by
    rw [hseed m, hscaled]
    calc
      (q * T.baseline.cellMass cell) /
            Fintype.card (B.sampleData.SampleAt cell) ≤
          (|q| * T.baseline.cellMass cell) /
            Fintype.card (B.sampleData.SampleAt cell) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self q) hcellPos.le)
          hcardPos.le
      _ ≤ (|q| * 1) /
            Fintype.card (B.sampleData.SampleAt cell) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcellOne (abs_nonneg q))
          hcardPos.le
      _ = |q| / Fintype.card (B.sampleData.SampleAt cell) := by
        ring
  have hmassUpper :
      |q| / Fintype.card (B.sampleData.SampleAt cell) ≤
        (Cq * secondOrderScale B.sampleData.n) /
          Fintype.card (B.sampleData.SampleAt cell) :=
    div_le_div_of_nonneg_right hq hcardPos.le
  have hfactorNonneg : 0 ≤ (Cq / density) / B.L :=
    div_nonneg (div_nonneg hCq hdensity.le) B.L_pos.le
  have hcardScaled :=
    mul_le_mul_of_nonneg_left (hcard cell) hfactorNonneg
  have hscaleIdentity :
      Cq * secondOrderScale B.sampleData.n =
        ((Cq / density) / B.L) *
          (density * (B.sampleData.n : Real)) := by
    change
      Cq * ((B.sampleData.n : Real) / B.L) =
        ((Cq / density) / B.L) *
          (density * (B.sampleData.n : Real))
    field_simp [hdensity.ne', B.L_pos.ne']
  have hcapacity :
      (Cq * secondOrderScale B.sampleData.n) /
            Fintype.card (B.sampleData.SampleAt cell) ≤
        (Cq / density) / B.L := by
    apply (div_le_iff₀ hcardPos).2
    calc
      Cq * secondOrderScale B.sampleData.n =
          ((Cq / density) / B.L) *
            (density * (B.sampleData.n : Real)) :=
        hscaleIdentity
      _ ≤ ((Cq / density) / B.L) *
            (Fintype.card (B.sampleData.SampleAt cell) : Real) :=
        hcardScaled
  exact hscaledUpper.trans (hmassUpper.trans hcapacity)

/-! ## Eventual canonical density wrapper -/

/-- The exact active-ledger package needed by the weak Section 9 local
input.  A single constant works for every sufficiently large canonical
sample, every compatible bridge, and every normalized barycentric target
whose scaled seed is the bridge baseline. -/
theorem exists_eventually_bankPaperCanonical_activeLedger_of_q0_isBigO
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
                B.baseline.baseWeight m ≤ Cactive / B.L := by
  rcases (isBigO_iff').mp Hq0 with ⟨Cq, hCq, hqUpper⟩
  let density := bankPaperCanonicalGuardedCellDensityFloor Phead I
  have hdensity : 0 < density := by
    simpa only [density] using
      bankPaperCanonicalGuardedCellDensityFloor_pos Phead I
  refine ⟨Cq / density, div_nonneg hCq.le hdensity.le, ?_⟩
  have hguardedDensity :=
    eventually_guarded_rawCell_density Phead I Cprom Cbank ledger
  filter_upwards [hqUpper, hguardedDensity, eventually_gt_atTop 1] with
      n hqUpperN hguardedDensityN hn
  intro B hBn hsep hremaining hcanonical T hseed
  have hscalePos : 0 < secondOrderScale n :=
    secondOrderScale_pos (by omega)
  have hqBound : |q0 n| ≤ Cq * secondOrderScale n := by
    simpa only [Real.norm_eq_abs, abs_of_pos hscalePos] using hqUpperN
  have hnReal : 0 < (n : Real) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hcard :
      ∀ cell : Cell Head,
        density * (B.sampleData.n : Real) ≤
          (Fintype.card (B.sampleData.SampleAt cell) : Real) := by
    intro cell
    have hcellFinset :
        B.sampleData.cellFinset cell =
          rawCell Phead I n cell \ (ledger n).guards := by
      calc
        B.sampleData.cellFinset cell =
            (canonicalSampleData (W := B.sampleData.W)
              Phead I (ledger B.sampleData.n)
                hsep hremaining).cellFinset cell :=
          congrArg
            (fun D : StructuredSampleData Head => D.cellFinset cell)
            hcanonical
        _ = rawCell Phead I B.sampleData.n cell \
            (ledger B.sampleData.n).guards :=
          canonicalSampleData_cellFinset
            Phead I (ledger B.sampleData.n) hsep hremaining cell
        _ = rawCell Phead I n cell \ (ledger n).guards := by
          rw [hBn]
    have hcardEq :
        (Fintype.card (B.sampleData.SampleAt cell) : Real) =
          ((rawCell Phead I n cell \ (ledger n).guards).card : Real) := by
      rw [Fintype.card_coe, hcellFinset]
    have hdensityLe :
        density ≤
          paperCellDensity (Phead cell.1)
            (I.lower cell.2) (I.upper cell.2) / 4 := by
      simpa only [density] using
        bankPaperCanonicalGuardedCellDensityFloor_le Phead I cell
    calc
      density * (B.sampleData.n : Real) =
          density * (n : Real) := by rw [hBn]
      _ ≤
          (paperCellDensity (Phead cell.1)
            (I.lower cell.2) (I.upper cell.2) / 4) * (n : Real) :=
        mul_le_mul_of_nonneg_right hdensityLe hnReal.le
      _ = paperCellDensity (Phead cell.1)
            (I.lower cell.2) (I.upper cell.2) * (n : Real) / 4 := by
        ring
      _ ≤ ((rawCell Phead I n cell \
          (ledger n).guards).card : Real) :=
        hguardedDensityN cell
      _ = (Fintype.card
          (B.sampleData.SampleAt cell) : Real) :=
        hcardEq.symm
  have hqBoundB :
      |q0 n| ≤ Cq * secondOrderScale B.sampleData.n := by
    simpa only [hBn] using hqBound
  exact
    bankPaperCanonical_activeLedger_of_scaledSeed_cellDensity
      B T (q0 n) Cq density hCq.le hdensity hqBoundB hcard hseed

end BankPaperRealization

end

end Erdos390.WholePaper
