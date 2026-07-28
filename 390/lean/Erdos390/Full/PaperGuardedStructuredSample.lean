import Erdos390.Full.PaperGuardCensus
import Erdos390.Full.PaperBridgeFit
import Erdos390.Full.GuardDeletionFamilyRows

/-!
# Canonical guarded structured sample

This module attaches the concrete guard ledger to the literal physical
structured cells used by the bridge.  Both physical endpoints are definitionally
`floor(A*n)`, and nonemptiness after guard deletion is derived from the proved
Dickman cell-density theorem and the concrete `O(y log n)` image census.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperGuardCensus

open ArithmeticModel Scale StructuredCells HeadPattern
open PaperScaleMarkedCell
open PaperBridgeFit

noncomputable section

/-- Fixed physical intervals for the two bridge pools. -/
structure PhysicalIntervals where
  lower : PhysicalSign → ℝ
  upper : PhysicalSign → ℝ
  lower_pos : ∀ sigma, 0 < lower sigma
  lower_lt_upper : ∀ sigma, lower sigma < upper sigma
  separated : upper .minus < lower .plus

variable {Head : Type*} [Fintype Head]

/-- The unguarded head/physical cell with the paper's natural endpoints. -/
def rawCell (P : Head → Pattern) (I : PhysicalIntervals)
    (n : ℕ) (c : Cell Head) : Finset ℕ :=
  structuredCell (P c.1)
    (physicalBound (I.lower c.2) n)
    (physicalBound (I.upper c.2) n)
    (yNat n)

omit [Fintype Head] in
theorem rawCell_eq (P : Head → Pattern) (I : PhysicalIntervals)
    (n : ℕ) (c : Cell Head) :
    rawCell P I n c =
      structuredCell (P c.1)
        (physicalBound (I.lower c.2) n)
        (physicalBound (I.upper c.2) n) (yNat n) := rfl

/-- Every raw cell has its proved positive Dickman density eventually. -/
theorem eventually_rawCell_density
    (P : Head → Pattern) (I : PhysicalIntervals) :
    ∀ᶠ n : ℕ in atTop, ∀ c : Cell Head,
      paperCellDensity (P c.1) (I.lower c.2) (I.upper c.2) *
          (n : ℝ) / 2 ≤ (rawCell P I n c).card := by
  rw [Filter.eventually_all]
  intro c
  obtain ⟨N₀, hN₀⟩ := exists_structuredCell_density_lower_bound
    (P c.1) (I.lower_pos c.2) (I.lower_lt_upper c.2)
  filter_upwards [eventually_ge_atTop N₀] with n hn
  simpa only [rawCell] using hN₀ hn

/-- Strict separation of the two floored physical pools follows from the
fixed strict separation of their real endpoints. -/
theorem eventually_physicalBound_separated (I : PhysicalIntervals) :
    ∀ᶠ n : ℕ in atTop,
      physicalBound (I.upper .minus) n <
        physicalBound (I.lower .plus) n := by
  let gap : ℝ := I.lower .plus - I.upper .minus
  have hgap : 0 < gap := sub_pos.mpr I.separated
  have htop : Tendsto (fun n : ℕ ↦ gap * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hgap)
  have hevent := htop.eventually (eventually_gt_atTop (1 : ℝ))
  filter_upwards [hevent, eventually_gt_atTop 0] with n hlarge hn
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hminus :
      (physicalBound (I.upper .minus) n : ℝ) ≤
        I.upper .minus * (n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg (le_of_lt
      ((I.lower_pos .minus).trans (I.lower_lt_upper .minus))) hn0)
  have hplus :
      I.lower .plus * (n : ℝ) <
        (physicalBound (I.lower .plus) n : ℝ) + 1 := by
    unfold physicalBound
    exact Nat.lt_floor_add_one _
  have hcast :
      (physicalBound (I.upper .minus) n : ℝ) <
        (physicalBound (I.lower .plus) n : ℝ) := by
    dsimp only [gap] at hlarge
    nlinarith
  exact_mod_cast hcast

/-- After the concrete image census, every physical/head cell remains
nonempty.  No cardinality estimate is supplied as a hypothesis. -/
theorem eventually_guarded_rawCell_nonempty
    [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    {Cprom Cbank : ℕ} (G : ∀ n, Ledger n Cprom Cbank) :
    ∀ᶠ n : ℕ in atTop, ∀ c : Cell Head,
      (rawCell P I n c \ (G n).guards).Nonempty := by
  have hdensity := eventually_rawCell_density P I
  have hratio := Ledger.tendsto_card_div_nat_zero G
  have hsmall : ∀ᶠ n : ℕ in atTop, ∀ c : Cell Head,
      ((G n).guards.card : ℝ) / (n : ℝ) <
        paperCellDensity (P c.1) (I.lower c.2) (I.upper c.2) / 2 := by
    rw [Filter.eventually_all]
    intro c
    have hc : 0 <
        paperCellDensity (P c.1) (I.lower c.2) (I.upper c.2) / 2 :=
      half_pos (paperCellDensity_pos (P c.1) (I.lower_lt_upper c.2))
    exact hratio.eventually (eventually_lt_nhds hc)
  filter_upwards [hdensity, hsmall, eventually_gt_atTop 0] with
      n hdens hguard hn c
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hguardScaled :
      ((G n).guards.card : ℝ) <
        paperCellDensity (P c.1) (I.lower c.2) (I.upper c.2) *
          (n : ℝ) / 2 := by
    have hmul := (div_lt_iff₀ hnR).mp (hguard c)
    nlinarith
  have hcardR : ((G n).guards.card : ℝ) < (rawCell P I n c).card :=
    hguardScaled.trans_le (hdens c)
  have hcard : (G n).guards.card < (rawCell P I n c).card := by
    exact_mod_cast hcardR
  rw [Finset.sdiff_nonempty]
  intro hsubset
  exact (Nat.not_lt_of_ge (Finset.card_le_card hsubset)) hcard

/-- Canonical `StructuredSampleData` built from fixed physical constants and
the concrete ledger.  Its endpoints and guard set reduce definitionally to
the paper objects. -/
def canonicalSampleData
    (P : Head → Pattern) (I : PhysicalIntervals)
    {n W Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (hsep : physicalBound (I.upper .minus) n <
      physicalBound (I.lower .plus) n)
    (hnonempty : ∀ c : Cell Head,
      (rawCell P I n c \ G.guards).Nonempty) :
    StructuredSampleData Head where
  n := n
  W := W
  pattern := P
  lo := fun sigma ↦ physicalBound (I.lower sigma) n
  hi := fun sigma ↦ physicalBound (I.upper sigma) n
  lo_le_hi := by
    intro sigma
    unfold physicalBound
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_right (I.lower_lt_upper sigma).le (by positivity)
  physical_separated := hsep
  guards := G.guards
  cell_nonempty := by
    intro c
    simpa only [rawCell] using hnonempty c

@[simp] theorem canonicalSampleData_n
    (P : Head → Pattern) (I : PhysicalIntervals)
    {n W Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (hsep) (hnonempty) :
    (canonicalSampleData (W := W) P I G hsep hnonempty).n = n := rfl

@[simp] theorem canonicalSampleData_W
    (P : Head → Pattern) (I : PhysicalIntervals)
    {n W Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (hsep) (hnonempty) :
    (canonicalSampleData (W := W) P I G hsep hnonempty).W = W := rfl

@[simp] theorem canonicalSampleData_pattern
    (P : Head → Pattern) (I : PhysicalIntervals)
    {n W Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (hsep) (hnonempty) :
    (canonicalSampleData (W := W) P I G hsep hnonempty).pattern = P := rfl

@[simp] theorem canonicalSampleData_lo
    (P : Head → Pattern) (I : PhysicalIntervals)
    {n W Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (hsep) (hnonempty) (sigma : PhysicalSign) :
    (canonicalSampleData (W := W) P I G hsep hnonempty).lo sigma =
      physicalBound (I.lower sigma) n := rfl

@[simp] theorem canonicalSampleData_hi
    (P : Head → Pattern) (I : PhysicalIntervals)
    {n W Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (hsep) (hnonempty) (sigma : PhysicalSign) :
    (canonicalSampleData (W := W) P I G hsep hnonempty).hi sigma =
      physicalBound (I.upper sigma) n := rfl

@[simp] theorem canonicalSampleData_guards
    (P : Head → Pattern) (I : PhysicalIntervals)
    {n W Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (hsep) (hnonempty) :
    (canonicalSampleData (W := W) P I G hsep hnonempty).guards = G.guards := rfl

@[simp] theorem canonicalSampleData_cellFinset
    (P : Head → Pattern) (I : PhysicalIntervals)
    {n W Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (hsep) (hnonempty) (c : Cell Head) :
    (canonicalSampleData (W := W) P I G hsep hnonempty).cellFinset c =
      rawCell P I n c \ G.guards := rfl

/-- For every sufficiently large `n`, the canonical fixed-endpoint,
concrete-guard sample data exists. -/
theorem eventually_exists_canonicalSampleData
    [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    (W Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank) :
    ∀ᶠ n : ℕ in atTop,
      ∃ D : StructuredSampleData Head,
        D.n = n ∧ D.W = W ∧ D.pattern = P ∧
        (∀ sigma, D.lo sigma = physicalBound (I.lower sigma) n) ∧
        (∀ sigma, D.hi sigma = physicalBound (I.upper sigma) n) ∧
        D.guards = (G n).guards ∧
        (∀ c, D.cellFinset c = rawCell P I n c \ (G n).guards) := by
  filter_upwards [eventually_physicalBound_separated I,
    eventually_guarded_rawCell_nonempty P I G] with n hsep hnonempty
  let D := canonicalSampleData (W := W) P I (G n) hsep hnonempty
  refine ⟨D, rfl, rfl, rfl, ?_, ?_, rfl, ?_⟩
  · intro sigma
    rfl
  · intro sigma
    rfl
  · intro c
    rfl

end

end Erdos390.Full.PaperGuardCensus
