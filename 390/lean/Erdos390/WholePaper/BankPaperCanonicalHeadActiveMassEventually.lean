import Erdos390.WholePaper.BankPaperCanonicalActualActiveMeasureConstruction
import Erdos390.WholePaper.UpperScale

/-!
# Eventual lower bound for the paper's head-reserve active mass

The paper obtains its final active mass from the exact ledger

`q^{act}(d) = q₀ - d`,

where the rough smooth active mass satisfies `q₀ ≍ n / log n` and the
height-centering change satisfies `d = O(n / log² n)`.  Only the lower
half of that comparison is needed to prove the constructor hypothesis
`1 <= q^{act}(d)` for all sufficiently large `n`.

The repository's `HeadSimplexReserve` currently stores only
`0 < activeMass`.  It has no family constructor, no connection to the
rough smooth active mass, and no asymptotic lower-bound field.  This file
therefore isolates the exact missing paper input as a positive lower
multiple of `secondOrderScale n = n / log n`.  Everything after that input
is proved here:

* the active mass tends to infinity and eventually exceeds every constant;
* in particular it is eventually at least one;
* an `o(n / log n)` height change preserves a fixed positive lower multiple;
* the paper's stronger `O(n / log² n)` change is automatically little-o;
* the canonical scaled seed has eventual mass at least one and its
  self-selector satisfies the full actual-active-measure constructor.

A concrete reserve of mass `1 / 2` is also constructed.  It proves that
strict positivity alone cannot imply the desired inequality, so the
repository needs an additional growth input until the missing
rough-active-mass construction is connected to `HeadSimplexReserve`.
The predicate below is exactly the lower half of the growth statement
used in the paper.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.Scale

noncomputable section

/-! ## The irreducible paper-scale input -/

/-- The lower half of the paper statement `q_n ≍ n / log n`.

This is strictly weaker than a two-sided comparison and is the minimal
asymptotic fact needed for eventual `1 <= q_n`. -/
def BankPaperCanonicalActiveMassPaperScaleLower
    (q : Nat -> Real) : Prop :=
  exists c : Real, 0 < c ∧
    ∀ᶠ n : Nat in atTop,
      c * secondOrderScale n <= q n

/-- Specialization of the minimal lower input to the mass stored in a
family of paper head-simplex reserves. -/
def BankPaperCanonicalHeadActiveMassPaperScaleLower
    {P : Finset Nat} (Rhead : Nat -> HeadSimplexReserve P) : Prop :=
  BankPaperCanonicalActiveMassPaperScaleLower
    (fun n => (Rhead n).activeMass)

/-! ## Positivity is genuinely insufficient -/

/-- A fully legal head-simplex reserve with positive mass strictly below
one.  The empty head set removes every valuation constraint and makes the
logical gap in `activeMass_pos` explicit. -/
def bankPaperCanonicalSubunitHeadSimplexReserve :
    HeadSimplexReserve (∅ : Finset Nat) where
  exponent := 1
  exponent_pos := by norm_num
  activeMass := 1 / 2
  activeMass_pos := by norm_num
  target := fun p => False.elim (by
    have hnot : ∀ a : Nat, a ∉ (∅ : Finset Nat) :=
      Finset.eq_empty_iff_forall_notMem.mp rfl
    exact hnot p.val p.property)
  margin := 1 / 2
  margin_pos := by norm_num
  vertex_margin := by
    intro p
    exact False.elim (by
      have hnot : ∀ a : Nat, a ∉ (∅ : Finset Nat) :=
        Finset.eq_empty_iff_forall_notMem.mp rfl
      exact hnot p.val p.property)
  zero_margin := by norm_num

@[simp] theorem bankPaperCanonicalSubunitHeadSimplexReserve_activeMass :
    bankPaperCanonicalSubunitHeadSimplexReserve.activeMass = 1 / 2 :=
  rfl

/-- Therefore the current structure fields do not imply `1 <= activeMass`. -/
theorem bankPaperCanonicalSubunitHeadSimplexReserve_not_one_le :
    ¬ 1 <= bankPaperCanonicalSubunitHeadSimplexReserve.activeMass := by
  rw [bankPaperCanonicalSubunitHeadSimplexReserve_activeMass]
  norm_num

/-- Existential form of the same obstruction, retaining the structure's
strict positivity field. -/
theorem exists_headSimplexReserve_pos_activeMass_not_one_le :
    exists Rhead : HeadSimplexReserve (∅ : Finset Nat),
      0 < Rhead.activeMass ∧ ¬ 1 <= Rhead.activeMass := by
  exact ⟨bankPaperCanonicalSubunitHeadSimplexReserve,
    bankPaperCanonicalSubunitHeadSimplexReserve.activeMass_pos,
    bankPaperCanonicalSubunitHeadSimplexReserve_not_one_le⟩

/-! ## All eventual consequences of the minimal input -/

/-- A fixed positive multiple of `n / log n` tends to infinity, hence so
does any active mass lying eventually above it. -/
theorem bankPaperCanonicalActiveMass_tendsto_atTop_of_paperScaleLower
    (q : Nat -> Real)
    (H : BankPaperCanonicalActiveMassPaperScaleLower q) :
    Tendsto q atTop atTop := by
  rcases H with ⟨c, hc, hq⟩
  have hscale : Tendsto
      (fun n : Nat => c * secondOrderScale n) atTop atTop :=
    secondOrderScale_tendsto_atTop.const_mul_atTop hc
  apply tendsto_atTop_mono' atTop _ hscale
  exact hq

/-- Every fixed real threshold is eventually below the active mass. -/
theorem eventually_const_le_bankPaperCanonicalActiveMass_of_paperScaleLower
    (q : Nat -> Real)
    (H : BankPaperCanonicalActiveMassPaperScaleLower q) (C : Real) :
    ∀ᶠ n : Nat in atTop, C <= q n :=
  (bankPaperCanonicalActiveMass_tendsto_atTop_of_paperScaleLower q H).eventually
    (eventually_ge_atTop C)

/-- The exact constructor threshold follows with `C = 1`. -/
theorem eventually_one_le_bankPaperCanonicalActiveMass_of_paperScaleLower
    (q : Nat -> Real)
    (H : BankPaperCanonicalActiveMassPaperScaleLower q) :
    ∀ᶠ n : Nat in atTop, 1 <= q n :=
  eventually_const_le_bankPaperCanonicalActiveMass_of_paperScaleLower
    q H 1

/-- Head-reserve specialization of divergence to infinity. -/
theorem bankPaperCanonicalHeadActiveMass_tendsto_atTop_of_paperScaleLower
    {P : Finset Nat} (Rhead : Nat -> HeadSimplexReserve P)
    (H : BankPaperCanonicalHeadActiveMassPaperScaleLower Rhead) :
    Tendsto (fun n => (Rhead n).activeMass) atTop atTop :=
  bankPaperCanonicalActiveMass_tendsto_atTop_of_paperScaleLower
    (fun n => (Rhead n).activeMass) H

/-- Head-reserve specialization of the eventual constructor threshold. -/
theorem eventually_one_le_bankPaperCanonicalHeadActiveMass
    {P : Finset Nat} (Rhead : Nat -> HeadSimplexReserve P)
    (H : BankPaperCanonicalHeadActiveMassPaperScaleLower Rhead) :
    ∀ᶠ n : Nat in atTop, 1 <= (Rhead n).activeMass :=
  eventually_one_le_bankPaperCanonicalActiveMass_of_paperScaleLower
    (fun n => (Rhead n).activeMass) H

/-! ## The exact `q₀-d` height-centering algebra -/

/-- The paper's error scale `n / log² n` is little-o of
`secondOrderScale n = n / log n`. -/
theorem secondOrderScale_div_L_isLittleO_secondOrderScale :
    (fun n : Nat => secondOrderScale n / L n) =o[atTop]
      secondOrderScale := by
  have hzero : ∀ᶠ n : Nat in atTop,
      secondOrderScale n = 0 -> secondOrderScale n / L n = 0 :=
    Eventually.of_forall fun n hn => by simp [hn]
  apply (isLittleO_iff_tendsto' hzero).mpr
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : Nat => (L n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hLTop
  apply hinv.congr'
  filter_upwards [eventually_secondOrderScale_pos,
      eventually_gt_atTop 1] with n hscale hn
  have hL : 0 < L n := L_pos hn
  field_simp [hscale.ne', hL.ne']

/-- Subtracting a little-o height-centering change from a macroscopically
positive base mass preserves half of its lower constant. -/
theorem bankPaperCanonicalActiveMassPaperScaleLower_sub_of_isLittleO
    (q0 d : Nat -> Real)
    (Hq0 : BankPaperCanonicalActiveMassPaperScaleLower q0)
    (hd : d =o[atTop] secondOrderScale) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (fun n => q0 n - d n) := by
  rcases Hq0 with ⟨c, hc, hq0⟩
  refine ⟨c / 2, half_pos hc, ?_⟩
  have hdBound := hd.bound (half_pos hc)
  filter_upwards [hq0, hdBound, eventually_secondOrderScale_pos]
      with n hq0n hdn hscale
  have hdn' : |d n| <= (c / 2) * secondOrderScale n := by
    simpa only [Real.norm_eq_abs, abs_of_pos hscale] using hdn
  have hdle : d n <= (c / 2) * secondOrderScale n :=
    (le_abs_self (d n)).trans hdn'
  calc
    (c / 2) * secondOrderScale n =
        c * secondOrderScale n -
          (c / 2) * secondOrderScale n := by ring
    _ <= q0 n - (c / 2) * secondOrderScale n :=
      sub_le_sub_right hq0n _
    _ <= q0 n - d n := sub_le_sub_left hdle _

/-- This is the paper's displayed implication: a base mass bounded below
on the `n / log n` scale and a change of order `n / log² n` yield a final
active mass with the required positive paper-scale lower bound. -/
theorem bankPaperCanonicalActiveMassPaperScaleLower_sub_of_logScale_isBigO
    (q0 d : Nat -> Real)
    (Hq0 : BankPaperCanonicalActiveMassPaperScaleLower q0)
    (hd : d =O[atTop]
      (fun n : Nat => secondOrderScale n / L n)) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (fun n => q0 n - d n) := by
  apply bankPaperCanonicalActiveMassPaperScaleLower_sub_of_isLittleO
    q0 d Hq0
  exact hd.trans_isLittleO
    secondOrderScale_div_L_isLittleO_secondOrderScale

/-- Exact specialization to `HeadSimplexReserve.activeMass`.  This is the
minimal bridge still missing from the repository's rough smooth ledger:
identify the stored mass with `q₀-d`, prove a positive lower multiple for
`q₀`, and prove the displayed logarithmic bound for `d`. -/
theorem bankPaperCanonicalHeadActiveMassPaperScaleLower_of_heightCenter
    {P : Finset Nat} (Rhead : Nat -> HeadSimplexReserve P)
    (q0 d : Nat -> Real)
    (hactiveMass : forall n,
      (Rhead n).activeMass = q0 n - d n)
    (Hq0 : BankPaperCanonicalActiveMassPaperScaleLower q0)
    (hd : d =O[atTop]
      (fun n : Nat => secondOrderScale n / L n)) :
    BankPaperCanonicalHeadActiveMassPaperScaleLower Rhead := by
  rcases bankPaperCanonicalActiveMassPaperScaleLower_sub_of_logScale_isBigO
      q0 d Hq0 hd with ⟨c, hc, hlower⟩
  exact ⟨c, hc, hlower.mono fun n hn => hn.trans_eq (hactiveMass n).symm⟩

/-- Direct eventual `1 <= activeMass` consequence of the paper's
`q₀-d` ledger inputs. -/
theorem eventually_one_le_bankPaperCanonicalHeadActiveMass_of_heightCenter
    {P : Finset Nat} (Rhead : Nat -> HeadSimplexReserve P)
    (q0 d : Nat -> Real)
    (hactiveMass : forall n,
      (Rhead n).activeMass = q0 n - d n)
    (Hq0 : BankPaperCanonicalActiveMassPaperScaleLower q0)
    (hd : d =O[atTop]
      (fun n : Nat => secondOrderScale n / L n)) :
    ∀ᶠ n : Nat in atTop, 1 <= (Rhead n).activeMass := by
  exact eventually_one_le_bankPaperCanonicalHeadActiveMass Rhead
    (bankPaperCanonicalHeadActiveMassPaperScaleLower_of_heightCenter
      Rhead q0 d hactiveMass Hq0 hd)

/-! ## Literal scaled seeds and actual-measure constructors -/

/-- The literal mass of the canonical scaled-seed family tends to infinity
under precisely the minimal paper-scale lower input. -/
theorem bankPaperCanonicalLiteralActiveMass_scaledFamily_tendsto_atTop
    {Head : Type*} [Fintype Head]
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (q : Nat -> Real)
    (H : BankPaperCanonicalActiveMassPaperScaleLower q) :
    Tendsto
      (fun n => bankPaperCanonicalLiteralActiveMass (D n)
        (bankPaperCanonicalScaledActiveSeed (T n) (q n)))
      atTop atTop := by
  simpa only [bankPaperCanonicalLiteralActiveMass_scaledActiveSeed] using
    bankPaperCanonicalActiveMass_tendsto_atTop_of_paperScaleLower q H

/-- Exact varying-mass input used by Proposition 8.7 for the scaled-seed
family, without first postulating an actual-measure constructor. -/
theorem eventually_one_le_bankPaperCanonicalLiteralQMass_scaledFamily
    {Head : Type*} [Fintype Head]
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (q : Nat -> Real)
    (H : BankPaperCanonicalActiveMassPaperScaleLower q) :
    ∀ᶠ n : Nat in atTop,
      1 <= bankPaperCanonicalLiteralQMass D
        (fun n => bankPaperCanonicalScaledActiveSeed (T n) (q n)) n := by
  simpa only [bankPaperCanonicalLiteralQMass,
    bankPaperCanonicalLiteralActiveMass_scaledActiveSeed] using
      eventually_one_le_bankPaperCanonicalActiveMass_of_paperScaleLower q H

/-- Once the eventual lower input is supplied, the unconditional
self-selector construction gives an eventual family of full actual active
measures.  No selector, support, or analytic hypothesis remains here. -/
theorem eventually_bankPaperCanonicalActualActiveMeasureConstructor_self
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (q : Nat -> Real)
    (H : BankPaperCanonicalActiveMassPaperScaleLower q) :
    ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor (D n) (T n)
        (bankPaperCanonicalStructuredActiveValues (D n))
        (bankPaperCanonicalScaledActivePreSelector (D n) (T n) (q n))
        (bankPaperCanonicalScaledActiveSeed (T n) (q n)) := by
  filter_upwards
      [eventually_one_le_bankPaperCanonicalActiveMass_of_paperScaleLower q H]
      with n hn
  exact bankPaperCanonicalActualActiveMeasureConstructor_self
    (D n) (T n) (q n) hn

/-! ## The literal paper-head specialization -/

/-- The structured seed built from the literal paper head data eventually
has mass at least one.  Its exact mass is the reserve's stored
`activeMass`; no normalization loss occurs. -/
theorem eventually_one_le_bankPaperCanonicalPaperDataActiveSeedMass
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : Nat -> BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : forall n sigma, (B n).sampleData.lo sigma =
      physicalBound (I.lower sigma) (B n).sampleData.n)
    (hhi : forall n sigma, (B n).sampleData.hi sigma =
      physicalBound (I.upper sigma) (B n).sampleData.n)
    (Rhead : Nat -> HeadSimplexReserve P)
    (Kphysical : Nat -> PhysicalInterpolationTarget I)
    (H : BankPaperCanonicalHeadActiveMassPaperScaleLower Rhead) :
    ∀ᶠ n : Nat in atTop,
      1 <= bankPaperCanonicalLiteralActiveMass (B n).sampleData
        (bankPaperCanonicalPaperDataActiveSeed
          (B n) I (hlo n) (hhi n) (Rhead n) (Kphysical n)) := by
  filter_upwards
      [eventually_one_le_bankPaperCanonicalHeadActiveMass Rhead H]
      with n hn
  rw [bankPaperCanonicalLiteralActiveMass_paperDataActiveSeed]
  exact hn

/-- The same paper-data family, with its canonical finite self-selector,
eventually satisfies the complete actual-active-measure constructor. -/
theorem eventually_bankPaperCanonicalPaperDataActualActiveMeasureConstructor_self
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : Nat -> BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : forall n sigma, (B n).sampleData.lo sigma =
      physicalBound (I.lower sigma) (B n).sampleData.n)
    (hhi : forall n sigma, (B n).sampleData.hi sigma =
      physicalBound (I.upper sigma) (B n).sampleData.n)
    (Rhead : Nat -> HeadSimplexReserve P)
    (Kphysical : Nat -> PhysicalInterpolationTarget I)
    (H : BankPaperCanonicalHeadActiveMassPaperScaleLower Rhead) :
    ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor (B n).sampleData
        ((B n).barycentricTargetOfPaperData
          I (hlo n) (hhi n) (Rhead n) (Kphysical n))
        (bankPaperCanonicalStructuredActiveValues (B n).sampleData)
        (bankPaperCanonicalScaledActivePreSelector
          (B n).sampleData
          ((B n).barycentricTargetOfPaperData
            I (hlo n) (hhi n) (Rhead n) (Kphysical n))
          (Rhead n).activeMass)
        (bankPaperCanonicalPaperDataActiveSeed
          (B n) I (hlo n) (hhi n) (Rhead n) (Kphysical n)) := by
  filter_upwards
      [eventually_one_le_bankPaperCanonicalHeadActiveMass Rhead H]
      with n hn
  simpa only [bankPaperCanonicalPaperDataActiveSeed] using
    bankPaperCanonicalActualActiveMeasureConstructor_self
      (B n).sampleData
      ((B n).barycentricTargetOfPaperData
        I (hlo n) (hhi n) (Rhead n) (Kphysical n))
      (Rhead n).activeMass hn

end

end Erdos390.WholePaper
