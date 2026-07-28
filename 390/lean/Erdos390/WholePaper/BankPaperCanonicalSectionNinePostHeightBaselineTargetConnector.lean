import Erdos390.Full.PaperCanonicalHeadPhysicalTarget
import Erdos390.Full.PaperProposition87Assembly
import Erdos390.WholePaper.BankPaperCanonicalSmoothAdditivePlacement
import Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightLedger

/-!
# The finite post-height baseline target

After the integer height `d` has been selected, the paper chooses a fresh
finite baseline.  Its total active mass is

`q_n = q0 - d`,

its unnormalized head-prime moments are the prescribed values
`A_p^act`, and its normalized logarithmic height above `n` is
`A(d) / q_n`.

In the repository, this last statistic is
`BridgeData.physicalScore = log (m/n)`.  The separately named
`BridgeData.ordinaryLogScore` is `log m`, so its unnormalized moment is
`A(d) + q_n L`, not `A(d)`.  Both identities are proved below.

The two-zero-cell rounding placement used to obtain the integer row quota
need not itself have barycentric product form.  Accordingly this module
does not identify that placement with the new baseline.  It instead uses
the paper's actual `HeadSimplexReserve`, `PhysicalInterpolationTarget`, and
`BridgeData.barycentricTargetOfPaperData` constructors to build a new
`BarycentricTarget`, and proves its finite moment identities directly.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex

noncomputable section

/-! ## Literal post-height scalar data -/

/-- The final active mass `q_n = q0 - d`. -/
def bankPaperCanonicalSectionNinePostHeightActiveMass
    (q0 : Real) (d : Int) : Real :=
  q0 - (d : Real)

@[simp] theorem bankPaperCanonicalSectionNinePostHeightActiveMass_eq
    (q0 : Real) (d : Int) :
    bankPaperCanonicalSectionNinePostHeightActiveMass q0 d =
      q0 - (d : Real) :=
  rfl

/-- The final unnormalized active logarithmic height above `n`,
`A(d) = A0 + d L`; formally this is the `physicalScore` moment. -/
def bankPaperCanonicalSectionNinePostHeightActiveHeight
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (A0 : Real) (d : Int) : Real :=
  A0 + (d : Real) * B.L

/-- The paper's final normalized logarithmic height above `n`,
`A(d) / q_n`.  This is the mean of `BridgeData.physicalScore = log(m/n)`. -/
def bankPaperCanonicalSectionNinePostHeightPhysicalLogMean
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (q0 A0 : Real) (d : Int) : Real :=
  bankPaperCanonicalSectionNinePostHeightActiveHeight B A0 d /
    bankPaperCanonicalSectionNinePostHeightActiveMass q0 d

/-- The repository's literal ordinary-log mean.  Since
`ordinaryLogScore = log m = log(m/n) + L`, this is
`A(d)/q_n + L`. -/
def bankPaperCanonicalSectionNinePostHeightOrdinaryLogMean
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (q0 A0 : Real) (d : Int) : Real :=
  bankPaperCanonicalSectionNinePostHeightPhysicalLogMean B q0 A0 d + B.L

/-- The physical-score target passed to `PhysicalInterpolationTarget`.
The paper's `A(d)` is already the active logarithmic height above `n`, so
no further subtraction of `L` occurs here. -/
def bankPaperCanonicalSectionNinePostHeightPhysicalMean
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (q0 A0 : Real) (d : Int) : Real :=
  bankPaperCanonicalSectionNinePostHeightPhysicalLogMean B q0 A0 d

/-! ## Genuine reserve and interpolation inputs -/

/-- The finite numerical inputs required to choose the post-height
barycentric target.

The head fields are precisely the coordinatewise interior conditions for
the simplex `{0, E e_p}` at total mass `q0-d`.  The two physical fields say
that the `log(m/n)` target `A(d)/(q0-d)` lies strictly between the two
selected physical pools.  No target, seed, moment, or placement conclusion
is stored in this structure. -/
structure BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (q0 A0 : Real) (d : Int) (exponent : Nat)
    (activeHeadTarget : {p : Nat // p ∈ P} → Real) where
  exponent_pos : 0 < exponent
  activeMass_pos :
    0 < bankPaperCanonicalSectionNinePostHeightActiveMass q0 d
  headMargin : Real
  headMargin_pos : 0 < headMargin
  vertex_margin : ∀ p,
    headMargin ≤
      activeHeadTarget p /
        ((exponent : Real) *
          bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)
  zero_margin :
    headMargin ≤
      1 - ∑ p : {p : Nat // p ∈ P},
        activeHeadTarget p /
          ((exponent : Real) *
            bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)
  physicalEta : Real
  physicalEta_pos : 0 < physicalEta
  minus_below :
    Real.log (I.upper .minus) ≤
      bankPaperCanonicalSectionNinePostHeightPhysicalMean B q0 A0 d -
        physicalEta
  plus_above :
    bankPaperCanonicalSectionNinePostHeightPhysicalMean B q0 A0 d +
        physicalEta ≤
      Real.log (I.lower .plus)

/-! ## Constructed paper data -/

/-- The literal post-height head-simplex reserve. -/
def bankPaperCanonicalSectionNinePostHeightHeadReserve
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    {B : BridgeData (PaperHeadSimplex.Tag P) Band}
    {I : PhysicalIntervals}
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget) :
    HeadSimplexReserve P where
  exponent := exponent
  exponent_pos := H.exponent_pos
  activeMass :=
    bankPaperCanonicalSectionNinePostHeightActiveMass q0 d
  activeMass_pos := H.activeMass_pos
  target := activeHeadTarget
  margin := H.headMargin
  margin_pos := H.headMargin_pos
  vertex_margin := H.vertex_margin
  zero_margin := H.zero_margin

/-- The literal post-height physical interpolation target. -/
def bankPaperCanonicalSectionNinePostHeightPhysicalTarget
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    {B : BridgeData (PaperHeadSimplex.Tag P) Band}
    {I : PhysicalIntervals}
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget) :
    PhysicalInterpolationTarget I where
  mu := bankPaperCanonicalSectionNinePostHeightPhysicalMean B q0 A0 d
  eta := H.physicalEta
  eta_pos := H.physicalEta_pos
  minus_below := H.minus_below
  plus_above := H.plus_above

/-- The paper-faithful post-height barycentric target `Tpost`. -/
def bankPaperCanonicalSectionNinePostHeightTarget
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget) :
    BarycentricTarget B.sampleData :=
  B.barycentricTargetOfPaperData I hlo hhi
    (bankPaperCanonicalSectionNinePostHeightHeadReserve H)
    (bankPaperCanonicalSectionNinePostHeightPhysicalTarget H)

/-- The scaled post-height seed attached to `Tpost`. -/
def bankPaperCanonicalSectionNinePostHeightActiveSeed
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget) :
    B.sampleData.Sample → Real :=
  bankPaperCanonicalScaledActiveSeed
    (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
    (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)

/-! ## Exact mass and head moments -/

/-- The constructed scaled seed has total mass exactly `q_n = q0-d`. -/
@[simp] theorem
    bankPaperCanonicalSectionNinePostHeight_literalActiveMass_activeSeed
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget) :
    bankPaperCanonicalLiteralActiveMass B.sampleData
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H) =
      bankPaperCanonicalSectionNinePostHeightActiveMass q0 d := by
  exact
    bankPaperCanonicalLiteralActiveMass_scaledActiveSeed
      (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
      (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)

/-- At every head prime, the sample-level scaled seed realizes the
unnormalized post-height target `A_p^act` exactly. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_activeSeed_headMoment
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (hprime : ∀ p ∈ P, p.Prime)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime exponent)
    (p : {p : Nat // p ∈ P}) :
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H m *
          valuation p.1 (B.sampleData.value m)) =
      activeHeadTarget p := by
  simpa only [
    bankPaperCanonicalSectionNinePostHeightActiveSeed,
    bankPaperCanonicalSectionNinePostHeightTarget,
    bankPaperCanonicalSectionNinePostHeightHeadReserve] using
    (BankPaperRealization.sum_bankPaperCanonicalScaledActiveSeed_mul_paperHeadValuation
      B hprime
        (bankPaperCanonicalSectionNinePostHeightHeadReserve H)
        I hlo hhi
        (bankPaperCanonicalSectionNinePostHeightPhysicalTarget H)
        hpattern p)

/-! ## Exact ordinary-log moment -/

/-- A uniform baseline allocation converts the sample physical-score sum
to the corresponding cell-log-mean sum. -/
theorem
    sum_baselineBaseWeight_mul_physicalScore_eq_cellLogMean
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (A : BaselineAllocation B.sampleData) :
    (∑ m : B.sampleData.Sample,
        A.baseWeight m * B.physicalScore m) =
      ∑ cell : Cell (PaperHeadSimplex.Tag P),
        A.cellMass cell * cellLogMean B.sampleData cell := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro cell _hcell
  simp only [BaselineAllocation.baseWeight, StructuredSampleData.cellOf,
    BridgeData.physicalScore, StructuredSampleData.value, cellLogMean]
  have hcard :
      (Fintype.card (B.sampleData.SampleAt cell) : Real) ≠ 0 := by
    exact_mod_cast
      Nat.ne_of_gt (B.sampleData.sampleAt_card_pos cell)
  rw [← Finset.mul_sum]
  field_simp [hcard]

/-- A scaled barycentric seed has physical-score moment `q*T.mu`. -/
theorem
    sum_bankPaperCanonicalScaledActiveSeed_mul_physicalScore
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (T : BarycentricTarget B.sampleData) (q : Real) :
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalScaledActiveSeed T q m *
          B.physicalScore m) =
      q * T.mu := by
  calc
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalScaledActiveSeed T q m *
          B.physicalScore m) =
        q * ∑ m : B.sampleData.Sample,
          T.baseline.baseWeight m * B.physicalScore m := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      unfold bankPaperCanonicalScaledActiveSeed
      ring
    _ = q * ∑ cell : Cell (PaperHeadSimplex.Tag P),
        T.baseline.cellMass cell *
          cellLogMean B.sampleData cell := by
      rw [sum_baselineBaseWeight_mul_physicalScore_eq_cellLogMean]
    _ = q * ∑ cell : Cell (PaperHeadSimplex.Tag P),
        T.baseline.normalizedCellMass cell *
          cellLogMean B.sampleData cell := by
      apply congrArg (q * ·)
      apply Finset.sum_congr rfl
      intro cell _hcell
      unfold BaselineAllocation.normalizedCellMass
      rw [T.baseline_totalMass, div_one]
    _ = q * T.mu := by
      rw [T.physicalLogMoment]

/-- The post-height seed has `log(m/n)` moment exactly `A(d)`.
Equivalently, the normalized physical-score mean is `A(d)/(q0-d)`, exactly
the value used to construct the physical interpolation target. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_activeSeed_physicalLogMoment
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget) :
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H m *
          B.physicalScore m) =
      bankPaperCanonicalSectionNinePostHeightActiveHeight B A0 d := by
  let Tpost :=
    bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H
  let qn := bankPaperCanonicalSectionNinePostHeightActiveMass q0 d
  have hq : qn ≠ 0 := ne_of_gt H.activeMass_pos
  calc
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H m *
          B.physicalScore m) =
        qn * Tpost.mu := by
      simpa only [Tpost, qn,
        bankPaperCanonicalSectionNinePostHeightActiveSeed] using
        (sum_bankPaperCanonicalScaledActiveSeed_mul_physicalScore
          B Tpost qn)
    _ =
        qn *
          (bankPaperCanonicalSectionNinePostHeightActiveHeight B A0 d /
            qn) := by
      rfl
    _ = bankPaperCanonicalSectionNinePostHeightActiveHeight B A0 d := by
      field_simp [hq]

/-- The normalized `log(m/n)` mean is exactly `A(d)/(q0-d)`. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_activeSeed_physicalLogMean
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget) :
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H m *
          B.physicalScore m) /
        bankPaperCanonicalSectionNinePostHeightActiveMass q0 d =
      bankPaperCanonicalSectionNinePostHeightPhysicalLogMean
        B q0 A0 d := by
  rw [
    bankPaperCanonicalSectionNinePostHeight_activeSeed_physicalLogMoment
      B I hlo hhi H]
  rfl

/-- For the repository's literal `ordinaryLogScore = log m`, the
post-height seed has unnormalized moment
`A(d) + (q0-d)L`.  This is the exact conversion from the paper's height
above `n`; in the Section 8 ledger it equals `logY - Lambda0`. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_activeSeed_ordinaryLogMoment
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget) :
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H m *
          B.ordinaryLogScore m) =
      bankPaperCanonicalSectionNinePostHeightActiveHeight B A0 d +
        bankPaperCanonicalSectionNinePostHeightActiveMass q0 d * B.L := by
  let Tpost :=
    bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H
  let qn := bankPaperCanonicalSectionNinePostHeightActiveMass q0 d
  have hq : qn ≠ 0 := ne_of_gt H.activeMass_pos
  have hphysical :
      (∑ m : B.sampleData.Sample,
          bankPaperCanonicalSectionNinePostHeightActiveSeed
              B I hlo hhi H m *
            B.physicalScore m) =
        qn * Tpost.mu := by
    simpa only [Tpost, qn,
      bankPaperCanonicalSectionNinePostHeightActiveSeed] using
      (sum_bankPaperCanonicalScaledActiveSeed_mul_physicalScore
        B Tpost qn)
  have hmass :
      (∑ m : B.sampleData.Sample,
          bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H m) = qn := by
    simpa only [bankPaperCanonicalLiteralActiveMass, qn] using
      (bankPaperCanonicalSectionNinePostHeight_literalActiveMass_activeSeed
        B I hlo hhi H)
  have hpoint (m : B.sampleData.Sample) :
      B.ordinaryLogScore m = B.physicalScore m + B.L := by
    have hm : (B.sampleData.value m : Real) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (B.sampleData.value_pos m)
    have hn : (B.sampleData.n : Real) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt B.n_gt_one)
    unfold BridgeData.ordinaryLogScore BridgeData.physicalScore BridgeData.L
    rw [Real.log_div hm hn]
    ring
  have hmu :
      Tpost.mu =
        bankPaperCanonicalSectionNinePostHeightActiveHeight B A0 d / qn := by
    rfl
  calc
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H m *
          B.ordinaryLogScore m) =
        (∑ m : B.sampleData.Sample,
          bankPaperCanonicalSectionNinePostHeightActiveSeed
              B I hlo hhi H m *
            B.physicalScore m) +
          (∑ m : B.sampleData.Sample,
            bankPaperCanonicalSectionNinePostHeightActiveSeed
              B I hlo hhi H m) * B.L := by
      simp_rw [hpoint]
      calc
        (∑ m : B.sampleData.Sample,
            bankPaperCanonicalSectionNinePostHeightActiveSeed
                B I hlo hhi H m *
              (B.physicalScore m + B.L)) =
            ∑ m : B.sampleData.Sample,
              (bankPaperCanonicalSectionNinePostHeightActiveSeed
                    B I hlo hhi H m *
                  B.physicalScore m +
                bankPaperCanonicalSectionNinePostHeightActiveSeed
                    B I hlo hhi H m * B.L) := by
          apply Finset.sum_congr rfl
          intro m _hm
          ring
        _ =
            (∑ m : B.sampleData.Sample,
              bankPaperCanonicalSectionNinePostHeightActiveSeed
                  B I hlo hhi H m *
                B.physicalScore m) +
              ∑ m : B.sampleData.Sample,
                bankPaperCanonicalSectionNinePostHeightActiveSeed
                  B I hlo hhi H m * B.L := by
          rw [Finset.sum_add_distrib]
        _ =
            (∑ m : B.sampleData.Sample,
              bankPaperCanonicalSectionNinePostHeightActiveSeed
                  B I hlo hhi H m *
                B.physicalScore m) +
              (∑ m : B.sampleData.Sample,
                bankPaperCanonicalSectionNinePostHeightActiveSeed
                  B I hlo hhi H m) * B.L := by
          rw [Finset.sum_mul]
    _ = qn * Tpost.mu + qn * B.L := by
      rw [hphysical, hmass]
    _ = bankPaperCanonicalSectionNinePostHeightActiveHeight B A0 d +
        bankPaperCanonicalSectionNinePostHeightActiveMass q0 d * B.L := by
      rw [hmu]
      change
        qn *
              (bankPaperCanonicalSectionNinePostHeightActiveHeight
                B A0 d / qn) +
            qn * B.L =
          bankPaperCanonicalSectionNinePostHeightActiveHeight B A0 d +
            qn * B.L
      field_simp [hq]

/-- Dividing the literal `log m` moment by the final active mass gives
`A(d)/(q0-d) + L`. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_activeSeed_ordinaryLogMean
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget) :
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H m *
          B.ordinaryLogScore m) /
        bankPaperCanonicalSectionNinePostHeightActiveMass q0 d =
      bankPaperCanonicalSectionNinePostHeightOrdinaryLogMean
        B q0 A0 d := by
  rw [
    bankPaperCanonicalSectionNinePostHeight_activeSeed_ordinaryLogMoment
      B I hlo hhi H]
  unfold bankPaperCanonicalSectionNinePostHeightOrdinaryLogMean
  unfold bankPaperCanonicalSectionNinePostHeightPhysicalLogMean
  have hq :
      bankPaperCanonicalSectionNinePostHeightActiveMass q0 d ≠ 0 :=
    ne_of_gt H.activeMass_pos
  field_simp [hq]

/-! ## Combined finite target constructor -/

/-- Construct the actual post-height target together with its exact mass,
head, above-`n`, and literal ordinary-log identities.  The witness is a newly selected
`BarycentricTarget`; the conclusion makes no assertion about the earlier
two-zero-cell placement seed. -/
theorem exists_bankPaperCanonicalSectionNinePostHeightBaselineTarget
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (hprime : ∀ p ∈ P, p.Prime)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime exponent) :
    ∃ Tpost : BarycentricTarget B.sampleData,
      bankPaperCanonicalLiteralActiveMass B.sampleData
          (bankPaperCanonicalScaledActiveSeed Tpost
            (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)) =
          bankPaperCanonicalSectionNinePostHeightActiveMass q0 d ∧
        (∀ p : {p : Nat // p ∈ P},
          (∑ m : B.sampleData.Sample,
              bankPaperCanonicalScaledActiveSeed Tpost
                  (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d) m *
                valuation p.1 (B.sampleData.value m)) =
            activeHeadTarget p) ∧
        (∑ m : B.sampleData.Sample,
            bankPaperCanonicalScaledActiveSeed Tpost
                (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d) m *
              B.physicalScore m) =
          bankPaperCanonicalSectionNinePostHeightActiveHeight B A0 d ∧
        (∑ m : B.sampleData.Sample,
            bankPaperCanonicalScaledActiveSeed Tpost
                (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d) m *
              B.ordinaryLogScore m) =
          bankPaperCanonicalSectionNinePostHeightActiveHeight B A0 d +
            bankPaperCanonicalSectionNinePostHeightActiveMass q0 d *
              B.L := by
  let Tpost :=
    bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H
  refine ⟨Tpost, ?_, ?_, ?_, ?_⟩
  · exact
      bankPaperCanonicalLiteralActiveMass_scaledActiveSeed Tpost
        (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)
  · intro p
    simpa only [Tpost,
      bankPaperCanonicalSectionNinePostHeightActiveSeed] using
      (bankPaperCanonicalSectionNinePostHeight_activeSeed_headMoment
        B I hlo hhi H hprime hpattern p)
  · simpa only [Tpost,
      bankPaperCanonicalSectionNinePostHeightActiveSeed] using
      (bankPaperCanonicalSectionNinePostHeight_activeSeed_physicalLogMoment
        B I hlo hhi H)
  · simpa only [Tpost,
      bankPaperCanonicalSectionNinePostHeightActiveSeed] using
      (bankPaperCanonicalSectionNinePostHeight_activeSeed_ordinaryLogMoment
        B I hlo hhi H)

/-! ## Quantitative target margin -/

/-- The post-height target has the explicit paper product margin. -/
theorem bankPaperCanonicalSectionNinePostHeightTarget_cellMassMargin
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget) :
    (bankPaperCanonicalSectionNinePostHeightTarget
        B I hlo hhi H).cellMassMargin =
      H.headMargin *
        (H.physicalEta /
          PhysicalInterpolationTarget.physicalSpan I) := by
  exact
    B.barycentricTargetOfPaperData_cellMassMargin I hlo hhi
      (bankPaperCanonicalSectionNinePostHeightHeadReserve H)
      (bankPaperCanonicalSectionNinePostHeightPhysicalTarget H)

/-- In particular the constructed target has a strictly positive common
cell-mass margin. -/
theorem bankPaperCanonicalSectionNinePostHeightTarget_cellMassMargin_pos
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget) :
    0 <
      (bankPaperCanonicalSectionNinePostHeightTarget
        B I hlo hhi H).cellMassMargin :=
  (bankPaperCanonicalSectionNinePostHeightTarget
    B I hlo hhi H).cellMassMargin_pos

/-- The explicit product margin is a lower bound for every normalized
post-height cell mass. -/
theorem bankPaperCanonicalSectionNinePostHeightTarget_cellMassMargin_le
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (cell : Cell (PaperHeadSimplex.Tag P)) :
    H.headMargin *
        (H.physicalEta /
          PhysicalInterpolationTarget.physicalSpan I) ≤
      (bankPaperCanonicalSectionNinePostHeightTarget
        B I hlo hhi H).baseline.normalizedCellMass cell := by
  rw [← bankPaperCanonicalSectionNinePostHeightTarget_cellMassMargin
    B I hlo hhi H]
  exact
    (bankPaperCanonicalSectionNinePostHeightTarget
      B I hlo hhi H).cellMassMargin_le cell

/-- Every unnormalized cell of the scaled post-height seed has strictly
positive total active mass. -/
theorem bankPaperCanonicalSectionNinePostHeightTarget_activeCellMass_pos
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (cell : Cell (PaperHeadSimplex.Tag P)) :
    0 <
      bankPaperCanonicalSectionNinePostHeightActiveMass q0 d *
        (bankPaperCanonicalSectionNinePostHeightTarget
          B I hlo hhi H).baseline.cellMass cell := by
  exact mul_pos H.activeMass_pos
    ((bankPaperCanonicalSectionNinePostHeightTarget
      B I hlo hhi H).baseline.cellMass_pos cell)

end

end Erdos390.WholePaper
