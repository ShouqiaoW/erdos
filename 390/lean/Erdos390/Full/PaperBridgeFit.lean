import Erdos390.Full.NonlinearFitODE
import Erdos390.Full.StructuredCells
import Erdos390.Full.ArithmeticBandGeometry
import Erdos390.Full.CoarseMixture
import Erdos390.Full.AffineCertificate
import Erdos390.Full.StableInverse
import Erdos390.Full.Scale

/-!
# The finite arithmetic data in the bridge fit

This file instantiates the nonlinear finite-family layer with the actual
objects appearing in Lemmas 8.5--8.6 and Proposition 8.7: guarded smooth
structured cells, arithmetic prime bands, valuation statistics, the physical
logarithm, centered head indicators, and the compensated slow score.

The sample is the tagged disjoint union of the paper's cells.  Tagging is the
formal counterpart of the disjointification performed before normalization;
the underlying integer remains available as `Sample.value`.

All statements in this file are finite identities.  Asymptotic marked-smooth
estimates are not silently inserted as hypotheses equivalent to the desired
fit.  Where a later analytic estimate is still needed, the exact finite
quantity it must bound is exposed explicitly.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full

noncomputable section

open ArithmeticModel StructuredCells HeadPattern

namespace PaperBridgeFit

/-- The two separated physical pools in the baseline construction. -/
inductive PhysicalSign
  | minus
  | plus
  deriving DecidableEq, Fintype, Inhabited

/-- A head-pattern/physical-pool cell. -/
abbrev Cell (Head : Type*) := Head × PhysicalSign

/-- Exact finite data defining the paper's guarded active sample `S_n`.
The smoothness cutoff is the actual `floor (n^(2/9))`. -/
structure StructuredSampleData (Head : Type*) [Fintype Head] where
  n : ℕ
  W : ℕ
  pattern : Head → HeadPattern.Pattern
  lo : PhysicalSign → ℕ
  hi : PhysicalSign → ℕ
  lo_le_hi : ∀ sigma, lo sigma ≤ hi sigma
  physical_separated : hi .minus < lo .plus
  guards : Finset ℕ
  cell_nonempty : ∀ c : Cell Head,
    ((structuredCell (pattern c.1) (lo c.2) (hi c.2) (yNat n)) \
      guards).Nonempty

namespace StructuredSampleData

variable {Head : Type*} [Fintype Head]

/-- The actual guard-deleted structured cell `C_{e,sigma,n}`. -/
def cellFinset (D : StructuredSampleData Head) (c : Cell Head) : Finset ℕ :=
  structuredCell (D.pattern c.1) (D.lo c.2) (D.hi c.2)
      (yNat D.n) \ D.guards

/-- Members of one actual structured cell. -/
abbrev SampleAt (D : StructuredSampleData Head) (c : Cell Head) :=
  {m : ℕ // m ∈ D.cellFinset c}

instance sampleAtFintype (D : StructuredSampleData Head) (c : Cell Head) :
    Fintype (D.SampleAt c) :=
  Fintype.ofFinset (D.cellFinset c) (fun _ => Iff.rfl)

instance sampleAtDecidableEq (D : StructuredSampleData Head) (c : Cell Head) :
    DecidableEq (D.SampleAt c) := inferInstance

/-- The tagged disjoint union `S_n = disjoint union C_{e,sigma,n}`. -/
abbrev Sample (D : StructuredSampleData Head) :=
  Sigma D.SampleAt

instance sampleFintype (D : StructuredSampleData Head) : Fintype D.Sample :=
  inferInstance

noncomputable instance sampleDecidableEq (D : StructuredSampleData Head) :
    DecidableEq D.Sample := Classical.decEq D.Sample

/-- The cell tag of a sample. -/
def cellOf (D : StructuredSampleData Head) (m : D.Sample) : Cell Head :=
  m.1

/-- The underlying positive integer. -/
def value (D : StructuredSampleData Head) (m : D.Sample) : ℕ :=
  m.2.1

theorem value_mem_cell (D : StructuredSampleData Head) (m : D.Sample) :
    D.value m ∈ D.cellFinset (D.cellOf m) :=
  m.2.2

theorem value_pos (D : StructuredSampleData Head) (m : D.Sample) :
    0 < D.value m := by
  have hm : D.value m ∈ structuredCell
      (D.pattern (D.cellOf m).1) (D.lo (D.cellOf m).2)
      (D.hi (D.cellOf m).2) (yNat D.n) :=
    (Finset.mem_sdiff.mp (D.value_mem_cell m)).1
  exact StructuredCells.pos_of_mem_smoothInterval
    (mem_structuredCell.mp hm).1

theorem lo_lt_value (D : StructuredSampleData Head) (m : D.Sample) :
    D.lo (D.cellOf m).2 < D.value m := by
  have hm : D.value m ∈ structuredCell
      (D.pattern (D.cellOf m).1) (D.lo (D.cellOf m).2)
      (D.hi (D.cellOf m).2) (yNat D.n) :=
    (Finset.mem_sdiff.mp (D.value_mem_cell m)).1
  exact (mem_smoothInterval.mp (mem_structuredCell.mp hm).1).1

theorem value_le_hi (D : StructuredSampleData Head) (m : D.Sample) :
    D.value m ≤ D.hi (D.cellOf m).2 := by
  have hm : D.value m ∈ structuredCell
      (D.pattern (D.cellOf m).1) (D.lo (D.cellOf m).2)
      (D.hi (D.cellOf m).2) (yNat D.n) :=
    (Finset.mem_sdiff.mp (D.value_mem_cell m)).1
  exact (mem_smoothInterval.mp (mem_structuredCell.mp hm).1).2.1

theorem value_matches_head (D : StructuredSampleData Head) (m : D.Sample) :
    (D.pattern (D.cellOf m).1).Matches (D.value m) := by
  have hm : D.value m ∈ structuredCell
      (D.pattern (D.cellOf m).1) (D.lo (D.cellOf m).2)
      (D.hi (D.cellOf m).2) (yNat D.n) :=
    (Finset.mem_sdiff.mp (D.value_mem_cell m)).1
  exact (mem_structuredCell.mp hm).2

/-- Every integer in the guarded sample is smooth at the paper's integral
cutoff.  Guard deletion changes neither smoothness nor the head pattern. -/
theorem value_mem_smoothNumbers (D : StructuredSampleData Head) (m : D.Sample) :
    D.value m ∈ Nat.smoothNumbers (yNat D.n + 1) := by
  have hm : D.value m ∈ structuredCell
      (D.pattern (D.cellOf m).1) (D.lo (D.cellOf m).2)
      (D.hi (D.cellOf m).2) (yNat D.n) :=
    (Finset.mem_sdiff.mp (D.value_mem_cell m)).1
  exact (mem_smoothInterval.mp (mem_structuredCell.mp hm).1).2.2

theorem value_not_guard (D : StructuredSampleData Head) (m : D.Sample) :
    D.value m ∉ D.guards :=
  (Finset.mem_sdiff.mp (D.value_mem_cell m)).2

theorem sampleAt_card_pos (D : StructuredSampleData Head) (c : Cell Head) :
    0 < Fintype.card (D.SampleAt c) := by
  rw [Fintype.card_pos_iff]
  obtain ⟨m, hm⟩ := D.cell_nonempty c
  exact ⟨⟨m, hm⟩⟩

end StructuredSampleData

/-- Explicit baseline masses, uniform within each structured cell as in
equation (8.7) of the paper. -/
structure BaselineAllocation
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) where
  cellMass : Cell Head → ℝ
  cellMass_pos : ∀ c, 0 < cellMass c

namespace BaselineAllocation

variable {Head : Type*} [Fintype Head]
  {D : StructuredSampleData Head}

/-- The paper's active mass `q_n`. -/
def totalMass (A : BaselineAllocation D) : ℝ :=
  ∑ c, A.cellMass c

theorem totalMass_pos [Nonempty Head] (A : BaselineAllocation D) :
    0 < A.totalMass := by
  exact Finset.sum_pos (fun c _ => A.cellMass_pos c)
    (Finset.univ_nonempty)

/-- The exact coordinate realization
`z_m^0 = q_{e,sigma,n} / #C_{e,sigma,n}`. -/
def baseWeight (A : BaselineAllocation D) (m : D.Sample) : ℝ :=
  A.cellMass (D.cellOf m) /
    Fintype.card (D.SampleAt (D.cellOf m))

theorem baseWeight_pos (A : BaselineAllocation D) (m : D.Sample) :
    0 < A.baseWeight m := by
  exact div_pos (A.cellMass_pos (D.cellOf m)) (by
    exact_mod_cast D.sampleAt_card_pos (D.cellOf m))

theorem baseWeight_nonneg (A : BaselineAllocation D) (m : D.Sample) :
    0 ≤ A.baseWeight m :=
  le_of_lt (A.baseWeight_pos m)

/-- Summing the explicit uniform weights recovers exactly `q_n`. -/
theorem baseWeight_sum (A : BaselineAllocation D) :
    ∑ m, A.baseWeight m = A.totalMass := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  simp only [baseWeight, StructuredSampleData.cellOf]
  have hcard : (Fintype.card (D.SampleAt c) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (D.sampleAt_card_pos c))
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hcard]

/-- Normalized mass of one reserved cell. -/
def normalizedCellMass (A : BaselineAllocation D) (c : Cell Head) : ℝ :=
  A.cellMass c / A.totalMass

theorem normalizedCellMass_pos [Nonempty Head]
    (A : BaselineAllocation D) (c : Cell Head) :
    0 < A.normalizedCellMass c :=
  div_pos (A.cellMass_pos c) A.totalMass_pos

theorem normalizedCellMass_sum [Nonempty Head] (A : BaselineAllocation D) :
    ∑ c, A.normalizedCellMass c = 1 := by
  simp only [normalizedCellMass]
  rw [← Finset.sum_div, totalMass]
  exact div_self (ne_of_gt A.totalMass_pos)

end BaselineAllocation

/-- Coordinates used in the simultaneous nonlinear fit.  The gauge indices
are the positive-band basis vectors `q^(j)`, the nuisance coordinates are the
physical logarithm and centered head indicators, and `slow` is the
compensated score. -/
inductive MomentCoord (Gauge HeadCoord : Type*)
  | gauge (j : Gauge)
  | physical
  | head (h : HeadCoord)
  | slow
  deriving DecidableEq, Fintype

/-- The finite nuisance block `(R,H^circ)` used before taking the Schur
complement. -/
inductive NuisanceCoord (HeadCoord : Type*)
  | physical
  | head (h : HeadCoord)
  deriving DecidableEq, Fintype

/-- The quotient-band plus compensated-score block, complementary to the
finite nuisance block. -/
inductive MainCoord (Gauge : Type*)
  | gauge (j : Gauge)
  | slow
  deriving DecidableEq, Fintype

/-- All concrete finite data entering the simultaneous fit. -/
structure BridgeData
    (Head Band : Type*) [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] where
  sampleData : StructuredSampleData Head
  baseline : BaselineAllocation sampleData
  partition : ArithmeticBandGeometry.Partition
    sampleData.n sampleData.W Band
  lowBand : Band
  referenceHead : Head
  w : ℝ
  w_pos : 0 < w
  n_gt_one : 1 < sampleData.n

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Positive-band coordinates, with the low row removed. -/
abbrev GaugeIndex := {j : Band // j ≠ B.lowBand}

/-- Centered head coordinates, with one reference pattern removed. -/
abbrev HeadIndex := {h : Head // h ≠ B.referenceHead}

/-- The actual finite coordinate type of Proposition 8.7. -/
abbrev Coord := MomentCoord B.GaugeIndex B.HeadIndex

/-- The Euclidean realization after the slow coordinate is rescaled by `w`.
Its ordinary Euclidean norm is the paper's anisotropic scaled Euclidean
norm on `(u,a,lambda)`, with the slow parameter represented by `w*lambda`. -/
abbrev ParamSpace := EuclideanSpace ℝ B.Coord

abbrev NuisanceSpace := EuclideanSpace ℝ (NuisanceCoord B.HeadIndex)

abbrev MainSpace := EuclideanSpace ℝ (MainCoord B.GaugeIndex)

/-- The paper's `L`; here it is tied to the actual integer `n`. -/
def L : ℝ := Real.log (B.sampleData.n : ℝ)

theorem L_pos : 0 < B.L := by
  rw [L, Real.log_pos_iff (by positivity)]
  exact_mod_cast B.n_gt_one

/-- The logarithmic smoothness scale is strictly positive on the actual
range `n > 1`; in particular all normalized logarithms below have a
nonzero denominator. -/
theorem log_y_pos : 0 < Real.log (ArithmeticModel.y B.sampleData.n) := by
  rw [Scale.log_y (Nat.zero_lt_of_lt B.n_gt_one)]
  exact mul_pos (by norm_num) (by simpa [Scale.L, L] using B.L_pos)

/-- The paper's active mass `q_n`. -/
def q : ℝ := B.baseline.totalMass

theorem q_pos [Nonempty Head] : 0 < B.q :=
  B.baseline.totalMass_pos

/-- Actual harmonic band mass `H_j`. -/
def harmonicMass (j : Band) : ℝ :=
  B.partition.mass j

theorem harmonicMass_pos (j : Band) : 0 < B.harmonicMass j :=
  B.partition.data.mass_pos j

/-- Actual arithmetic center `alpha_j`. -/
def bandCenter (j : Band) : ℝ :=
  B.partition.center j

theorem bandPrime_tPrime_pos
    (p : ArithmeticBandGeometry.BandPrime
      B.sampleData.n B.sampleData.W) :
    0 < ArithmeticModel.tPrime B.sampleData.n p.1 := by
  have hn : 0 < B.sampleData.n := Nat.zero_lt_of_lt B.n_gt_one
  have hpPrime := ArithmeticModel.prime_of_mem_primeBand p.2
  have hpOne : (1 : ℝ) < (p.1 : ℝ) := by
    exact_mod_cast hpPrime.one_lt
  have hpLeNat : (p.1 : ℝ) ≤
      (ArithmeticModel.yNat B.sampleData.n : ℝ) := by
    exact_mod_cast ArithmeticModel.le_yNat_of_mem_primeBand p.2
  have hfloor : (ArithmeticModel.yNat B.sampleData.n : ℝ) ≤
      ArithmeticModel.y B.sampleData.n := by
    exact Nat.floor_le (le_of_lt (Scale.y_pos hn))
  have hyOne : (1 : ℝ) < ArithmeticModel.y B.sampleData.n :=
    hpOne.trans_le (hpLeNat.trans hfloor)
  exact div_pos (Real.log_pos hpOne) (Real.log_pos hyOne)

theorem bandCenter_pos (j : Band) : 0 < B.bandCenter j := by
  change 0 <
    (∑ p ∈ B.partition.data.fiber j,
      (1 / (p.1 : ℝ)) *
        ArithmeticModel.tPrime B.sampleData.n p.1) /
      B.partition.data.mass j
  apply div_pos
  · apply Finset.sum_pos
    · intro p hp
      exact mul_pos (by
        exact one_div_pos.mpr (by
          exact_mod_cast
            (ArithmeticModel.prime_of_mem_primeBand p.2).pos))
        (B.bandPrime_tPrime_pos p)
    · obtain ⟨p, hp⟩ := B.partition.fiber_nonempty j
      exact ⟨p, by
        simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hp⟩
  · exact B.partition.data.mass_pos j

/-- The actual valuation statistic `Omega_j(m)`. -/
def bandScore (j : Band) (m : B.sampleData.Sample) : ℝ :=
  ∑ p ∈ B.partition.data.fiber j,
    ArithmeticModel.valuation p.1 (B.sampleData.value m)

/-- The coefficient of the low row in the concrete gauge basis
`q^(j)=e_j-(H_j alpha_j)/(H_0 alpha_0)e_0`. -/
def lowRatio (j : B.GaugeIndex) : ℝ :=
  B.harmonicMass j.1 * B.bandCenter j.1 /
    (B.harmonicMass B.lowBand * B.bandCenter B.lowBand)

/-- The quotient-band score corresponding to the paper's concrete basis. -/
def gaugeScore (j : B.GaugeIndex) (m : B.sampleData.Sample) : ℝ :=
  B.bandScore j.1 m - B.lowRatio j * B.bandScore B.lowBand m

/-- The physical logarithm `R(m)=log(m/n)`. -/
def physicalScore (m : B.sampleData.Sample) : ℝ :=
  Real.log ((B.sampleData.value m : ℝ) / (B.sampleData.n : ℝ))

/-- A deterministic value strictly between the two physical pools. -/
def physicalSeparator : ℝ :=
  Real.log ((B.sampleData.lo .plus : ℝ) / (B.sampleData.n : ℝ))

theorem physicalScore_lt_separator_of_minus
    (m : B.sampleData.Sample)
    (hm : (B.sampleData.cellOf m).2 = .minus) :
    B.physicalScore m < B.physicalSeparator := by
  have hn : 0 < (B.sampleData.n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt B.n_gt_one)
  have hvpos : 0 < (B.sampleData.value m : ℝ) := by
    exact_mod_cast B.sampleData.value_pos m
  have hvlt : (B.sampleData.value m : ℝ) <
      (B.sampleData.lo .plus : ℝ) := by
    exact_mod_cast (lt_of_le_of_lt (by
      simpa only [hm] using B.sampleData.value_le_hi m)
      B.sampleData.physical_separated)
  unfold physicalScore physicalSeparator
  exact Real.log_lt_log (div_pos hvpos hn)
    (div_lt_div_of_pos_right hvlt hn)

theorem separator_lt_physicalScore_of_plus
    (m : B.sampleData.Sample)
    (hm : (B.sampleData.cellOf m).2 = .plus) :
    B.physicalSeparator < B.physicalScore m := by
  have hn : 0 < (B.sampleData.n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt B.n_gt_one)
  have hloposNat : 0 < B.sampleData.lo .plus :=
    lt_of_le_of_lt (Nat.zero_le _) B.sampleData.physical_separated
  have hlopos : 0 < (B.sampleData.lo .plus : ℝ) := by
    exact_mod_cast hloposNat
  have hlt : (B.sampleData.lo .plus : ℝ) <
      (B.sampleData.value m : ℝ) := by
    exact_mod_cast (by
      simpa only [hm] using B.sampleData.lo_lt_value m)
  unfold physicalScore physicalSeparator
  exact Real.log_lt_log (div_pos hlopos hn)
    (div_lt_div_of_pos_right hlt hn)

/-- Indicator of a tagged head-pattern cell. -/
def headIndicator (h : Head) (m : B.sampleData.Sample) : ℝ :=
  if (B.sampleData.cellOf m).1 = h then 1 else 0

/-- Exact baseline probability of a head pattern, summed over its two
physical pools. -/
def headBaselineMass [Nonempty Head] (h : Head) : ℝ :=
  ∑ sigma : PhysicalSign,
    B.baseline.normalizedCellMass (h, sigma)

/-- The centered head indicator `H_h^circ`. -/
def centeredHeadScore [Nonempty Head]
    (h : B.HeadIndex) (m : B.sampleData.Sample) : ℝ :=
  B.headIndicator h.1 m - B.headBaselineMass h.1

/-- The exact arithmetic cell deviation `g_p=alpha_{j(p)}-t_p`. -/
def primeDeviation (p : ArithmeticBandGeometry.BandPrime
    B.sampleData.n B.sampleData.W) : ℝ :=
  B.bandCenter (B.partition.band p) -
    ArithmeticModel.tPrime B.sampleData.n p.1

/-- The raw compensated score `S_g=sum_p g_p v_p(m)`. -/
def slowScore (m : B.sampleData.Sample) : ℝ :=
  ∑ p : ArithmeticBandGeometry.BandPrime
      B.sampleData.n B.sampleData.W,
    B.primeDeviation p *
      ArithmeticModel.valuation p.1 (B.sampleData.value m)

/-- The medium-prime logarithmic score removed by compensation. -/
def primeLogScore (m : B.sampleData.Sample) : ℝ :=
  ∑ p : ArithmeticBandGeometry.BandPrime
      B.sampleData.n B.sampleData.W,
    ArithmeticModel.tPrime B.sampleData.n p.1 *
      ArithmeticModel.valuation p.1 (B.sampleData.value m)

/-- The logarithm contributed by the prescribed finite head pattern. -/
def headLogScore (h : Head) : ℝ :=
  ∑ p ∈ (B.sampleData.pattern h).primes,
    ((B.sampleData.pattern h).exponent p : ℝ) * Real.log (p : ℝ)

/-- Reindex the subtype sum defining the medium-prime logarithmic score
back onto the actual finite prime band.  This is an exact identity, with no
prime-sum or smooth-number approximation. -/
theorem primeLogScore_eq_bandFactorization_div
    (m : B.sampleData.Sample) :
    B.primeLogScore m =
      (∑ p ∈ ArithmeticModel.primeBand
          B.sampleData.n B.sampleData.W,
        ((B.sampleData.value m).factorization p : ℝ) *
          Real.log (p : ℝ)) /
        Real.log (ArithmeticModel.y B.sampleData.n) := by
  unfold primeLogScore ArithmeticModel.tPrime ArithmeticModel.valuation
  have hattach :
      (∑ p : ArithmeticBandGeometry.BandPrime
          B.sampleData.n B.sampleData.W,
        Real.log (p.1 : ℝ) /
            Real.log (ArithmeticModel.y B.sampleData.n) *
          ((B.sampleData.value m).factorization p.1 : ℝ)) =
        ∑ p ∈ ArithmeticModel.primeBand
            B.sampleData.n B.sampleData.W,
          Real.log (p : ℝ) /
              Real.log (ArithmeticModel.y B.sampleData.n) *
            ((B.sampleData.value m).factorization p : ℝ) := by
    simpa only [Finset.univ_eq_attach] using
      (Finset.sum_attach
        (ArithmeticModel.primeBand B.sampleData.n B.sampleData.W)
        (fun p => Real.log (p : ℝ) /
            Real.log (ArithmeticModel.y B.sampleData.n) *
          ((B.sampleData.value m).factorization p : ℝ)))
  rw [hattach, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- If every prime at most `W` is recorded in each head pattern, then the
factorization logarithm of every structured sample splits exactly into its
prescribed head contribution and the actual band `W < p ≤ floor(y)`.

The hypothesis is stated for every head tag because the sample is a tagged
disjoint union.  No convergence of head patterns, no limiting mixture, and
no prime-number estimate is used here. -/
theorem log_value_eq_headLogScore_add_bandFactorization
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W)
    (m : B.sampleData.Sample) :
    Real.log (B.sampleData.value m : ℝ) =
      B.headLogScore (B.sampleData.cellOf m).1 +
        ∑ p ∈ ArithmeticModel.primeBand
            B.sampleData.n B.sampleData.W,
          ((B.sampleData.value m).factorization p : ℝ) *
            Real.log (p : ℝ) := by
  let h : Head := (B.sampleData.cellOf m).1
  let P : HeadPattern.Pattern := B.sampleData.pattern h
  let band : Finset ℕ := ArithmeticModel.primeBand
    B.sampleData.n B.sampleData.W
  let support : Finset ℕ := (B.sampleData.value m).factorization.support
  let summand : ℕ → ℝ := fun p =>
    ((B.sampleData.value m).factorization p : ℝ) * Real.log (p : ℝ)
  have hsmooth := B.sampleData.value_mem_smoothNumbers m
  have hsupport : support ⊆ P.primes ∪ band := by
    intro p hp
    have hpFactors : p ∈ (B.sampleData.value m).primeFactors := by
      simpa [support] using hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpFactors
    have hpBelow : p ∈ (ArithmeticModel.yNat B.sampleData.n + 1).primesBelow :=
      Nat.primeFactors_subset_of_mem_smoothNumbers hsmooth hpFactors
    have hpLeY : p ≤ ArithmeticModel.yNat B.sampleData.n := by
      have hpLt : p < ArithmeticModel.yNat B.sampleData.n + 1 :=
        (Nat.mem_primesBelow.mp hpBelow).1
      omega
    by_cases hpW : p ≤ B.sampleData.W
    · apply Finset.mem_union_left
      exact (hhead h p).mpr ⟨hpPrime, hpW⟩
    · apply Finset.mem_union_right
      exact ArithmeticModel.mem_primeBand.mpr
        ⟨hpPrime, Nat.lt_of_not_ge hpW, hpLeY⟩
  have hdisjoint : Disjoint P.primes band := by
    rw [Finset.disjoint_left]
    intro p hpHead hpBand
    have hpLeW : p ≤ B.sampleData.W := (hhead h p).mp hpHead |>.2
    have hpGtW : B.sampleData.W < p :=
      ArithmeticModel.cutoff_lt_of_mem_primeBand hpBand
    exact (Nat.not_lt_of_ge hpLeW) hpGtW
  have hextend :
      ∑ p ∈ support, summand p =
        ∑ p ∈ P.primes ∪ band, summand p := by
    apply Finset.sum_subset hsupport
    intro p hpUnion hpNotSupport
    have hzero : (B.sampleData.value m).factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by simpa [support] using hpNotSupport)
    simp [summand, hzero]
  have hheadSum :
      ∑ p ∈ P.primes, summand p = B.headLogScore h := by
    unfold headLogScore
    apply Finset.sum_congr (by rfl)
    intro p hp
    have hmatch := B.sampleData.value_matches_head m
    simp only [summand]
    rw [show (B.sampleData.value m).factorization p = P.exponent p by
      exact hmatch p (by simpa [P, h] using hp)]
  calc
    Real.log (B.sampleData.value m : ℝ) =
        (B.sampleData.value m).factorization.sum
          (fun p t => (t : ℝ) * Real.log (p : ℝ)) :=
      Real.log_nat_eq_sum_factorization (B.sampleData.value m)
    _ = ∑ p ∈ support, summand p := by
      rfl
    _ = ∑ p ∈ P.primes ∪ band, summand p := hextend
    _ = (∑ p ∈ P.primes, summand p) +
        ∑ p ∈ band, summand p := Finset.sum_union hdisjoint
    _ = B.headLogScore h + ∑ p ∈ band, summand p := by rw [hheadSum]
    _ = B.headLogScore (B.sampleData.cellOf m).1 +
        ∑ p ∈ ArithmeticModel.primeBand
            B.sampleData.n B.sampleData.W,
          ((B.sampleData.value m).factorization p : ℝ) *
            Real.log (p : ℝ) := by
      rfl

/-- Exact arithmetic centering of the compensated prime coefficients on
each actual band.  This is deliberately an identity for the finite prime
set, not a continuum approximation. -/
theorem primeDeviation_fiber_sum (j : Band) :
    ∑ p ∈ B.partition.data.fiber j,
      (1 / (p.1 : ℝ)) * B.primeDeviation p = 0 := by
  calc
    ∑ p ∈ B.partition.data.fiber j,
        (1 / (p.1 : ℝ)) * B.primeDeviation p =
        ∑ p ∈ B.partition.data.fiber j,
          (1 / (p.1 : ℝ)) *
            (B.bandCenter j -
              ArithmeticModel.tPrime B.sampleData.n p.1) := by
      apply Finset.sum_congr rfl
      intro p hp
      unfold primeDeviation
      have hpj : B.partition.band p = j :=
        (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff
          B.partition.data).mp hp
      rw [hpj]
    _ = 0 := B.partition.center_fiber_sum j

/-- The raw slow score is exactly the centered combination of the band
valuations and the physical logarithmic prime score.  This finite identity
is the algebra behind the compensated coordinate in Lemmas 8.5--8.6. -/
theorem slowScore_decomposition (m : B.sampleData.Sample) :
    B.slowScore m =
      (∑ j : Band, B.bandCenter j * B.bandScore j m) -
        ∑ p : ArithmeticBandGeometry.BandPrime
            B.sampleData.n B.sampleData.W,
          ArithmeticModel.tPrime B.sampleData.n p.1 *
            ArithmeticModel.valuation p.1 (B.sampleData.value m) := by
  unfold slowScore primeDeviation
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  unfold bandScore
  rw [← Finset.sum_fiberwise Finset.univ B.partition.band
    (fun p => B.bandCenter (B.partition.band p) *
      ArithmeticModel.valuation p.1 (B.sampleData.value m))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpj : B.partition.band p = j := (Finset.mem_filter.mp hp).2
  rw [hpj]

theorem slowScore_eq_bandScore_sub_primeLogScore
    (m : B.sampleData.Sample) :
    B.slowScore m =
      (∑ j : Band, B.bandCenter j * B.bandScore j m) -
        B.primeLogScore m := by
  exact B.slowScore_decomposition m

/-- Raw paper statistic before anisotropic coordinate scaling. -/
def rawStatistic [Nonempty Head]
    (m : B.sampleData.Sample) : B.Coord → ℝ
  | .gauge j => B.gaugeScore j m
  | .physical => B.physicalScore m
  | .head h => B.centeredHeadScore h m
  | .slow => B.slowScore m

/-- Coordinate scaling: only the slow statistic is divided by `w`, so its
dual parameter is `w*lambda`. -/
def coordScale (c : B.Coord) : ℝ :=
  match c with
  | .slow => B.w
  | _ => 1

theorem coordScale_pos (c : B.Coord) : 0 < B.coordScale c := by
  cases c <;> simp [coordScale, B.w_pos]

/-- The actual statistic vector used by `VectorExponentialFamily`. -/
def statistic [Nonempty Head]
    (m : B.sampleData.Sample) : B.ParamSpace :=
  (EuclideanSpace.equiv B.Coord ℝ).symm
    (fun c => B.rawStatistic m c / B.coordScale c)

@[simp]
theorem statistic_apply [Nonempty Head]
    (m : B.sampleData.Sample) (c : B.Coord) :
    (B.statistic m : B.Coord → ℝ) c =
      B.rawStatistic m c / B.coordScale c := by
  rfl

/-! ### Exact main/nuisance coordinate splitting -/

/-- Coordinate inclusion of quotient-band and slow variables. -/
def mainEmbed (u : B.MainSpace) : B.ParamSpace :=
  (EuclideanSpace.equiv B.Coord ℝ).symm (fun c => match c with
    | .gauge j => u (MainCoord.gauge j)
    | .slow => u MainCoord.slow
    | .physical => 0
    | .head _ => 0)

/-- Coordinate inclusion of physical/head nuisance variables. -/
def nuisanceEmbed (z : B.NuisanceSpace) : B.ParamSpace :=
  (EuclideanSpace.equiv B.Coord ℝ).symm (fun c => match c with
    | .physical => z NuisanceCoord.physical
    | .head h => z (NuisanceCoord.head h)
    | .gauge _ => 0
    | .slow => 0)

@[simp] theorem mainEmbed_gauge (u : B.MainSpace) (j : B.GaugeIndex) :
    B.mainEmbed u (MomentCoord.gauge j) = u (MainCoord.gauge j) := rfl

@[simp] theorem mainEmbed_slow (u : B.MainSpace) :
    B.mainEmbed u MomentCoord.slow = u MainCoord.slow := rfl

@[simp] theorem mainEmbed_physical (u : B.MainSpace) :
    B.mainEmbed u MomentCoord.physical = 0 := rfl

@[simp] theorem mainEmbed_head (u : B.MainSpace) (h : B.HeadIndex) :
    B.mainEmbed u (MomentCoord.head h) = 0 := rfl

@[simp] theorem nuisanceEmbed_gauge (z : B.NuisanceSpace)
    (j : B.GaugeIndex) : B.nuisanceEmbed z (MomentCoord.gauge j) = 0 := rfl

@[simp] theorem nuisanceEmbed_slow (z : B.NuisanceSpace) :
    B.nuisanceEmbed z MomentCoord.slow = 0 := rfl

@[simp] theorem nuisanceEmbed_physical (z : B.NuisanceSpace) :
    B.nuisanceEmbed z MomentCoord.physical = z NuisanceCoord.physical := rfl

@[simp] theorem nuisanceEmbed_head (z : B.NuisanceSpace)
    (h : B.HeadIndex) :
    B.nuisanceEmbed z (MomentCoord.head h) = z (NuisanceCoord.head h) := rfl

def mainEmbedding : B.MainSpace →ₗ[ℝ] B.ParamSpace where
  toFun := B.mainEmbed
  map_add' := by
    intro u v
    apply (EuclideanSpace.equiv B.Coord ℝ).injective
    funext c
    cases c <;> simp [mainEmbed]
  map_smul' := by
    intro a u
    apply (EuclideanSpace.equiv B.Coord ℝ).injective
    funext c
    cases c <;> simp [mainEmbed]

def nuisanceEmbedding : B.NuisanceSpace →ₗ[ℝ] B.ParamSpace where
  toFun := B.nuisanceEmbed
  map_add' := by
    intro u v
    apply (EuclideanSpace.equiv B.Coord ℝ).injective
    funext c
    cases c <;> simp [nuisanceEmbed]
  map_smul' := by
    intro a u
    apply (EuclideanSpace.equiv B.Coord ℝ).injective
    funext c
    cases c <;> simp [nuisanceEmbed]

def mainEmbeddingCLM : B.MainSpace →L[ℝ] B.ParamSpace :=
  B.mainEmbedding.toContinuousLinearMap

def nuisanceEmbeddingCLM : B.NuisanceSpace →L[ℝ] B.ParamSpace :=
  B.nuisanceEmbedding.toContinuousLinearMap

/-- Recombination of the two complementary coordinate blocks. -/
def combine (u : B.MainSpace) (z : B.NuisanceSpace) : B.ParamSpace :=
  B.mainEmbed u + B.nuisanceEmbed z

@[simp] theorem combine_gauge (u : B.MainSpace) (z : B.NuisanceSpace)
    (j : B.GaugeIndex) :
    B.combine u z (MomentCoord.gauge j) = u (MainCoord.gauge j) := by
  simp [combine]

@[simp] theorem combine_slow (u : B.MainSpace) (z : B.NuisanceSpace) :
    B.combine u z MomentCoord.slow = u MainCoord.slow := by
  simp [combine]

@[simp] theorem combine_physical (u : B.MainSpace) (z : B.NuisanceSpace) :
    B.combine u z MomentCoord.physical = z NuisanceCoord.physical := by
  simp [combine]

@[simp] theorem combine_head (u : B.MainSpace) (z : B.NuisanceSpace)
    (h : B.HeadIndex) :
    B.combine u z (MomentCoord.head h) = z (NuisanceCoord.head h) := by
  simp [combine]

/-- The coordinate type is exactly the disjoint union of the main and
nuisance coordinate types.  Making this equivalence explicit avoids relying
on fragile simplification of sums over a derived `Fintype` instance. -/
def coordSplitEquiv :
    B.Coord ≃ (MainCoord B.GaugeIndex ⊕ NuisanceCoord B.HeadIndex) where
  toFun
    | .gauge j => Sum.inl (.gauge j)
    | .slow => Sum.inl .slow
    | .physical => Sum.inr .physical
    | .head h => Sum.inr (.head h)
  invFun
    | Sum.inl (.gauge j) => .gauge j
    | Sum.inl .slow => .slow
    | Sum.inr .physical => .physical
    | Sum.inr (.head h) => .head h
  left_inv c := by cases c <;> rfl
  right_inv c := by
    rcases c with c | c <;> cases c <;> rfl

theorem sum_coord_split (f : B.Coord → ℝ) :
    (∑ c : B.Coord, f c) =
      (∑ c : MainCoord B.GaugeIndex,
        f (match c with
          | .gauge j => .gauge j
          | .slow => .slow)) +
      ∑ c : NuisanceCoord B.HeadIndex,
        f (match c with
          | .physical => .physical
          | .head h => .head h) := by
  calc
    (∑ c : B.Coord, f c) =
        ∑ s : (MainCoord B.GaugeIndex ⊕ NuisanceCoord B.HeadIndex),
          f (B.coordSplitEquiv.symm s) := by
      exact Fintype.sum_equiv B.coordSplitEquiv f
        (fun s => f (B.coordSplitEquiv.symm s)) (fun c => by simp)
    _ = _ := by
      rw [Fintype.sum_sum_type]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro c hc
        cases c <;> simp [coordSplitEquiv]
      · apply Finset.sum_congr rfl
        intro c hc
        cases c <;> simp [coordSplitEquiv]

theorem combine_norm_sq (u : B.MainSpace) (z : B.NuisanceSpace) :
    ‖B.combine u z‖ ^ 2 = ‖u‖ ^ 2 + ‖z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs]
  change (∑ c : B.Coord, |B.combine u z c| ^ 2) =
    (∑ c : MainCoord B.GaugeIndex, |u c| ^ 2) +
      ∑ c : NuisanceCoord B.HeadIndex, |z c| ^ 2
  rw [B.sum_coord_split]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro c hc
    cases c <;> simp
  · apply Finset.sum_congr rfl
    intro c hc
    cases c <;> simp

theorem norm_mainEmbed (u : B.MainSpace) :
    ‖B.mainEmbed u‖ = ‖u‖ := by
  have hcombine : B.combine u 0 = B.mainEmbed u := by
    apply (EuclideanSpace.equiv B.Coord ℝ).injective
    funext c
    cases c <;> simp [combine]
  have h := B.combine_norm_sq u 0
  rw [hcombine] at h
  norm_num at h
  nlinarith [norm_nonneg (B.mainEmbed u), norm_nonneg u]

theorem norm_nuisanceEmbed (z : B.NuisanceSpace) :
    ‖B.nuisanceEmbed z‖ = ‖z‖ := by
  have hcombine : B.combine 0 z = B.nuisanceEmbed z := by
    apply (EuclideanSpace.equiv B.Coord ℝ).injective
    funext c
    cases c <;> simp [combine]
  have h := B.combine_norm_sq 0 z
  rw [hcombine] at h
  norm_num at h
  nlinarith [norm_nonneg (B.nuisanceEmbed z), norm_nonneg z]

theorem mainEmbeddingCLM_norm_le_one :
    ‖B.mainEmbeddingCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖B.mainEmbed u‖ ≤ 1 * ‖u‖
  rw [B.norm_mainEmbed, one_mul]

theorem nuisanceEmbeddingCLM_norm_le_one :
    ‖B.nuisanceEmbeddingCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖B.nuisanceEmbed z‖ ≤ 1 * ‖z‖
  rw [B.norm_nuisanceEmbed, one_mul]

theorem inner_mainEmbed_combine (u v : B.MainSpace)
    (z : B.NuisanceSpace) :
    inner ℝ (B.mainEmbed u) (B.combine v z) = inner ℝ u v := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  change (∑ c : B.Coord, B.combine v z c * B.mainEmbed u c) =
    ∑ c : MainCoord B.GaugeIndex, v c * u c
  rw [B.sum_coord_split]
  have hmain : (∑ c : MainCoord B.GaugeIndex,
      B.combine v z (match c with
        | .gauge j => .gauge j
        | .slow => .slow) *
      B.mainEmbed u (match c with
        | .gauge j => .gauge j
        | .slow => .slow)) = ∑ c, v c * u c := by
    apply Finset.sum_congr rfl
    intro c hc
    cases c <;> simp
  have hnuisance : (∑ c : NuisanceCoord B.HeadIndex,
      B.combine v z (match c with
        | .physical => .physical
        | .head h => .head h) *
      B.mainEmbed u (match c with
        | .physical => .physical
        | .head h => .head h)) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    cases c <;> simp
  rw [hmain, hnuisance, add_zero]

theorem inner_nuisanceEmbed_combine (z v : B.NuisanceSpace)
    (u : B.MainSpace) :
    inner ℝ (B.nuisanceEmbed z) (B.combine u v) = inner ℝ z v := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  change (∑ c : B.Coord, B.combine u v c * B.nuisanceEmbed z c) =
    ∑ c : NuisanceCoord B.HeadIndex, v c * z c
  rw [B.sum_coord_split]
  have hmain : (∑ c : MainCoord B.GaugeIndex,
      B.combine u v (match c with
        | .gauge j => .gauge j
        | .slow => .slow) *
      B.nuisanceEmbed z (match c with
        | .gauge j => .gauge j
        | .slow => .slow)) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    cases c <;> simp
  have hnuisance : (∑ c : NuisanceCoord B.HeadIndex,
      B.combine u v (match c with
        | .physical => .physical
        | .head h => .head h) *
      B.nuisanceEmbed z (match c with
        | .physical => .physical
        | .head h => .head h)) = ∑ c, v c * z c := by
    apply Finset.sum_congr rfl
    intro c hc
    cases c <;> simp
  rw [hmain, hnuisance, zero_add]

/-- The quotient/slow portion of the actual statistic vector. -/
def mainStatistic [Nonempty Head]
    (m : B.sampleData.Sample) : B.MainSpace :=
  (EuclideanSpace.equiv (MainCoord B.GaugeIndex) ℝ).symm
    (fun c => match c with
      | .gauge j => B.statistic m (MomentCoord.gauge j)
      | .slow => B.statistic m MomentCoord.slow)

@[simp] theorem mainStatistic_gauge [Nonempty Head]
    (m : B.sampleData.Sample) (j : B.GaugeIndex) :
    B.mainStatistic m (MainCoord.gauge j) =
      B.statistic m (MomentCoord.gauge j) := rfl

@[simp] theorem mainStatistic_slow [Nonempty Head]
    (m : B.sampleData.Sample) :
    B.mainStatistic m MainCoord.slow = B.statistic m MomentCoord.slow := rfl

/-- The concrete self-dual exponential family.  In the scaled coordinates
`theta_slow=w*lambda`, its exponent is exactly
`L^(-1)(sum u_j Q_j + a^T Z + lambda S_g)`. -/
def vectorFamily [Nonempty Head] :
    VectorExponentialFamily B.sampleData.Sample B.ParamSpace where
  baseWeight := B.baseline.baseWeight
  baseWeight_nonneg := B.baseline.baseWeight_nonneg
  baseMass_pos := by
    rw [B.baseline.baseWeight_sum]
    exact B.q_pos
  scale := B.L
  scale_pos := B.L_pos
  statistic := B.statistic

theorem vectorFamily_baseMass [Nonempty Head] :
    B.vectorFamily.baseMass = B.q := by
  simp only [VectorExponentialFamily.baseMass,
    VectorExponentialFamily.scalarFamily,
    FiniteExponentialFamily.baseMass, vectorFamily, q]
  exact B.baseline.baseWeight_sum

/-- The normalized covariance operator.  The factor `L/q` removes the
active-mass Jacobian normalization, so its quadratic form is exactly the
probability covariance of the actual statistic vector. -/
def covarianceOperator [Nonempty Head]
    (xi : B.ParamSpace) : B.ParamSpace →L[ℝ] B.ParamSpace :=
  (B.L / B.q) • B.vectorFamily.jacobian xi

/-- Bilinear covariance--Jacobian identity for the concrete vector family. -/
theorem inner_jacobian [Nonempty Head]
    (xi x y : B.ParamSpace) :
    inner ℝ x (B.vectorFamily.jacobian xi y) =
      (B.q / B.L) * B.vectorFamily.scalarFamily.covariance
        (fun m => inner ℝ x (B.statistic m))
        (fun m => inner ℝ y (B.statistic m)) xi := by
  let F : B.sampleData.Sample → ℝ :=
    fun m => inner ℝ x (B.statistic m)
  have hleft : HasFDerivAt
      (fun eta => inner ℝ x (B.vectorFamily.vectorMoment eta))
      (((innerSL ℝ) x).comp (B.vectorFamily.jacobian xi)) xi := by
    exact ((innerSL ℝ) x).hasFDerivAt.comp xi
      (B.vectorFamily.hasFDerivAt_vectorMoment xi)
  have hright : HasFDerivAt
      (B.vectorFamily.scalarFamily.moment F)
      ((B.vectorFamily.baseMass / B.vectorFamily.scale) •
        B.vectorFamily.scalarFamily.covarianceScore F xi) xi :=
    B.vectorFamily.scalarFamily.hasFDerivAt_moment_covariance F xi
  have hfun : (fun eta => inner ℝ x
      (B.vectorFamily.vectorMoment eta)) =
      B.vectorFamily.scalarFamily.moment F := by
    funext eta
    exact B.vectorFamily.inner_vectorMoment x eta
  have hmaps : ((innerSL ℝ) x).comp (B.vectorFamily.jacobian xi) =
      (B.vectorFamily.baseMass / B.vectorFamily.scale) •
        B.vectorFamily.scalarFamily.covarianceScore F xi :=
    hleft.unique (hfun ▸ hright)
  have happ := congrArg
    (fun T : B.ParamSpace →L[ℝ] ℝ => T y) hmaps
  change inner ℝ x (B.vectorFamily.jacobian xi y) =
    (B.vectorFamily.baseMass / B.vectorFamily.scale) *
      B.vectorFamily.scalarFamily.covarianceScore F xi y at happ
  rw [B.vectorFamily.scalarFamily.covarianceScore_apply F xi y] at happ
  have hscore :
      (fun m => B.vectorFamily.scalarFamily.score m y) =
        fun m => inner ℝ y (B.statistic m) := by
    funext m
    simp only [VectorExponentialFamily.scalarFamily, innerSL_apply_apply]
    exact real_inner_comm _ _
  rw [hscore, B.vectorFamily_baseMass] at happ
  simpa only [vectorFamily] using happ

theorem inner_covarianceOperator [Nonempty Head]
    (xi x y : B.ParamSpace) :
    inner ℝ x (B.covarianceOperator xi y) =
      B.vectorFamily.scalarFamily.covariance
        (fun m => inner ℝ x (B.statistic m))
        (fun m => inner ℝ y (B.statistic m)) xi := by
  rw [covarianceOperator, ContinuousLinearMap.smul_apply, inner_smul_right,
    B.inner_jacobian]
  field_simp [ne_of_gt B.L_pos, ne_of_gt B.q_pos]

theorem covarianceOperator_symmetric [Nonempty Head]
    (xi x y : B.ParamSpace) :
    inner ℝ x (B.covarianceOperator xi y) =
      inner ℝ y (B.covarianceOperator xi x) := by
  rw [B.inner_covarianceOperator, B.inner_covarianceOperator]
  unfold FiniteExponentialFamily.covariance FiniteProbability.covariance
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    ring
  · ring

theorem inner_covarianceOperator_self [Nonempty Head]
    (xi x : B.ParamSpace) :
    inner ℝ x (B.covarianceOperator xi x) =
      (B.vectorFamily.tiltedMixture xi).covarianceForm x := by
  rw [covarianceOperator, ContinuousLinearMap.smul_apply, inner_smul_right,
    B.vectorFamily.inner_jacobian_self]
  have hL : B.L ≠ 0 := ne_of_gt B.L_pos
  have hq : B.q ≠ 0 := ne_of_gt B.q_pos
  rw [B.vectorFamily_baseMass]
  change (B.L / B.q) *
      (B.q / B.L *
        (B.vectorFamily.tiltedMixture xi).covarianceForm x) =
    (B.vectorFamily.tiltedMixture xi).covarianceForm x
  field_simp

/-- Actual quotient/slow covariance block. -/
def mainCovarianceOperator [Nonempty Head]
    (xi : B.ParamSpace) : B.MainSpace →L[ℝ] B.MainSpace :=
  B.mainEmbeddingCLM.adjoint.comp
    ((B.covarianceOperator xi).comp B.mainEmbeddingCLM)

/-- Actual finite nuisance covariance `Γ_{xi,n}`. -/
def nuisanceCovarianceOperator [Nonempty Head]
    (xi : B.ParamSpace) : B.NuisanceSpace →L[ℝ] B.NuisanceSpace :=
  B.nuisanceEmbeddingCLM.adjoint.comp
    ((B.covarianceOperator xi).comp B.nuisanceEmbeddingCLM)

/-- The actual main-to-nuisance cross-covariance block. -/
def crossCovarianceOperator [Nonempty Head]
    (xi : B.ParamSpace) : B.MainSpace →L[ℝ] B.NuisanceSpace :=
  B.nuisanceEmbeddingCLM.adjoint.comp
    ((B.covarianceOperator xi).comp B.mainEmbeddingCLM)

/-- Residual main score after subtracting a nuisance regression. -/
def schurResidual (R : B.MainSpace → B.NuisanceSpace)
    (u : B.MainSpace) : B.ParamSpace :=
  B.combine u (-R u)

theorem schurResidual_eq_sub (R : B.MainSpace → B.NuisanceSpace)
    (u : B.MainSpace) :
    B.schurResidual R u = B.mainEmbed u - B.nuisanceEmbed (R u) := by
  unfold schurResidual combine
  have hneg : B.nuisanceEmbed (-R u) = -B.nuisanceEmbed (R u) :=
    B.nuisanceEmbedding.map_neg (R u)
  rw [hneg]
  rfl

/-- Exact two-sided block orthogonality of a nuisance regression.  This is
an algebraic equation for the displayed actual covariance operator, not a
spectral-gap hypothesis. -/
def IsNuisanceRegression [Nonempty Head] (xi : B.ParamSpace)
    (R : B.MainSpace → B.NuisanceSpace) : Prop :=
  ∀ u z,
    inner ℝ (B.schurResidual R u)
        (B.covarianceOperator xi (B.nuisanceEmbed z)) = 0 ∧
      inner ℝ (B.nuisanceEmbed z)
        (B.covarianceOperator xi (B.schurResidual R u)) = 0

theorem nuisanceCovarianceOperator_injective [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    Function.Injective (B.nuisanceCovarianceOperator xi) := by
  intro z₁ z₂ heq
  have hzero : B.nuisanceCovarianceOperator xi (z₁ - z₂) = 0 := by
    rw [map_sub, heq, sub_self]
  have hcoer := hgap (z₁ - z₂)
  rw [hzero, inner_zero_right] at hcoer
  have hnorm : ‖z₁ - z₂‖ = 0 := by
    by_contra hn
    have hnpos : 0 < ‖z₁ - z₂‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    have : 0 < gamma * ‖z₁ - z₂‖ ^ 2 :=
      mul_pos hgamma (sq_pos_of_pos hnpos)
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- The actual nuisance block as an equivalence, constructed from a proved
finite coercivity bound. -/
def nuisanceCovarianceEquiv [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    B.NuisanceSpace ≃L[ℝ] B.NuisanceSpace :=
  (LinearEquiv.ofInjectiveEndo
    ((B.nuisanceCovarianceOperator xi :
      B.NuisanceSpace →L[ℝ] B.NuisanceSpace) :
        B.NuisanceSpace →ₗ[ℝ] B.NuisanceSpace)
    (B.nuisanceCovarianceOperator_injective xi hgamma hgap)).toContinuousLinearEquiv

theorem nuisanceCovarianceEquiv_apply [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (z : B.NuisanceSpace) :
    B.nuisanceCovarianceEquiv xi hgamma hgap z =
      B.nuisanceCovarianceOperator xi z := by
  simp [nuisanceCovarianceEquiv]

/-- The actual finite nuisance regression `Γ_{xi,n}^{-1} B_{xi,n}`. -/
def exactNuisanceRegression [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) : B.NuisanceSpace :=
  (B.nuisanceCovarianceEquiv xi hgamma hgap).symm
    (B.crossCovarianceOperator xi u)

def exactNuisanceRegressionCLM [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    B.MainSpace →L[ℝ] B.NuisanceSpace :=
  (B.nuisanceCovarianceEquiv xi hgamma hgap).symm.toContinuousLinearMap.comp
    (B.crossCovarianceOperator xi)

@[simp] theorem exactNuisanceRegressionCLM_apply [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    B.exactNuisanceRegressionCLM xi hgamma hgap u =
      B.exactNuisanceRegression xi hgamma hgap u := rfl

/-- Linear residual inclusion `u ↦ (u,-Γ⁻¹Bu)`. -/
def exactSchurEmbeddingCLM [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    B.MainSpace →L[ℝ] B.ParamSpace :=
  B.mainEmbeddingCLM - B.nuisanceEmbeddingCLM.comp
    (B.exactNuisanceRegressionCLM xi hgamma hgap)

@[simp] theorem exactSchurEmbeddingCLM_apply [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    B.exactSchurEmbeddingCLM xi hgamma hgap u =
      B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) u := by
  rw [B.schurResidual_eq_sub]
  rfl

/-- Actual main/slow Schur-complement operator after exact finite nuisance
regression. -/
def exactSchurCovarianceOperator [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    B.MainSpace →L[ℝ] B.MainSpace :=
  B.mainEmbeddingCLM.adjoint.comp
    ((B.covarianceOperator xi).comp
      (B.exactSchurEmbeddingCLM xi hgamma hgap))

theorem exactNuisanceRegression_solve [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    B.nuisanceCovarianceOperator xi
        (B.exactNuisanceRegression xi hgamma hgap u) =
      B.crossCovarianceOperator xi u := by
  rw [← B.nuisanceCovarianceEquiv_apply xi hgamma hgap]
  exact (B.nuisanceCovarianceEquiv xi hgamma hgap).apply_symm_apply _

theorem exactNuisanceRegression_isRegression [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    B.IsNuisanceRegression xi
      (B.exactNuisanceRegression xi hgamma hgap) := by
  intro u z
  let R := B.exactNuisanceRegression xi hgamma hgap
  have hres : B.schurResidual R u =
      B.mainEmbed u - B.nuisanceEmbed (R u) :=
    B.schurResidual_eq_sub R u
  have hcross : inner ℝ (B.nuisanceEmbed z)
      (B.covarianceOperator xi (B.mainEmbed u)) =
      inner ℝ z (B.crossCovarianceOperator xi u) := by
    simpa only [crossCovarianceOperator, ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.adjoint_inner_right B.nuisanceEmbeddingCLM z
        (B.covarianceOperator xi (B.mainEmbeddingCLM u))).symm
  have hblock : inner ℝ (B.nuisanceEmbed z)
      (B.covarianceOperator xi (B.nuisanceEmbed (R u))) =
      inner ℝ z (B.nuisanceCovarianceOperator xi (R u)) := by
    simpa only [nuisanceCovarianceOperator,
      ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.adjoint_inner_right B.nuisanceEmbeddingCLM z
        (B.covarianceOperator xi
          (B.nuisanceEmbeddingCLM (R u)))).symm
  have hsecond : inner ℝ (B.nuisanceEmbed z)
      (B.covarianceOperator xi (B.schurResidual R u)) = 0 := by
    rw [hres, map_sub, inner_sub_right, hcross, hblock]
    rw [B.exactNuisanceRegression_solve xi hgamma hgap]
    exact sub_self _
  refine ⟨?_, hsecond⟩
  rw [B.covarianceOperator_symmetric xi]
  exact hsecond

theorem exactSchurCovarianceOperator_quadratic [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    inner ℝ u (B.exactSchurCovarianceOperator xi hgamma hgap u) =
      inner ℝ
        (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) u)
        (B.covarianceOperator xi
          (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) u)) := by
  let R := B.exactNuisanceRegression xi hgamma hgap
  let residual := B.schurResidual R u
  have hleft : inner ℝ u
      (B.exactSchurCovarianceOperator xi hgamma hgap u) =
      inner ℝ (B.mainEmbed u) (B.covarianceOperator xi residual) := by
    simpa only [exactSchurCovarianceOperator,
      ContinuousLinearMap.comp_apply,
      B.exactSchurEmbeddingCLM_apply, R, residual] using
      (ContinuousLinearMap.adjoint_inner_right B.mainEmbeddingCLM u
        (B.covarianceOperator xi residual))
  have hres : residual = B.mainEmbed u - B.nuisanceEmbed (R u) := by
    exact B.schurResidual_eq_sub R u
  have horth :=
    (B.exactNuisanceRegression_isRegression xi hgamma hgap u (R u)).2
  have hmain : B.mainEmbed u = residual + B.nuisanceEmbed (R u) := by
    rw [hres]
    abel
  calc
    inner ℝ u (B.exactSchurCovarianceOperator xi hgamma hgap u) =
        inner ℝ (B.mainEmbed u) (B.covarianceOperator xi residual) := hleft
    _ = inner ℝ residual (B.covarianceOperator xi residual) := by
      rw [hmain, inner_add_left, horth, add_zero]

/-- Transfer a continuum/reference Schur gap to the actual arithmetic
Schur block from an explicit quadratic-form error.  This is the precise
place where the sharp-relative `C/W + o(1)` estimate of Lemma 8.6 enters. -/
theorem exactSchur_gap_of_referenceComparison [Nonempty Head]
    (xi : B.ParamSpace) {gammaNuisance : ℝ}
    (hNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (reference : B.MainSpace →L[ℝ] B.MainSpace)
    (gammaReference delta : ℝ)
    (href : ∀ u, gammaReference * ‖u‖ ^ 2 ≤
      inner ℝ u (reference u))
    (hcomparison : ∀ u,
      |inner ℝ u
        ((B.exactSchurCovarianceOperator xi hNuisance hGamma -
          reference) u)| ≤ delta * ‖u‖ ^ 2)
    (u : B.MainSpace) :
    (gammaReference - delta) * ‖u‖ ^ 2 ≤
      inner ℝ
        (B.schurResidual
          (B.exactNuisanceRegression xi hNuisance hGamma) u)
        (B.covarianceOperator xi
          (B.schurResidual
            (B.exactNuisanceRegression xi hNuisance hGamma) u)) := by
  rw [← B.exactSchurCovarianceOperator_quadratic]
  have hdiffLower : -(delta * ‖u‖ ^ 2) ≤
      inner ℝ u
        ((B.exactSchurCovarianceOperator xi hNuisance hGamma -
          reference) u) :=
    neg_le_of_abs_le (hcomparison u)
  have hsplit : inner ℝ u
      (B.exactSchurCovarianceOperator xi hNuisance hGamma u) =
      inner ℝ u (reference u) +
        inner ℝ u
          ((B.exactSchurCovarianceOperator xi hNuisance hGamma -
            reference) u) := by
    simp only [ContinuousLinearMap.sub_apply, inner_sub_right]
    ring
  rw [hsplit]
  nlinarith [href u]

/-- Stable-inverse transfer for the same actual Schur block.  Invertibility
and the inverse bound are conclusions of the reference inverse plus a
genuine operator-norm error estimate. -/
theorem exists_exactSchurEquiv_of_referenceInverse [Nonempty Head]
    (xi : B.ParamSpace) {gammaNuisance : ℝ}
    (hNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (reference referenceInv : B.MainSpace →L[ℝ] B.MainSpace)
    (C delta : ℝ) (hC : 0 ≤ C) (hsmall : C * delta < 1)
    (hleft : ∀ u, referenceInv (reference u) = u)
    (hinv : ∀ v, ‖referenceInv v‖ ≤ C * ‖v‖)
    (herror : ∀ u,
      ‖(B.exactSchurCovarianceOperator xi hNuisance hGamma -
        reference) u‖ ≤ delta * ‖u‖) :
    ∃ e : B.MainSpace ≃L[ℝ] B.MainSpace,
      (∀ u, e u = B.exactSchurCovarianceOperator xi hNuisance hGamma u) ∧
      ∀ v, ‖e.symm v‖ ≤ (C / (1 - C * delta)) * ‖v‖ := by
  let E := B.exactSchurCovarianceOperator xi hNuisance hGamma - reference
  let e := StableInverse.perturbedEquiv reference referenceInv E C delta
    hC hsmall hleft hinv (by simpa only [E] using herror)
  refine ⟨e, ?_, ?_⟩
  · intro u
    rw [show e u = (reference + E) u by
      exact StableInverse.perturbedEquiv_apply reference referenceInv E C delta
        hC hsmall hleft hinv (by simpa only [E] using herror) u]
    simp only [E, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply]
    abel
  · intro v
    exact StableInverse.perturbed_inverse_bound reference referenceInv E C delta
      hC hsmall hleft hinv (by simpa only [E] using herror) v

theorem exactNuisanceRegression_norm_le [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    ‖B.exactNuisanceRegression xi hgamma hgap u‖ ≤
      (‖B.crossCovarianceOperator xi‖ / gamma) * ‖u‖ := by
  let r := B.exactNuisanceRegression xi hgamma hgap u
  have hcoer := hgap r
  rw [B.exactNuisanceRegression_solve xi hgamma hgap] at hcoer
  have hinner : inner ℝ r (B.crossCovarianceOperator xi u) ≤
      ‖r‖ * ‖B.crossCovarianceOperator xi u‖ :=
    real_inner_le_norm _ _
  have hcross : ‖B.crossCovarianceOperator xi u‖ ≤
      ‖B.crossCovarianceOperator xi‖ * ‖u‖ :=
    B.crossCovarianceOperator xi |>.le_opNorm u
  by_cases hr : ‖r‖ = 0
  · change ‖r‖ ≤ (‖B.crossCovarianceOperator xi‖ / gamma) * ‖u‖
    rw [hr]
    exact mul_nonneg
      (div_nonneg (norm_nonneg _) (le_of_lt hgamma)) (norm_nonneg _)
  · have hrpos : 0 < ‖r‖ :=
      lt_of_le_of_ne (norm_nonneg r) (Ne.symm hr)
    have hcancel : gamma * ‖r‖ ≤
        ‖B.crossCovarianceOperator xi u‖ := by
      have hmul : (gamma * ‖r‖) * ‖r‖ ≤
          ‖B.crossCovarianceOperator xi u‖ * ‖r‖ := by
        calc
          (gamma * ‖r‖) * ‖r‖ = gamma * ‖r‖ ^ 2 := by ring
          _ ≤ inner ℝ r (B.crossCovarianceOperator xi u) := hcoer
          _ ≤ ‖B.crossCovarianceOperator xi u‖ * ‖r‖ := by
            simpa [mul_comm] using hinner
      exact (mul_le_mul_iff_right₀ hrpos).mp (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmul)
    calc
      ‖B.exactNuisanceRegression xi hgamma hgap u‖ = ‖r‖ := rfl
      _ ≤ ‖B.crossCovarianceOperator xi u‖ / gamma := by
        exact (le_div_iff₀ hgamma).2 (by simpa [mul_comm] using hcancel)
      _ ≤ (‖B.crossCovarianceOperator xi‖ * ‖u‖) / gamma :=
        div_le_div_of_nonneg_right hcross (le_of_lt hgamma)
      _ = (‖B.crossCovarianceOperator xi‖ / gamma) * ‖u‖ := by ring

/-- Exact coordinate recombination underlying the Schur decomposition. -/
theorem combine_eq_schurResidual_add
    (R : B.MainSpace → B.NuisanceSpace)
    (u : B.MainSpace) (z : B.NuisanceSpace) :
    B.combine u z = B.schurResidual R u + B.nuisanceEmbed (z + R u) := by
  apply (EuclideanSpace.equiv B.Coord ℝ).injective
  funext c
  cases c <;> simp [combine, schurResidual]

/-- With an exact regression, the full covariance quadratic form splits
into its Schur residual and the shifted nuisance quadratic form. -/
theorem covarianceForm_schur_decomposition [Nonempty Head]
    (xi : B.ParamSpace) (R : B.MainSpace → B.NuisanceSpace)
    (hR : B.IsNuisanceRegression xi R)
    (u : B.MainSpace) (z : B.NuisanceSpace) :
    (B.vectorFamily.tiltedMixture xi).covarianceForm (B.combine u z) =
      inner ℝ (B.schurResidual R u)
          (B.covarianceOperator xi (B.schurResidual R u)) +
        inner ℝ (B.nuisanceEmbed (z + R u))
          (B.covarianceOperator xi (B.nuisanceEmbed (z + R u))) := by
  rw [← B.inner_covarianceOperator_self,
    B.combine_eq_schurResidual_add R u z]
  simp only [map_add, inner_add_left, inner_add_right]
  rw [(hR u (z + R u)).1, (hR u (z + R u)).2]
  ring

/-- Explicit Euclidean loss when recombining a Schur residual with a
bounded regression. -/
theorem combine_norm_sq_le_schur_coordinates
    (R : B.MainSpace → B.NuisanceSpace) (C : ℝ)
    (hC : 0 ≤ C) (hRnorm : ∀ u, ‖R u‖ ≤ C * ‖u‖)
    (u : B.MainSpace) (z : B.NuisanceSpace) :
    ‖B.combine u z‖ ^ 2 ≤
      (3 + 2 * C ^ 2) * (‖u‖ ^ 2 + ‖z + R u‖ ^ 2) := by
  have hz : ‖z‖ ≤ ‖z + R u‖ + ‖R u‖ := by
    have hid : z = (z + R u) - R u := by abel
    calc
      ‖z‖ = ‖(z + R u) - R u‖ := congrArg norm hid
      _ ≤ ‖z + R u‖ + ‖R u‖ := norm_sub_le (z + R u) (R u)
  have hzC : ‖z‖ ≤ ‖z + R u‖ + C * ‖u‖ :=
    hz.trans (add_le_add (le_refl ‖z + R u‖) (hRnorm u))
  have hzsq : ‖z‖ ^ 2 ≤
      2 * ‖z + R u‖ ^ 2 + 2 * C ^ 2 * ‖u‖ ^ 2 := by
    have hsquare := pow_le_pow_left₀ (norm_nonneg z) hzC 2
    have hprod : 0 ≤ ‖z + R u‖ * (C * ‖u‖) :=
      mul_nonneg (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))
    calc
      ‖z‖ ^ 2 ≤ (‖z + R u‖ + C * ‖u‖) ^ 2 := hsquare
      _ ≤ 2 * ‖z + R u‖ ^ 2 + 2 * C ^ 2 * ‖u‖ ^ 2 := by
        nlinarith [sq_nonneg (‖z + R u‖ - C * ‖u‖)]
  rw [B.combine_norm_sq]
  have hcoef : 0 ≤ 3 + 2 * C ^ 2 := by positivity
  nlinarith [sq_nonneg ‖u‖, sq_nonneg ‖z + R u‖]

/-- Concrete full-gap conclusion from the two paper Schur blocks.  In
particular the proposition-level ODE need not assume a full covariance
gap once Lemma 8.6 supplies the residual bound and the finite nuisance
block supplies its bound. -/
theorem hasCovarianceGap_of_schur [Nonempty Head]
    (xi : B.ParamSpace) (R : B.MainSpace → B.NuisanceSpace)
    (C gammaMain gammaNuisance : ℝ)
    (hC : 0 ≤ C) (hMain : 0 < gammaMain)
    (hNuisance : 0 < gammaNuisance)
    (hRnorm : ∀ u, ‖R u‖ ≤ C * ‖u‖)
    (hRegression : B.IsNuisanceRegression xi R)
    (hSchur : ∀ u,
      gammaMain * ‖u‖ ^ 2 ≤
        inner ℝ (B.schurResidual R u)
          (B.covarianceOperator xi (B.schurResidual R u)))
    (hGamma : ∀ z,
      gammaNuisance * ‖z‖ ^ 2 ≤
        inner ℝ (B.nuisanceEmbed z)
          (B.covarianceOperator xi (B.nuisanceEmbed z))) :
    B.vectorFamily.HasCovarianceGap
      (min gammaMain gammaNuisance / (3 + 2 * C ^ 2)) xi := by
  intro x
  -- Every full parameter has a unique coordinate split; define it directly.
  let u : B.MainSpace :=
    (EuclideanSpace.equiv (MainCoord B.GaugeIndex) ℝ).symm (fun c =>
      match c with
      | .gauge j => x (MomentCoord.gauge j)
      | .slow => x MomentCoord.slow)
  let z : B.NuisanceSpace :=
    (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).symm (fun c =>
      match c with
      | .physical => x MomentCoord.physical
      | .head h => x (MomentCoord.head h))
  have hx : x = B.combine u z := by
    apply (EuclideanSpace.equiv B.Coord ℝ).injective
    funext c
    cases c <;> simp [u, z]
  rw [hx, B.covarianceForm_schur_decomposition xi R hRegression]
  have hminMain : min gammaMain gammaNuisance * ‖u‖ ^ 2 ≤
      inner ℝ (B.schurResidual R u)
        (B.covarianceOperator xi (B.schurResidual R u)) :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg ‖u‖)).trans
      (hSchur u)
  have hminNuisance : min gammaMain gammaNuisance * ‖z + R u‖ ^ 2 ≤
      inner ℝ (B.nuisanceEmbed (z + R u))
        (B.covarianceOperator xi (B.nuisanceEmbed (z + R u))) :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _)
      (sq_nonneg ‖z + R u‖)).trans (hGamma (z + R u))
  have hsum : min gammaMain gammaNuisance *
      (‖u‖ ^ 2 + ‖z + R u‖ ^ 2) ≤
      inner ℝ (B.schurResidual R u)
          (B.covarianceOperator xi (B.schurResidual R u)) +
        inner ℝ (B.nuisanceEmbed (z + R u))
          (B.covarianceOperator xi (B.nuisanceEmbed (z + R u))) := by
    nlinarith
  have hden : 0 < 3 + 2 * C ^ 2 := by positivity
  have hmin : 0 < min gammaMain gammaNuisance :=
    lt_min hMain hNuisance
  have hnorm := B.combine_norm_sq_le_schur_coordinates R C hC hRnorm u z
  apply le_trans ?_ hsum
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).2
  have hmul := mul_le_mul_of_nonneg_left hnorm (le_of_lt hmin)
  nlinarith

/-- Block-inverse form with the nuisance regression constructed internally
as `Γ_{xi,n}^{-1}B_{xi,n}`. -/
theorem hasCovarianceGap_of_exactSchur [Nonempty Head]
    (xi : B.ParamSpace) (gammaMain gammaNuisance : ℝ)
    (hMain : 0 < gammaMain) (hNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z,
      gammaNuisance * ‖z‖ ^ 2 ≤
        inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hSchur : ∀ u,
      gammaMain * ‖u‖ ^ 2 ≤
        inner ℝ
          (B.schurResidual
            (B.exactNuisanceRegression xi hNuisance hGamma) u)
          (B.covarianceOperator xi
            (B.schurResidual
              (B.exactNuisanceRegression xi hNuisance hGamma) u))) :
    B.vectorFamily.HasCovarianceGap
      (min gammaMain gammaNuisance /
        (3 + 2 *
          (‖B.crossCovarianceOperator xi‖ / gammaNuisance) ^ 2)) xi := by
  apply B.hasCovarianceGap_of_schur xi
    (B.exactNuisanceRegression xi hNuisance hGamma)
    (‖B.crossCovarianceOperator xi‖ / gammaNuisance)
    gammaMain gammaNuisance
    (div_nonneg (norm_nonneg _) (le_of_lt hNuisance))
    hMain hNuisance
    (B.exactNuisanceRegression_norm_le xi hNuisance hGamma)
    (B.exactNuisanceRegression_isRegression xi hNuisance hGamma)
    hSchur
  intro z
  simpa only [nuisanceCovarianceOperator,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right] using hGamma z

/-! ## Exact target and moment correspondence -/

/-- The unscaled endpoint requested by a band residual vector `Delta`.
The slow component is `alpha^T Delta`; the physical and head components
are zero. -/
def unscaledTarget (Delta : Band → ℝ) : B.Coord → ℝ
  | .gauge j => Delta j.1 - B.lowRatio j * Delta B.lowBand
  | .physical => 0
  | .head _ => 0
  | .slow => ∑ j, B.bandCenter j * Delta j

/-- Endpoint in the anisotropically scaled Euclidean coordinates. -/
def targetVector (Delta : Band → ℝ) : B.ParamSpace :=
  (EuclideanSpace.equiv B.Coord ℝ).symm
    (fun c => B.unscaledTarget Delta c / B.coordScale c)

@[simp]
theorem targetVector_apply (Delta : Band → ℝ) (c : B.Coord) :
    (B.targetVector Delta : B.Coord → ℝ) c =
      B.unscaledTarget Delta c / B.coordScale c := by
  rfl

/-- The normalized target `tau=(L/q) target` displayed in Proposition 8.7. -/
def normalizedTarget [Nonempty Head] (Delta : Band → ℝ) : B.ParamSpace :=
  (B.L / B.q) • B.targetVector Delta

@[simp]
theorem normalizedTarget_apply [Nonempty Head]
    (Delta : Band → ℝ) (c : B.Coord) :
    (B.normalizedTarget Delta : B.Coord → ℝ) c =
      (B.L / B.q) *
        (B.unscaledTarget Delta c / B.coordScale c) := by
  rfl

/-- Raw active moment of a paper statistic. -/
def paperMoment [Nonempty Head]
    (F : B.sampleData.Sample → ℝ) (xi : B.ParamSpace) : ℝ :=
  B.vectorFamily.scalarFamily.moment F xi

theorem paperMoment_sub [Nonempty Head]
    (F G : B.sampleData.Sample → ℝ) (xi : B.ParamSpace) :
    B.paperMoment (fun m => F m - G m) xi =
      B.paperMoment F xi - B.paperMoment G xi := by
  unfold paperMoment FiniteExponentialFamily.moment
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem paperMoment_add [Nonempty Head]
    (F G : B.sampleData.Sample → ℝ) (xi : B.ParamSpace) :
    B.paperMoment (fun m => F m + G m) xi =
      B.paperMoment F xi + B.paperMoment G xi := by
  unfold paperMoment FiniteExponentialFamily.moment
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem paperMoment_const_mul [Nonempty Head]
    (a : ℝ) (F : B.sampleData.Sample → ℝ) (xi : B.ParamSpace) :
    B.paperMoment (fun m => a * F m) xi =
      a * B.paperMoment F xi := by
  unfold paperMoment FiniteExponentialFamily.moment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem paperMoment_fintype_sum [Nonempty Head]
    {I : Type*} [Fintype I]
    (F : I → B.sampleData.Sample → ℝ) (xi : B.ParamSpace) :
    B.paperMoment (fun m => ∑ i, F i m) xi =
      ∑ i, B.paperMoment (F i) xi := by
  unfold paperMoment FiniteExponentialFamily.moment
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem paperMoment_const [Nonempty Head]
    (a : ℝ) (xi : B.ParamSpace) :
    B.paperMoment (fun _ => a) xi = B.q * a := by
  unfold paperMoment FiniteExponentialFamily.moment
  rw [← Finset.sum_mul,
    B.vectorFamily.scalarFamily.activeWeight_sum]
  change B.vectorFamily.baseMass * a = B.q * a
  rw [B.vectorFamily_baseMass]

/-- A coordinate of the vector moment is exactly the corresponding raw paper
moment divided by its anisotropic coordinate scale. -/
theorem paperMoment_eq_coordScale_mul_vectorMoment [Nonempty Head]
    (xi : B.ParamSpace) (c : B.Coord) :
    B.paperMoment (fun m => B.rawStatistic m c) xi =
      B.coordScale c * B.vectorFamily.vectorMoment xi c := by
  change (∑ m, B.vectorFamily.scalarFamily.activeWeight xi m *
      B.rawStatistic m c) =
    B.coordScale c *
      (∑ m, B.vectorFamily.scalarFamily.activeWeight xi m •
        B.statistic m) c
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, B.statistic_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  field_simp [ne_of_gt (B.coordScale_pos c)]

/-- Exact coordinate-by-coordinate meaning of the vector endpoint.  No
asymptotic estimate is used here. -/
theorem endpoint_iff_paperMoments [Nonempty Head]
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace) :
    B.vectorFamily.vectorMoment xi1 =
        B.vectorFamily.vectorMoment xi0 + B.targetVector Delta ↔
      ∀ c : B.Coord,
        B.paperMoment (fun m => B.rawStatistic m c) xi1 =
          B.paperMoment (fun m => B.rawStatistic m c) xi0 +
            B.unscaledTarget Delta c := by
  constructor
  · intro h c
    have hc := congrArg
      (fun z : B.ParamSpace => (z : B.Coord → ℝ) c) h
    change B.vectorFamily.vectorMoment xi1 c =
      B.vectorFamily.vectorMoment xi0 c + B.targetVector Delta c at hc
    rw [B.targetVector_apply] at hc
    rw [B.paperMoment_eq_coordScale_mul_vectorMoment,
      B.paperMoment_eq_coordScale_mul_vectorMoment]
    rw [hc]
    field_simp [ne_of_gt (B.coordScale_pos c)]
  · intro h
    apply (EuclideanSpace.equiv B.Coord ℝ).injective
    funext c
    have hc := h c
    rw [B.paperMoment_eq_coordScale_mul_vectorMoment,
      B.paperMoment_eq_coordScale_mul_vectorMoment] at hc
    change B.vectorFamily.vectorMoment xi1 c =
      B.vectorFamily.vectorMoment xi0 c +
        B.unscaledTarget Delta c / B.coordScale c
    apply (mul_left_cancel₀ (ne_of_gt (B.coordScale_pos c)))
    rw [mul_add]
    field_simp [ne_of_gt (B.coordScale_pos c)] at hc ⊢
    exact hc

theorem endpoint_preserves_physical [Nonempty Head]
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (h : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta) :
    B.paperMoment B.physicalScore xi1 =
      B.paperMoment B.physicalScore xi0 := by
  have hc := (B.endpoint_iff_paperMoments Delta xi0 xi1).mp h
    (MomentCoord.physical : B.Coord)
  simpa [rawStatistic, unscaledTarget] using hc

theorem endpoint_preserves_head [Nonempty Head]
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (h : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta)
    (head : B.HeadIndex) :
    B.paperMoment (B.centeredHeadScore head) xi1 =
      B.paperMoment (B.centeredHeadScore head) xi0 := by
  have hc := (B.endpoint_iff_paperMoments Delta xi0 xi1).mp h
    (MomentCoord.head head : B.Coord)
  simpa [rawStatistic, unscaledTarget] using hc

theorem endpoint_preserves_headIndicator [Nonempty Head]
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (h : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta)
    (head : B.HeadIndex) :
    B.paperMoment (B.headIndicator head.1) xi1 =
      B.paperMoment (B.headIndicator head.1) xi0 := by
  have hc := B.endpoint_preserves_head Delta xi0 xi1 h head
  have hexpand (xi : B.ParamSpace) :
      B.paperMoment (B.centeredHeadScore head) xi =
        B.paperMoment (B.headIndicator head.1) xi -
          B.q * B.headBaselineMass head.1 := by
    calc
      B.paperMoment (B.centeredHeadScore head) xi =
          B.paperMoment (fun m => B.headIndicator head.1 m -
            B.headBaselineMass head.1) xi := rfl
      _ = B.paperMoment (B.headIndicator head.1) xi -
          B.paperMoment (fun _ => B.headBaselineMass head.1) xi :=
        B.paperMoment_sub _ _ xi
      _ = B.paperMoment (B.headIndicator head.1) xi -
          B.q * B.headBaselineMass head.1 := by
        rw [B.paperMoment_const]
  rw [hexpand, hexpand] at hc
  linarith

/-- Any statistic depending only on the tagged head pattern. -/
def headFunctionScore (phi : Head → ℝ)
    (m : B.sampleData.Sample) : ℝ :=
  phi (B.sampleData.cellOf m).1

theorem headFunctionScore_decomposition (phi : Head → ℝ)
    (m : B.sampleData.Sample) :
    B.headFunctionScore phi m = phi B.referenceHead +
      ∑ h : B.HeadIndex,
        (phi h.1 - phi B.referenceHead) * B.headIndicator h.1 m := by
  let tag := (B.sampleData.cellOf m).1
  by_cases htag : tag = B.referenceHead
  · have hvalue : B.headFunctionScore phi m = phi B.referenceHead := by
      change phi tag = phi B.referenceHead
      rw [htag]
    rw [hvalue]
    suffices (∑ h : B.HeadIndex,
        (phi h.1 - phi B.referenceHead) * B.headIndicator h.1 m) = 0 by
      rw [this, add_zero]
    apply Finset.sum_eq_zero
    intro h hh
    have hne : tag ≠ h.1 := by
      intro heq
      exact h.2 (heq.symm.trans htag)
    change (phi h.1 - phi B.referenceHead) *
      (if tag = h.1 then 1 else 0) = 0
    rw [if_neg hne, mul_zero]
  · let htagIndex : B.HeadIndex := ⟨tag, htag⟩
    change phi tag = phi B.referenceHead +
      ∑ h : B.HeadIndex,
        (phi h.1 - phi B.referenceHead) * B.headIndicator h.1 m
    have hsum : (∑ h : B.HeadIndex,
        (phi h.1 - phi B.referenceHead) * B.headIndicator h.1 m) =
        phi tag - phi B.referenceHead := by
      rw [Finset.sum_eq_single htagIndex]
      · change (phi tag - phi B.referenceHead) *
          (if tag = tag then 1 else 0) = phi tag - phi B.referenceHead
        simp
      · intro h hh hne
        have hval : h.1 ≠ tag := by
          intro heq
          exact hne (Subtype.ext heq)
        change (phi h.1 - phi B.referenceHead) *
          (if tag = h.1 then 1 else 0) = 0
        rw [if_neg hval.symm, mul_zero]
      · intro hnot
        exact (hnot (Finset.mem_univ htagIndex)).elim
    rw [hsum]
    ring

theorem endpoint_preserves_headFunction [Nonempty Head]
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (h : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta)
    (phi : Head → ℝ) :
    B.paperMoment (B.headFunctionScore phi) xi1 =
      B.paperMoment (B.headFunctionScore phi) xi0 := by
  have hexpand (xi : B.ParamSpace) :
      B.paperMoment (B.headFunctionScore phi) xi =
        B.q * phi B.referenceHead +
          ∑ k : B.HeadIndex,
            (phi k.1 - phi B.referenceHead) *
              B.paperMoment (B.headIndicator k.1) xi := by
    calc
      B.paperMoment (B.headFunctionScore phi) xi =
          B.paperMoment (fun m => phi B.referenceHead +
            ∑ k : B.HeadIndex,
              (phi k.1 - phi B.referenceHead) *
                B.headIndicator k.1 m) xi := by
            congr 1
            funext m
            exact B.headFunctionScore_decomposition phi m
      _ = B.paperMoment (fun _ => phi B.referenceHead) xi +
          B.paperMoment (fun m => ∑ k : B.HeadIndex,
            (phi k.1 - phi B.referenceHead) *
              B.headIndicator k.1 m) xi := by
            have := B.paperMoment_sub
            unfold paperMoment FiniteExponentialFamily.moment
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro m hm
            ring
      _ = B.q * phi B.referenceHead +
          ∑ k : B.HeadIndex,
            (phi k.1 - phi B.referenceHead) *
              B.paperMoment (B.headIndicator k.1) xi := by
            rw [B.paperMoment_const, B.paperMoment_fintype_sum]
            apply congrArg₂ (· + ·) rfl
            apply Finset.sum_congr rfl
            intro k hk
            exact B.paperMoment_const_mul
              (phi k.1 - phi B.referenceHead)
              (B.headIndicator k.1) xi
  rw [hexpand, hexpand]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro k hk
  rw [B.endpoint_preserves_headIndicator Delta xi0 xi1 h k]

/-- Exact finite logarithmic compatibility required by the paper: on the
guarded smooth sample, the medium-prime logarithmic score is an affine
combination of the ordinary physical logarithm and the tagged head pattern.
The later arithmetic factorization theorem must produce this identity. -/
def HasPrimeLogCompatibility : Prop :=
  ∃ a : ℝ, ∃ phi : Head → ℝ, ∀ m : B.sampleData.Sample,
    B.primeLogScore m =
      a * B.physicalScore m + B.headFunctionScore phi m

/-- The abstract compatibility interface is discharged by the exact
arithmetic condition used in the paper: every prime at most `W` occurs in
the head pattern, while every remaining prime factor of a structured smooth
sample lies in the actual band `W < p ≤ floor(y)`.

This theorem closes a previously explicit finite-algebra interface.  It does
not address the analytic existence or asymptotic size of the structured
cells. -/
theorem hasPrimeLogCompatibility_of_exactHeadPrimes
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W) :
    B.HasPrimeLogCompatibility := by
  let logY : ℝ := Real.log (ArithmeticModel.y B.sampleData.n)
  refine ⟨1 / logY,
    fun h => (Real.log (B.sampleData.n : ℝ) - B.headLogScore h) / logY,
    ?_⟩
  intro m
  have hsplit := B.log_value_eq_headLogScore_add_bandFactorization hhead m
  have hband :
      (∑ p ∈ ArithmeticModel.primeBand
          B.sampleData.n B.sampleData.W,
        ((B.sampleData.value m).factorization p : ℝ) *
          Real.log (p : ℝ)) =
        Real.log (B.sampleData.value m : ℝ) -
          B.headLogScore (B.sampleData.cellOf m).1 := by
    linarith
  have hvalue : (B.sampleData.value m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (B.sampleData.value_pos m))
  have hn : (B.sampleData.n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt B.n_gt_one))
  have hlogY : logY ≠ 0 := by
    exact ne_of_gt (by simpa [logY] using B.log_y_pos)
  rw [B.primeLogScore_eq_bandFactorization_div m, hband]
  unfold physicalScore headFunctionScore
  rw [Real.log_div hvalue hn]
  dsimp only [logY]
  field_simp
  ring

theorem endpoint_preserves_primeLogScore_of_compatibility [Nonempty Head]
    (hcompat : B.HasPrimeLogCompatibility)
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (h : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta) :
    B.paperMoment B.primeLogScore xi1 =
      B.paperMoment B.primeLogScore xi0 := by
  obtain ⟨a, phi, hpoint⟩ := hcompat
  have hexpand (xi : B.ParamSpace) :
      B.paperMoment B.primeLogScore xi =
        a * B.paperMoment B.physicalScore xi +
          B.paperMoment (B.headFunctionScore phi) xi := by
    calc
      B.paperMoment B.primeLogScore xi =
          B.paperMoment (fun m =>
            a * B.physicalScore m + B.headFunctionScore phi m) xi := by
            congr 1
            funext m
            exact hpoint m
      _ = B.paperMoment (fun m => a * B.physicalScore m) xi +
          B.paperMoment (B.headFunctionScore phi) xi :=
        B.paperMoment_add _ _ xi
      _ = a * B.paperMoment B.physicalScore xi +
          B.paperMoment (B.headFunctionScore phi) xi := by
        rw [B.paperMoment_const_mul]
  rw [hexpand, hexpand,
    B.endpoint_preserves_physical Delta xi0 xi1 h,
    B.endpoint_preserves_headFunction Delta xi0 xi1 h phi]

theorem endpoint_gauge_moment [Nonempty Head]
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (h : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta)
    (j : B.GaugeIndex) :
    B.paperMoment (B.gaugeScore j) xi1 =
      B.paperMoment (B.gaugeScore j) xi0 +
        Delta j.1 - B.lowRatio j * Delta B.lowBand := by
  have hc := (B.endpoint_iff_paperMoments Delta xi0 xi1).mp h
    (MomentCoord.gauge j : B.Coord)
  simpa [rawStatistic, unscaledTarget, add_sub_assoc] using hc

theorem endpoint_slow_moment [Nonempty Head]
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (h : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta) :
    B.paperMoment B.slowScore xi1 =
      B.paperMoment B.slowScore xi0 +
        ∑ j, B.bandCenter j * Delta j := by
  have hc := (B.endpoint_iff_paperMoments Delta xi0 xi1).mp h
    (MomentCoord.slow : B.Coord)
  simpa [rawStatistic, unscaledTarget] using hc

theorem paperMoment_gaugeScore [Nonempty Head]
    (j : B.GaugeIndex) (xi : B.ParamSpace) :
    B.paperMoment (B.gaugeScore j) xi =
      B.paperMoment (B.bandScore j.1) xi -
        B.lowRatio j * B.paperMoment (B.bandScore B.lowBand) xi := by
  calc
    B.paperMoment (B.gaugeScore j) xi =
        B.paperMoment (fun m => B.bandScore j.1 m -
          B.lowRatio j * B.bandScore B.lowBand m) xi := rfl
    _ = B.paperMoment (B.bandScore j.1) xi -
        B.paperMoment (fun m =>
          B.lowRatio j * B.bandScore B.lowBand m) xi :=
      B.paperMoment_sub _ _ xi
    _ = B.paperMoment (B.bandScore j.1) xi -
        B.lowRatio j * B.paperMoment (B.bandScore B.lowBand) xi := by
      rw [B.paperMoment_const_mul]

theorem paperMoment_slow_decomposition [Nonempty Head]
    (xi : B.ParamSpace) :
    B.paperMoment B.slowScore xi =
      (∑ j : Band,
        B.bandCenter j * B.paperMoment (B.bandScore j) xi) -
        B.paperMoment B.primeLogScore xi := by
  calc
    B.paperMoment B.slowScore xi =
        B.paperMoment (fun m =>
          (∑ j : Band, B.bandCenter j * B.bandScore j m) -
            B.primeLogScore m) xi := by
      congr 1
      funext m
      exact B.slowScore_eq_bandScore_sub_primeLogScore m
    _ = B.paperMoment (fun m =>
          ∑ j : Band, B.bandCenter j * B.bandScore j m) xi -
        B.paperMoment B.primeLogScore xi :=
      B.paperMoment_sub _ _ xi
    _ = (∑ j : Band,
          B.bandCenter j * B.paperMoment (B.bandScore j) xi) -
        B.paperMoment B.primeLogScore xi := by
      rw [B.paperMoment_fintype_sum]
      apply congrArg₂ (· - ·)
      · apply Finset.sum_congr rfl
        intro j hj
        exact B.paperMoment_const_mul (B.bandCenter j)
          (B.bandScore j) xi
      · rfl

/-- The one-dimensional band vector invisible to the concrete gauge
coordinates. -/
def bandKernelVector (j : Band) : ℝ :=
  if h : j = B.lowBand then 1 else B.lowRatio ⟨j, h⟩

def bandRecoveryCoefficient : ℝ :=
  ∑ j : Band, B.bandCenter j * B.bandKernelVector j

theorem lowRatio_pos (j : B.GaugeIndex) : 0 < B.lowRatio j := by
  exact div_pos
    (mul_pos (B.harmonicMass_pos j.1) (B.bandCenter_pos j.1))
    (mul_pos (B.harmonicMass_pos B.lowBand)
      (B.bandCenter_pos B.lowBand))

theorem bandKernelVector_pos (j : Band) : 0 < B.bandKernelVector j := by
  by_cases hj : j = B.lowBand
  · simp [bandKernelVector, hj]
  · simpa only [bandKernelVector, hj, dite_false] using
      B.lowRatio_pos (⟨j, hj⟩ : B.GaugeIndex)

theorem bandRecoveryCoefficient_pos : 0 < B.bandRecoveryCoefficient := by
  unfold bandRecoveryCoefficient
  exact Finset.sum_pos
    (fun j hj => mul_pos (B.bandCenter_pos j) (B.bandKernelVector_pos j))
    ⟨B.lowBand, Finset.mem_univ _⟩

def bandMomentError [Nonempty Head]
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace) (j : Band) : ℝ :=
  B.paperMoment (B.bandScore j) xi1 -
    B.paperMoment (B.bandScore j) xi0 - Delta j

/-- Gauge moments plus the compensated moment recover every individual
band moment once the medium-prime logarithmic score is preserved.  The
single nonvanishing coefficient is exposed explicitly, so this converse is
not hidden inside a coordinate assertion. -/
theorem endpoint_recovers_all_bandMoments [Nonempty Head]
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (hendpoint : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta)
    (hlog : B.paperMoment B.primeLogScore xi1 =
      B.paperMoment B.primeLogScore xi0) :
    ∀ j : Band,
      B.paperMoment (B.bandScore j) xi1 =
        B.paperMoment (B.bandScore j) xi0 + Delta j := by
  let e : Band → ℝ := B.bandMomentError Delta xi0 xi1
  have hrelation : ∀ j, e j = B.bandKernelVector j * e B.lowBand := by
    intro j
    by_cases hj : j = B.lowBand
    · subst j
      simp [bandKernelVector]
    · let jg : B.GaugeIndex := ⟨j, hj⟩
      have hg := B.endpoint_gauge_moment Delta xi0 xi1 hendpoint jg
      rw [B.paperMoment_gaugeScore, B.paperMoment_gaugeScore] at hg
      simp only [e, bandMomentError, bandKernelVector, hj, dite_false]
      linarith
  have hsum : ∑ j : Band, B.bandCenter j * e j = 0 := by
    have hs := B.endpoint_slow_moment Delta xi0 xi1 hendpoint
    rw [B.paperMoment_slow_decomposition,
      B.paperMoment_slow_decomposition, hlog] at hs
    simp only [e, bandMomentError]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    linarith
  have hfactor : B.bandRecoveryCoefficient * e B.lowBand = 0 := by
    rw [bandRecoveryCoefficient, Finset.sum_mul]
    calc
      (∑ j : Band,
          B.bandCenter j * B.bandKernelVector j * e B.lowBand) =
          ∑ j : Band, B.bandCenter j * e j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hrelation j]
            ring
      _ = 0 := hsum
  have helow : e B.lowBand = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left
      (ne_of_gt B.bandRecoveryCoefficient_pos)
  intro j
  have hej : e j = 0 := by rw [hrelation j, helow, mul_zero]
  simp only [e, bandMomentError] at hej
  linarith

theorem endpoint_recovers_all_bandMoments_of_compatibility [Nonempty Head]
    (hcompat : B.HasPrimeLogCompatibility)
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (hendpoint : B.vectorFamily.vectorMoment xi1 =
      B.vectorFamily.vectorMoment xi0 + B.targetVector Delta) :
    ∀ j : Band,
      B.paperMoment (B.bandScore j) xi1 =
        B.paperMoment (B.bandScore j) xi0 + Delta j := by
  exact B.endpoint_recovers_all_bandMoments Delta xi0 xi1 hendpoint
    (B.endpoint_preserves_primeLogScore_of_compatibility
      hcompat Delta xi0 xi1 hendpoint)

theorem rawEndpoint_recovers_all_bandMoments [Nonempty Head]
    (hcompat : B.HasPrimeLogCompatibility)
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace)
    (hraw : ∀ c : B.Coord,
      B.paperMoment (fun m => B.rawStatistic m c) xi1 =
        B.paperMoment (fun m => B.rawStatistic m c) xi0 +
          B.unscaledTarget Delta c) :
    ∀ j : Band,
      B.paperMoment (B.bandScore j) xi1 =
        B.paperMoment (B.bandScore j) xi0 + Delta j := by
  exact B.endpoint_recovers_all_bandMoments_of_compatibility hcompat
    Delta xi0 xi1 ((B.endpoint_iff_paperMoments Delta xi0 xi1).mpr hraw)

/-- Exact squared norm of the anisotropically scaled target. -/
theorem targetVector_norm_sq (Delta : Band → ℝ) :
    ‖B.targetVector Delta‖ ^ 2 =
      ∑ c : B.Coord,
        (B.unscaledTarget Delta c / B.coordScale c) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, B.targetVector_apply]

theorem normalizedTarget_norm [Nonempty Head] (Delta : Band → ℝ) :
    ‖B.normalizedTarget Delta‖ =
      (B.L / B.q) * ‖B.targetVector Delta‖ := by
  rw [normalizedTarget, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos B.L_pos B.q_pos)]

/-- The generic ODE radius condition is exactly the normalized target radius
used in the paper. -/
theorem target_radius_identity [Nonempty Head]
    (Delta : Band → ℝ) (gamma : ℝ) (hgamma : 0 < gamma) :
    ‖B.targetVector Delta‖ /
        ((B.q / B.L) * gamma) =
      ‖B.normalizedTarget Delta‖ / gamma := by
  rw [B.normalizedTarget_norm]
  field_simp [ne_of_gt B.q_pos, ne_of_gt B.L_pos, ne_of_gt hgamma]

theorem normalizedTarget_slow_apply [Nonempty Head]
    (Delta : Band → ℝ) :
    B.normalizedTarget Delta (MomentCoord.slow : B.Coord) =
      (B.L / B.q) *
        ((∑ j, B.bandCenter j * Delta j) / B.w) := by
  rfl

/-! ## Actual baseline mixture and coarse cells -/

/-- At parameter zero the normalized tilted law is exactly the explicit
baseline law `z_m^0/q_n`. -/
theorem probabilityMass_zero [Nonempty Head]
    (m : B.sampleData.Sample) :
    B.vectorFamily.probabilityMass 0 m =
      B.baseline.baseWeight m / B.q := by
  simp only [VectorExponentialFamily.probabilityMass,
    VectorExponentialFamily.scalarFamily,
    FiniteExponentialFamily.probabilityMass,
    FiniteExponentialFamily.unnormalizedWeight,
    FiniteExponentialFamily.partition, vectorFamily,
    map_zero, zero_div, Real.exp_zero, mul_one]
  rw [B.baseline.baseWeight_sum]
  rfl

/-- The canonical coarse mixture obtained from the actual fine baseline and
the literal cell tag. -/
def coarseBaseline [Nonempty Head] : PatternMixture (Cell Head) B.ParamSpace :=
  CanonicalCoarseMixture.coarse
    (B.vectorFamily.tiltedMixture 0) B.sampleData.cellOf

theorem coarseBaseline_weight [Nonempty Head] (c : Cell Head) :
    B.coarseBaseline.weight c = B.baseline.normalizedCellMass c := by
  change CanonicalCoarseMixture.fiberWeight
      (B.vectorFamily.tiltedMixture 0) B.sampleData.cellOf c =
    B.baseline.normalizedCellMass c
  simp only [CanonicalCoarseMixture.fiberWeight,
    VectorExponentialFamily.tiltedMixture]
  have hp (m : B.sampleData.Sample) :
      B.vectorFamily.probabilityMass 0 m =
        B.baseline.baseWeight m / B.q :=
    B.probabilityMass_zero m
  simp_rw [hp]
  rw [Finset.sum_filter]
  rw [Fintype.sum_sigma]
  simp only [StructuredSampleData.cellOf]
  rw [Finset.sum_eq_single c]
  · simp only [BaselineAllocation.baseWeight,
      BaselineAllocation.normalizedCellMass,
      StructuredSampleData.cellOf, if_true, q]
    rw [← Finset.sum_div]
    have hcard : (Fintype.card (B.sampleData.SampleAt c) : ℝ) ≠ 0 := by
      exact_mod_cast
        (Nat.ne_of_gt (B.sampleData.sampleAt_card_pos c))
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hcard]
  · intro c' _ hne
    simp [hne]
  · intro hc
    exact (hc (Finset.mem_univ c)).elim

theorem coarseBaseline_weight_pos [Nonempty Head] (c : Cell Head) :
    0 < B.coarseBaseline.weight c := by
  rw [B.coarseBaseline_weight c]
  exact B.baseline.normalizedCellMass_pos c

/-- The conditional means and the law-of-total-variance connection are
generated from the actual cells, rather than postulated. -/
def coarseBaselineCertificate [Nonempty Head] :
    PatternMixture.CoarseMeanCertificate
      (B.vectorFamily.tiltedMixture 0) B.coarseBaseline :=
  CanonicalCoarseMixture.certificate
    (B.vectorFamily.tiltedMixture 0) B.sampleData.cellOf (by
      intro c
      simpa only [CanonicalCoarseMixture.fiberWeight,
        ← CanonicalCoarseMixture.coarse_weight] using
        B.coarseBaseline_weight_pos c)

/-- The smallest actual finite baseline cell mass.  This is defined from the
finite weights themselves, so it exists without assuming convergence of the
mixture as `n` varies. -/
def finiteCellLowerBound [Nonempty Head] : ℝ :=
  let weights := (Finset.univ : Finset (Cell Head)).image
    B.baseline.normalizedCellMass
  weights.min' (by
    exact Finset.image_nonempty.mpr Finset.univ_nonempty)

theorem finiteCellLowerBound_pos [Nonempty Head] :
    0 < B.finiteCellLowerBound := by
  let weights := (Finset.univ : Finset (Cell Head)).image
    B.baseline.normalizedCellMass
  have hmem : B.finiteCellLowerBound ∈ weights := by
    exact Finset.min'_mem weights _
  obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hmem
  rw [← hc]
  exact B.baseline.normalizedCellMass_pos c

theorem finiteCellLowerBound_le [Nonempty Head] (c : Cell Head) :
    B.finiteCellLowerBound ≤ B.coarseBaseline.weight c := by
  rw [B.coarseBaseline_weight c]
  let weights := (Finset.univ : Finset (Cell Head)).image
    B.baseline.normalizedCellMass
  exact Finset.min'_le weights _
    (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩)

/-- The actual nuisance statistic `Z=(R,H_1^circ,...,H_e^circ)`. -/
def nuisanceStatistic [Nonempty Head]
    (m : B.sampleData.Sample) : B.NuisanceSpace :=
  (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).symm
    (fun c => match c with
      | .physical => B.physicalScore m
      | .head h => B.centeredHeadScore h m)

@[simp]
theorem nuisanceStatistic_physical [Nonempty Head]
    (m : B.sampleData.Sample) :
    B.nuisanceStatistic m (NuisanceCoord.physical) = B.physicalScore m := by
  rfl

@[simp]
theorem nuisanceStatistic_head [Nonempty Head]
    (m : B.sampleData.Sample) (h : B.HeadIndex) :
    B.nuisanceStatistic m (NuisanceCoord.head h) =
      B.centeredHeadScore h m := by
  rfl

/-- The full statistic is exactly the orthogonal coordinate recombination
of the main and nuisance blocks. -/
theorem statistic_eq_combine [Nonempty Head]
    (m : B.sampleData.Sample) :
    B.statistic m = B.combine (B.mainStatistic m) (B.nuisanceStatistic m) := by
  apply (EuclideanSpace.equiv B.Coord ℝ).injective
  funext c
  cases c with
  | gauge j => simp
  | slow => simp
  | physical => simp [statistic_apply, rawStatistic, coordScale]
  | head h => simp [statistic_apply, rawStatistic, coordScale]

/-- Fine baseline law on the actual nuisance patterns. -/
def nuisanceFineBaseline [Nonempty Head] :
    PatternMixture B.sampleData.Sample B.NuisanceSpace where
  weight := B.vectorFamily.probabilityMass 0
  weight_nonneg := B.vectorFamily.scalarFamily.probabilityMass_nonneg 0
  weight_sum := B.vectorFamily.scalarFamily.probabilityMass_sum 0
  pattern := B.nuisanceStatistic

/-- Nuisance marginal at an arbitrary point of the actual tilt path. -/
def nuisanceFineAt [Nonempty Head] (xi : B.ParamSpace) :
    PatternMixture B.sampleData.Sample B.NuisanceSpace where
  weight := B.vectorFamily.probabilityMass xi
  weight_nonneg := B.vectorFamily.scalarFamily.probabilityMass_nonneg xi
  weight_sum := B.vectorFamily.scalarFamily.probabilityMass_sum xi
  pattern := B.nuisanceStatistic

@[simp] theorem nuisanceFineAt_zero [Nonempty Head] :
    B.nuisanceFineAt 0 = B.nuisanceFineBaseline := rfl

/-- The abstract block `Γ_{xi,n}` is exactly the covariance of the literal
physical/head statistic under the actual tilted finite law. -/
theorem nuisanceCovarianceOperator_quadratic [Nonempty Head]
    (xi : B.ParamSpace) (z : B.NuisanceSpace) :
    inner ℝ z (B.nuisanceCovarianceOperator xi z) =
      (B.nuisanceFineAt xi).covarianceForm z := by
  have hinter : inner ℝ z (B.nuisanceCovarianceOperator xi z) =
      inner ℝ (B.nuisanceEmbed z)
        (B.covarianceOperator xi (B.nuisanceEmbed z)) := by
    simpa only [nuisanceCovarianceOperator,
      ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.adjoint_inner_right B.nuisanceEmbeddingCLM z
        (B.covarianceOperator xi (B.nuisanceEmbeddingCLM z)))
  rw [hinter, B.inner_covarianceOperator_self]
  unfold PatternMixture.covarianceForm PatternMixture.probability
    FiniteProbability.covariance FiniteProbability.expect
  simp only [VectorExponentialFamily.tiltedMixture, nuisanceFineAt]
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    rw [show B.vectorFamily.statistic m = B.statistic m by rfl,
      B.statistic_eq_combine m,
      B.inner_nuisanceEmbed_combine z (B.nuisanceStatistic m)
        (B.mainStatistic m)]
  · apply congrArg₂ (· * ·)
    · apply Finset.sum_congr rfl
      intro m hm
      rw [show B.vectorFamily.statistic m = B.statistic m by rfl,
        B.statistic_eq_combine m,
        B.inner_nuisanceEmbed_combine z (B.nuisanceStatistic m)
          (B.mainStatistic m)]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [show B.vectorFamily.statistic m = B.statistic m by rfl,
        B.statistic_eq_combine m,
        B.inner_nuisanceEmbed_combine z (B.nuisanceStatistic m)
          (B.mainStatistic m)]

theorem inner_nuisanceEmbed_covarianceOperator [Nonempty Head]
    (xi : B.ParamSpace) (z : B.NuisanceSpace) :
    inner ℝ (B.nuisanceEmbed z)
        (B.covarianceOperator xi (B.nuisanceEmbed z)) =
      inner ℝ z (B.nuisanceCovarianceOperator xi z) := by
  simpa only [nuisanceCovarianceOperator,
    ContinuousLinearMap.comp_apply] using
    (ContinuousLinearMap.adjoint_inner_right B.nuisanceEmbeddingCLM z
      (B.covarianceOperator xi (B.nuisanceEmbeddingCLM z))).symm

theorem nuisanceFineBaseline_weight_pos [Nonempty Head]
    (m : B.sampleData.Sample) : 0 < B.nuisanceFineBaseline.weight m := by
  change 0 < B.vectorFamily.probabilityMass 0 m
  rw [B.probabilityMass_zero m]
  exact div_pos (B.baseline.baseWeight_pos m) B.q_pos

/-- Canonical nuisance cell mixture. -/
def nuisanceCoarseBaseline [Nonempty Head] :
    PatternMixture (Cell Head) B.NuisanceSpace :=
  CanonicalCoarseMixture.coarse B.nuisanceFineBaseline B.sampleData.cellOf

theorem nuisanceCoarseBaseline_weight [Nonempty Head] (c : Cell Head) :
    B.nuisanceCoarseBaseline.weight c =
      B.baseline.normalizedCellMass c := by
  change CanonicalCoarseMixture.fiberWeight
      B.nuisanceFineBaseline B.sampleData.cellOf c =
    B.baseline.normalizedCellMass c
  change CanonicalCoarseMixture.fiberWeight
      (B.vectorFamily.tiltedMixture 0) B.sampleData.cellOf c =
    B.baseline.normalizedCellMass c
  exact B.coarseBaseline_weight c

theorem nuisanceCoarseBaseline_weight_pos [Nonempty Head]
    (c : Cell Head) : 0 < B.nuisanceCoarseBaseline.weight c := by
  rw [B.nuisanceCoarseBaseline_weight c]
  exact B.baseline.normalizedCellMass_pos c

/-- Every centered-head coordinate is literally constant on a tagged
head/physical cell, so its conditional mean is the same constant. -/
theorem nuisanceCoarseBaseline_pattern_head [Nonempty Head]
    (c : Cell Head) (h : B.HeadIndex) :
    B.nuisanceCoarseBaseline.pattern c (NuisanceCoord.head h) =
      (if c.1 = h.1 then 1 else 0) - B.headBaselineMass h.1 := by
  change ((CanonicalCoarseMixture.fiberWeight
      B.nuisanceFineBaseline B.sampleData.cellOf c)⁻¹ •
    CanonicalCoarseMixture.fiberMoment
      B.nuisanceFineBaseline B.sampleData.cellOf c)
        (NuisanceCoord.head h) = _
  simp only [Pi.smul_apply, smul_eq_mul,
    CanonicalCoarseMixture.fiberMoment, WithLp.ofLp_sum,
    WithLp.ofLp_smul, Finset.sum_apply, nuisanceFineBaseline,
    nuisanceStatistic_head]
  let K : ℝ := (if c.1 = h.1 then 1 else 0) -
    B.headBaselineMass h.1
  have hconstant : ∀ m : B.sampleData.Sample,
      m ∈ (Finset.univ : Finset B.sampleData.Sample) →
      B.sampleData.cellOf m = c → B.centeredHeadScore h m = K := by
    intro m hm hmc
    simp only [centeredHeadScore, headIndicator, K, hmc]
  have hsum :
      (∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
          B.sampleData.cellOf m = c,
        B.nuisanceFineBaseline.weight m * B.centeredHeadScore h m) =
        CanonicalCoarseMixture.fiberWeight
          B.nuisanceFineBaseline B.sampleData.cellOf c * K := by
    rw [CanonicalCoarseMixture.fiberWeight, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    rw [hconstant m (Finset.mem_univ m) (Finset.mem_filter.mp hm).2]
  change (CanonicalCoarseMixture.fiberWeight
      B.nuisanceFineBaseline B.sampleData.cellOf c)⁻¹ *
      (∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
        B.sampleData.cellOf m = c,
        B.nuisanceFineBaseline.weight m * B.centeredHeadScore h m) = _
  rw [hsum]
  have hweight : CanonicalCoarseMixture.fiberWeight
      B.nuisanceFineBaseline B.sampleData.cellOf c ≠ 0 := by
    exact ne_of_gt (by
      simpa only [← CanonicalCoarseMixture.coarse_weight] using
        B.nuisanceCoarseBaseline_weight_pos c)
  dsimp only [K]
  field_simp

/-- The physical coordinate of an actual coarse conditional mean. -/
def cellPhysicalMean [Nonempty Head] (c : Cell Head) : ℝ :=
  B.nuisanceCoarseBaseline.pattern c NuisanceCoord.physical

/-- Changing only the physical sign of a cell changes its nuisance pattern
only along the physical coordinate. -/
theorem nuisancePattern_sameHead_sub [Nonempty Head] (h : Head) :
    B.nuisanceCoarseBaseline.pattern (h, .plus) -
        B.nuisanceCoarseBaseline.pattern (h, .minus) =
      (B.cellPhysicalMean (h, .plus) -
        B.cellPhysicalMean (h, .minus)) •
          EuclideanSpace.single NuisanceCoord.physical (1 : ℝ) := by
  apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
  funext c
  change (B.nuisanceCoarseBaseline.pattern (h, .plus) -
      B.nuisanceCoarseBaseline.pattern (h, .minus)) c =
    ((B.cellPhysicalMean (h, .plus) -
      B.cellPhysicalMean (h, .minus)) •
        EuclideanSpace.single NuisanceCoord.physical (1 : ℝ)) c
  cases c with
  | physical => simp [cellPhysicalMean]
  | head k =>
      rw [WithLp.ofLp_sub, Pi.sub_apply,
        WithLp.ofLp_smul, Pi.smul_apply,
        B.nuisanceCoarseBaseline_pattern_head,
        B.nuisanceCoarseBaseline_pattern_head]
      simp [EuclideanSpace.single_apply]

/-- Changing the head tag at a fixed physical sign changes the head block
by exactly one coordinate, plus a possibly nonzero physical displacement. -/
theorem nuisancePattern_head_sub [Nonempty Head]
    (h : B.HeadIndex) (sigma : PhysicalSign) :
    B.nuisanceCoarseBaseline.pattern (h.1, sigma) -
        B.nuisanceCoarseBaseline.pattern (B.referenceHead, sigma) =
      (B.cellPhysicalMean (h.1, sigma) -
        B.cellPhysicalMean (B.referenceHead, sigma)) •
          EuclideanSpace.single NuisanceCoord.physical (1 : ℝ) +
        EuclideanSpace.single (NuisanceCoord.head h) (1 : ℝ) := by
  apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
  funext c
  change (B.nuisanceCoarseBaseline.pattern (h.1, sigma) -
      B.nuisanceCoarseBaseline.pattern (B.referenceHead, sigma)) c =
    (((B.cellPhysicalMean (h.1, sigma) -
        B.cellPhysicalMean (B.referenceHead, sigma)) •
          EuclideanSpace.single NuisanceCoord.physical (1 : ℝ) +
      EuclideanSpace.single (NuisanceCoord.head h) (1 : ℝ)) :
        B.NuisanceSpace) c
  cases c with
  | physical => simp [cellPhysicalMean]
  | head k =>
      rw [WithLp.ofLp_sub, Pi.sub_apply,
        WithLp.ofLp_add, Pi.add_apply,
        WithLp.ofLp_smul, Pi.smul_apply,
        B.nuisanceCoarseBaseline_pattern_head,
        B.nuisanceCoarseBaseline_pattern_head]
      simp only [smul_eq_mul,
        EuclideanSpace.single_apply]
      by_cases hhk : h = k
      · subst k
        have href : B.referenceHead ≠ h.1 := Ne.symm h.2
        simp [href]
      · have hval : h.1 ≠ k.1 := by
          intro heq
          exact hhk (Subtype.ext heq)
        have href : B.referenceHead ≠ k.1 := Ne.symm k.2
        have hkh : k ≠ h := Ne.symm hhk
        simp [hval, href, hkh]

/-- The actual finite nuisance mixture affinely spans as soon as the two
physical conditional means are separated for each head.  This is a
checkable statement about the displayed finite cells, not a covariance-gap
assumption and not a limiting-mixture argument. -/
theorem exists_nuisanceAffineCertificate_of_meanSeparation [Nonempty Head]
    (hsep : ∀ h : Head,
      B.cellPhysicalMean (h, .minus) <
        B.cellPhysicalMean (h, .plus)) :
    Nonempty (PatternMixture.AffineSpanningCertificate
      B.nuisanceCoarseBaseline) := by
  apply PatternMixture.exists_affineSpanningCertificate_of_kernel
    B.nuisanceCoarseBaseline
  intro x hkernel
  let h0 : Head := Classical.choice (inferInstance : Nonempty Head)
  have hphysicalPair := hkernel (h0, .plus) (h0, .minus)
  rw [B.nuisancePattern_sameHead_sub h0, inner_smul_right,
    EuclideanSpace.inner_single_right] at hphysicalPair
  simp only [RCLike.conj_to_real] at hphysicalPair
  have hmean_ne : B.cellPhysicalMean (h0, .plus) -
      B.cellPhysicalMean (h0, .minus) ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt (hsep h0))
  have hxphysical : x NuisanceCoord.physical = 0 := by
    simpa using (mul_eq_zero.mp hphysicalPair).resolve_left hmean_ne
  apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
  funext c
  change x c = 0
  cases c with
  | physical => exact hxphysical
  | head h =>
      have hheadPair := hkernel (h.1, .minus) (B.referenceHead, .minus)
      rw [B.nuisancePattern_head_sub h .minus, inner_add_right,
        inner_smul_right, EuclideanSpace.inner_single_right,
        EuclideanSpace.inner_single_right] at hheadPair
      simp only [RCLike.conj_to_real, hxphysical, mul_zero,
        zero_add] at hheadPair
      simpa using hheadPair

/-- Exact nuisance conditional-mean certificate. -/
def nuisanceCoarseCertificate [Nonempty Head] :
    PatternMixture.CoarseMeanCertificate
      B.nuisanceFineBaseline B.nuisanceCoarseBaseline :=
  CanonicalCoarseMixture.certificate
    B.nuisanceFineBaseline B.sampleData.cellOf (by
      intro c
      simpa only [CanonicalCoarseMixture.fiberWeight,
        ← CanonicalCoarseMixture.coarse_weight] using
        B.nuisanceCoarseBaseline_weight_pos c)

/-- First-moment identity for the physical coordinate in one actual cell. -/
theorem cellPhysicalMean_mul_weight [Nonempty Head] (c : Cell Head) :
    B.nuisanceCoarseBaseline.weight c * B.cellPhysicalMean c =
      ∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
          B.sampleData.cellOf m = c,
        B.nuisanceFineBaseline.weight m * B.physicalScore m := by
  have h := B.nuisanceCoarseCertificate.cell_firstMoment c
    (EuclideanSpace.single NuisanceCoord.physical (1 : ℝ))
  change (∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
      B.sampleData.cellOf m = c,
      B.nuisanceFineBaseline.weight m *
        inner ℝ (EuclideanSpace.single NuisanceCoord.physical (1 : ℝ))
          (B.nuisanceStatistic m)) =
    B.nuisanceCoarseBaseline.weight c *
      inner ℝ (EuclideanSpace.single NuisanceCoord.physical (1 : ℝ))
        (B.nuisanceCoarseBaseline.pattern c) at h
  simpa only [EuclideanSpace.inner_single_left, RCLike.conj_to_real,
    one_mul, B.nuisanceStatistic_physical, cellPhysicalMean] using h.symm

theorem cellPhysicalMean_minus_le_separator [Nonempty Head] (h : Head) :
    B.cellPhysicalMean (h, .minus) ≤ B.physicalSeparator := by
  let c : Cell Head := (h, .minus)
  let s := (Finset.univ : Finset B.sampleData.Sample).filter
    (fun m => B.sampleData.cellOf m = c)
  have hterm : ∀ m ∈ s,
      B.nuisanceFineBaseline.weight m * B.physicalScore m ≤
        B.nuisanceFineBaseline.weight m * B.physicalSeparator := by
    intro m hm
    have hcell : B.sampleData.cellOf m = c :=
      (Finset.mem_filter.mp hm).2
    have hsign : (B.sampleData.cellOf m).2 = .minus := by
      rw [hcell]
    exact mul_le_mul_of_nonneg_left
      (le_of_lt (B.physicalScore_lt_separator_of_minus m hsign))
      (B.nuisanceFineBaseline.weight_nonneg m)
  have hmassRaw := B.nuisanceCoarseCertificate.cell_mass c
  change (∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
      B.sampleData.cellOf m = c, B.nuisanceFineBaseline.weight m) =
    B.nuisanceCoarseBaseline.weight c at hmassRaw
  have hmass : (∑ m ∈ s, B.nuisanceFineBaseline.weight m) =
      B.nuisanceCoarseBaseline.weight c := by
    simpa only [s] using hmassRaw
  have hsum :
      (∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
          B.sampleData.cellOf m = c,
        B.nuisanceFineBaseline.weight m * B.physicalScore m) ≤
      B.nuisanceCoarseBaseline.weight c * B.physicalSeparator := by
    calc
      (∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
          B.sampleData.cellOf m = c,
        B.nuisanceFineBaseline.weight m * B.physicalScore m)
          ≤ ∑ m ∈ s,
              B.nuisanceFineBaseline.weight m *
                B.physicalSeparator := by
            exact Finset.sum_le_sum fun m hm => hterm m hm
      _ = (∑ m ∈ s, B.nuisanceFineBaseline.weight m) *
            B.physicalSeparator := by rw [Finset.sum_mul]
      _ = B.nuisanceCoarseBaseline.weight c *
            B.physicalSeparator := by
          rw [hmass]
  rw [← B.cellPhysicalMean_mul_weight c] at hsum
  exact (mul_le_mul_iff_right₀
    (B.nuisanceCoarseBaseline_weight_pos c)).mp hsum

theorem separator_lt_cellPhysicalMean_plus [Nonempty Head] (h : Head) :
    B.physicalSeparator < B.cellPhysicalMean (h, .plus) := by
  let c : Cell Head := (h, .plus)
  let s := (Finset.univ : Finset B.sampleData.Sample).filter
    (fun m => B.sampleData.cellOf m = c)
  have hs : s.Nonempty := by
    obtain ⟨v, hv⟩ := B.sampleData.cell_nonempty c
    let m : B.sampleData.Sample := ⟨c, ⟨v, hv⟩⟩
    refine ⟨m, ?_⟩
    simp [s, m, StructuredSampleData.cellOf]
  have hterm : ∀ m ∈ s,
      B.nuisanceFineBaseline.weight m * B.physicalSeparator <
        B.nuisanceFineBaseline.weight m * B.physicalScore m := by
    intro m hm
    have hcell : B.sampleData.cellOf m = c :=
      (Finset.mem_filter.mp hm).2
    have hsign : (B.sampleData.cellOf m).2 = .plus := by
      rw [hcell]
    exact mul_lt_mul_of_pos_left
      (B.separator_lt_physicalScore_of_plus m hsign)
      (B.nuisanceFineBaseline_weight_pos m)
  have hmassRaw := B.nuisanceCoarseCertificate.cell_mass c
  change (∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
      B.sampleData.cellOf m = c, B.nuisanceFineBaseline.weight m) =
    B.nuisanceCoarseBaseline.weight c at hmassRaw
  have hmass : (∑ m ∈ s, B.nuisanceFineBaseline.weight m) =
      B.nuisanceCoarseBaseline.weight c := by
    simpa only [s] using hmassRaw
  have hsum : B.nuisanceCoarseBaseline.weight c * B.physicalSeparator <
      ∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
          B.sampleData.cellOf m = c,
        B.nuisanceFineBaseline.weight m * B.physicalScore m := by
    calc
      B.nuisanceCoarseBaseline.weight c * B.physicalSeparator
          = (∑ m ∈ s, B.nuisanceFineBaseline.weight m) *
              B.physicalSeparator := by
            rw [hmass]
      _ = ∑ m ∈ s,
              B.nuisanceFineBaseline.weight m *
                B.physicalSeparator := by rw [Finset.sum_mul]
      _ < ∑ m ∈ s,
              B.nuisanceFineBaseline.weight m *
                B.physicalScore m :=
            Finset.sum_lt_sum_of_nonempty hs hterm
  rw [← B.cellPhysicalMean_mul_weight c] at hsum
  exact (mul_lt_mul_iff_right₀
    (B.nuisanceCoarseBaseline_weight_pos c)).mp hsum

/-- The interval separation built into `StructuredSampleData` supplies the
mean-separation hypothesis, hence an actual finite affine-spanning
certificate for `Γ_{0,n}` with no subsequence or limiting mixture. -/
theorem exists_nuisanceAffineCertificate_from_cells [Nonempty Head] :
    Nonempty (PatternMixture.AffineSpanningCertificate
      B.nuisanceCoarseBaseline) := by
  apply B.exists_nuisanceAffineCertificate_of_meanSeparation
  intro h
  exact (B.cellPhysicalMean_minus_le_separator h).trans_lt
    (B.separator_lt_cellPhysicalMean_plus h)

/-- A certificate chosen from the explicit finite cell geometry.  Its
existence was proved above; it is not supplied as extra bridge data. -/
def nuisanceAffineCertificate [Nonempty Head] :
    PatternMixture.AffineSpanningCertificate B.nuisanceCoarseBaseline :=
  Classical.choice B.exists_nuisanceAffineCertificate_from_cells

/-- The positive finite-`n` nuisance gap obtained from the actual minimum
cell mass and the actual affine reconstruction. -/
def nuisanceBaselineGap [Nonempty Head] : ℝ :=
  PatternMixture.baselineGap B.finiteCellLowerBound
    B.nuisanceAffineCertificate

theorem nuisanceBaselineGap_pos [Nonempty Head] :
    0 < B.nuisanceBaselineGap := by
  exact PatternMixture.baselineGap_pos B.finiteCellLowerBound
    B.finiteCellLowerBound_pos B.nuisanceAffineCertificate

/-- Uniformity in a fixed paper instance is obtained directly from the
actual `Γ_{0,n}`: all cells have at least the finite lower bound and the
coarse conditional means affinely span.  No limiting covariance `Γ₀` is
introduced. -/
theorem nuisanceFineBaseline_covariance_gap [Nonempty Head]
    (x : B.NuisanceSpace) :
    B.nuisanceBaselineGap * ‖x‖ ^ 2 ≤
      B.nuisanceFineBaseline.covarianceForm x := by
  exact PatternMixture.covarianceForm_uniform_gap_of_coarsening
    B.nuisanceFineBaseline B.nuisanceCoarseBaseline
    B.nuisanceCoarseCertificate B.nuisanceAffineCertificate
    B.finiteCellLowerBound B.finiteCellLowerBound_pos
    (fun c => B.finiteCellLowerBound_le c) x

theorem nuisanceCovarianceOperator_zero_gap [Nonempty Head]
    (z : B.NuisanceSpace) :
    B.nuisanceBaselineGap * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator 0 z) := by
  rw [B.nuisanceCovarianceOperator_quadratic, B.nuisanceFineAt_zero]
  exact B.nuisanceFineBaseline_covariance_gap z

/-- A concrete finite diameter for the nuisance patterns. -/
def nuisanceStatisticDiameter [Nonempty Head] : ℝ :=
  ∑ i : B.sampleData.Sample, ∑ j : B.sampleData.Sample,
    ‖B.nuisanceStatistic i - B.nuisanceStatistic j‖

theorem nuisanceStatistic_distance_le_diameter [Nonempty Head]
    (i j : B.sampleData.Sample) :
    ‖B.nuisanceStatistic i - B.nuisanceStatistic j‖ ≤
      B.nuisanceStatisticDiameter := by
  calc
    ‖B.nuisanceStatistic i - B.nuisanceStatistic j‖
        ≤ ∑ k : B.sampleData.Sample,
            ‖B.nuisanceStatistic i - B.nuisanceStatistic k‖ := by
          exact Finset.single_le_sum
            (fun k _ => norm_nonneg
              (B.nuisanceStatistic i - B.nuisanceStatistic k))
            (Finset.mem_univ j)
    _ ≤ ∑ h : B.sampleData.Sample, ∑ k : B.sampleData.Sample,
          ‖B.nuisanceStatistic h - B.nuisanceStatistic k‖ := by
          exact Finset.single_le_sum
            (fun h _ => Finset.sum_nonneg fun k _ =>
              norm_nonneg (B.nuisanceStatistic h - B.nuisanceStatistic k))
            (Finset.mem_univ i)

theorem nuisanceFineBaseline_weightL1_eq [Nonempty Head]
    (xi : B.ParamSpace) :
    B.nuisanceFineBaseline.weightL1Distance
        (B.vectorFamily.probabilityMass xi) =
      (B.vectorFamily.tiltedMixture 0).weightL1Distance
        (B.vectorFamily.probabilityMass xi) := rfl

/-- A finite tilt preserves half of the actual `Γ_{0,n}` gap.  The only
smallness condition is an explicit inequality involving the already
defined `ℓ¹` distance and actual nuisance diameter. -/
theorem nuisanceCovarianceOperator_half_gap_of_l1 [Nonempty Head]
    (xi : B.ParamSpace) (epsilon : ℝ)
    (hl1 : (B.vectorFamily.tiltedMixture 0).weightL1Distance
      (B.vectorFamily.probabilityMass xi) ≤ epsilon)
    (hsmall : epsilon * B.nuisanceStatisticDiameter ^ 2 ≤
      B.nuisanceBaselineGap / 2) (z : B.NuisanceSpace) :
    (B.nuisanceBaselineGap / 2) * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z) := by
  rw [B.nuisanceCovarianceOperator_quadratic]
  have h := PatternMixture.actualCovarianceForm_reweight_half_gap_of_coarsening
    B.nuisanceFineBaseline B.nuisanceCoarseBaseline
    B.nuisanceCoarseCertificate B.nuisanceAffineCertificate
    B.finiteCellLowerBound B.finiteCellLowerBound_pos
    (fun c => B.finiteCellLowerBound_le c)
    (B.vectorFamily.probabilityMass xi)
    (B.vectorFamily.scalarFamily.probabilityMass_nonneg xi)
    (B.vectorFamily.scalarFamily.probabilityMass_sum xi)
    B.nuisanceStatisticDiameter epsilon
    (fun i j => B.nuisanceStatistic_distance_le_diameter i j)
    (by simpa only [B.nuisanceFineBaseline_weightL1_eq] using hl1)
    hsmall z
  simpa only [nuisanceBaselineGap, nuisanceFineAt, nuisanceFineBaseline,
    PatternMixture.reweight] using h

/-- Canonical proof term for the finite nuisance half-gap, used to define
the actual Schur regression without adding it to `BridgeData`. -/
def nuisanceHalfGapProof [Nonempty Head]
    (xi : B.ParamSpace) (epsilon : ℝ)
    (hl1 : (B.vectorFamily.tiltedMixture 0).weightL1Distance
      (B.vectorFamily.probabilityMass xi) ≤ epsilon)
    (hsmall : epsilon * B.nuisanceStatisticDiameter ^ 2 ≤
      B.nuisanceBaselineGap / 2) :
    ∀ z, (B.nuisanceBaselineGap / 2) * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z) :=
  fun z => B.nuisanceCovarianceOperator_half_gap_of_l1
    xi epsilon hl1 hsmall z

/-- Actual regression after the explicit finite `ℓ¹` check. -/
def l1NuisanceRegression [Nonempty Head]
    (xi : B.ParamSpace) (epsilon : ℝ)
    (hl1 : (B.vectorFamily.tiltedMixture 0).weightL1Distance
      (B.vectorFamily.probabilityMass xi) ≤ epsilon)
    (hsmall : epsilon * B.nuisanceStatisticDiameter ^ 2 ≤
      B.nuisanceBaselineGap / 2) : B.MainSpace → B.NuisanceSpace :=
  B.exactNuisanceRegression xi
    (div_pos B.nuisanceBaselineGap_pos (by norm_num))
    (B.nuisanceHalfGapProof xi epsilon hl1 hsmall)

/-- Full actual covariance gap after the nuisance block and regression have
been constructed from cells and the only remaining Lemma 8.6 input is the
sharp-relative main/slow Schur lower bound. -/
theorem hasCovarianceGap_of_exactSchur_and_l1 [Nonempty Head]
    (xi : B.ParamSpace) (gammaMain epsilon : ℝ)
    (hMain : 0 < gammaMain)
    (hl1 : (B.vectorFamily.tiltedMixture 0).weightL1Distance
      (B.vectorFamily.probabilityMass xi) ≤ epsilon)
    (hsmall : epsilon * B.nuisanceStatisticDiameter ^ 2 ≤
      B.nuisanceBaselineGap / 2)
    (hSchur : ∀ u,
      gammaMain * ‖u‖ ^ 2 ≤
        inner ℝ (B.schurResidual
          (B.l1NuisanceRegression xi epsilon hl1 hsmall) u)
          (B.covarianceOperator xi (B.schurResidual
            (B.l1NuisanceRegression xi epsilon hl1 hsmall) u))) :
    B.vectorFamily.HasCovarianceGap
      (min gammaMain (B.nuisanceBaselineGap / 2) /
        (3 + 2 * (‖B.crossCovarianceOperator xi‖ /
          (B.nuisanceBaselineGap / 2)) ^ 2)) xi := by
  let hNuisance : 0 < B.nuisanceBaselineGap / 2 :=
    div_pos B.nuisanceBaselineGap_pos (by norm_num)
  let hGamma := B.nuisanceHalfGapProof xi epsilon hl1 hsmall
  have hreg : B.l1NuisanceRegression xi epsilon hl1 hsmall =
      B.exactNuisanceRegression xi hNuisance hGamma := by
    rfl
  apply B.hasCovarianceGap_of_exactSchur xi gammaMain
    (B.nuisanceBaselineGap / 2) hMain hNuisance hGamma
  simpa only [← hreg] using hSchur

/-- Fully transferred pointwise gap: the inputs are a proved reference
coercivity and a sharp relative comparison for the actual Schur operator,
not an assumed covariance gap. -/
theorem hasCovarianceGap_of_referenceComparison_and_l1 [Nonempty Head]
    (xi : B.ParamSpace) (epsilon : ℝ)
    (hl1 : (B.vectorFamily.tiltedMixture 0).weightL1Distance
      (B.vectorFamily.probabilityMass xi) ≤ epsilon)
    (hsmall : epsilon * B.nuisanceStatisticDiameter ^ 2 ≤
      B.nuisanceBaselineGap / 2)
    (reference : B.MainSpace →L[ℝ] B.MainSpace)
    (gammaReference delta : ℝ)
    (hdelta : delta < gammaReference)
    (href : ∀ u, gammaReference * ‖u‖ ^ 2 ≤
      inner ℝ u (reference u))
    (hcomparison : ∀ u,
      |inner ℝ u
        ((B.exactSchurCovarianceOperator xi
          (div_pos B.nuisanceBaselineGap_pos (by norm_num))
          (B.nuisanceHalfGapProof xi epsilon hl1 hsmall) - reference) u)| ≤
        delta * ‖u‖ ^ 2) :
    B.vectorFamily.HasCovarianceGap
      (min (gammaReference - delta) (B.nuisanceBaselineGap / 2) /
        (3 + 2 * (‖B.crossCovarianceOperator xi‖ /
          (B.nuisanceBaselineGap / 2)) ^ 2)) xi := by
  apply B.hasCovarianceGap_of_exactSchur_and_l1 xi
    (gammaReference - delta) epsilon (sub_pos.mpr hdelta)
    hl1 hsmall
  intro u
  let hNuisance : 0 < B.nuisanceBaselineGap / 2 :=
    div_pos B.nuisanceBaselineGap_pos (by norm_num)
  let hGamma := B.nuisanceHalfGapProof xi epsilon hl1 hsmall
  have hreg : B.l1NuisanceRegression xi epsilon hl1 hsmall =
      B.exactNuisanceRegression xi hNuisance hGamma := by rfl
  rw [hreg]
  exact B.exactSchur_gap_of_referenceComparison xi hNuisance hGamma
    reference gammaReference delta href hcomparison u

/-- Lemma 8.6 interface after the finite nuisance block has been discharged
from the actual cells.  The remaining substantive input is precisely the
main/slow Schur residual estimate; the full covariance gap is a conclusion. -/
theorem hasCovarianceGap_of_schur_and_l1 [Nonempty Head]
    (xi : B.ParamSpace) (R : B.MainSpace → B.NuisanceSpace)
    (C gammaMain epsilon : ℝ)
    (hC : 0 ≤ C) (hMain : 0 < gammaMain)
    (hRnorm : ∀ u, ‖R u‖ ≤ C * ‖u‖)
    (hRegression : B.IsNuisanceRegression xi R)
    (hSchur : ∀ u,
      gammaMain * ‖u‖ ^ 2 ≤
        inner ℝ (B.schurResidual R u)
          (B.covarianceOperator xi (B.schurResidual R u)))
    (hl1 : (B.vectorFamily.tiltedMixture 0).weightL1Distance
      (B.vectorFamily.probabilityMass xi) ≤ epsilon)
    (hsmall : epsilon * B.nuisanceStatisticDiameter ^ 2 ≤
      B.nuisanceBaselineGap / 2) :
    B.vectorFamily.HasCovarianceGap
      (min gammaMain (B.nuisanceBaselineGap / 2) /
        (3 + 2 * C ^ 2)) xi := by
  apply B.hasCovarianceGap_of_schur xi R C gammaMain
    (B.nuisanceBaselineGap / 2) hC hMain
    (div_pos B.nuisanceBaselineGap_pos (by norm_num)) hRnorm
    hRegression hSchur
  intro z
  rw [B.inner_nuisanceEmbed_covarianceOperator]
  exact B.nuisanceCovarianceOperator_half_gap_of_l1 xi epsilon
    hl1 hsmall z

/-- Affine spanning is reduced to the literal finite pattern-difference
kernel check.  This is the non-covariance certificate used by the finite
nuisance-gap theorem. -/
theorem exists_nuisanceAffineCertificate [Nonempty Head]
    (hkernel : ∀ x : B.NuisanceSpace,
      (∀ i j, inner ℝ x
        (B.nuisanceCoarseBaseline.pattern i -
          B.nuisanceCoarseBaseline.pattern j) = 0) → x = 0) :
    Nonempty (PatternMixture.AffineSpanningCertificate
      B.nuisanceCoarseBaseline) :=
  PatternMixture.exists_affineSpanningCertificate_of_kernel
    B.nuisanceCoarseBaseline hkernel

/-! ## Explicit finite diameter -/

/-- A concrete (not optimized) finite diameter certificate. -/
def statisticDiameter [Nonempty Head] : ℝ :=
  ∑ i : B.sampleData.Sample, ∑ j : B.sampleData.Sample,
    ‖B.statistic i - B.statistic j‖

theorem statisticDiameter_nonneg [Nonempty Head] :
    0 ≤ B.statisticDiameter :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem statistic_distance_le_diameter [Nonempty Head]
    (i j : B.sampleData.Sample) :
    ‖B.statistic i - B.statistic j‖ ≤ B.statisticDiameter := by
  calc
    ‖B.statistic i - B.statistic j‖
        ≤ ∑ k : B.sampleData.Sample, ‖B.statistic i - B.statistic k‖ := by
          exact Finset.single_le_sum
            (fun k _ => norm_nonneg (B.statistic i - B.statistic k))
            (Finset.mem_univ j)
    _ ≤ ∑ h : B.sampleData.Sample, ∑ k : B.sampleData.Sample,
          ‖B.statistic h - B.statistic k‖ := by
          exact Finset.single_le_sum
            (fun h _ => Finset.sum_nonneg fun k _ =>
              norm_nonneg (B.statistic h - B.statistic k))
            (Finset.mem_univ i)

/-- The bilinear pair-difference formula for a finite probability law.  We
record it here because it gives a completely explicit, tilt-independent
operator-norm bound for every covariance block used in Proposition 8.7. -/
theorem finiteProbability_covariance_pairDifference
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (F G : Omega → ℝ) :
    mu.covariance F G =
      (1 / 2 : ℝ) * ∑ i, ∑ j,
        mu.mass i * mu.mass j * (F i - F j) * (G i - G j) := by
  have hA : (∑ i, ∑ j,
      mu.mass i * mu.mass j * (F i * G i)) =
      ∑ i, mu.mass i * (F i * G i) := by
    calc
      (∑ i, ∑ j, mu.mass i * mu.mass j * (F i * G i)) =
          ∑ i, (mu.mass i * (F i * G i)) * ∑ j, mu.mass j := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ i, mu.mass i * (F i * G i) := by
        rw [mu.mass_sum]
        simp
  have hB : (∑ i, ∑ j,
      mu.mass i * mu.mass j * (F j * G j)) =
      ∑ j, mu.mass j * (F j * G j) := by
    rw [Finset.sum_comm]
    calc
      (∑ j, ∑ i, mu.mass i * mu.mass j * (F j * G j)) =
          ∑ j, (mu.mass j * (F j * G j)) * ∑ i, mu.mass i := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = ∑ j, mu.mass j * (F j * G j) := by
        rw [mu.mass_sum]
        simp
  have hC : (∑ i, ∑ j,
      mu.mass i * mu.mass j * (F i * G j)) =
      (∑ i, mu.mass i * F i) * (∑ j, mu.mass j * G j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hD : (∑ i, ∑ j,
      mu.mass i * mu.mass j * (F j * G i)) =
      (∑ i, mu.mass i * F i) * (∑ j, mu.mass j * G j) := by
    rw [Finset.sum_comm, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [FiniteProbability.covariance, FiniteProbability.expect]
  calc
    (∑ i, mu.mass i * (F i * G i)) -
        (∑ i, mu.mass i * F i) * (∑ i, mu.mass i * G i) =
      (1 / 2 : ℝ) *
        ((∑ i, mu.mass i * (F i * G i)) +
          (∑ j, mu.mass j * (F j * G j)) -
          (∑ i, mu.mass i * F i) * (∑ j, mu.mass j * G j) -
          (∑ i, mu.mass i * F i) * (∑ j, mu.mass j * G j)) := by ring
    _ = (1 / 2 : ℝ) *
        ((∑ i, ∑ j, mu.mass i * mu.mass j * (F i * G i)) +
          (∑ i, ∑ j, mu.mass i * mu.mass j * (F j * G j)) -
          (∑ i, ∑ j, mu.mass i * mu.mass j * (F i * G j)) -
          (∑ i, ∑ j, mu.mass i * mu.mass j * (F j * G i))) := by
      rw [hA, hB, hC, hD]
    _ = (1 / 2 : ℝ) * ∑ i, ∑ j,
        mu.mass i * mu.mass j * (F i - F j) * (G i - G j) := by
      congr 1
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The covariance operator as a finite positive sum of rank-one pair
differences.  This is an identity for the actual tilted law at every finite
`n`, with no compactness or asymptotic input. -/
def covariancePairOperator [Nonempty Head]
    (xi : B.ParamSpace) : B.ParamSpace →L[ℝ] B.ParamSpace :=
  (1 / 2 : ℝ) • ∑ i : B.sampleData.Sample,
    ∑ j : B.sampleData.Sample,
      (B.vectorFamily.probabilityMass xi i *
        B.vectorFamily.probabilityMass xi j) •
          InnerProductSpace.rankOne ℝ
            (B.statistic i - B.statistic j)
            (B.statistic i - B.statistic j)

theorem covarianceOperator_eq_covariancePairOperator [Nonempty Head]
    (xi : B.ParamSpace) :
    B.covarianceOperator xi = B.covariancePairOperator xi := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℝ
  intro x
  rw [B.inner_covarianceOperator]
  unfold FiniteExponentialFamily.covariance
  rw [finiteProbability_covariance_pairDifference]
  simp only [FiniteExponentialFamily.tiltedProbability]
  unfold covariancePairOperator VectorExponentialFamily.probabilityMass
  rw [ContinuousLinearMap.smul_apply, inner_smul_right]
  congr 1
  simp_rw [ContinuousLinearMap.sum_apply, inner_sum]
  simp only [ContinuousLinearMap.smul_apply, inner_smul_right,
    InnerProductSpace.rankOne_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_sub_left, inner_sub_right,
    real_inner_comm (B.statistic i) y,
    real_inner_comm (B.statistic j) y]
  ring

/-- Canonical, finite and tilt-independent cross-block bound.  It is crude
but completely explicit: every covariance block is dominated by one half
of the squared diameter of the actual statistic vectors. -/
def canonicalCrossBound [Nonempty Head] : ℝ :=
  B.statisticDiameter ^ 2 / 2

theorem canonicalCrossBound_nonneg [Nonempty Head] :
    0 ≤ B.canonicalCrossBound := by
  exact div_nonneg (sq_nonneg _) (by norm_num)

theorem covarianceOperator_norm_le_canonicalCrossBound [Nonempty Head]
    (xi : B.ParamSpace) :
    ‖B.covarianceOperator xi‖ ≤ B.canonicalCrossBound := by
  rw [B.covarianceOperator_eq_covariancePairOperator]
  unfold covariancePairOperator canonicalCrossBound
  calc
    ‖(1 / 2 : ℝ) • ∑ i : B.sampleData.Sample,
        ∑ j : B.sampleData.Sample,
          (B.vectorFamily.probabilityMass xi i *
            B.vectorFamily.probabilityMass xi j) •
              InnerProductSpace.rankOne ℝ
                (B.statistic i - B.statistic j)
                (B.statistic i - B.statistic j)‖
        ≤ (1 / 2 : ℝ) * ∑ i : B.sampleData.Sample,
            ∑ j : B.sampleData.Sample,
              (B.vectorFamily.probabilityMass xi i *
                B.vectorFamily.probabilityMass xi j) *
                ‖B.statistic i - B.statistic j‖ ^ 2 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          calc
            ‖∑ i : B.sampleData.Sample,
                ∑ j : B.sampleData.Sample,
                  (B.vectorFamily.probabilityMass xi i *
                    B.vectorFamily.probabilityMass xi j) •
                      InnerProductSpace.rankOne ℝ
                        (B.statistic i - B.statistic j)
                        (B.statistic i - B.statistic j)‖
                ≤ ∑ i : B.sampleData.Sample,
                    ‖∑ j : B.sampleData.Sample,
                      (B.vectorFamily.probabilityMass xi i *
                        B.vectorFamily.probabilityMass xi j) •
                          InnerProductSpace.rankOne ℝ
                            (B.statistic i - B.statistic j)
                            (B.statistic i - B.statistic j)‖ :=
                  norm_sum_le _ _
            _ ≤ ∑ i : B.sampleData.Sample,
                ∑ j : B.sampleData.Sample,
                  ‖(B.vectorFamily.probabilityMass xi i *
                    B.vectorFamily.probabilityMass xi j) •
                      InnerProductSpace.rankOne ℝ
                        (B.statistic i - B.statistic j)
                        (B.statistic i - B.statistic j)‖ := by
                  apply Finset.sum_le_sum
                  intro i _
                  exact norm_sum_le _ _
            _ = ∑ i : B.sampleData.Sample,
                ∑ j : B.sampleData.Sample,
                  (B.vectorFamily.probabilityMass xi i *
                    B.vectorFamily.probabilityMass xi j) *
                    ‖B.statistic i - B.statistic j‖ ^ 2 := by
                  apply Finset.sum_congr rfl
                  intro i _
                  apply Finset.sum_congr rfl
                  intro j _
                  have hi : 0 ≤ B.vectorFamily.probabilityMass xi i :=
                    B.vectorFamily.scalarFamily.probabilityMass_nonneg xi i
                  have hj : 0 ≤ B.vectorFamily.probabilityMass xi j :=
                    B.vectorFamily.scalarFamily.probabilityMass_nonneg xi j
                  rw [norm_smul, InnerProductSpace.norm_rankOne,
                    Real.norm_eq_abs,
                    abs_of_nonneg (mul_nonneg hi hj)]
                  ring
    _ ≤ (1 / 2 : ℝ) * ∑ i : B.sampleData.Sample,
          ∑ j : B.sampleData.Sample,
            (B.vectorFamily.probabilityMass xi i *
              B.vectorFamily.probabilityMass xi j) *
              B.statisticDiameter ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _)
            (B.statistic_distance_le_diameter i j) 2)
          (mul_nonneg
            (B.vectorFamily.scalarFamily.probabilityMass_nonneg xi i)
            (B.vectorFamily.scalarFamily.probabilityMass_nonneg xi j))
    _ = B.statisticDiameter ^ 2 / 2 := by
      have hsum : ∑ i : B.sampleData.Sample,
          B.vectorFamily.probabilityMass xi i = 1 :=
        B.vectorFamily.scalarFamily.probabilityMass_sum xi
      have hdouble :
          (∑ i : B.sampleData.Sample,
            ∑ j : B.sampleData.Sample,
              (B.vectorFamily.probabilityMass xi i *
                B.vectorFamily.probabilityMass xi j) *
                B.statisticDiameter ^ 2) =
              B.statisticDiameter ^ 2 := by
        calc
        (∑ i : B.sampleData.Sample,
            ∑ j : B.sampleData.Sample,
              (B.vectorFamily.probabilityMass xi i *
                B.vectorFamily.probabilityMass xi j) *
                B.statisticDiameter ^ 2) =
            ∑ i : B.sampleData.Sample,
              (B.vectorFamily.probabilityMass xi i *
                B.statisticDiameter ^ 2) *
                ∑ j : B.sampleData.Sample,
                  B.vectorFamily.probabilityMass xi j := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = ∑ i : B.sampleData.Sample,
              B.vectorFamily.probabilityMass xi i *
                B.statisticDiameter ^ 2 := by rw [hsum]; simp
        _ = (∑ i : B.sampleData.Sample,
              B.vectorFamily.probabilityMass xi i) *
                B.statisticDiameter ^ 2 := by rw [Finset.sum_mul]
        _ = B.statisticDiameter ^ 2 := by rw [hsum, one_mul]
      rw [hdouble]
      ring

/-- In particular, the main-to-nuisance cross block has the same canonical
tilt-independent bound.  Thus Proposition 8.7 does not need an additional
analytic cross-block hypothesis or a box-dependent constant. -/
theorem crossCovarianceOperator_norm_le_canonicalCrossBound
    [Nonempty Head] (xi : B.ParamSpace) :
    ‖B.crossCovarianceOperator xi‖ ≤ B.canonicalCrossBound := by
  have hAdj : ‖B.nuisanceEmbeddingCLM.adjoint‖ ≤ 1 := by
    simpa using B.nuisanceEmbeddingCLM_norm_le_one
  have hinner :
      ‖(B.covarianceOperator xi).comp B.mainEmbeddingCLM‖ ≤
        B.canonicalCrossBound * 1 := by
    calc
      ‖(B.covarianceOperator xi).comp B.mainEmbeddingCLM‖ ≤
          ‖B.covarianceOperator xi‖ * ‖B.mainEmbeddingCLM‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ B.canonicalCrossBound * 1 :=
        mul_le_mul (B.covarianceOperator_norm_le_canonicalCrossBound xi)
          B.mainEmbeddingCLM_norm_le_one
          (norm_nonneg _) B.canonicalCrossBound_nonneg
  unfold crossCovarianceOperator
  calc
    ‖B.nuisanceEmbeddingCLM.adjoint.comp
        ((B.covarianceOperator xi).comp B.mainEmbeddingCLM)‖ ≤
        ‖B.nuisanceEmbeddingCLM.adjoint‖ *
          ‖(B.covarianceOperator xi).comp B.mainEmbeddingCLM‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (B.canonicalCrossBound * 1) :=
      mul_le_mul hAdj hinner (norm_nonneg _) zero_le_one
    _ = B.canonicalCrossBound := by ring

/-! ## A finite `ell^1` tilt bound -/

/-- An explicit finite radius dominating every log-density score. -/
def scoreRadius [Nonempty Head] (xi : B.ParamSpace) : ℝ :=
  ∑ m : B.sampleData.Sample,
    |B.vectorFamily.scalarFamily.score m xi / B.L|

theorem scoreRadius_nonneg [Nonempty Head] (xi : B.ParamSpace) :
    0 ≤ B.scoreRadius xi :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_scaledScore_le_scoreRadius [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    |B.vectorFamily.scalarFamily.score m xi / B.L| ≤ B.scoreRadius xi := by
  exact Finset.single_le_sum (fun k _ =>
    abs_nonneg (B.vectorFamily.scalarFamily.score k xi / B.L))
    (Finset.mem_univ m)

theorem scaledScore_le_scoreRadius [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.score m xi / B.L ≤ B.scoreRadius xi :=
  (le_abs_self _).trans (B.abs_scaledScore_le_scoreRadius xi m)

theorem neg_scoreRadius_le_scaledScore [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    -B.scoreRadius xi ≤
      B.vectorFamily.scalarFamily.score m xi / B.L := by
  have h := neg_abs_le
    (B.vectorFamily.scalarFamily.score m xi / B.L)
  linarith [B.abs_scaledScore_le_scoreRadius xi m]

theorem partition_le_exp_scoreRadius_mul_q [Nonempty Head]
    (xi : B.ParamSpace) :
    B.vectorFamily.scalarFamily.partition xi ≤
      Real.exp (B.scoreRadius xi) * B.q := by
  rw [FiniteExponentialFamily.partition]
  calc
    (∑ m, B.vectorFamily.scalarFamily.unnormalizedWeight xi m)
        ≤ ∑ m, B.baseline.baseWeight m *
            Real.exp (B.scoreRadius xi) := by
          apply Finset.sum_le_sum
          intro m _
          simp only [FiniteExponentialFamily.unnormalizedWeight,
            vectorFamily, VectorExponentialFamily.scalarFamily]
          exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (B.scaledScore_le_scoreRadius xi m))
            (B.baseline.baseWeight_nonneg m)
    _ = Real.exp (B.scoreRadius xi) * B.q := by
      rw [← Finset.sum_mul, B.baseline.baseWeight_sum]
      simp [q, mul_comm]

theorem exp_neg_scoreRadius_mul_q_le_partition [Nonempty Head]
    (xi : B.ParamSpace) :
    Real.exp (-B.scoreRadius xi) * B.q ≤
      B.vectorFamily.scalarFamily.partition xi := by
  rw [FiniteExponentialFamily.partition]
  calc
    Real.exp (-B.scoreRadius xi) * B.q
        = ∑ m, B.baseline.baseWeight m *
            Real.exp (-B.scoreRadius xi) := by
          rw [← Finset.sum_mul, B.baseline.baseWeight_sum]
          simp [q, mul_comm]
    _ ≤ ∑ m, B.vectorFamily.scalarFamily.unnormalizedWeight xi m := by
      apply Finset.sum_le_sum
      intro m _
      simp only [FiniteExponentialFamily.unnormalizedWeight,
        vectorFamily, VectorExponentialFamily.scalarFamily]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (B.neg_scoreRadius_le_scaledScore xi m))
        (B.baseline.baseWeight_nonneg m)

theorem probabilityMass_le_exp_twoRadius_mul_baseline [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.vectorFamily.probabilityMass xi m ≤
      Real.exp (2 * B.scoreRadius xi) *
        B.vectorFamily.probabilityMass 0 m := by
  let r := B.scoreRadius xi
  have hq : B.q ≠ 0 := ne_of_gt B.q_pos
  have hZ : 0 < B.vectorFamily.scalarFamily.partition xi :=
    B.vectorFamily.scalarFamily.partition_pos xi
  have hexp : Real.exp (2 * r) * Real.exp (-r) = Real.exp r := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [B.probabilityMass_zero m]
  change B.vectorFamily.scalarFamily.unnormalizedWeight xi m /
      B.vectorFamily.scalarFamily.partition xi ≤
    Real.exp (2 * r) * (B.baseline.baseWeight m / B.q)
  apply (div_le_iff₀ hZ).2
  calc
    B.vectorFamily.scalarFamily.unnormalizedWeight xi m
        = B.baseline.baseWeight m * Real.exp
            (B.vectorFamily.scalarFamily.score m xi / B.L) := by
          rfl
    _ ≤ B.baseline.baseWeight m * Real.exp r := by
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (B.scaledScore_le_scoreRadius xi m))
        (B.baseline.baseWeight_nonneg m)
    _ = (Real.exp (2 * r) * (B.baseline.baseWeight m / B.q)) *
          (Real.exp (-r) * B.q) := by
      field_simp [hq]
      calc
        B.baseline.baseWeight m * Real.exp r =
            B.baseline.baseWeight m *
              (Real.exp (2 * r) * Real.exp (-r)) := by rw [hexp]
        _ = B.baseline.baseWeight m * Real.exp (2 * r) *
              Real.exp (-r) := by ring
    _ ≤ (Real.exp (2 * r) * (B.baseline.baseWeight m / B.q)) *
          B.vectorFamily.scalarFamily.partition xi := by
      exact mul_le_mul_of_nonneg_left
        (B.exp_neg_scoreRadius_mul_q_le_partition xi)
        (mul_nonneg (le_of_lt (Real.exp_pos _))
          (div_nonneg (B.baseline.baseWeight_nonneg m)
            (le_of_lt B.q_pos)))

theorem exp_neg_twoRadius_mul_baseline_le_probabilityMass
    [Nonempty Head] (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    Real.exp (-2 * B.scoreRadius xi) *
        B.vectorFamily.probabilityMass 0 m ≤
      B.vectorFamily.probabilityMass xi m := by
  let r := B.scoreRadius xi
  have hq : B.q ≠ 0 := ne_of_gt B.q_pos
  have hZ : 0 < B.vectorFamily.scalarFamily.partition xi :=
    B.vectorFamily.scalarFamily.partition_pos xi
  have hexp : Real.exp (-2 * r) * Real.exp r = Real.exp (-r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [B.probabilityMass_zero m]
  change Real.exp (-2 * r) * (B.baseline.baseWeight m / B.q) ≤
    B.vectorFamily.scalarFamily.unnormalizedWeight xi m /
      B.vectorFamily.scalarFamily.partition xi
  apply (le_div_iff₀ hZ).2
  calc
    (Real.exp (-2 * r) * (B.baseline.baseWeight m / B.q)) *
          B.vectorFamily.scalarFamily.partition xi
        ≤ (Real.exp (-2 * r) * (B.baseline.baseWeight m / B.q)) *
            (Real.exp r * B.q) := by
          exact mul_le_mul_of_nonneg_left
            (B.partition_le_exp_scoreRadius_mul_q xi)
            (mul_nonneg (le_of_lt (Real.exp_pos _))
              (div_nonneg (B.baseline.baseWeight_nonneg m)
                (le_of_lt B.q_pos)))
    _ = B.baseline.baseWeight m * Real.exp (-r) := by
      field_simp [hq]
      calc
        Real.exp (-(2 * r)) * B.baseline.baseWeight m * Real.exp r =
            B.baseline.baseWeight m *
              (Real.exp (-2 * r) * Real.exp r) := by ring_nf
        _ = B.baseline.baseWeight m * Real.exp (-r) := by rw [hexp]
    _ ≤ B.baseline.baseWeight m * Real.exp
          (B.vectorFamily.scalarFamily.score m xi / B.L) := by
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (B.neg_scoreRadius_le_scaledScore xi m))
        (B.baseline.baseWeight_nonneg m)
    _ = B.vectorFamily.scalarFamily.unnormalizedWeight xi m := rfl

theorem baselineProbability_le_exp_twoRadius_mul_probabilityMass
    [Nonempty Head] (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.vectorFamily.probabilityMass 0 m ≤
      Real.exp (2 * B.scoreRadius xi) *
        B.vectorFamily.probabilityMass xi m := by
  let r := B.scoreRadius xi
  have hlower := B.exp_neg_twoRadius_mul_baseline_le_probabilityMass xi m
  have hexp : Real.exp (2 * r) * Real.exp (-2 * r) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero
    ring
  calc
    B.vectorFamily.probabilityMass 0 m
        = Real.exp (2 * r) *
            (Real.exp (-2 * r) *
              B.vectorFamily.probabilityMass 0 m) := by rw [← mul_assoc, hexp, one_mul]
    _ ≤ Real.exp (2 * r) * B.vectorFamily.probabilityMass xi m :=
      mul_le_mul_of_nonneg_left hlower (le_of_lt (Real.exp_pos _))

theorem abs_probabilityMass_sub_baseline_le [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    |B.vectorFamily.probabilityMass xi m -
        B.vectorFamily.probabilityMass 0 m| ≤
      (Real.exp (2 * B.scoreRadius xi) - 1) *
        (B.vectorFamily.probabilityMass xi m +
          B.vectorFamily.probabilityMass 0 m) := by
  let E := Real.exp (2 * B.scoreRadius xi)
  have hE : 1 ≤ E := by
    dsimp only [E]
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr
      (mul_nonneg (by norm_num) (B.scoreRadius_nonneg xi))
  have hup := B.probabilityMass_le_exp_twoRadius_mul_baseline xi m
  have hdown := B.baselineProbability_le_exp_twoRadius_mul_probabilityMass xi m
  have hp := B.vectorFamily.scalarFamily.probabilityMass_nonneg xi m
  have hp0 := B.vectorFamily.scalarFamily.probabilityMass_nonneg 0 m
  by_cases horder : B.vectorFamily.probabilityMass 0 m ≤
      B.vectorFamily.probabilityMass xi m
  · rw [abs_of_nonneg (sub_nonneg.mpr horder)]
    have hdiff : B.vectorFamily.probabilityMass xi m -
        B.vectorFamily.probabilityMass 0 m ≤
          (E - 1) * B.vectorFamily.probabilityMass 0 m := by
      dsimp only [E] at hup ⊢
      linarith
    exact hdiff.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left hp) (sub_nonneg.mpr hE))
  · have horder' : B.vectorFamily.probabilityMass xi m ≤
        B.vectorFamily.probabilityMass 0 m := le_of_not_ge horder
    rw [abs_of_nonpos (sub_nonpos.mpr horder')]
    have hdiff : B.vectorFamily.probabilityMass 0 m -
        B.vectorFamily.probabilityMass xi m ≤
          (E - 1) * B.vectorFamily.probabilityMass xi m := by
      dsimp only [E] at hdown ⊢
      linarith
    have hfinal := hdiff.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right hp0) (sub_nonneg.mpr hE))
    simpa only [neg_sub] using hfinal

/-- Explicit total-variation estimate for the actual finite tilt. -/
theorem weightL1Distance_tilt_le [Nonempty Head] (xi : B.ParamSpace) :
    (B.vectorFamily.tiltedMixture 0).weightL1Distance
        (B.vectorFamily.probabilityMass xi) ≤
      2 * (Real.exp (2 * B.scoreRadius xi) - 1) := by
  simp only [PatternMixture.weightL1Distance,
    VectorExponentialFamily.tiltedMixture]
  calc
    (∑ m, |B.vectorFamily.probabilityMass xi m -
        B.vectorFamily.probabilityMass 0 m|)
        ≤ ∑ m, (Real.exp (2 * B.scoreRadius xi) - 1) *
            (B.vectorFamily.probabilityMass xi m +
              B.vectorFamily.probabilityMass 0 m) := by
          exact Finset.sum_le_sum fun m _ =>
            B.abs_probabilityMass_sub_baseline_le xi m
    _ = 2 * (Real.exp (2 * B.scoreRadius xi) - 1) := by
      have hsumxi : ∑ m, B.vectorFamily.probabilityMass xi m = 1 :=
        B.vectorFamily.scalarFamily.probabilityMass_sum xi
      have hsum0 : ∑ m, B.vectorFamily.probabilityMass 0 m = 1 :=
        B.vectorFamily.scalarFamily.probabilityMass_sum 0
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hsumxi, hsum0]
      ring

/-- Finite sum of statistic norms, used for a completely explicit compact-box
tilt estimate.  The paper's sharper arithmetic estimate replaces this crude
finite bound by `B/log W + o(1)`, but no existence statement is needed here. -/
def totalStatisticNorm [Nonempty Head] : ℝ :=
  ∑ m : B.sampleData.Sample, ‖B.statistic m‖

theorem totalStatisticNorm_nonneg [Nonempty Head] :
    0 ≤ B.totalStatisticNorm :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem scoreRadius_le_norm_mul_totalStatisticNorm_div_L
    [Nonempty Head] (xi : B.ParamSpace) :
    B.scoreRadius xi ≤ ‖xi‖ * B.totalStatisticNorm / B.L := by
  have hL : 0 ≤ B.L := le_of_lt B.L_pos
  calc
    B.scoreRadius xi
        ≤ ∑ m : B.sampleData.Sample,
            (‖xi‖ * ‖B.statistic m‖) / B.L := by
          apply Finset.sum_le_sum
          intro m _
          rw [abs_div, abs_of_pos B.L_pos]
          apply div_le_div_of_nonneg_right _ hL
          change |inner ℝ (B.statistic m) xi| ≤
            ‖xi‖ * ‖B.statistic m‖
          simpa [mul_comm] using
            (abs_real_inner_le_norm (B.statistic m) xi)
    _ = ‖xi‖ * B.totalStatisticNorm / B.L := by
      rw [← Finset.sum_div, ← Finset.mul_sum]
      rfl

theorem weightL1Distance_tilt_on_normBall [Nonempty Head]
    (xi : B.ParamSpace) (radius : ℝ)
    (hxi : ‖xi‖ ≤ radius) :
    (B.vectorFamily.tiltedMixture 0).weightL1Distance
        (B.vectorFamily.probabilityMass xi) ≤
      2 * (Real.exp
        (2 * (radius * B.totalStatisticNorm / B.L)) - 1) := by
  have hscore : B.scoreRadius xi ≤
      radius * B.totalStatisticNorm / B.L := by
    exact (B.scoreRadius_le_norm_mul_totalStatisticNorm_div_L xi).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hxi B.totalStatisticNorm_nonneg)
        (le_of_lt B.L_pos))
  calc
    (B.vectorFamily.tiltedMixture 0).weightL1Distance
        (B.vectorFamily.probabilityMass xi)
        ≤ 2 * (Real.exp (2 * B.scoreRadius xi) - 1) :=
          B.weightL1Distance_tilt_le xi
    _ ≤ 2 * (Real.exp
          (2 * (radius * B.totalStatisticNorm / B.L)) - 1) := by
      have hexp : Real.exp (2 * B.scoreRadius xi) ≤
          Real.exp (2 * (radius * B.totalStatisticNorm / B.L)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hscore (by norm_num))
      linarith

/-- Explicit `ℓ¹` budget on a preselected Euclidean ball. -/
def ballTiltEpsilon [Nonempty Head] (radius : ℝ) : ℝ :=
  2 * (Real.exp
    (2 * (radius * B.totalStatisticNorm / B.L)) - 1)

def ballL1Proof [Nonempty Head]
    (xi : B.ParamSpace) (radius : ℝ) (hxi : ‖xi‖ ≤ radius) :
    (B.vectorFamily.tiltedMixture 0).weightL1Distance
      (B.vectorFamily.probabilityMass xi) ≤ B.ballTiltEpsilon radius := by
  exact B.weightL1Distance_tilt_on_normBall xi radius hxi

def ballNuisanceGapProof [Nonempty Head]
    (xi : B.ParamSpace) (radius : ℝ) (hxi : ‖xi‖ ≤ radius)
    (hsmall : B.ballTiltEpsilon radius *
      B.nuisanceStatisticDiameter ^ 2 ≤ B.nuisanceBaselineGap / 2) :
    ∀ z, (B.nuisanceBaselineGap / 2) * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z) :=
  B.nuisanceHalfGapProof xi (B.ballTiltEpsilon radius)
    (B.ballL1Proof xi radius hxi) hsmall

/-- Actual `Γ^{-1}B` regression on a preselected ball. -/
def ballNuisanceRegression [Nonempty Head]
    (xi : B.ParamSpace) (radius : ℝ) (hxi : ‖xi‖ ≤ radius)
    (hsmall : B.ballTiltEpsilon radius *
      B.nuisanceStatisticDiameter ^ 2 ≤ B.nuisanceBaselineGap / 2) :
    B.MainSpace → B.NuisanceSpace :=
  B.exactNuisanceRegression xi
    (div_pos B.nuisanceBaselineGap_pos (by norm_num))
    (B.ballNuisanceGapProof xi radius hxi hsmall)

/-- Uniform full covariance gap on a preselected ball, derived from the
actual finite nuisance cells plus the paper's main/slow Schur estimate and
a canonical finite cross-block bound.  There is neither a full-gap
hypothesis nor an independent box-dependent cross-block hypothesis. -/
theorem hasCovarianceGap_on_normBall_of_schur [Nonempty Head]
    (radius gammaMain : ℝ)
    (hMain : 0 < gammaMain)
    (hsmall : B.ballTiltEpsilon radius *
      B.nuisanceStatisticDiameter ^ 2 ≤ B.nuisanceBaselineGap / 2)
    (hSchur : ∀ xi (hxi : ‖xi‖ ≤ radius) u,
      gammaMain * ‖u‖ ^ 2 ≤
        inner ℝ
          (B.schurResidual
            (B.ballNuisanceRegression xi radius hxi hsmall) u)
          (B.covarianceOperator xi
            (B.schurResidual
              (B.ballNuisanceRegression xi radius hxi hsmall) u))) :
    ∀ xi, ‖xi‖ ≤ radius →
      B.vectorFamily.HasCovarianceGap
        (min gammaMain (B.nuisanceBaselineGap / 2) /
          (3 + 2 * (B.canonicalCrossBound /
            (B.nuisanceBaselineGap / 2)) ^ 2)) xi := by
  intro xi hxi
  let gammaN := B.nuisanceBaselineGap / 2
  have hgammaN : 0 < gammaN :=
    div_pos B.nuisanceBaselineGap_pos (by norm_num)
  let hGamma := B.ballNuisanceGapProof xi radius hxi hsmall
  let R := B.ballNuisanceRegression xi radius hxi hsmall
  have hRdef : R = B.exactNuisanceRegression xi hgammaN hGamma := by rfl
  apply B.hasCovarianceGap_of_schur xi R
    (B.canonicalCrossBound / gammaN) gammaMain gammaN
    (div_nonneg B.canonicalCrossBound_nonneg (le_of_lt hgammaN))
    hMain hgammaN
  · intro u
    rw [hRdef]
    calc
      ‖B.exactNuisanceRegression xi hgammaN hGamma u‖
          ≤ (‖B.crossCovarianceOperator xi‖ / gammaN) * ‖u‖ :=
        B.exactNuisanceRegression_norm_le xi hgammaN hGamma u
      _ ≤ (B.canonicalCrossBound / gammaN) * ‖u‖ := by
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right
            (B.crossCovarianceOperator_norm_le_canonicalCrossBound xi)
            (le_of_lt hgammaN)) (norm_nonneg u)
  · rw [hRdef]
    exact B.exactNuisanceRegression_isRegression xi hgammaN hGamma
  · exact hSchur xi hxi
  · intro z
    simpa only [nuisanceCovarianceOperator,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right] using hGamma z

/-- Uniform reference-to-arithmetic Schur transfer on the preselected ball.
This packages the quantifiers needed from the continuum/prime-row modules:
the reference gap and error budget are fixed before the path. -/
theorem schurGap_on_normBall_of_referenceComparison [Nonempty Head]
    (radius : ℝ) (reference : B.MainSpace →L[ℝ] B.MainSpace)
    (gammaReference delta : ℝ)
    (hsmall : B.ballTiltEpsilon radius *
      B.nuisanceStatisticDiameter ^ 2 ≤ B.nuisanceBaselineGap / 2)
    (href : ∀ u, gammaReference * ‖u‖ ^ 2 ≤
      inner ℝ u (reference u))
    (hcomparison : ∀ xi (hxi : ‖xi‖ ≤ radius) u,
      |inner ℝ u
        ((B.exactSchurCovarianceOperator xi
          (div_pos B.nuisanceBaselineGap_pos (by norm_num))
          (B.ballNuisanceGapProof xi radius hxi hsmall) - reference) u)| ≤
        delta * ‖u‖ ^ 2) :
    ∀ xi (hxi : ‖xi‖ ≤ radius) u,
      (gammaReference - delta) * ‖u‖ ^ 2 ≤
        inner ℝ
          (B.schurResidual
            (B.ballNuisanceRegression xi radius hxi hsmall) u)
          (B.covarianceOperator xi
            (B.schurResidual
              (B.ballNuisanceRegression xi radius hxi hsmall) u)) := by
  intro xi hxi u
  let hNuisance : 0 < B.nuisanceBaselineGap / 2 :=
    div_pos B.nuisanceBaselineGap_pos (by norm_num)
  let hGamma := B.ballNuisanceGapProof xi radius hxi hsmall
  have hreg : B.ballNuisanceRegression xi radius hxi hsmall =
      B.exactNuisanceRegression xi hNuisance hGamma := by rfl
  rw [hreg]
  exact B.exactSchur_gap_of_referenceComparison xi hNuisance hGamma
    reference gammaReference delta href (hcomparison xi hxi) u

/-! ## Target envelopes imply the ODE radius margin -/

/-- The two target estimates supplied before Proposition 8.7: the strict
band-rate envelope and the sharper compensated scalar estimate. -/
def HasTargetEnvelopes [Nonempty Head]
    (C : ℝ) (Delta : Band → ℝ) : Prop :=
  (∀ j, |Delta j| ≤
      (B.q / B.L) * C * |B.harmonicMass j|) ∧
    |∑ j, B.bandCenter j * Delta j| ≤
      (B.q / B.L) * C * B.w

/-- A coordinatewise bound for the normalized target. -/
def targetCoordinateBound [Nonempty Head] (C : ℝ) : B.Coord → ℝ
  | .gauge j => (B.L / B.q) *
      ((B.q / B.L) * C * |B.harmonicMass j.1| +
        |B.lowRatio j| *
          ((B.q / B.L) * C * |B.harmonicMass B.lowBand|))
  | .physical => 0
  | .head _ => 0
  | .slow => (B.L / B.q) *
      (((B.q / B.L) * C * B.w) / B.w)

theorem targetCoordinateBound_nonneg [Nonempty Head]
    {C : ℝ} (hC : 0 ≤ C) (c : B.Coord) :
    0 ≤ B.targetCoordinateBound C c := by
  cases c with
  | gauge j =>
      simp only [targetCoordinateBound]
      have hLq : 0 ≤ B.L / B.q := le_of_lt (div_pos B.L_pos B.q_pos)
      have hqL : 0 ≤ B.q / B.L := le_of_lt (div_pos B.q_pos B.L_pos)
      exact mul_nonneg hLq (add_nonneg
        (mul_nonneg (mul_nonneg hqL hC) (abs_nonneg _))
        (mul_nonneg (abs_nonneg _) (mul_nonneg
          (mul_nonneg hqL hC) (abs_nonneg _))))
  | physical => simp [targetCoordinateBound]
  | head h => simp [targetCoordinateBound]
  | slow =>
      simp only [targetCoordinateBound]
      exact mul_nonneg (le_of_lt (div_pos B.L_pos B.q_pos))
        (div_nonneg
          (mul_nonneg
            (mul_nonneg (le_of_lt (div_pos B.q_pos B.L_pos)) hC)
            (le_of_lt B.w_pos))
          (le_of_lt B.w_pos))

theorem abs_normalizedTarget_apply_le [Nonempty Head]
    {C : ℝ} (Delta : Band → ℝ)
    (henv : B.HasTargetEnvelopes C Delta) (c : B.Coord) :
    |B.normalizedTarget Delta c| ≤ B.targetCoordinateBound C c := by
  rcases henv with ⟨hband, hslow⟩
  cases c with
  | gauge j =>
      rw [B.normalizedTarget_apply]
      simp only [unscaledTarget, coordScale, div_one]
      rw [abs_mul, abs_of_pos (div_pos B.L_pos B.q_pos)]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (div_pos B.L_pos B.q_pos))
      calc
        |Delta j.1 - B.lowRatio j * Delta B.lowBand|
            ≤ |Delta j.1| + |B.lowRatio j * Delta B.lowBand| :=
              abs_sub _ _
        _ = |Delta j.1| + |B.lowRatio j| * |Delta B.lowBand| := by
              rw [abs_mul]
        _ ≤ (B.q / B.L) * C * |B.harmonicMass j.1| +
            |B.lowRatio j| *
              ((B.q / B.L) * C * |B.harmonicMass B.lowBand|) :=
          add_le_add (hband j.1)
            (mul_le_mul_of_nonneg_left (hband B.lowBand)
              (abs_nonneg (B.lowRatio j)))
  | physical => simp [normalizedTarget_apply, unscaledTarget,
      coordScale, targetCoordinateBound]
  | head h => simp [normalizedTarget_apply, unscaledTarget,
      coordScale, targetCoordinateBound]
  | slow =>
      rw [B.normalizedTarget_slow_apply]
      simp only [targetCoordinateBound]
      rw [abs_mul, abs_of_pos (div_pos B.L_pos B.q_pos), abs_div,
        abs_of_pos B.w_pos]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hslow (le_of_lt B.w_pos))
        (le_of_lt (div_pos B.L_pos B.q_pos))

/-- Explicit Euclidean bound obtained by summing the coordinate envelopes. -/
def targetEnvelopeNorm [Nonempty Head] (C : ℝ) : ℝ :=
  Real.sqrt (∑ c : B.Coord, (B.targetCoordinateBound C c) ^ 2)

theorem normalizedTarget_norm_le_envelope [Nonempty Head]
    {C : ℝ} (Delta : Band → ℝ)
    (henv : B.HasTargetEnvelopes C Delta) :
    ‖B.normalizedTarget Delta‖ ≤ B.targetEnvelopeNorm C := by
  have hsum : ‖B.normalizedTarget Delta‖ ^ 2 ≤
      ∑ c : B.Coord, (B.targetCoordinateBound C c) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    apply Finset.sum_le_sum
    intro c _
    simpa only [sq_abs] using
      (pow_le_pow_left₀ (abs_nonneg (B.normalizedTarget Delta c))
        (B.abs_normalizedTarget_apply_le Delta henv c) 2)
  have hnon : 0 ≤ ∑ c : B.Coord,
      (B.targetCoordinateBound C c) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsqrt : (B.targetEnvelopeNorm C) ^ 2 =
      ∑ c : B.Coord, (B.targetCoordinateBound C c) ^ 2 := by
    exact Real.sq_sqrt hnon
  have hsqrtnon : 0 ≤ B.targetEnvelopeNorm C := Real.sqrt_nonneg _
  nlinarith [norm_nonneg (B.normalizedTarget Delta)]

/-- A check on the preselected radius using only the preceding target
envelopes. -/
theorem target_radius_margin_of_envelopes [Nonempty Head]
    {C gamma : ℝ} (hgamma : 0 < gamma)
    (Delta : Band → ℝ) (henv : B.HasTargetEnvelopes C Delta)
    (a : ℝ) (ha : B.targetEnvelopeNorm C / gamma ≤ a) :
    ‖B.targetVector Delta‖ / ((B.q / B.L) * gamma) ≤ a := by
  rw [B.target_radius_identity Delta gamma hgamma]
  exact (div_le_div_of_nonneg_right
    (B.normalizedTarget_norm_le_envelope Delta henv)
    (le_of_lt hgamma)).trans ha

/-! ## Concrete Proposition 8.7 endpoint -/

/-- Once the analytic covariance gap of Lemmas 8.5--8.6 has been proved on
the ball chosen in advance, the abstract nonlinear lift specializes to the
actual guarded sample and actual paper statistics.  The conclusion is
stated directly as the requested raw moment identities.

Thus the hypothesis below isolates the remaining analytic input; the
inverse Jacobian, ODE existence, confinement, and endpoint equations are
conclusions. -/
theorem exists_paperFit_on_preselectedBall [Nonempty Head]
    (Delta : Band → ℝ) (a : NNReal) {gamma : ℝ}
    (hgamma : 0 < gamma)
    (hgap : ∀ xi ∈ closedBall (0 : B.ParamSpace) (a : ℝ),
      B.vectorFamily.HasCovarianceGap gamma xi)
    (hmargin : ‖B.targetVector Delta‖ /
      ((B.q / B.L) * gamma) ≤ (a : ℝ)) :
    ∃ path : ℝ → B.ParamSpace,
      path 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        path t ∈ closedBall (0 : B.ParamSpace) (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path
          (B.vectorFamily.vectorField (B.targetVector Delta) (path t))
          (Icc (0 : ℝ) 1) t) ∧
      (∀ c : B.Coord,
        B.paperMoment (fun m => B.rawStatistic m c) (path 1) =
          B.paperMoment (fun m => B.rawStatistic m c) 0 +
            B.unscaledTarget Delta c) := by
  have hgenericMargin : ‖B.targetVector Delta‖ /
      ((B.vectorFamily.baseMass / B.vectorFamily.scale) * gamma) ≤
        (a : ℝ) := by
    simpa only [B.vectorFamily_baseMass] using hmargin
  obtain ⟨path, hzero, hball, hderiv, hend⟩ :=
    B.vectorFamily.exists_straightTargetLift_on_preselectedBall
      (0 : B.ParamSpace) (B.targetVector Delta) a hgamma hgap
        hgenericMargin
  refine ⟨path, hzero, hball, hderiv, ?_⟩
  exact (B.endpoint_iff_paperMoments Delta 0 (path 1)).mp hend

/-- Target envelopes and the normalized radius check discharge the entire
ODE margin in the concrete fit theorem.  No choice of a posteriori tilt box
is made here. -/
theorem exists_paperFit_of_envelopes_on_preselectedBall [Nonempty Head]
    {C gamma : ℝ} (hgamma : 0 < gamma)
    (Delta : Band → ℝ) (henv : B.HasTargetEnvelopes C Delta)
    (a : NNReal)
    (henvelope : B.targetEnvelopeNorm C / gamma ≤ (a : ℝ))
    (hgap : ∀ xi ∈ closedBall (0 : B.ParamSpace) (a : ℝ),
      B.vectorFamily.HasCovarianceGap gamma xi) :
    ∃ path : ℝ → B.ParamSpace,
      path 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        path t ∈ closedBall (0 : B.ParamSpace) (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path
          (B.vectorFamily.vectorField (B.targetVector Delta) (path t))
          (Icc (0 : ℝ) 1) t) ∧
      (∀ c : B.Coord,
        B.paperMoment (fun m => B.rawStatistic m c) (path 1) =
          B.paperMoment (fun m => B.rawStatistic m c) 0 +
            B.unscaledTarget Delta c) := by
  apply B.exists_paperFit_on_preselectedBall Delta a hgamma hgap
  exact B.target_radius_margin_of_envelopes hgamma Delta henv a henvelope

/-- Proposition 8.7 with the full covariance-gap hypothesis eliminated.
The remaining analytic input is exactly the uniform main/slow Schur bound
of Lemma 8.6; the cross bound, nuisance gap, regression, full block inverse,
ODE, and endpoint are all constructed from the actual finite sample. -/
theorem exists_paperFit_of_schur_on_preselectedBall [Nonempty Head]
    (Delta : Band → ℝ) (a : NNReal)
    (gammaMain : ℝ)
    (hMain : 0 < gammaMain)
    (hsmall : B.ballTiltEpsilon (a : ℝ) *
      B.nuisanceStatisticDiameter ^ 2 ≤ B.nuisanceBaselineGap / 2)
    (hSchur : ∀ xi (hxi : ‖xi‖ ≤ (a : ℝ)) u,
      gammaMain * ‖u‖ ^ 2 ≤
        inner ℝ
          (B.schurResidual
            (B.ballNuisanceRegression xi (a : ℝ) hxi hsmall) u)
          (B.covarianceOperator xi
            (B.schurResidual
              (B.ballNuisanceRegression xi (a : ℝ) hxi hsmall) u)))
    (hmargin : ‖B.targetVector Delta‖ /
      ((B.q / B.L) *
        (min gammaMain (B.nuisanceBaselineGap / 2) /
          (3 + 2 * (B.canonicalCrossBound /
            (B.nuisanceBaselineGap / 2)) ^ 2))) ≤ (a : ℝ)) :
    ∃ path : ℝ → B.ParamSpace,
      path 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        path t ∈ closedBall (0 : B.ParamSpace) (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path
          (B.vectorFamily.vectorField (B.targetVector Delta) (path t))
          (Icc (0 : ℝ) 1) t) ∧
      (∀ c : B.Coord,
        B.paperMoment (fun m => B.rawStatistic m c) (path 1) =
          B.paperMoment (fun m => B.rawStatistic m c) 0 +
            B.unscaledTarget Delta c) := by
  let gammaFull := min gammaMain (B.nuisanceBaselineGap / 2) /
    (3 + 2 *
      (B.canonicalCrossBound / (B.nuisanceBaselineGap / 2)) ^ 2)
  have hNuisance : 0 < B.nuisanceBaselineGap / 2 :=
    div_pos B.nuisanceBaselineGap_pos (by norm_num)
  have hden : 0 < 3 + 2 *
      (B.canonicalCrossBound /
        (B.nuisanceBaselineGap / 2)) ^ 2 := by positivity
  have hgammaFull : 0 < gammaFull := by
    exact div_pos (lt_min hMain hNuisance) hden
  apply B.exists_paperFit_on_preselectedBall Delta a hgammaFull
  · intro xi hxi
    have hnorm : ‖xi‖ ≤ (a : ℝ) := by
      simpa only [mem_closedBall, dist_zero_right] using hxi
    exact B.hasCovarianceGap_on_normBall_of_schur
      (a : ℝ) gammaMain hMain hsmall hSchur xi hnorm
  · simpa only [gammaFull] using hmargin

/-- Exact-band form of Proposition 8.7.  The logarithmic compatibility is a
finite arithmetic identity about the guarded sample; once supplied, the
gauge/slow endpoint is proved to be all individual band equations. -/
theorem exists_paperFit_allBands_of_schur_on_preselectedBall [Nonempty Head]
    (hcompat : B.HasPrimeLogCompatibility)
    (Delta : Band → ℝ) (a : NNReal)
    (gammaMain : ℝ)
    (hMain : 0 < gammaMain)
    (hsmall : B.ballTiltEpsilon (a : ℝ) *
      B.nuisanceStatisticDiameter ^ 2 ≤ B.nuisanceBaselineGap / 2)
    (hSchur : ∀ xi (hxi : ‖xi‖ ≤ (a : ℝ)) u,
      gammaMain * ‖u‖ ^ 2 ≤
        inner ℝ
          (B.schurResidual
            (B.ballNuisanceRegression xi (a : ℝ) hxi hsmall) u)
          (B.covarianceOperator xi
            (B.schurResidual
              (B.ballNuisanceRegression xi (a : ℝ) hxi hsmall) u)))
    (hmargin : ‖B.targetVector Delta‖ /
      ((B.q / B.L) *
        (min gammaMain (B.nuisanceBaselineGap / 2) /
          (3 + 2 * (B.canonicalCrossBound /
            (B.nuisanceBaselineGap / 2)) ^ 2))) ≤ (a : ℝ)) :
    ∃ path : ℝ → B.ParamSpace,
      path 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        path t ∈ closedBall (0 : B.ParamSpace) (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path
          (B.vectorFamily.vectorField (B.targetVector Delta) (path t))
          (Icc (0 : ℝ) 1) t) ∧
      ∀ j : Band,
        B.paperMoment (B.bandScore j) (path 1) =
          B.paperMoment (B.bandScore j) 0 + Delta j := by
  obtain ⟨path, hzero, hball, hderiv, hraw⟩ :=
    B.exists_paperFit_of_schur_on_preselectedBall Delta a
      gammaMain hMain hsmall hSchur hmargin
  exact ⟨path, hzero, hball, hderiv,
    B.rawEndpoint_recovers_all_bandMoments hcompat Delta 0 (path 1) hraw⟩

/-- Exact Proposition 8.7 endpoint expressed directly in the form needed
from the analytic part of Lemma 8.6.  A coercive reference operator and a
uniform quadratic-form comparison produce the Schur estimate; all remaining
finite covariance, regression, continuation, and band-recovery steps are
proved above.  In particular, this theorem makes the sole outstanding
analytic comparison visible instead of repackaging it as a full covariance
gap. -/
theorem exists_paperFit_allBands_of_referenceComparison_on_preselectedBall
    [Nonempty Head]
    (hcompat : B.HasPrimeLogCompatibility)
    (Delta : Band → ℝ) (a : NNReal)
    (reference : B.MainSpace →L[ℝ] B.MainSpace)
    (gammaReference delta : ℝ)
    (hdelta : delta < gammaReference)
    (hsmall : B.ballTiltEpsilon (a : ℝ) *
      B.nuisanceStatisticDiameter ^ 2 ≤ B.nuisanceBaselineGap / 2)
    (href : ∀ u, gammaReference * ‖u‖ ^ 2 ≤
      inner ℝ u (reference u))
    (hcomparison : ∀ xi (hxi : ‖xi‖ ≤ (a : ℝ)) u,
      |inner ℝ u
        ((B.exactSchurCovarianceOperator xi
          (div_pos B.nuisanceBaselineGap_pos (by norm_num))
          (B.ballNuisanceGapProof xi (a : ℝ) hxi hsmall) - reference) u)| ≤
        delta * ‖u‖ ^ 2)
    (hmargin : ‖B.targetVector Delta‖ /
      ((B.q / B.L) *
        (min (gammaReference - delta)
            (B.nuisanceBaselineGap / 2) /
          (3 + 2 * (B.canonicalCrossBound /
            (B.nuisanceBaselineGap / 2)) ^ 2))) ≤ (a : ℝ)) :
    ∃ path : ℝ → B.ParamSpace,
      path 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        path t ∈ closedBall (0 : B.ParamSpace) (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path
          (B.vectorFamily.vectorField (B.targetVector Delta) (path t))
          (Icc (0 : ℝ) 1) t) ∧
      ∀ j : Band,
        B.paperMoment (B.bandScore j) (path 1) =
          B.paperMoment (B.bandScore j) 0 + Delta j := by
  apply B.exists_paperFit_allBands_of_schur_on_preselectedBall
    hcompat Delta a (gammaReference - delta) (sub_pos.mpr hdelta)
    hsmall
  · exact B.schurGap_on_normBall_of_referenceComparison
      (a : ℝ) reference gammaReference delta hsmall href hcomparison
  · exact hmargin

end BridgeData

/-! ## Non-circular order of asymptotic choices -/

/-- Abstract quantifier-order lemma used by the sharp-relative transfer.
The box may be chosen after `W`; only the final threshold is allowed to
depend on that box.  The conclusion visibly places the cutoff outside the
universal box quantifier. -/
theorem choose_cutoff_before_box
    {Box : Type*} (C gap : ℝ) (hC : 0 ≤ C) (hgap : 0 < gap)
    (remainder : ℕ → Box → ℕ → ℝ)
    (hremainder : ∀ W box epsilon, 0 < epsilon →
      ∃ n₀, ∀ n ≥ n₀, |remainder W box n| < epsilon) :
    ∃ W : ℕ, 0 < W ∧ C / (W : ℝ) < gap / 2 ∧
      ∀ box, ∃ n₀, ∀ n ≥ n₀,
        |remainder W box n| < gap / 2 := by
  obtain ⟨W, hW⟩ := exists_nat_gt (2 * C / gap)
  have hnonneg : 0 ≤ 2 * C / gap :=
    div_nonneg (mul_nonneg (by norm_num) hC) (le_of_lt hgap)
  have hWposReal : 0 < (W : ℝ) := lt_of_le_of_lt hnonneg hW
  have hWpos : 0 < W := by exact_mod_cast hWposReal
  refine ⟨W, hWpos, ?_, ?_⟩
  · apply (div_lt_iff₀ hWposReal).2
    have hscaled := (div_lt_iff₀ hgap).mp hW
    nlinarith
  · intro box
    exact hremainder W box (gap / 2) (half_pos hgap)

end PaperBridgeFit

end


end Erdos390.Full
