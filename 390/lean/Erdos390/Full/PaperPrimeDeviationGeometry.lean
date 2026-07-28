import Erdos390.Full.PaperPrimeDeviationMoments

/-!
# Deterministic geometry of the actual prime deviations

These are the finite inequalities used in the `L¹` and variance census of
Lemma 8.6.  They apply to the actual arithmetic centers and actual primes.
No continuum center and no prime-number estimate occurs here; analytic
quadrature can therefore be inserted afterwards without a centering error.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PositiveCellTransfer KernelPrimeQuadrature

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Weighted `L¹` deviation on one actual arithmetic band. -/
def bandDeviationL1 (j : Band) : ℝ :=
  ∑ p ∈ B.partition.data.fiber j,
    (1 / (p.1 : ℝ)) * |B.primeDeviation p|

/-- The paper's full `sum |g_p|/p`. -/
def primeDeviationL1 : ℝ :=
  ∑ p : BandPrime B.sampleData.n B.sampleData.W,
    (1 / (p.1 : ℝ)) * |B.primeDeviation p|

theorem primeDeviationL1_eq_sum_bandDeviationL1 :
    B.primeDeviationL1 = ∑ j : Band, B.bandDeviationL1 j := by
  unfold primeDeviationL1 bandDeviationL1
  rw [← Finset.sum_fiberwise Finset.univ B.partition.band
    (fun p : BandPrime B.sampleData.n B.sampleData.W ↦
      (1 / (p.1 : ℝ)) * |B.primeDeviation p|)]
  apply Finset.sum_congr rfl
  intro j hj
  rfl

/-- The coordinate of a prime in a certified cell lies between the two
normalized endpoint coordinates. -/
theorem realLogCoordinate_lower_le_tPrime
    (E : B.PositiveCellCertificate) (j : Band)
    (p : BandPrime B.sampleData.n B.sampleData.W)
    (hp : p ∈ B.partition.data.fiber j)
    (hLowerPos : 0 < E.lower j) :
    realLogCoordinate (y B.sampleData.n) (E.lower j : ℝ) ≤
      tPrime B.sampleData.n p.1 := by
  have hpj : B.partition.band p = j :=
    (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff
      B.partition.data).mp hp
  have hpLower : E.lower j < p.1 := (E.band_eq_iff p j).mp hpj |>.1
  have hcastPos : (0 : ℝ) < (E.lower j : ℝ) := by exact_mod_cast hLowerPos
  have hcastLe : (E.lower j : ℝ) ≤ (p.1 : ℝ) := by
    exact_mod_cast hpLower.le
  have hlogLe : Real.log (E.lower j : ℝ) ≤ Real.log (p.1 : ℝ) :=
    Real.log_le_log hcastPos hcastLe
  unfold realLogCoordinate tPrime
  exact div_le_div_of_nonneg_right hlogLe B.log_y_pos.le

theorem tPrime_le_realLogCoordinate_upper
    (E : B.PositiveCellCertificate) (j : Band)
    (p : BandPrime B.sampleData.n B.sampleData.W)
    (hp : p ∈ B.partition.data.fiber j) :
    tPrime B.sampleData.n p.1 ≤
      realLogCoordinate (y B.sampleData.n) (E.upper j : ℝ) := by
  have hpj : B.partition.band p = j :=
    (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff
      B.partition.data).mp hp
  have hpUpper : p.1 ≤ E.upper j := (E.band_eq_iff p j).mp hpj |>.2
  have hpPos : (0 : ℝ) < (p.1 : ℝ) := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  have hcastLe : (p.1 : ℝ) ≤ (E.upper j : ℝ) := by
    exact_mod_cast hpUpper
  have hlogLe : Real.log (p.1 : ℝ) ≤ Real.log (E.upper j : ℝ) :=
    Real.log_le_log hpPos hcastLe
  unfold realLogCoordinate tPrime
  exact div_le_div_of_nonneg_right hlogLe B.log_y_pos.le

/-- A positive weighted arithmetic center stays in the same interval as all
coordinates in its fiber. -/
theorem bandCenter_mem_endpointInterval
    (E : B.PositiveCellCertificate) (j : Band)
    (hLowerPos : 0 < E.lower j) :
    B.bandCenter j ∈ Set.Icc
      (realLogCoordinate (y B.sampleData.n) (E.lower j : ℝ))
      (realLogCoordinate (y B.sampleData.n) (E.upper j : ℝ)) := by
  let a := realLogCoordinate (y B.sampleData.n) (E.lower j : ℝ)
  let b := realLogCoordinate (y B.sampleData.n) (E.upper j : ℝ)
  let F := B.partition.data.fiber j
  let H := B.harmonicMass j
  have hH : 0 < H := B.harmonicMass_pos j
  have hLowerSum : a * H ≤
      ∑ p ∈ F, (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1 := by
    change a * (∑ p ∈ F, 1 / (p.1 : ℝ)) ≤ _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hw : 0 ≤ 1 / (p.1 : ℝ) := by positivity
    simpa only [a, mul_comm] using
      (mul_le_mul_of_nonneg_right
        (B.realLogCoordinate_lower_le_tPrime E j p hp hLowerPos) hw)
  have hUpperSum :
      (∑ p ∈ F, (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) ≤
        b * H := by
    change _ ≤ b * (∑ p ∈ F, 1 / (p.1 : ℝ))
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hw : 0 ≤ 1 / (p.1 : ℝ) := by positivity
    have hcoord := B.tPrime_le_realLogCoordinate_upper E j p hp
    calc
      (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1 ≤
          (1 / (p.1 : ℝ)) * b :=
        mul_le_mul_of_nonneg_left hcoord hw
      _ = b * (1 / (p.1 : ℝ)) := by ring
  change
    ((∑ p ∈ F, (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) / H) ∈
      Set.Icc a b
  constructor
  · exact (le_div_iff₀ hH).2 hLowerSum
  · exact (div_le_iff₀ hH).2 (by
      simpa only [mul_comm] using hUpperSum)

/-- On one certified cell every actual centered deviation is at most the
normalized cell width. -/
theorem abs_primeDeviation_le_cellWidth
    (E : B.PositiveCellCertificate) (j : Band)
    (p : BandPrime B.sampleData.n B.sampleData.W)
    (hp : p ∈ B.partition.data.fiber j)
    (hLowerPos : 0 < E.lower j) :
    |B.primeDeviation p| ≤
      realLogCoordinate (y B.sampleData.n) (E.upper j : ℝ) -
        realLogCoordinate (y B.sampleData.n) (E.lower j : ℝ) := by
  have hpj : B.partition.band p = j :=
    (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff
      B.partition.data).mp hp
  have hc := B.bandCenter_mem_endpointInterval E j hLowerPos
  have htLower := B.realLogCoordinate_lower_le_tPrime E j p hp hLowerPos
  have htUpper := B.tPrime_le_realLogCoordinate_upper E j p hp
  rw [primeDeviation, hpj, abs_le]
  constructor <;> linarith [hc.1, hc.2]

/-- Deterministic `L¹` bound on one cell. -/
theorem bandDeviationL1_le_cellWidth_mul_mass
    (E : B.PositiveCellCertificate) (j : Band)
    (hLowerPos : 0 < E.lower j) :
    B.bandDeviationL1 j ≤
      (realLogCoordinate (y B.sampleData.n) (E.upper j : ℝ) -
        realLogCoordinate (y B.sampleData.n) (E.lower j : ℝ)) *
          B.harmonicMass j := by
  unfold bandDeviationL1 harmonicMass
  change (∑ p ∈ B.partition.data.fiber j,
      (1 / (p.1 : ℝ)) * |B.primeDeviation p|) ≤
    _ * (∑ p ∈ B.partition.data.fiber j, 1 / (p.1 : ℝ))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hw : 0 ≤ 1 / (p.1 : ℝ) := by positivity
  calc
    (1 / (p.1 : ℝ)) * |B.primeDeviation p| ≤
        (1 / (p.1 : ℝ)) *
          (realLogCoordinate (y B.sampleData.n) (E.upper j : ℝ) -
            realLogCoordinate (y B.sampleData.n) (E.lower j : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (B.abs_primeDeviation_le_cellWidth E j p hp hLowerPos) hw
    _ = _ := by ring

/-- Deterministic quadratic upper bound on one cell. -/
theorem bandDeviationVariance_le_cellWidth_sq_mul_mass
    (E : B.PositiveCellCertificate) (j : Band)
    (hLowerPos : 0 < E.lower j) :
    B.bandDeviationVariance j ≤
      (realLogCoordinate (y B.sampleData.n) (E.upper j : ℝ) -
        realLogCoordinate (y B.sampleData.n) (E.lower j : ℝ)) ^ 2 *
          B.harmonicMass j := by
  unfold bandDeviationVariance harmonicMass
  change (∑ p ∈ B.partition.data.fiber j,
      (1 / (p.1 : ℝ)) * B.primeDeviation p ^ 2) ≤
    _ * (∑ p ∈ B.partition.data.fiber j, 1 / (p.1 : ℝ))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hw : 0 ≤ 1 / (p.1 : ℝ) := by positivity
  have habs := B.abs_primeDeviation_le_cellWidth E j p hp hLowerPos
  have hwidth : 0 ≤
      realLogCoordinate (y B.sampleData.n) (E.upper j : ℝ) -
        realLogCoordinate (y B.sampleData.n) (E.lower j : ℝ) :=
    (abs_nonneg (B.primeDeviation p)).trans habs
  have hsq : B.primeDeviation p ^ 2 ≤
      (realLogCoordinate (y B.sampleData.n) (E.upper j : ℝ) -
        realLogCoordinate (y B.sampleData.n) (E.lower j : ℝ)) ^ 2 := by
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg hwidth] using habs)
  calc
    (1 / (p.1 : ℝ)) * B.primeDeviation p ^ 2 ≤
        (1 / (p.1 : ℝ)) *
          (realLogCoordinate (y B.sampleData.n) (E.upper j : ℝ) -
            realLogCoordinate (y B.sampleData.n) (E.lower j : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hw
    _ = _ := by ring

/-- A sharper low-cell estimate: nonnegativity and exact arithmetic
centering alone give `sum |alpha-t|/p ≤ 2 H alpha`. -/
theorem bandDeviationL1_le_two_mul_mass_mul_center (j : Band) :
    B.bandDeviationL1 j ≤
      2 * B.harmonicMass j * B.bandCenter j := by
  have hfirst :
      (∑ p ∈ B.partition.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) =
        B.harmonicMass j * B.bandCenter j := by
    change (∑ p ∈ B.partition.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) =
      B.partition.data.mass j *
        ((∑ p ∈ B.partition.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) /
            B.partition.data.mass j)
    field_simp [ne_of_gt (B.partition.data.mass_pos j)]
  have hmass :
      (∑ p ∈ B.partition.data.fiber j, 1 / (p.1 : ℝ)) =
        B.harmonicMass j := by
    rfl
  unfold bandDeviationL1
  calc
    (∑ p ∈ B.partition.data.fiber j,
        (1 / (p.1 : ℝ)) * |B.primeDeviation p|) ≤
      ∑ p ∈ B.partition.data.fiber j,
        (1 / (p.1 : ℝ)) *
          (B.bandCenter j + tPrime B.sampleData.n p.1) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpj : B.partition.band p = j :=
        (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff
          B.partition.data).mp hp
      have hcenter0 := (B.bandCenter_pos j).le
      have ht0 := (B.bandPrime_tPrime_pos p).le
      rw [primeDeviation, hpj]
      exact mul_le_mul_of_nonneg_left (abs_sub_le_iff.2
        ⟨by linarith, by linarith⟩) (by positivity)
    _ = 2 * B.harmonicMass j * B.bandCenter j := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hmass, hfirst]
      ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
