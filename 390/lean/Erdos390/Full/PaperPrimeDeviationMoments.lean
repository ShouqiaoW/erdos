import Erdos390.Full.PaperBridgeQuadrature
import Erdos390.Full.PrimeCoordinateSecondMoment

/-!
# Actual prime-deviation moments in the paper bridge

This file identifies the quadratic quantity used in Lemma 8.6 with genuine
finite prime sums.  In particular, the second coordinate moment on a
certified band is not supplied as a field of a bridge certificate: it is the
literal square-coordinate prime sum, and its error follows from the proved
PNT quadrature in `PrimeCoordinateSecondMoment`.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PositiveCellTransfer KernelPrimeQuadrature
open PrimeCoordinateSecondMoment

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The literal second logarithmic-coordinate moment in one arithmetic
band. -/
def bandSecondMoment (j : Band) : ℝ :=
  ∑ p ∈ B.partition.data.fiber j,
    (1 / (p.1 : ℝ)) * (tPrime B.sampleData.n p.1) ^ 2

/-- The literal centered quadratic moment in one arithmetic band. -/
def bandDeviationVariance (j : Band) : ℝ :=
  ∑ p ∈ B.partition.data.fiber j,
    (1 / (p.1 : ℝ)) * (B.primeDeviation p) ^ 2

/-- The paper's global quadratic deviation
`V_n = sum_{W < p <= y} g_p^2 / p`. -/
def primeDeviationVariance : ℝ :=
  ∑ p : BandPrime B.sampleData.n B.sampleData.W,
    (1 / (p.1 : ℝ)) * (B.primeDeviation p) ^ 2

/-- The global literal definition agrees definitionally with the arithmetic
cell variance already used in the quotient-gap identity. -/
theorem primeDeviationVariance_eq_partition_variance :
    B.primeDeviationVariance = B.partition.variance := by
  unfold primeDeviationVariance
  change
    (∑ p : BandPrime B.sampleData.n B.sampleData.W,
      (1 / (p.1 : ℝ)) * (B.primeDeviation p) ^ 2) =
    ∑ p : BandPrime B.sampleData.n B.sampleData.W,
      (1 / (p.1 : ℝ)) *
        B.partition.data.cellDeviation p *
          B.partition.data.cellDeviation p
  apply Finset.sum_congr rfl
  intro p hp
  simp only [primeDeviation,
    Erdos390.Lemma84.WeightedBandData.cellDeviation]
  change (1 / (p.1 : ℝ)) *
      (B.bandCenter (B.partition.band p) -
        tPrime B.sampleData.n p.1) ^ 2 =
    (1 / (p.1 : ℝ)) *
      (B.bandCenter (B.partition.band p) -
        tPrime B.sampleData.n p.1) *
      (B.bandCenter (B.partition.band p) -
        tPrime B.sampleData.n p.1)
  rw [pow_two]
  ring

/-- The global quadratic deviation is the sum of its actual band
contributions. -/
theorem primeDeviationVariance_eq_sum_bandDeviationVariance :
    B.primeDeviationVariance = ∑ j : Band, B.bandDeviationVariance j := by
  unfold primeDeviationVariance bandDeviationVariance
  rw [← Finset.sum_fiberwise Finset.univ B.partition.band
    (fun p : BandPrime B.sampleData.n B.sampleData.W ↦
      (1 / (p.1 : ℝ)) * (B.primeDeviation p) ^ 2)]
  apply Finset.sum_congr rfl
  intro j hj
  rfl

/-- Exact finite variance identity on one band.  This is the arithmetic
version of centering: there is no replacement of the arithmetic center by a
continuum center. -/
theorem bandDeviationVariance_eq_second_sub_mass_center_sq (j : Band) :
    B.bandDeviationVariance j =
      B.bandSecondMoment j - B.harmonicMass j * B.bandCenter j ^ 2 := by
  have hrewrite : B.bandDeviationVariance j =
      ∑ p ∈ B.partition.data.fiber j,
        (1 / (p.1 : ℝ)) *
          (B.bandCenter j - tPrime B.sampleData.n p.1) ^ 2 := by
    unfold bandDeviationVariance
    apply Finset.sum_congr rfl
    intro p hp
    have hpj : B.partition.band p = j :=
      (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff
        B.partition.data).mp hp
    rw [primeDeviation, hpj]
  rw [hrewrite]
  unfold bandSecondMoment
  have hmass :
      (∑ p ∈ B.partition.data.fiber j, 1 / (p.1 : ℝ)) =
        B.harmonicMass j := by
    rfl
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
  calc
    (∑ p ∈ B.partition.data.fiber j,
        (1 / (p.1 : ℝ)) *
          (B.bandCenter j - tPrime B.sampleData.n p.1) ^ 2) =
        ∑ p ∈ B.partition.data.fiber j,
          ((1 / (p.1 : ℝ)) * B.bandCenter j ^ 2 -
            2 * B.bandCenter j *
              ((1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) +
            (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1 ^ 2) := by
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = (∑ p ∈ B.partition.data.fiber j, 1 / (p.1 : ℝ)) *
          B.bandCenter j ^ 2 -
        2 * B.bandCenter j *
          (∑ p ∈ B.partition.data.fiber j,
            (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) +
        ∑ p ∈ B.partition.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1 ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum]
    _ = B.bandSecondMoment j -
        B.harmonicMass j * B.bandCenter j ^ 2 := by
      rw [hmass, hfirst]
      unfold bandSecondMoment
      ring

/-- Reindex the genuine square-coordinate prime sum from a certified band to
the corresponding natural prime interval. -/
theorem bandSecondMoment_eq_cellPrimeSum
    (E : B.PositiveCellCertificate) (j : Band) :
    B.bandSecondMoment j =
      ∑ q ∈ E.cellPrimes j,
        squareCoordinate (realLogCoordinate
          (y B.sampleData.n) (q : ℝ)) / (q : ℝ) := by
  unfold bandSecondMoment
  apply Finset.sum_bij (fun p _hp ↦ p.1)
  · intro p hp
    have hpBand : B.partition.band p = j := by
      simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hp
    exact E.mem_cellPrimes_iff.mpr
      ⟨prime_of_mem_primeBand p.2, (E.band_eq_iff p j).mp hpBand⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    exact Subtype.ext heq
  · intro q hq
    have hqData := E.mem_cellPrimes_iff.mp hq
    have hqBand : q ∈ primeBand B.sampleData.n B.sampleData.W := by
      exact mem_primeBand.mpr
        ⟨hqData.1,
          (E.cutoff_le_lower j).trans_lt hqData.2.1,
          hqData.2.2.trans (E.upper_le_yNat j)⟩
    let p : BandPrime B.sampleData.n B.sampleData.W := ⟨q, hqBand⟩
    have hpFiber : p ∈ B.partition.data.fiber j := by
      simp only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff]
      exact (E.band_eq_iff p j).mpr hqData.2
    exact ⟨p, hpFiber, rfl⟩
  · intro p hp
    unfold squareCoordinate realLogCoordinate tPrime
    ring

/-- Exact endpoint identity for the actual band second moment. -/
theorem bandSecondMoment_eq_fullWeightedReciprocalSum_sub
    (E : B.PositiveCellCertificate) (j : Band) :
    B.bandSecondMoment j =
      fullWeightedReciprocalSum squareCoordinate (y B.sampleData.n)
          (E.upper j) -
        fullWeightedReciprocalSum squareCoordinate (y B.sampleData.n)
          (E.lower j) := by
  rw [B.bandSecondMoment_eq_cellPrimeSum E j]
  have hsub : PrimeSums.primesUpTo (E.lower j) ⊆
      PrimeSums.primesUpTo (E.upper j) := by
    intro p hp
    simp only [PrimeSums.primesUpTo, Finset.mem_filter,
      Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans (E.lower_le_upper j)⟩, hp.2⟩
  have hsum := Finset.sum_sdiff hsub
    (f := fun q : ℕ ↦
      squareCoordinate (realLogCoordinate
        (y B.sampleData.n) (q : ℝ)) / (q : ℝ))
  change (∑ q ∈ PrimeSums.primesUpTo (E.upper j) \
      PrimeSums.primesUpTo (E.lower j),
        squareCoordinate (realLogCoordinate
          (y B.sampleData.n) (q : ℝ)) / (q : ℝ)) = _
  exact eq_sub_of_add_eq hsum

/-- The ambient logarithmic scale used by every actual band is greater than
one. -/
theorem y_gt_one : 1 < y B.sampleData.n := by
  rw [← Real.log_pos_iff (Scale.y_pos
    (Nat.zero_lt_of_lt B.n_gt_one)).le]
  exact B.log_y_pos

/-- Unconditional second-coordinate quadrature in the actual bridge
notation, uniform over every certified band whose lower endpoint has crossed
the absolute PNT threshold. -/
theorem exists_bandSecondMoment_quadrature_bound
    (E : B.PositiveCellCertificate) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ j : Band,
      X₀ ≤ E.lower j →
      |B.bandSecondMoment j -
          ((realLogCoordinate (y B.sampleData.n) (E.upper j : ℝ)) ^ 2 -
            (realLogCoordinate (y B.sampleData.n) (E.lower j : ℝ)) ^ 2) /
            2| ≤
        3 * C /
          (Real.log (y B.sampleData.n) ^ 2 *
            Real.log (E.lower j : ℝ)) := by
  obtain ⟨C, hC, X₀, hquad⟩ :=
    exists_uniform_squarePrimeCell_error_bound
  refine ⟨C, hC, X₀, ?_⟩
  intro j hLower
  rw [B.bandSecondMoment_eq_fullWeightedReciprocalSum_sub E j]
  exact hquad (y B.sampleData.n) B.y_gt_one
    (E.lower j) (E.upper j) hLower (E.lower_le_upper j)

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
