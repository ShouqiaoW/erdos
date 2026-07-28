import Erdos390.Full.PrimeSquarefreeDirichletGeometry
import Erdos390.Full.PaperCompensatedCoefficientBounds

/-!
# General band-vector Dirichlet gap

This is the quadratic-form part of the arithmetic bridge for an arbitrary
raw-gauge band vector.  It is deliberately separate from the compensated
slow coefficient used later in Lemma 8.6.  A band vector is lifted literally
to every prime in its cell; its reciprocal prime square norm is exactly the
`D`-norm, and its physical quotient distance dominates that norm by the
exact arithmetic centering identity.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperBandQuadraticGeometry

open ArithmeticBandGeometry
open ArithmeticBandGeometry.Partition
open ArithmeticModel
open PaperWeightedInverseExport
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]

/-- Literal prime lift of an arbitrary band coefficient. -/
def liftBandCoefficient (P : Partition n W Band) (q : Band → ℝ)
    (p : PrimeIndex n W) : ℝ := q (P.band p)

/-- Every literal reciprocal prime square norm is the corresponding
`WeightedBandData` prime norm. -/
theorem primeCoefficientL2Sq_eq_data_primeNormSq
    (P : Partition n W Band) (c : PrimeIndex n W → ℝ) :
    primeCoefficientL2Sq c = P.data.primeNormSq c := by
  unfold primeCoefficientL2Sq
    Erdos390.Lemma84.WeightedBandData.primeNormSq
    Erdos390.Lemma84.WeightedBandData.primeInner
  apply Finset.sum_congr rfl
  intro p hp
  change (1 / (p.1 : ℝ)) * c p ^ 2 =
    (1 / (p.1 : ℝ)) * c p * c p
  ring

/-- The literal physical distance is the weighted prime norm after
subtracting the same arithmetic logarithmic coordinate. -/
theorem primePhysicalDistance_eq_data_primeNormSq
    (P : Partition n W Band) (c : PrimeIndex n W → ℝ) (mu : ℝ) :
    primePhysicalDistance n c mu =
      P.data.primeNormSq (fun p ↦ c p - mu * P.data.coord p) := by
  unfold primePhysicalDistance
    Erdos390.Lemma84.WeightedBandData.primeNormSq
    Erdos390.Lemma84.WeightedBandData.primeInner
  apply Finset.sum_congr rfl
  intro p hp
  change (1 / (p.1 : ℝ)) * (c p - mu * tPrime n p.1) ^ 2 =
    (1 / (p.1 : ℝ)) * (c p - mu * tPrime n p.1) *
      (c p - mu * tPrime n p.1)
  ring

/-- The reciprocal prime square norm of a band lift is exactly its
arithmetic `D`-norm. -/
theorem primeCoefficientL2Sq_liftBandCoefficient
    (P : Partition n W Band) (q : Band → ℝ) :
    primeCoefficientL2Sq (liftBandCoefficient P q) = P.data.bandNormSq q := by
  have hlift :
      primeCoefficientL2Sq (liftBandCoefficient P q) =
        P.data.primeNormSq (P.data.lift q) := by
    unfold primeCoefficientL2Sq liftBandCoefficient
      Erdos390.Lemma84.WeightedBandData.primeNormSq
      Erdos390.Lemma84.WeightedBandData.primeInner
      Erdos390.Lemma84.WeightedBandData.lift
    apply Finset.sum_congr rfl
    intro p hp
    change (1 / (p.1 : ℝ)) * q (P.band p) ^ 2 =
      (1 / (p.1 : ℝ)) * q (P.band p) * q (P.band p)
    ring
  rw [hlift]
  simpa [Erdos390.Lemma84.WeightedBandData.primeNormSq,
    Erdos390.Lemma84.WeightedBandData.bandNormSq] using
      P.data.primeInner_lifts q q

/-- Subtracting the exact arithmetic least-squares physical direction
makes the prime coefficient orthogonal to `t`.  Hence every subsequent
constant representative in the conjugated Dirichlet coordinate can only
increase its reciprocal prime square norm. -/
theorem primeCoefficientL2Sq_le_physicalDistance_residualMinimizer
    [Nonempty Band]
    (P : Partition n W Band) (hn : 1 < n)
    (b : Band → ℝ) (nu : ℝ) :
    primeCoefficientL2Sq
        (P.data.residual b (P.data.physicalMinimizer b)) ≤
      primePhysicalDistance n
        (P.data.residual b (P.data.physicalMinimizer b)) nu := by
  let c : PrimeIndex n W → ℝ :=
    P.data.residual b (P.data.physicalMinimizer b)
  have hvariance : 0 ≤ P.variance :=
    P.data.primeNormSq_nonneg P.data.cellDeviation
  have hcoordPos : 0 < P.data.coordEnergy := by
    rw [P.data.coordEnergy_eq]
    exact add_pos_of_pos_of_nonneg (P.centerEnergy_pos hn) hvariance
  have hnormal : P.data.primeInner P.data.coord c = 0 := by
    simpa only [c] using
      P.data.physicalMinimizer_normal b hcoordPos.ne'
  have hnormal' : P.data.primeInner c P.data.coord = 0 := by
    rw [P.data.primeInner_comm]
    exact hnormal
  have hexpand :
      P.data.primeNormSq (fun p ↦ c p - nu * P.data.coord p) =
        P.data.primeNormSq c + nu ^ 2 * P.data.coordEnergy := by
    have hfun : (fun p ↦ c p - nu * P.data.coord p) =
        fun p ↦ c p + (-nu) * P.data.coord p := by
      funext p
      ring
    rw [hfun, P.data.primeNormSq_add, P.data.primeNormSq_smul,
      P.data.primeInner_smul_right, hnormal']
    unfold Erdos390.Lemma84.WeightedBandData.coordEnergy
    ring
  rw [primeCoefficientL2Sq_eq_data_primeNormSq P,
    primePhysicalDistance_eq_data_primeNormSq P, hexpand]
  exact le_add_of_nonneg_right
    (mul_nonneg (sq_nonneg _) (P.data.primeNormSq_nonneg P.data.coord))

/-- The prime quotient distance of the literal lift is the exact arithmetic
physical square from the finite weighted-band data. -/
theorem primePhysicalDistance_liftBandCoefficient
    (P : Partition n W Band) (q : Band → ℝ) (mu : ℝ) :
    primePhysicalDistance n (liftBandCoefficient P q) mu =
      P.data.physicalSq q mu := by
  unfold primePhysicalDistance liftBandCoefficient
    Erdos390.Lemma84.WeightedBandData.physicalSq
    Erdos390.Lemma84.WeightedBandData.primeNormSq
    Erdos390.Lemma84.WeightedBandData.primeInner
    Erdos390.Lemma84.WeightedBandData.residual
    Erdos390.Lemma84.WeightedBandData.lift
  apply Finset.sum_congr rfl
  intro p hp
  change (1 / (p.1 : ℝ)) * (q (P.band p) - mu * tPrime n p.1) ^ 2 =
    (1 / (p.1 : ℝ)) * (q (P.band p) - mu * tPrime n p.1) *
      (q (P.band p) - mu * tPrime n p.1)
  ring

/-- Exact arithmetic gauge centering implies that every physical scalar
representative stays at least one `D`-norm away. -/
theorem bandNormSq_le_primePhysicalDistance
    (P : Partition n W Band)
    (q : RawGaugeSpace P.mass P.center) (mu : ℝ) :
    P.data.bandNormSq q.1 ≤
      primePhysicalDistance n (liftBandCoefficient P q.1) mu := by
  rw [primePhysicalDistance_liftBandCoefficient]
  simpa only [zero_mul, add_zero] using
    P.physicalSq_ge_gauge q.1 0 mu (P.rawGauge_inGauge q)

/-- The squarefree reference form has a structural `D`-gap after paying
only the explicitly relative row residual.  Neither an inverse nor a
quadratic gap is an input. -/
theorem exists_primeReference_band_lower
    [Nonempty Band]
    (P : Partition n W Band) (hn : 1 < n)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2)
    (anchor : Finset (PrimeIndex n W))
    (hinterior : ∀ p ∈ anchor,
      tPrime n p.1 ∈ Icc epsilon (1 - epsilon))
    (hmass : 0 < anchorMass (primeWeight n) anchor)
    {rowError : ℝ}
    (hrow : ∀ p : PrimeIndex n W,
      |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
        rowError * tPrime n p.1) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ q : RawGaugeSpace P.mass P.center,
        ((kappa / 2) * anchorMass (primeWeight n) anchor - rowError) *
            P.data.bandNormSq q.1 ≤
          primeReferenceQuadratic n (liftBandCoefficient P q.1) := by
  obtain ⟨kappa, hkappa, henergy⟩ :=
    exists_primeDirichlet_anchor_lower hn hepsilon hhalf anchor hinterior hmass
  refine ⟨kappa, hkappa, ?_⟩
  intro q
  let c : PrimeIndex n W → ℝ := liftBandCoefficient P q.1
  let mu : ℝ := anchorMean n anchor c
  have hdistance : P.data.bandNormSq q.1 ≤ primePhysicalDistance n c mu := by
    simpa only [c] using bandNormSq_le_primePhysicalDistance P q mu
  have hcoef : 0 ≤ (kappa / 2) * anchorMass (primeWeight n) anchor :=
    mul_nonneg (div_nonneg hkappa.le (by norm_num)) hmass.le
  have hdistanceScaled := mul_le_mul_of_nonneg_left hdistance hcoef
  have henergyLower :
      ((kappa / 2) * anchorMass (primeWeight n) anchor) *
          P.data.bandNormSq q.1 ≤
        dirichletEnergy (primeWeight n) (primeKernel n)
          (dirichletCoordinate n c) := by
    exact hdistanceScaled.trans (henergy c)
  have hresidualAbs :=
    abs_rowResidualContribution_le hn c hrow
  have hresidualAbs' :
      |∑ p, primeWeight n p *
          rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p *
            (dirichletCoordinate n c p) ^ 2| ≤
        rowError * P.data.bandNormSq q.1 := by
    simpa only [c, primeCoefficientL2Sq_liftBandCoefficient] using hresidualAbs
  have hresidualLower := neg_le_of_abs_le hresidualAbs'
  rw [primeReferenceQuadratic_eq_dirichlet_add_residual hn c]
  have hbandNonneg : 0 ≤ P.data.bandNormSq q.1 := P.data.bandNormSq_nonneg q.1
  nlinarith

/-- Full arithmetic quotient version.  For an arbitrary band vector `b`,
we subtract its exact finite-prime least-squares logarithmic direction
before applying the reference form.  The row-residual loss is therefore
measured in that same minimizing physical norm, not in the potentially
much larger norm of `b`.  Once the relative row error is smaller than the
explicit anchor gap, the resulting coefficient controls the literal
arithmetic `D`-distance of `b` from the center direction. -/
theorem exists_primeReference_fullQuotient_lower
    [Nonempty Band]
    (P : Partition n W Band) (hn : 1 < n)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2)
    (anchor : Finset (PrimeIndex n W))
    (hinterior : ∀ p ∈ anchor,
      tPrime n p.1 ∈ Icc epsilon (1 - epsilon))
    (hmass : 0 < anchorMass (primeWeight n) anchor)
    {rowError : ℝ}
    (hrow : ∀ p : PrimeIndex n W,
      |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
        rowError * tPrime n p.1) :
    ∃ kappa : ℝ, 0 < kappa ∧
      (rowError ≤ (kappa / 2) * anchorMass (primeWeight n) anchor →
        ∀ b : Band → ℝ,
          ((kappa / 2) * anchorMass (primeWeight n) anchor - rowError) *
              P.data.bandNormSq (P.data.gaugePart b) ≤
            primeReferenceQuadratic n
              (P.data.residual b (P.data.physicalMinimizer b))) := by
  obtain ⟨kappa, hkappa, henergy⟩ :=
    exists_primeDirichlet_anchor_lower hn hepsilon hhalf anchor hinterior hmass
  refine ⟨kappa, hkappa, ?_⟩
  intro hsmall b
  let c : PrimeIndex n W → ℝ :=
    P.data.residual b (P.data.physicalMinimizer b)
  let A : ℝ := (kappa / 2) * anchorMass (primeWeight n) anchor
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (div_nonneg hkappa.le (by norm_num)) hmass.le
  have hcoefficient : 0 ≤ A - rowError := sub_nonneg.mpr (by
    simpa only [A] using hsmall)
  have hdistance :
      primeCoefficientL2Sq c ≤
        primePhysicalDistance n c (anchorMean n anchor c) := by
    simpa only [c] using
      primeCoefficientL2Sq_le_physicalDistance_residualMinimizer P hn b
        (anchorMean n anchor c)
  have henergyLower :
      A * primeCoefficientL2Sq c ≤
        dirichletEnergy (primeWeight n) (primeKernel n)
          (dirichletCoordinate n c) := by
    have hscaled := mul_le_mul_of_nonneg_left hdistance hA
    exact hscaled.trans (by simpa only [A] using henergy c)
  have hresidualAbs := abs_rowResidualContribution_le hn c hrow
  have hresidualLower :
      -(rowError * primeCoefficientL2Sq c) ≤
        ∑ p, primeWeight n p *
          rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p *
            (dirichletCoordinate n c p) ^ 2 :=
    neg_le_of_abs_le hresidualAbs
  have hreference :
      (A - rowError) * primeCoefficientL2Sq c ≤
        primeReferenceQuadratic n c := by
    rw [primeReferenceQuadratic_eq_dirichlet_add_residual hn c]
    linarith
  let q : Band → ℝ := P.data.gaugePart b
  let lambda : ℝ := P.data.gaugeCoefficient b
  have hq : P.data.inGauge q := by
    simpa only [q] using P.data.gaugePart_inGauge b
      (P.centerEnergy_pos hn).ne'
  have hdecomp : (fun j ↦ q j + lambda * P.center j) = b := by
    funext j
    exact P.data.gauge_decomposition b j
  have hvariance : 0 ≤ P.variance :=
    P.data.primeNormSq_nonneg P.data.cellDeviation
  have hbandPhysical :
      P.data.bandNormSq q ≤
        P.data.physicalSq b (P.data.physicalMinimizer b) := by
    have h := P.data.physical_lower_bound q lambda hq hvariance
    rw [hdecomp] at h
    exact h
  have hcoefficientPhysical :
      primeCoefficientL2Sq c =
        P.data.physicalSq b (P.data.physicalMinimizer b) := by
    rw [primeCoefficientL2Sq_eq_data_primeNormSq P]
    rfl
  have hbandCoefficient :
      P.data.bandNormSq q ≤ primeCoefficientL2Sq c := by
    rw [hcoefficientPhysical]
    exact hbandPhysical
  calc
    ((kappa / 2) * anchorMass (primeWeight n) anchor - rowError) *
          P.data.bandNormSq (P.data.gaugePart b) =
        (A - rowError) * P.data.bandNormSq q := by rfl
    _ ≤ (A - rowError) * primeCoefficientL2Sq c :=
      mul_le_mul_of_nonneg_left hbandCoefficient hcoefficient
    _ ≤ primeReferenceQuadratic n c := hreference

end Erdos390.Full.PaperBandQuadraticGeometry
