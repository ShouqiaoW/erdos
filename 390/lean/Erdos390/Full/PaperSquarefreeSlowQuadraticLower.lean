import Erdos390.Full.PrimeSquarefreeDirichletGeometry
import Erdos390.Full.FiniteSignedQuadraticEntryTransfer
import Erdos390.Full.PaperCompensatedCoefficientBounds
import Erdos390.Full.SquarefreeReferenceOperatorIdentification
import Erdos390.Full.PaperPrimePowerRelativeQuadratic

/-!
# The literal squarefree slow lower bound

This file specializes the prime-level Dirichlet geometry to the paper's
actual compensated coefficient

`c_p = alpha_{j(p)} - t_p - q_{j(p)}`.

It proves three separate facts, so that their analytic inputs can be audited
independently:

1. the graph quotient distance is exactly the arithmetic `physicalSq`;
2. a relative finite row-residual estimate is absorbed by the literal
   compensated `L²` ledger;
3. signed entrywise squarefree-reference errors aggregate in the correct
   product-reciprocal and diagonal norms.

In particular, no squarefree variance lower bound occurs as a hypothesis.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperSquarefreeSlowQuadraticLower

open ArithmeticModel ArithmeticBandGeometry
open ArithmeticBandGeometry.Partition
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference
open SquarefreeReferenceOperatorIdentification
open PrimePowerCovariance

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
variable (P : Partition n W Band)

abbrev Prime (n W : ℕ) := PrimeIndex n W

def reciprocalWeight (p : Prime n W) : ℝ := 1 / (p.1 : ℝ)

def compensatedPrimeCoefficient
    (q : PaperWeightedInverseExport.RawGaugeSpace P.mass P.center)
    (p : Prime n W) : ℝ :=
  P.compensatedCoefficient q p

/-- The genuine squarefree covariance quadratic, indexed by the actual
prime subtype. -/
def subtypeSquarefreeQuadratic {Omega : Type*} [Fintype Omega] {M : ℕ}
    (law : BoundedValuationLaw Omega M) (c : Prime n W → ℝ) : ℝ :=
  matrixQuadratic (fun p r ↦ law.covII p.1 r.1) c

theorem weightedL1_compensated_eq
    (q : PaperWeightedInverseExport.RawGaugeSpace P.mass P.center) :
    weightedL1 (reciprocalWeight (n := n) (W := W))
        (compensatedPrimeCoefficient P q) =
      P.compensatedL1 q := by
  rfl

theorem weightedL2Sq_compensated_eq
    (q : PaperWeightedInverseExport.RawGaugeSpace P.mass P.center) :
    weightedL2Sq (reciprocalWeight (n := n) (W := W))
        (compensatedPrimeCoefficient P q) =
      P.compensatedL2Sq q := by
  rfl

/-- The second reciprocal diagonal costs one explicit cutoff factor. -/
theorem weightedL2SqSecond_le_invCutoff_mul_weightedL2Sq
    (hW : 0 < W) (c : Prime n W → ℝ) :
    weightedL2SqSecond (reciprocalWeight (n := n) (W := W)) c ≤
      (1 / (W : ℝ)) *
        weightedL2Sq (reciprocalWeight (n := n) (W := W)) c := by
  unfold weightedL2SqSecond weightedL2Sq reciprocalWeight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hWp : (W : ℝ) ≤ (p.1 : ℝ) := by
    exact_mod_cast (cutoff_lt_of_mem_primeBand p.2).le
  have hinv : 1 / (p.1 : ℝ) ≤ 1 / (W : ℝ) :=
    one_div_le_one_div_of_le hWR hWp
  have hrecip : 0 ≤ 1 / (p.1 : ℝ) := by positivity
  have hsq : 0 ≤ c p ^ 2 := sq_nonneg _
  calc
    (1 / (p.1 : ℝ)) ^ 2 * c p ^ 2 =
        (1 / (p.1 : ℝ)) * ((1 / (p.1 : ℝ)) * c p ^ 2) := by ring
    _ ≤ (1 / (W : ℝ)) * ((1 / (p.1 : ℝ)) * c p ^ 2) :=
      mul_le_mul_of_nonneg_right hinv (mul_nonneg hrecip hsq)
    _ = (1 / (W : ℝ)) * (1 / (p.1 : ℝ) * c p ^ 2) := by ring

/-- The graph distance of the compensated coefficient is the exact finite
arithmetic physical distance, with the harmless shift `mu ↦ mu+1`. -/
theorem primePhysicalDistance_compensated_eq_physicalSq
    (q : PaperWeightedInverseExport.RawGaugeSpace P.mass P.center)
    (mu : ℝ) :
    primePhysicalDistance n (compensatedPrimeCoefficient P q) mu =
      P.data.physicalSq (fun j ↦ -q.1 j + P.center j) (mu + 1) := by
  unfold primePhysicalDistance compensatedPrimeCoefficient
    Erdos390.Lemma84.WeightedBandData.physicalSq
    Erdos390.Lemma84.WeightedBandData.primeNormSq
    Erdos390.Lemma84.WeightedBandData.primeInner
    Erdos390.Lemma84.WeightedBandData.residual
    Erdos390.Lemma84.WeightedBandData.lift
    compensatedCoefficient regressionCoefficient
  apply Finset.sum_congr rfl
  intro p hp
  change (1 / (p.1 : ℝ)) *
      (P.center (P.band p) - tPrime n p.1 - q.1 (P.band p) -
        mu * tPrime n p.1) ^ 2 =
    (1 / (p.1 : ℝ)) *
      ((-q.1 (P.band p) + P.center (P.band p)) -
        (mu + 1) * tPrime n p.1) *
      ((-q.1 (P.band p) + P.center (P.band p)) -
        (mu + 1) * tPrime n p.1)
  ring

/-- The exact arithmetic completion of squares applies at the anchor mean,
or indeed at any scalar representative of the scale-null direction. -/
theorem half_variance_le_primePhysicalDistance_compensated
    [Nonempty Band] (hn : 1 < n)
    (q : PaperWeightedInverseExport.RawGaugeSpace P.mass P.center)
    (mu : ℝ) (hvariance : P.variance ≤ P.centerEnergy) :
    P.variance / 2 ≤
      primePhysicalDistance n (compensatedPrimeCoefficient P q) mu := by
  rw [primePhysicalDistance_compensated_eq_physicalSq P q mu]
  simpa only [neg_neg] using
    P.half_variance_le_physicalSq_rawGauge hn (-q) (mu + 1) hvariance

/-- A row residual of size `rowError * t_p` contributes at most
`rowError * sum_p c_p²/p`.  This is the relative estimate needed in the
moving low cell: an additive `o(1)` row bound would not suffice. -/
theorem abs_primeRowResidualContribution_le
    (hn : 1 < n)
    (q : PaperWeightedInverseExport.RawGaugeSpace P.mass P.center)
    {rowError : ℝ}
    (hrow : ∀ p : Prime n W,
      |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
        rowError * tPrime n p.1) :
    |∑ p, primeWeight n p *
        rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p *
          (dirichletCoordinate n (compensatedPrimeCoefficient P q) p) ^ 2| ≤
      rowError * P.compensatedL2Sq q := by
  simpa only [primeCoefficientL2Sq, compensatedPrimeCoefficient,
    compensatedL2Sq] using
      (PrimeSquarefreeDirichletGeometry.abs_rowResidualContribution_le
        hn (compensatedPrimeCoefficient P q) hrow)

/-- The reference quadratic has a genuine slow lower bound, derived from
the exact arithmetic physical gap and the explicit finite row residual.
The conclusion is uniform in the fitted raw-gauge vector `q`. -/
theorem exists_primeReference_compensated_lower
    [Nonempty Band] (hn : 1 < n)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2)
    (anchor : Finset (Prime n W))
    (hinterior : ∀ p ∈ anchor,
      tPrime n p.1 ∈ Icc epsilon (1 - epsilon))
    (hmass : 0 < anchorMass (primeWeight n) anchor)
    {rowError : ℝ}
    (hrow : ∀ p : Prime n W,
      |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
        rowError * tPrime n p.1)
    (hvariance : P.variance ≤ P.centerEnergy) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ q : PaperWeightedInverseExport.RawGaugeSpace P.mass P.center,
        (kappa / 4) * anchorMass (primeWeight n) anchor * P.variance -
            rowError * P.compensatedL2Sq q ≤
          primeReferenceQuadratic n (compensatedPrimeCoefficient P q) := by
  obtain ⟨kappa, hkappa, henergy⟩ :=
    exists_primeDirichlet_anchor_lower hn hepsilon hhalf anchor hinterior hmass
  refine ⟨kappa, hkappa, ?_⟩
  intro q
  let c : Prime n W → ℝ := compensatedPrimeCoefficient P q
  let mu : ℝ := anchorMean n anchor c
  have hdistance : P.variance / 2 ≤ primePhysicalDistance n c mu := by
    exact half_variance_le_primePhysicalDistance_compensated P
      hn q mu hvariance
  have hcoef : 0 ≤ (kappa / 2) * anchorMass (primeWeight n) anchor :=
    mul_nonneg (div_nonneg hkappa.le (by norm_num)) hmass.le
  have hscaled := mul_le_mul_of_nonneg_left hdistance hcoef
  have henergyLower :
      (kappa / 4) * anchorMass (primeWeight n) anchor * P.variance ≤
        dirichletEnergy (primeWeight n) (primeKernel n)
          (dirichletCoordinate n c) := by
    calc
      (kappa / 4) * anchorMass (primeWeight n) anchor * P.variance =
          ((kappa / 2) * anchorMass (primeWeight n) anchor) *
            (P.variance / 2) := by ring
      _ ≤ ((kappa / 2) * anchorMass (primeWeight n) anchor) *
            primePhysicalDistance n c mu := hscaled
      _ ≤ dirichletEnergy (primeWeight n) (primeKernel n)
            (dirichletCoordinate n c) := henergy c
  have hresAbs := abs_primeRowResidualContribution_le P hn q hrow
  have hresLower :
      -(rowError * P.compensatedL2Sq q) ≤
        ∑ p, primeWeight n p *
          rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p *
            (dirichletCoordinate n c p) ^ 2 :=
    neg_le_of_abs_le (by simpa only [c] using hresAbs)
  rw [primeReferenceQuadratic_eq_dirichlet_add_residual hn c]
  linarith

/-- The separated reference quadratic is exactly the matrix quadratic of
the signed reference entries used in the squarefree profile theorem. -/
theorem matrixQuadratic_squarefreeReferenceEntry_eq_primeReference
    (c : Prime n W → ℝ) :
    matrixQuadratic
        (fun p r : Prime n W ↦ squarefreeReferenceEntry n p.1 r.1) c =
      primeReferenceQuadratic n c := by
  change primeReferenceEntryQuadratic n c = primeReferenceQuadratic n c
  exact (primeReferenceQuadratic_eq_entryQuadratic c).symm

/-- Signed entrywise profile estimates aggregate to a quantitative
squarefree-reference quadratic estimate. -/
theorem abs_subtypeSquarefreeQuadratic_sub_primeReference_le
    {Omega : Type*} [Fintype Omega] {M : ℕ}
    (law : BoundedValuationLaw Omega M) (c : Prime n W → ℝ)
    {epsilonOff epsilonDiag epsilonSecond : ℝ}
    (hentry : ∀ p r : Prime n W,
      |law.covII p.1 r.1 - squarefreeReferenceEntry n p.1 r.1| ≤
        epsilonOff * reciprocalWeight p * reciprocalWeight r +
          if p = r then
            epsilonDiag * reciprocalWeight p +
              epsilonSecond * reciprocalWeight p ^ 2
          else 0) :
    |subtypeSquarefreeQuadratic law c - primeReferenceQuadratic n c| ≤
      epsilonOff * weightedL1 (reciprocalWeight (n := n) (W := W)) c ^ 2 +
        epsilonDiag * weightedL2Sq
          (reciprocalWeight (n := n) (W := W)) c +
        epsilonSecond * weightedL2SqSecond
          (reciprocalWeight (n := n) (W := W)) c := by
  unfold subtypeSquarefreeQuadratic
  rw [← matrixQuadratic_squarefreeReferenceEntry_eq_primeReference]
  exact abs_matrixQuadratic_sub_le
    (fun p r : Prime n W ↦ law.covII p.1 r.1)
    (fun p r : Prime n W ↦ squarefreeReferenceEntry n p.1 r.1)
    (reciprocalWeight (n := n) (W := W)) c hentry

/-- A uniform bound for `F` and the signed Dickman kernel gives a completely
explicit upper bound for the finite reference quadratic. -/
theorem abs_primeReferenceQuadratic_le
    (c : Prime n W → ℝ) {CF CKernel : ℝ}
    (hF : ∀ p : Prime n W, |DickmanBasic.F (tPrime n p.1)| ≤ CF)
    (hKernel : ∀ p r : Prime n W,
      |ConditionedPoissonLimit.covarianceKernel
        (tPrime n p.1) (tPrime n r.1)| ≤ CKernel) :
    |primeReferenceQuadratic n c| ≤
      CKernel * weightedL1 reciprocalWeight c ^ 2 +
        CF * weightedL2Sq reciprocalWeight c := by
  have hentry : ∀ p r : Prime n W,
      |squarefreeReferenceEntry n p.1 r.1 - 0| ≤
        CKernel * reciprocalWeight p * reciprocalWeight r +
          if p = r then CF * reciprocalWeight p + 0 * reciprocalWeight p ^ 2
          else 0 := by
    intro p r
    have hpR : (0 : ℝ) < p.1 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos
    have hrR : (0 : ℝ) < r.1 := by
      exact_mod_cast (prime_of_mem_primeBand r.2).pos
    by_cases hpr : p = r
    · subst r
      rw [if_pos rfl, sub_zero]
      unfold squarefreeReferenceEntry squarefreeKernelEntry reciprocalWeight
      rw [if_pos rfl]
      calc
        |DickmanBasic.F (tPrime n p.1) / (p.1 : ℝ) +
            ConditionedPoissonLimit.covarianceKernel
              (tPrime n p.1) (tPrime n p.1) /
                ((p.1 : ℝ) * (p.1 : ℝ))| ≤
            |DickmanBasic.F (tPrime n p.1) / (p.1 : ℝ)| +
              |ConditionedPoissonLimit.covarianceKernel
                (tPrime n p.1) (tPrime n p.1) /
                  ((p.1 : ℝ) * (p.1 : ℝ))| := abs_add_le _ _
        _ ≤ CF * (1 / (p.1 : ℝ)) +
              CKernel * (1 / (p.1 : ℝ)) * (1 / (p.1 : ℝ)) := by
          rw [abs_div, abs_of_pos hpR, abs_div,
            abs_of_pos (mul_pos hpR hpR)]
          calc
            |DickmanBasic.F (tPrime n p.1)| / (p.1 : ℝ) +
                |ConditionedPoissonLimit.covarianceKernel
                  (tPrime n p.1) (tPrime n p.1)| /
                    ((p.1 : ℝ) * (p.1 : ℝ)) ≤
              CF / (p.1 : ℝ) + CKernel / ((p.1 : ℝ) * (p.1 : ℝ)) :=
                add_le_add
                  (div_le_div_of_nonneg_right (hF p) hpR.le)
                  (div_le_div_of_nonneg_right (hKernel p p)
                    (mul_nonneg hpR.le hpR.le))
            _ = CF * (1 / (p.1 : ℝ)) +
                CKernel * (1 / (p.1 : ℝ)) * (1 / (p.1 : ℝ)) := by
              field_simp [ne_of_gt hpR]
        _ = CKernel * (1 / (p.1 : ℝ)) * (1 / (p.1 : ℝ)) +
              (CF * (1 / (p.1 : ℝ)) + 0 * (1 / (p.1 : ℝ)) ^ 2) := by
          ring
    · rw [if_neg hpr, sub_zero]
      have hval : p.1 ≠ r.1 := by
        intro h
        exact hpr (Subtype.ext h)
      unfold squarefreeReferenceEntry squarefreeKernelEntry reciprocalWeight
      rw [if_neg hval, abs_div, abs_of_pos (mul_pos hpR hrR)]
      calc
        |ConditionedPoissonLimit.covarianceKernel
            (tPrime n p.1) (tPrime n r.1)| /
              ((p.1 : ℝ) * (r.1 : ℝ)) ≤
            CKernel / ((p.1 : ℝ) * (r.1 : ℝ)) :=
          div_le_div_of_nonneg_right (hKernel p r)
            (mul_nonneg hpR.le hrR.le)
        _ = CKernel * (1 / (p.1 : ℝ)) * (1 / (r.1 : ℝ)) + 0 := by
          field_simp [ne_of_gt hpR, ne_of_gt hrR]
          ring
  have hbound := abs_matrixQuadratic_sub_le
    (fun p r : Prime n W ↦ squarefreeReferenceEntry n p.1 r.1)
    (fun _p _r : Prime n W ↦ 0) reciprocalWeight c hentry
  rw [matrixQuadratic_squarefreeReferenceEntry_eq_primeReference] at hbound
  simpa [matrixQuadratic] using hbound

end Erdos390.Full.PaperSquarefreeSlowQuadraticLower
