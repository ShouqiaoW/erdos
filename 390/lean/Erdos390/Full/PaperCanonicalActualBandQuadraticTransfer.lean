import Erdos390.Full.PaperBandQuadraticGeometry
import Erdos390.Full.PaperActualSquarefreeSlowLower
import Erdos390.Full.PaperActualSchurMarkedRow
import Erdos390.Full.PaperExactSchurTwoStageQuadratic
import Erdos390.Full.PaperCanonicalSlowKappa

/-!
# Fixed-kappa actual band and nuisance-Schur gaps

This file is the fixed-constant counterpart of the existential quadratic
transfer in `PaperActualBandQuadraticTransfer`.  The structural constant is
the single continuum constant `PaperCanonicalSlowKappa.canonicalSlowKappa`;
it is therefore selected before the arithmetic mesh, the cutoff, and every
finite-`n` law.  All finite row, signed-profile, prime-power, and nuisance
losses remain displayed as coefficients of the literal arithmetic `D`-norm.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperCanonicalActualBandQuadraticTransfer

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open PaperBandQuadraticGeometry
open PaperCanonicalSlowKappa
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open FiniteSignedQuadraticEntryTransfer
open PaperSquarefreeSlowQuadraticLower
open SquarefreeCovarianceReference

variable {Omega : Type*} [Fintype Omega] {M n W : ℕ}
variable {Band : Type*} [Fintype Band] [DecidableEq Band]

/-- Full-valuation covariance quadratic on the literal prime subtype. -/
def subtypeFullQuadratic (law : BoundedValuationLaw Omega M)
    (c : PrimeIndex n W → ℝ) : ℝ :=
  matrixQuadratic (fun p r ↦ law.covVV p.1 r.1) c

theorem covarianceDifference_symm (law : BoundedValuationLaw Omega M)
    (p r : PrimeIndex n W) :
    law.covVV p.1 r.1 - law.covII p.1 r.1 =
      law.covVV r.1 p.1 - law.covII r.1 p.1 := by
  unfold covVV covII
  rw [law.probability.covariance_comm (law.V p.1) (law.V r.1),
    law.probability.covariance_comm (law.I p.1) (law.I r.1)]

/-- A literal normalized weighted row controls every symmetric coefficient
in the reciprocal-prime square norm. -/
theorem abs_subtypeFull_sub_squarefree_le_of_weightedRow
    (P : Partition n W Band)
    (law : BoundedValuationLaw Omega M)
    (c : PrimeIndex n W → ℝ) {R : ℝ}
    (hrow : ∀ p : PrimeIndex n W,
      (p.1 : ℝ) * ∑ r : PrimeIndex n W,
        |law.covVV p.1 r.1 - law.covII p.1 r.1| ≤ R) :
    |subtypeFullQuadratic law c - subtypeSquarefreeQuadratic law c| ≤
      R * primeCoefficientL2Sq c := by
  let E : PrimeIndex n W → PrimeIndex n W → ℝ :=
    fun p r ↦ law.covVV p.1 r.1 - law.covII p.1 r.1
  have hsymm : ∀ p r, E p r = E r p := by
    intro p r
    exact covarianceDifference_symm law p r
  have hrow' : ∀ p : PrimeIndex n W,
      (∑ r : PrimeIndex n W, |E p r|) ≤ R * P.data.weight p := by
    intro p
    have hp : (0 : ℝ) < (p.1 : ℝ) := by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos
    calc
      (∑ r : PrimeIndex n W, |E p r|) ≤ R / (p.1 : ℝ) :=
        (le_div_iff₀ hp).2 (by simpa only [mul_comm] using hrow p)
      _ = R * P.data.weight p := by
        simp only [Partition.data, div_eq_mul_inv, one_mul]
  have hquad := P.data.symmetric_prime_row_quadratic_error
    E c R hsymm hrow'
  have hidentify :
      Erdos390.Lemma84.WeightedBandData.primeQuadratic E c =
        subtypeFullQuadratic law c - subtypeSquarefreeQuadratic law c := by
    unfold Erdos390.Lemma84.WeightedBandData.primeQuadratic
      subtypeFullQuadratic subtypeSquarefreeQuadratic matrixQuadratic E
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [hidentify] at hquad
  simpa only [primeCoefficientL2Sq_eq_data_primeNormSq P] using hquad

/-- Weighted Cauchy--Schwarz for reciprocal prime coefficients. -/
theorem weightedL1_sq_le_totalWeight_mul_weightedL2Sq
    (c : PrimeIndex n W → ℝ) :
    weightedL1 (reciprocalWeight (n := n) (W := W)) c ^ 2 ≤
      (∑ p : PrimeIndex n W, reciprocalWeight p) *
        weightedL2Sq reciprocalWeight c := by
  let a : PrimeIndex n W → ℝ :=
    fun p ↦ Real.sqrt (reciprocalWeight p)
  let b : PrimeIndex n W → ℝ :=
    fun p ↦ Real.sqrt (reciprocalWeight p) * |c p|
  have hw (p : PrimeIndex n W) : 0 ≤ reciprocalWeight p := by
    unfold reciprocalWeight
    positivity
  have hsqa (p : PrimeIndex n W) : a p ^ 2 = reciprocalWeight p := by
    dsimp only [a]
    rw [Real.sq_sqrt (hw p)]
  have hsqb (p : PrimeIndex n W) : b p ^ 2 =
      reciprocalWeight p * c p ^ 2 := by
    dsimp only [b]
    rw [mul_pow, Real.sq_sqrt (hw p), sq_abs]
  have hab (p : PrimeIndex n W) : a p * b p =
      reciprocalWeight p * |c p| := by
    dsimp only [a, b]
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (hw p)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  simp_rw [hab, hsqa, hsqb] at hcs
  simpa only [weightedL1, weightedL2Sq] using hcs

/-- Signed squarefree-reference errors are relative to the reciprocal-prime
square norm, including the moving low prime range. -/
theorem abs_squarefree_sub_reference_le_relative
    (law : BoundedValuationLaw Omega M)
    (c : PrimeIndex n W → ℝ)
    {epsilonOff epsilonDiag epsilonSecond totalWeight invW : ℝ}
    (hOff : 0 ≤ epsilonOff) (hSecond : 0 ≤ epsilonSecond)
    (hW : 0 < W)
    (hTotal : (∑ p : PrimeIndex n W, reciprocalWeight p) ≤ totalWeight)
    (hInvW : (1 / (W : ℝ)) ≤ invW)
    (hentry : ∀ p r : PrimeIndex n W,
      |law.covII p.1 r.1 - squarefreeReferenceEntry n p.1 r.1| ≤
        epsilonOff * reciprocalWeight p * reciprocalWeight r +
          if p = r then
            epsilonDiag * reciprocalWeight p +
              epsilonSecond * reciprocalWeight p ^ 2
          else 0) :
    |subtypeSquarefreeQuadratic law c - primeReferenceQuadratic n c| ≤
      (epsilonOff * totalWeight + epsilonDiag + epsilonSecond * invW) *
        primeCoefficientL2Sq c := by
  have hbase := abs_subtypeSquarefreeQuadratic_sub_primeReference_le
    law c hentry
  have hL1 := weightedL1_sq_le_totalWeight_mul_weightedL2Sq c
  have htotalNonneg : 0 ≤ ∑ p : PrimeIndex n W, reciprocalWeight p := by
    apply Finset.sum_nonneg
    intro p hp
    unfold reciprocalWeight
    positivity
  have htotalWeight : 0 ≤ totalWeight := htotalNonneg.trans hTotal
  have hL1' : weightedL1 reciprocalWeight c ^ 2 ≤
      totalWeight * weightedL2Sq reciprocalWeight c := by
    exact hL1.trans (mul_le_mul_of_nonneg_right hTotal (by
      unfold weightedL2Sq
      apply Finset.sum_nonneg
      intro p hp
      exact mul_nonneg (by unfold reciprocalWeight; positivity) (sq_nonneg _)))
  have hSecondBase := weightedL2SqSecond_le_invCutoff_mul_weightedL2Sq
    (n := n) (W := W) hW c
  have hSecond' : weightedL2SqSecond reciprocalWeight c ≤
      invW * weightedL2Sq reciprocalWeight c := by
    exact hSecondBase.trans (mul_le_mul_of_nonneg_right hInvW (by
      unfold weightedL2Sq
      apply Finset.sum_nonneg
      intro p hp
      exact mul_nonneg (by unfold reciprocalWeight; positivity) (sq_nonneg _)))
  have hL2id : weightedL2Sq reciprocalWeight c =
      primeCoefficientL2Sq c := rfl
  calc
    |subtypeSquarefreeQuadratic law c - primeReferenceQuadratic n c| ≤
        epsilonOff * weightedL1 reciprocalWeight c ^ 2 +
          epsilonDiag * weightedL2Sq reciprocalWeight c +
          epsilonSecond * weightedL2SqSecond reciprocalWeight c := hbase
    _ ≤ epsilonOff * (totalWeight * weightedL2Sq reciprocalWeight c) +
          epsilonDiag * weightedL2Sq reciprocalWeight c +
          epsilonSecond * (invW * weightedL2Sq reciprocalWeight c) := by
      gcongr
    _ = (epsilonOff * totalWeight + epsilonDiag + epsilonSecond * invW) *
          primeCoefficientL2Sq c := by
      rw [← hL2id]
      ring

/-- The fixed Dickman quotient gap gives the arbitrary-band squarefree
reference lower bound.  This proof starts directly from
`canonicalSlowKappa_primeDirichlet_anchor_lower`; in particular there is no
finite-mesh existential choice of `kappa`. -/
theorem canonicalSlowKappa_primeReference_band_lower
    [Nonempty Band]
    (P : Partition n W Band) (hn : 1 < n)
    (anchor : Finset (PrimeIndex n W))
    (hinterior : ∀ p ∈ anchor,
      tPrime n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight n) anchor)
    {rowError : ℝ}
    (hrow : ∀ p : PrimeIndex n W,
      |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
        rowError * tPrime n p.1) :
    ∀ q : RawGaugeSpace P.mass P.center,
      ((canonicalSlowKappa / 2) *
            anchorMass (primeWeight n) anchor - rowError) *
          P.data.bandNormSq q.1 ≤
        primeReferenceQuadratic n (liftBandCoefficient P q.1) := by
  intro q
  let c : PrimeIndex n W → ℝ := liftBandCoefficient P q.1
  let mu : ℝ := anchorMean n anchor c
  have hdistance : P.data.bandNormSq q.1 ≤
      primePhysicalDistance n c mu := by
    simpa only [c] using bandNormSq_le_primePhysicalDistance P q mu
  have hcoef : 0 ≤
      (canonicalSlowKappa / 2) * anchorMass (primeWeight n) anchor :=
    mul_nonneg (div_nonneg canonicalSlowKappa_pos.le (by norm_num)) hmass.le
  have henergyLower :
      ((canonicalSlowKappa / 2) *
          anchorMass (primeWeight n) anchor) *
          P.data.bandNormSq q.1 ≤
        dirichletEnergy (primeWeight n) (primeKernel n)
          (dirichletCoordinate n c) := by
    exact (mul_le_mul_of_nonneg_left hdistance hcoef).trans
      (canonicalSlowKappa_primeDirichlet_anchor_lower
        hn anchor hinterior hmass c)
  have hresidualAbs := abs_rowResidualContribution_le hn c hrow
  have hresidualAbs' :
      |∑ p, primeWeight n p *
          rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p *
            (dirichletCoordinate n c p) ^ 2| ≤
        rowError * P.data.bandNormSq q.1 := by
    simpa only [c, primeCoefficientL2Sq_liftBandCoefficient] using
      hresidualAbs
  have hresidualLower := neg_le_of_abs_le hresidualAbs'
  rw [primeReferenceQuadratic_eq_dirichlet_add_residual hn c]
  have hbandNonneg : 0 ≤ P.data.bandNormSq q.1 :=
    P.data.bandNormSq_nonneg q.1
  nlinarith

/-- Strong fixed-kappa reference bound for the exact physical least-squares
residual of an arbitrary band vector.  The norm on the left is the literal
prime norm of that residual, before passing to the smaller band quotient
distance. -/
theorem canonicalSlowKappa_primeReference_physicalResidual_lower
    [Nonempty Band]
    (P : Partition n W Band) (hn : 1 < n)
    (anchor : Finset (PrimeIndex n W))
    (hinterior : ∀ p ∈ anchor,
      tPrime n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight n) anchor)
    {rowError : ℝ}
    (hrow : ∀ p : PrimeIndex n W,
      |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
        rowError * tPrime n p.1)
    (b : Band → ℝ) :
    ((canonicalSlowKappa / 2) *
          anchorMass (primeWeight n) anchor - rowError) *
        primeCoefficientL2Sq
          (P.data.residual b (P.data.physicalMinimizer b)) ≤
      primeReferenceQuadratic n
        (P.data.residual b (P.data.physicalMinimizer b)) := by
  let c : PrimeIndex n W → ℝ :=
    P.data.residual b (P.data.physicalMinimizer b)
  let A : ℝ :=
    (canonicalSlowKappa / 2) * anchorMass (primeWeight n) anchor
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (div_nonneg canonicalSlowKappa_pos.le (by norm_num)) hmass.le
  have hdistance : primeCoefficientL2Sq c ≤
      primePhysicalDistance n c (anchorMean n anchor c) := by
    simpa only [c] using
      primeCoefficientL2Sq_le_physicalDistance_residualMinimizer
        P hn b (anchorMean n anchor c)
  have henergyLower :
      A * primeCoefficientL2Sq c ≤
        dirichletEnergy (primeWeight n) (primeKernel n)
          (dirichletCoordinate n c) := by
    exact (mul_le_mul_of_nonneg_left hdistance hA).trans (by
      simpa only [A] using
        canonicalSlowKappa_primeDirichlet_anchor_lower
          hn anchor hinterior hmass c)
  have hresidualAbs := abs_rowResidualContribution_le hn c hrow
  have hresidualLower :
      -(rowError * primeCoefficientL2Sq c) ≤
        ∑ p, primeWeight n p *
          rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p *
            (dirichletCoordinate n c p) ^ 2 :=
    neg_le_of_abs_le hresidualAbs
  rw [primeReferenceQuadratic_eq_dirichlet_add_residual hn c]
  dsimp only [c, A] at henergyLower hresidualLower ⊢
  linarith

/-- Exact arbitrary-band quotient form of the preceding theorem.  The
smallness premise is only what is needed to multiply the comparison
`D(gaugePart b) ≤ ‖physicalResidual b‖²` by a nonnegative coefficient. -/
theorem canonicalSlowKappa_primeReference_fullQuotient_lower
    [Nonempty Band]
    (P : Partition n W Band) (hn : 1 < n)
    (anchor : Finset (PrimeIndex n W))
    (hinterior : ∀ p ∈ anchor,
      tPrime n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight n) anchor)
    {rowError : ℝ}
    (hrow : ∀ p : PrimeIndex n W,
      |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
        rowError * tPrime n p.1)
    (hsmall : rowError ≤
      (canonicalSlowKappa / 2) * anchorMass (primeWeight n) anchor) :
    ∀ b : Band → ℝ,
      ((canonicalSlowKappa / 2) *
            anchorMass (primeWeight n) anchor - rowError) *
          P.data.bandNormSq (P.data.gaugePart b) ≤
        primeReferenceQuadratic n
          (P.data.residual b (P.data.physicalMinimizer b)) := by
  intro b
  have href := canonicalSlowKappa_primeReference_physicalResidual_lower
    P hn anchor hinterior hmass hrow b
  let c : PrimeIndex n W → ℝ :=
    P.data.residual b (P.data.physicalMinimizer b)
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
  have hbandPhysical : P.data.bandNormSq q ≤
      P.data.physicalSq b (P.data.physicalMinimizer b) := by
    have h := P.data.physical_lower_bound q lambda hq hvariance
    rw [hdecomp] at h
    exact h
  have hcoefficientPhysical : primeCoefficientL2Sq c =
      P.data.physicalSq b (P.data.physicalMinimizer b) := by
    rw [primeCoefficientL2Sq_eq_data_primeNormSq P]
    rfl
  have hbandCoefficient : P.data.bandNormSq q ≤
      primeCoefficientL2Sq c := by
    rw [hcoefficientPhysical]
    exact hbandPhysical
  have hcoef : 0 ≤
      (canonicalSlowKappa / 2) *
          anchorMass (primeWeight n) anchor - rowError :=
    sub_nonneg.mpr hsmall
  calc
    ((canonicalSlowKappa / 2) *
          anchorMass (primeWeight n) anchor - rowError) *
        P.data.bandNormSq (P.data.gaugePart b) =
      ((canonicalSlowKappa / 2) *
          anchorMass (primeWeight n) anchor - rowError) *
        P.data.bandNormSq q := by rfl
    _ ≤ ((canonicalSlowKappa / 2) *
          anchorMass (primeWeight n) anchor - rowError) *
        primeCoefficientL2Sq c :=
      mul_le_mul_of_nonneg_left hbandCoefficient hcoef
    _ ≤ primeReferenceQuadratic n c := by
      simpa only [c] using href

/-- Fixed-kappa full-valuation gap for a literal law on the prime subtype.
The two comparison losses and the prime-power loss are all relative to the
same reciprocal-prime square norm. -/
theorem subtypeFull_band_lower_canonicalKappa_of_entry_and_row
    [Nonempty Band]
    (P : Partition n W Band) (hn : 1 < n)
    (law : BoundedValuationLaw Omega M)
    (anchor : Finset (PrimeIndex n W))
    (hinterior : ∀ p ∈ anchor,
      tPrime n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight n) anchor)
    {rowError epsilonOff epsilonDiag epsilonSecond totalWeight invW R : ℝ}
    (hOff : 0 ≤ epsilonOff) (hSecond : 0 ≤ epsilonSecond)
    (hW : 0 < W)
    (hTotal : (∑ p : PrimeIndex n W, reciprocalWeight p) ≤ totalWeight)
    (hInvW : (1 / (W : ℝ)) ≤ invW)
    (hrowReference : ∀ p : PrimeIndex n W,
      |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
        rowError * tPrime n p.1)
    (hentry : ∀ p r : PrimeIndex n W,
      |law.covII p.1 r.1 - squarefreeReferenceEntry n p.1 r.1| ≤
        epsilonOff * reciprocalWeight p * reciprocalWeight r +
          if p = r then
            epsilonDiag * reciprocalWeight p +
              epsilonSecond * reciprocalWeight p ^ 2
          else 0)
    (hrowPower : ∀ p : PrimeIndex n W,
      (p.1 : ℝ) * ∑ r : PrimeIndex n W,
        |law.covVV p.1 r.1 - law.covII p.1 r.1| ≤ R) :
    ∀ q : RawGaugeSpace P.mass P.center,
      ((canonicalSlowKappa / 2) *
              anchorMass (primeWeight n) anchor -
            rowError -
            (epsilonOff * totalWeight + epsilonDiag +
              epsilonSecond * invW) - R) *
          P.data.bandNormSq q.1 ≤
        subtypeFullQuadratic law (liftBandCoefficient P q.1) := by
  intro q
  let c : PrimeIndex n W → ℝ := liftBandCoefficient P q.1
  let profileLoss : ℝ :=
    epsilonOff * totalWeight + epsilonDiag + epsilonSecond * invW
  have href := canonicalSlowKappa_primeReference_band_lower
    P hn anchor hinterior hmass hrowReference q
  have hsf := abs_squarefree_sub_reference_le_relative law c
    hOff hSecond hW hTotal hInvW hentry
  have hfull := abs_subtypeFull_sub_squarefree_le_of_weightedRow
    P law c hrowPower
  have hnorm : primeCoefficientL2Sq c = P.data.bandNormSq q.1 := by
    simpa only [c] using primeCoefficientL2Sq_liftBandCoefficient P q.1
  have hsfLower :
      primeReferenceQuadratic n c -
          profileLoss * P.data.bandNormSq q.1 ≤
        subtypeSquarefreeQuadratic law c := by
    have h := (abs_le.mp hsf).1
    rw [hnorm] at h
    simpa only [profileLoss] using (show
      primeReferenceQuadratic n c -
          profileLoss * P.data.bandNormSq q.1 ≤
        subtypeSquarefreeQuadratic law c by linarith)
  have hfullLower :
      subtypeSquarefreeQuadratic law c - R * P.data.bandNormSq q.1 ≤
        subtypeFullQuadratic law c := by
    have h := (abs_le.mp hfull).1
    rw [hnorm] at h
    linarith
  have hband : 0 ≤ P.data.bandNormSq q.1 :=
    P.data.bandNormSq_nonneg q.1
  dsimp only [profileLoss] at hsfLower
  nlinarith

/-- Fixed-kappa full-valuation bound for the exact physical residual of an
arbitrary band vector.  The comparison errors are measured in precisely the
same residual prime norm as the reference form. -/
theorem subtypeFull_physicalResidual_lower_canonicalKappa_of_entry_and_row
    [Nonempty Band]
    (P : Partition n W Band) (hn : 1 < n)
    (law : BoundedValuationLaw Omega M)
    (anchor : Finset (PrimeIndex n W))
    (hinterior : ∀ p ∈ anchor,
      tPrime n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight n) anchor)
    {rowError epsilonOff epsilonDiag epsilonSecond totalWeight invW R : ℝ}
    (hOff : 0 ≤ epsilonOff) (hSecond : 0 ≤ epsilonSecond)
    (hW : 0 < W)
    (hTotal : (∑ p : PrimeIndex n W, reciprocalWeight p) ≤ totalWeight)
    (hInvW : (1 / (W : ℝ)) ≤ invW)
    (hrowReference : ∀ p : PrimeIndex n W,
      |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
        rowError * tPrime n p.1)
    (hentry : ∀ p r : PrimeIndex n W,
      |law.covII p.1 r.1 - squarefreeReferenceEntry n p.1 r.1| ≤
        epsilonOff * reciprocalWeight p * reciprocalWeight r +
          if p = r then
            epsilonDiag * reciprocalWeight p +
              epsilonSecond * reciprocalWeight p ^ 2
          else 0)
    (hrowPower : ∀ p : PrimeIndex n W,
      (p.1 : ℝ) * ∑ r : PrimeIndex n W,
        |law.covVV p.1 r.1 - law.covII p.1 r.1| ≤ R)
    (b : Band → ℝ) :
    ((canonicalSlowKappa / 2) *
              anchorMass (primeWeight n) anchor -
            rowError -
            (epsilonOff * totalWeight + epsilonDiag +
              epsilonSecond * invW) - R) *
        primeCoefficientL2Sq
          (P.data.residual b (P.data.physicalMinimizer b)) ≤
      subtypeFullQuadratic law
        (P.data.residual b (P.data.physicalMinimizer b)) := by
  let c : PrimeIndex n W → ℝ :=
    P.data.residual b (P.data.physicalMinimizer b)
  let profileLoss : ℝ :=
    epsilonOff * totalWeight + epsilonDiag + epsilonSecond * invW
  have href := canonicalSlowKappa_primeReference_physicalResidual_lower
    P hn anchor hinterior hmass hrowReference b
  have hsf := abs_squarefree_sub_reference_le_relative law c
    hOff hSecond hW hTotal hInvW hentry
  have hfull := abs_subtypeFull_sub_squarefree_le_of_weightedRow
    P law c hrowPower
  have hsfLower :
      primeReferenceQuadratic n c -
          profileLoss * primeCoefficientL2Sq c ≤
        subtypeSquarefreeQuadratic law c := by
    have h := (abs_le.mp hsf).1
    simpa only [profileLoss] using (show
      primeReferenceQuadratic n c -
          profileLoss * primeCoefficientL2Sq c ≤
        subtypeSquarefreeQuadratic law c by linarith)
  have hfullLower :
      subtypeSquarefreeQuadratic law c - R * primeCoefficientL2Sq c ≤
        subtypeFullQuadratic law c := by
    have h := (abs_le.mp hfull).1
    linarith
  have hnorm : 0 ≤ primeCoefficientL2Sq c := by
    unfold primeCoefficientL2Sq
    exact Finset.sum_nonneg fun p _ ↦
      mul_nonneg (by positivity) (sq_nonneg _)
  dsimp only [c, profileLoss] at href hsfLower hfullLower hnorm ⊢
  nlinarith

/-- The exact arithmetic quotient distance is no larger than the prime norm
of the physical least-squares residual. -/
theorem bandNormSq_gaugePart_le_physicalResidual_primeCoefficientL2Sq
    [Nonempty Band]
    (P : Partition n W Band) (hn : 1 < n) (b : Band → ℝ) :
    P.data.bandNormSq (P.data.gaugePart b) ≤
      primeCoefficientL2Sq
        (P.data.residual b (P.data.physicalMinimizer b)) := by
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
  have hphysical : P.data.bandNormSq q ≤
      P.data.physicalSq b (P.data.physicalMinimizer b) := by
    have h := P.data.physical_lower_bound q lambda hq hvariance
    rw [hdecomp] at h
    exact h
  rw [primeCoefficientL2Sq_eq_data_primeNormSq P]
  exact hphysical

/-- Arbitrary-band full-valuation quotient gap.  Positivity of the final
displayed coefficient is stated explicitly because it is exactly what lets
the residual prime norm be replaced by the smaller quotient `D`-distance. -/
theorem subtypeFull_fullQuotient_lower_canonicalKappa_of_entry_and_row
    [Nonempty Band]
    (P : Partition n W Band) (hn : 1 < n)
    (law : BoundedValuationLaw Omega M)
    (anchor : Finset (PrimeIndex n W))
    (hinterior : ∀ p ∈ anchor,
      tPrime n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight n) anchor)
    {rowError epsilonOff epsilonDiag epsilonSecond totalWeight invW R : ℝ}
    (hOff : 0 ≤ epsilonOff) (hSecond : 0 ≤ epsilonSecond)
    (hW : 0 < W)
    (hTotal : (∑ p : PrimeIndex n W, reciprocalWeight p) ≤ totalWeight)
    (hInvW : (1 / (W : ℝ)) ≤ invW)
    (hrowReference : ∀ p : PrimeIndex n W,
      |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
        rowError * tPrime n p.1)
    (hentry : ∀ p r : PrimeIndex n W,
      |law.covII p.1 r.1 - squarefreeReferenceEntry n p.1 r.1| ≤
        epsilonOff * reciprocalWeight p * reciprocalWeight r +
          if p = r then
            epsilonDiag * reciprocalWeight p +
              epsilonSecond * reciprocalWeight p ^ 2
          else 0)
    (hrowPower : ∀ p : PrimeIndex n W,
      (p.1 : ℝ) * ∑ r : PrimeIndex n W,
        |law.covVV p.1 r.1 - law.covII p.1 r.1| ≤ R)
    (hsmall : rowError +
        (epsilonOff * totalWeight + epsilonDiag + epsilonSecond * invW) + R ≤
      (canonicalSlowKappa / 2) * anchorMass (primeWeight n) anchor) :
    ∀ b : Band → ℝ,
      ((canonicalSlowKappa / 2) *
              anchorMass (primeWeight n) anchor -
            rowError -
            (epsilonOff * totalWeight + epsilonDiag +
              epsilonSecond * invW) - R) *
          P.data.bandNormSq (P.data.gaugePart b) ≤
        subtypeFullQuadratic law
          (P.data.residual b (P.data.physicalMinimizer b)) := by
  intro b
  have hstrong :=
    subtypeFull_physicalResidual_lower_canonicalKappa_of_entry_and_row
      P hn law anchor hinterior hmass hOff hSecond hW hTotal hInvW
      hrowReference hentry hrowPower b
  have hdistance :=
    bandNormSq_gaugePart_le_physicalResidual_primeCoefficientL2Sq P hn b
  have hcoef : 0 ≤
      (canonicalSlowKappa / 2) * anchorMass (primeWeight n) anchor -
        rowError -
        (epsilonOff * totalWeight + epsilonDiag + epsilonSecond * invW) - R := by
    linarith
  exact (mul_le_mul_of_nonneg_left hdistance hcoef).trans hstrong

end Erdos390.Full.PaperCanonicalActualBandQuadraticTransfer

namespace Erdos390.Full.PaperBridgeFit.BridgeData

open ArithmeticModel ArithmeticBandGeometry
open PaperCanonicalSlowKappa
open PaperCanonicalActualBandQuadraticTransfer
open PaperPrimePowerChamberError
open PaperWeightedInverseExport
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open PaperSquarefreeSlowQuadraticLower
open FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference
open OmittedTiltPairChamber

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : PaperBridgeFit.BridgeData Head Band)

/-- The arbitrary band-lift full quadratic is exactly the covariance of the
literal actual full-valuation band score. -/
theorem subtypeFullQuadratic_actual_eq_bandCovariance
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) :
    subtypeFullQuadratic (B.actualValuationLaw xi)
        (PaperBandQuadraticGeometry.liftBandCoefficient B.partition q.1) =
      (B.tiltedLaw xi).covariance
        (B.bandRegressionScore q) (B.bandRegressionScore q) := by
  let c : BandPrime B.sampleData.n B.sampleData.W → ℝ :=
    PaperBandQuadraticGeometry.liftBandCoefficient B.partition q.1
  have hscore : B.bandRegressionScore q =
      fun m ↦ ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        c p * valuation p.1 (B.sampleData.value m) := by
    funext m
    rw [B.bandRegressionScore_eq_primeSum q m]
    apply Finset.sum_congr rfl
    intro p hp
    rfl
  rw [hscore, (B.tiltedLaw xi).covariance_sum_left]
  unfold subtypeFullQuadratic matrixQuadratic
    actualValuationLaw PrimePowerCovariance.BoundedValuationLaw.covVV
    PrimePowerCovariance.BoundedValuationLaw.V
  apply Finset.sum_congr rfl
  intro p hp
  rw [(B.tiltedLaw xi).covariance_sum_right]
  apply Finset.sum_congr rfl
  intro r hr
  rw [(B.tiltedLaw xi).covariance_smul_left,
    (B.tiltedLaw xi).covariance_smul_right]
  ring

/-- Literal full-valuation score for an arbitrary coefficient on the actual
prime subtype. -/
def primeValuationScore
    (c : BandPrime B.sampleData.n B.sampleData.W → ℝ)
    (m : B.sampleData.Sample) : ℝ :=
  ∑ p : BandPrime B.sampleData.n B.sampleData.W,
    c p * valuation p.1 (B.sampleData.value m)

/-- The subtype full quadratic is exactly the variance of the corresponding
literal actual prime score. -/
theorem subtypeFullQuadratic_actual_eq_primeValuationScore_covariance
    [Nonempty Head]
    (xi : B.ParamSpace)
    (c : BandPrime B.sampleData.n B.sampleData.W → ℝ) :
    subtypeFullQuadratic (B.actualValuationLaw xi) c =
      (B.tiltedLaw xi).covariance
        (B.primeValuationScore c) (B.primeValuationScore c) := by
  unfold primeValuationScore
  rw [(B.tiltedLaw xi).covariance_sum_left]
  unfold subtypeFullQuadratic matrixQuadratic
    actualValuationLaw PrimePowerCovariance.BoundedValuationLaw.covVV
    PrimePowerCovariance.BoundedValuationLaw.V
  apply Finset.sum_congr rfl
  intro p hp
  rw [(B.tiltedLaw xi).covariance_sum_right]
  apply Finset.sum_congr rfl
  intro r hr
  rw [(B.tiltedLaw xi).covariance_smul_left,
    (B.tiltedLaw xi).covariance_smul_right]
  ring

/-- Weighted Cauchy--Schwarz in the literal arithmetic band `D`-norm. -/
theorem bandWeightedL1_sq_le_mass_mul_bandNormSq
    (q : B.RawBandGauge) :
    (∑ j : Band, B.harmonicMass j * |q.1 j|) ^ 2 ≤
      (∑ j : Band, B.harmonicMass j) *
        B.partition.data.bandNormSq q.1 := by
  let a : Band → ℝ := fun j ↦ Real.sqrt (B.harmonicMass j)
  let b : Band → ℝ :=
    fun j ↦ Real.sqrt (B.harmonicMass j) * |q.1 j|
  have hH (j : Band) : 0 ≤ B.harmonicMass j :=
    (B.harmonicMass_pos j).le
  have hsqa (j : Band) : a j ^ 2 = B.harmonicMass j := by
    dsimp only [a]
    rw [Real.sq_sqrt (hH j)]
  have hsqb (j : Band) : b j ^ 2 =
      B.harmonicMass j * q.1 j ^ 2 := by
    dsimp only [b]
    rw [mul_pow, Real.sq_sqrt (hH j), sq_abs]
  have hab (j : Band) : a j * b j =
      B.harmonicMass j * |q.1 j| := by
    dsimp only [a, b]
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (hH j)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  simp_rw [hab, hsqa, hsqb] at hcs
  have hnorm : B.partition.data.bandNormSq q.1 =
      ∑ j : Band, B.harmonicMass j * q.1 j ^ 2 := by
    unfold Erdos390.Lemma84.WeightedBandData.bandNormSq
      Erdos390.Lemma84.WeightedBandData.bandInner
    apply Finset.sum_congr rfl
    intro j hj
    change B.harmonicMass j * q.1 j * q.1 j =
      B.harmonicMass j * q.1 j ^ 2
    ring
  rw [hnorm]
  exact hcs

/-- A reciprocal marked nuisance family costs only a `D`-relative amount;
no inverse low-cell centre occurs. -/
theorem nuisanceRegressionLoss_bandScore_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma Cmarked : ℝ}
    (hgamma : 0 < gamma) (hCmarked : 0 ≤ Cmarked)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (q : B.RawBandGauge) :
    inner ℝ
        (B.nuisanceCoefficientOfScore xi hgamma hgap
          (B.bandRegressionScore q))
        (B.nuisanceCovarianceVector xi (B.bandRegressionScore q)) ≤
      ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * Cmarked ^ 2 *
          (∑ j : Band, B.harmonicMass j) / gamma) *
        B.partition.data.bandNormSq q.1 := by
  let L1 : ℝ := ∑ j : Band, B.harmonicMass j * |q.1 j|
  have hL1 : 0 ≤ L1 := by
    dsimp only [L1]
    exact Finset.sum_nonneg fun j _ ↦
      mul_nonneg (B.harmonicMass_pos j).le (abs_nonneg _)
  have hcoord (c : NuisanceCoord B.HeadIndex) :
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m c)
          (B.bandRegressionScore q)| ≤ Cmarked * L1 := by
    let mu := B.tiltedLaw xi
    let Z : B.sampleData.Sample → ℝ :=
      fun m ↦ B.nuisanceStatistic m c
    have hsum : mu.covariance Z (B.bandRegressionScore q) =
        ∑ j : Band, q.1 j * mu.covariance Z (B.bandScore j) := by
      unfold bandRegressionScore
      rw [show (fun m ↦ ∑ j : Band, q.1 j * B.bandScore j m) =
        fun m ↦ ∑ j ∈ (Finset.univ : Finset Band),
          q.1 j * B.bandScore j m by simp]
      rw [mu.covariance_sum_right]
      apply Finset.sum_congr rfl
      intro j hj
      rw [mu.covariance_smul_right]
    change |mu.covariance Z (B.bandRegressionScore q)| ≤ _
    rw [hsum]
    calc
      |∑ j : Band, q.1 j * mu.covariance Z (B.bandScore j)| ≤
          ∑ j : Band, |q.1 j * mu.covariance Z (B.bandScore j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Band, |q.1 j| *
          (Cmarked * B.harmonicMass j) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (B.abs_covariance_nuisance_bandScore_le_of_marked
            xi c j (fun p ↦ hmarked c p)) (abs_nonneg _)
      _ = Cmarked * L1 := by
        dsimp only [L1]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hK : 0 ≤ Cmarked * L1 := mul_nonneg hCmarked hL1
  have hvec := B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
    xi (B.bandRegressionScore q) hK hcoord
  have hvecSq :
      ‖B.nuisanceCovarianceVector xi (B.bandRegressionScore q)‖ ^ 2 ≤
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked ^ 2 * L1 ^ 2 := by
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hvec 2
    have hcard : 0 ≤
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) := by positivity
    calc
      ‖B.nuisanceCovarianceVector xi (B.bandRegressionScore q)‖ ^ 2 ≤
          (Real.sqrt (Fintype.card
              (NuisanceCoord B.HeadIndex) : ℝ) * (Cmarked * L1)) ^ 2 :=
        hsquare
      _ = (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked ^ 2 * L1 ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hcard]
        ring
  have hL1Sq := B.bandWeightedL1_sq_le_mass_mul_bandNormSq q
  have hcardC : 0 ≤
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * Cmarked ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  have hvecD :
      ‖B.nuisanceCovarianceVector xi (B.bandRegressionScore q)‖ ^ 2 ≤
        ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * Cmarked ^ 2 *
          (∑ j : Band, B.harmonicMass j)) *
            B.partition.data.bandNormSq q.1 := by
    exact hvecSq.trans (by
      calc
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked ^ 2 * L1 ^ 2 ≤
          ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked ^ 2) *
              ((∑ j : Band, B.harmonicMass j) *
                B.partition.data.bandNormSq q.1) :=
          mul_le_mul_of_nonneg_left hL1Sq hcardC
        _ = _ := by ring)
  have hloss := B.nuisanceRegressionLoss_bounds
    xi hgamma hgap (B.bandRegressionScore q)
  have hdiv := div_le_div_of_nonneg_right hvecD hgamma.le
  calc
    inner ℝ
        (B.nuisanceCoefficientOfScore xi hgamma hgap
          (B.bandRegressionScore q))
        (B.nuisanceCovarianceVector xi (B.bandRegressionScore q)) ≤
      ‖B.nuisanceCovarianceVector xi (B.bandRegressionScore q)‖ ^ 2 /
        gamma := hloss.2
    _ ≤ (((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked ^ 2 * (∑ j : Band, B.harmonicMass j)) *
        B.partition.data.bandNormSq q.1) / gamma := hdiv
    _ = ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * Cmarked ^ 2 *
          (∑ j : Band, B.harmonicMass j) / gamma) *
        B.partition.data.bandNormSq q.1 := by ring

/-- Marked nuisance rows control the regression loss of an arbitrary prime
coefficient in the same reciprocal-prime square norm. -/
theorem nuisanceRegressionLoss_primeValuationScore_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma Cmarked totalWeight : ℝ}
    (hgamma : 0 < gamma) (hCmarked : 0 ≤ Cmarked)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hTotal : (∑ p : BandPrime B.sampleData.n B.sampleData.W,
      reciprocalWeight p) ≤ totalWeight)
    (hmarked : ∀ (z : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m z)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (c : BandPrime B.sampleData.n B.sampleData.W → ℝ) :
    inner ℝ
        (B.nuisanceCoefficientOfScore xi hgamma hgap
          (B.primeValuationScore c))
        (B.nuisanceCovarianceVector xi (B.primeValuationScore c)) ≤
      ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked ^ 2 * totalWeight / gamma) *
        primeCoefficientL2Sq c := by
  let L1 : ℝ := weightedL1 reciprocalWeight c
  have hL1 : 0 ≤ L1 := by
    dsimp only [L1]
    unfold weightedL1
    exact Finset.sum_nonneg fun p _ ↦
      mul_nonneg (by unfold reciprocalWeight; positivity) (abs_nonneg _)
  have hcoord (z : NuisanceCoord B.HeadIndex) :
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m z)
          (B.primeValuationScore c)| ≤ Cmarked * L1 := by
    unfold primeValuationScore
    rw [(B.tiltedLaw xi).covariance_sum_right]
    simp_rw [(B.tiltedLaw xi).covariance_smul_right]
    calc
      |∑ p : BandPrime B.sampleData.n B.sampleData.W,
          c p * (B.tiltedLaw xi).covariance
            (fun m ↦ B.nuisanceStatistic m z)
            (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          |c p * (B.tiltedLaw xi).covariance
            (fun m ↦ B.nuisanceStatistic m z)
            (fun m ↦ valuation p.1 (B.sampleData.value m))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          |c p| * (Cmarked * (1 / (p.1 : ℝ))) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hmarked z p) (abs_nonneg _)
      _ = Cmarked * L1 := by
        dsimp only [L1]
        unfold weightedL1 reciprocalWeight
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  have hK : 0 ≤ Cmarked * L1 := mul_nonneg hCmarked hL1
  have hvec := B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
    xi (B.primeValuationScore c) hK hcoord
  have hvecSq :
      ‖B.nuisanceCovarianceVector xi (B.primeValuationScore c)‖ ^ 2 ≤
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked ^ 2 * L1 ^ 2 := by
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hvec 2
    have hcard : 0 ≤
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) := by positivity
    calc
      ‖B.nuisanceCovarianceVector xi (B.primeValuationScore c)‖ ^ 2 ≤
          (Real.sqrt (Fintype.card
              (NuisanceCoord B.HeadIndex) : ℝ) * (Cmarked * L1)) ^ 2 :=
        hsquare
      _ = (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked ^ 2 * L1 ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hcard]
        ring
  have hL1Base := weightedL1_sq_le_totalWeight_mul_weightedL2Sq c
  have hnormNonneg : 0 ≤ weightedL2Sq reciprocalWeight c := by
    unfold weightedL2Sq
    exact Finset.sum_nonneg fun p _ ↦
      mul_nonneg (by unfold reciprocalWeight; positivity) (sq_nonneg _)
  have hL1Sq : L1 ^ 2 ≤ totalWeight * primeCoefficientL2Sq c := by
    have h := hL1Base.trans
      (mul_le_mul_of_nonneg_right hTotal hnormNonneg)
    simpa only [L1] using h
  have hcardC : 0 ≤
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * Cmarked ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  have hvecD :
      ‖B.nuisanceCovarianceVector xi (B.primeValuationScore c)‖ ^ 2 ≤
        ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked ^ 2 * totalWeight) * primeCoefficientL2Sq c :=
    hvecSq.trans (by
      calc
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked ^ 2 * L1 ^ 2 ≤
          ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked ^ 2) *
              (totalWeight * primeCoefficientL2Sq c) :=
          mul_le_mul_of_nonneg_left hL1Sq hcardC
        _ = _ := by ring)
  have hloss := B.nuisanceRegressionLoss_bounds
    xi hgamma hgap (B.primeValuationScore c)
  have hdiv := div_le_div_of_nonneg_right hvecD hgamma.le
  calc
    inner ℝ
        (B.nuisanceCoefficientOfScore xi hgamma hgap
          (B.primeValuationScore c))
        (B.nuisanceCovarianceVector xi (B.primeValuationScore c)) ≤
      ‖B.nuisanceCovarianceVector xi (B.primeValuationScore c)‖ ^ 2 /
        gamma := hloss.2
    _ ≤ (((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked ^ 2 * totalWeight) * primeCoefficientL2Sq c) / gamma :=
      hdiv
    _ = ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked ^ 2 * totalWeight / gamma) *
        primeCoefficientL2Sq c := by ring

/-- The full covariance form for the actual law, with the fixed canonical
structural gap and all finite comparison losses explicit. -/
theorem actualFull_bandCovariance_lower_canonicalKappa_of_profiles_and_row
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    {rowError Eprofile CKernel totalWeight invW R : ℝ}
    (hEprofile : 0 ≤ Eprofile) (hCKernel : 0 ≤ CKernel)
    (hW : 0 < B.sampleData.W)
    (hTotal : (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        reciprocalWeight p) ≤ totalWeight)
    (hInvW : (1 / (B.sampleData.W : ℝ)) ≤ invW)
    (hrowReference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hpair : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p r 1 1)| ≤
        Eprofile * pairWeight p r 1 1)
    (hsingle : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel)
    (hrowPower : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) * ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV p.1 r.1 -
          (B.actualValuationLaw xi).covII p.1 r.1| ≤ R) :
    ∀ q : B.RawBandGauge,
      ((canonicalSlowKappa / 2) *
              anchorMass (primeWeight B.sampleData.n) anchor -
            rowError -
            ((4 * pairCovarianceScale Eprofile) * totalWeight +
              2 * Eprofile +
              ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                CKernel) * invW) - R) *
          B.partition.data.bandNormSq q.1 ≤
        (B.tiltedLaw xi).covariance
          (B.bandRegressionScore q) (B.bandRegressionScore q) := by
  have hentry := B.actual_squarefree_reference_entry_bound_of_profiles
    xi hEprofile hpair hsingle hKernel
  have hfull := subtypeFull_band_lower_canonicalKappa_of_entry_and_row
    B.partition B.n_gt_one (B.actualValuationLaw xi)
    anchor hinterior hmass
    (mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hEprofile))
    (add_nonneg (sq_nonneg _) hCKernel) hW hTotal hInvW
    hrowReference hentry hrowPower
  intro q
  have hq := hfull q
  rw [B.subtypeFullQuadratic_actual_eq_bandCovariance xi q] at hq
  exact hq

/-- Actual full-covariance lower bound for the exact physical residual of
an arbitrary band vector. -/
theorem actualFull_physicalResidual_lower_canonicalKappa_of_profiles_and_row
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    {rowError Eprofile CKernel totalWeight invW R : ℝ}
    (hEprofile : 0 ≤ Eprofile) (hCKernel : 0 ≤ CKernel)
    (hW : 0 < B.sampleData.W)
    (hTotal : (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        reciprocalWeight p) ≤ totalWeight)
    (hInvW : (1 / (B.sampleData.W : ℝ)) ≤ invW)
    (hrowReference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hpair : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p r 1 1)| ≤
        Eprofile * pairWeight p r 1 1)
    (hsingle : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel)
    (hrowPower : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) * ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV p.1 r.1 -
          (B.actualValuationLaw xi).covII p.1 r.1| ≤ R)
    (b : Band → ℝ) :
    let c := B.partition.data.residual b
      (B.partition.data.physicalMinimizer b)
    ((canonicalSlowKappa / 2) *
              anchorMass (primeWeight B.sampleData.n) anchor -
            rowError -
            ((4 * pairCovarianceScale Eprofile) * totalWeight +
              2 * Eprofile +
              ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                CKernel) * invW) - R) *
        primeCoefficientL2Sq c ≤
      (B.tiltedLaw xi).covariance
        (B.primeValuationScore c) (B.primeValuationScore c) := by
  dsimp only
  have hentry := B.actual_squarefree_reference_entry_bound_of_profiles
    xi hEprofile hpair hsingle hKernel
  have hfull :=
    subtypeFull_physicalResidual_lower_canonicalKappa_of_entry_and_row
      B.partition B.n_gt_one (B.actualValuationLaw xi)
      anchor hinterior hmass
      (mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hEprofile))
      (add_nonneg (sq_nonneg _) hCKernel) hW hTotal hInvW
      hrowReference hentry hrowPower b
  rw [B.subtypeFullQuadratic_actual_eq_primeValuationScore_covariance xi
    (B.partition.data.residual b
      (B.partition.data.physicalMinimizer b))] at hfull
  exact hfull

/-- Actual full-covariance quotient form for every band vector. -/
theorem actualFull_fullQuotient_lower_canonicalKappa_of_profiles_and_row
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    {rowError Eprofile CKernel totalWeight invW R : ℝ}
    (hEprofile : 0 ≤ Eprofile) (hCKernel : 0 ≤ CKernel)
    (hW : 0 < B.sampleData.W)
    (hTotal : (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        reciprocalWeight p) ≤ totalWeight)
    (hInvW : (1 / (B.sampleData.W : ℝ)) ≤ invW)
    (hrowReference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hpair : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p r 1 1)| ≤
        Eprofile * pairWeight p r 1 1)
    (hsingle : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel)
    (hrowPower : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) * ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV p.1 r.1 -
          (B.actualValuationLaw xi).covII p.1 r.1| ≤ R)
    (hsmall : rowError +
        ((4 * pairCovarianceScale Eprofile) * totalWeight +
          2 * Eprofile +
          ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
            CKernel) * invW) + R ≤
      (canonicalSlowKappa / 2) *
        anchorMass (primeWeight B.sampleData.n) anchor) :
    ∀ b : Band → ℝ,
      let c := B.partition.data.residual b
        (B.partition.data.physicalMinimizer b)
      ((canonicalSlowKappa / 2) *
              anchorMass (primeWeight B.sampleData.n) anchor -
            rowError -
            ((4 * pairCovarianceScale Eprofile) * totalWeight +
              2 * Eprofile +
              ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                CKernel) * invW) - R) *
          B.partition.data.bandNormSq (B.partition.data.gaugePart b) ≤
        (B.tiltedLaw xi).covariance
          (B.primeValuationScore c) (B.primeValuationScore c) := by
  intro b
  dsimp only
  have hstrong := B.actualFull_physicalResidual_lower_canonicalKappa_of_profiles_and_row
    xi anchor hinterior hmass hEprofile hCKernel hW hTotal hInvW
    hrowReference hpair hsingle hKernel hrowPower b
  have hdistance :=
    bandNormSq_gaugePart_le_physicalResidual_primeCoefficientL2Sq
      B.partition B.n_gt_one b
  have hcoef : 0 ≤
      (canonicalSlowKappa / 2) *
          anchorMass (primeWeight B.sampleData.n) anchor -
        rowError -
        ((4 * pairCovarianceScale Eprofile) * totalWeight +
          2 * Eprofile +
          ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
            CKernel) * invW) - R := by
    linarith
  exact (mul_le_mul_of_nonneg_left hdistance hcoef).trans hstrong

/-- Arbitrary-band nuisance-Schur quotient gap for the exact physical
least-squares residual score.  This is the full quotient statement: `b` is
not assumed to lie in the arithmetic gauge, and the left side is the exact
finite distance represented by `bandNormSq (gaugePart b)`. -/
theorem actualPhysicalResidualSchur_fullQuotient_Dgap_canonicalKappa
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma Cmarked : ℝ}
    (hgamma : 0 < gamma) (hCmarked : 0 ≤ Cmarked)
    (hgapNuisance : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    {rowError Eprofile CKernel totalWeight invW R : ℝ}
    (hEprofile : 0 ≤ Eprofile) (hCKernel : 0 ≤ CKernel)
    (hW : 0 < B.sampleData.W)
    (hTotal : (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        reciprocalWeight p) ≤ totalWeight)
    (hInvW : (1 / (B.sampleData.W : ℝ)) ≤ invW)
    (hrowReference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hpair : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p r 1 1)| ≤
        Eprofile * pairWeight p r 1 1)
    (hsingle : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel)
    (hrowPower : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) * ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV p.1 r.1 -
          (B.actualValuationLaw xi).covII p.1 r.1| ≤ R)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (hsmall : rowError +
          ((4 * pairCovarianceScale Eprofile) * totalWeight +
            2 * Eprofile +
            ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
              CKernel) * invW) +
          R +
          ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked ^ 2 * totalWeight / gamma) ≤
        (canonicalSlowKappa / 2) *
          anchorMass (primeWeight B.sampleData.n) anchor) :
    ∀ b : Band → ℝ,
      let c := B.partition.data.residual b
        (B.partition.data.physicalMinimizer b)
      let F := B.primeValuationScore c
      ((canonicalSlowKappa / 2) *
                anchorMass (primeWeight B.sampleData.n) anchor -
              rowError -
              ((4 * pairCovarianceScale Eprofile) * totalWeight +
                2 * Eprofile +
                ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                  CKernel) * invW) -
              R -
              ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
                Cmarked ^ 2 * totalWeight / gamma)) *
            B.partition.data.bandNormSq (B.partition.data.gaugePart b) ≤
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgapNuisance F)
          (B.nuisanceResidualScore xi hgamma hgapNuisance F) := by
  intro b
  dsimp only
  let c := B.partition.data.residual b
    (B.partition.data.physicalMinimizer b)
  let F := B.primeValuationScore c
  let nuisanceLoss : ℝ :=
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
      Cmarked ^ 2 * totalWeight / gamma
  have hfull := B.actualFull_physicalResidual_lower_canonicalKappa_of_profiles_and_row
    xi anchor hinterior hmass hEprofile hCKernel hW hTotal hInvW
    hrowReference hpair hsingle hKernel hrowPower b
  have hloss := B.nuisanceRegressionLoss_primeValuationScore_le_of_marked
    xi hgamma hCmarked hgapNuisance hTotal hmarked c
  have hvariance := B.nuisanceResidualScore_variance_identity
    xi hgamma hgapNuisance F
  have hstrong :
      ((canonicalSlowKappa / 2) *
                anchorMass (primeWeight B.sampleData.n) anchor -
              rowError -
              ((4 * pairCovarianceScale Eprofile) * totalWeight +
                2 * Eprofile +
                ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                  CKernel) * invW) -
              R - nuisanceLoss) * primeCoefficientL2Sq c ≤
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgapNuisance F)
          (B.nuisanceResidualScore xi hgamma hgapNuisance F) := by
    rw [hvariance]
    dsimp only [c, F, nuisanceLoss] at hfull hloss ⊢
    nlinarith
  have hdistance :=
    bandNormSq_gaugePart_le_physicalResidual_primeCoefficientL2Sq
      B.partition B.n_gt_one b
  have hcoef : 0 ≤
      (canonicalSlowKappa / 2) *
              anchorMass (primeWeight B.sampleData.n) anchor -
            rowError -
            ((4 * pairCovarianceScale Eprofile) * totalWeight +
              2 * Eprofile +
              ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                CKernel) * invW) -
            R - nuisanceLoss := by
    dsimp only [nuisanceLoss]
    linarith
  dsimp only [c, F, nuisanceLoss] at hstrong ⊢
  exact (mul_le_mul_of_nonneg_left hdistance hcoef).trans hstrong

/-- Complete actual nuisance-Schur `D`-gap with the same fixed canonical
structural constant.  No inverse or mesh-dependent positive constant is an
input to this finite statement. -/
theorem actualBandSchur_Dgap_canonicalKappa_of_profiles_rows_marked
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma Cmarked : ℝ}
    (hgamma : 0 < gamma) (hCmarked : 0 ≤ Cmarked)
    (hgapNuisance : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    {rowError Eprofile CKernel totalWeight invW R : ℝ}
    (hEprofile : 0 ≤ Eprofile) (hCKernel : 0 ≤ CKernel)
    (hW : 0 < B.sampleData.W)
    (hTotal : (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        reciprocalWeight p) ≤ totalWeight)
    (hInvW : (1 / (B.sampleData.W : ℝ)) ≤ invW)
    (hrowReference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hpair : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p r 1 1)| ≤
        Eprofile * pairWeight p r 1 1)
    (hsingle : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel)
    (hrowPower : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) * ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV p.1 r.1 -
          (B.actualValuationLaw xi).covII p.1 r.1| ≤ R)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    ∀ q : B.RawBandGauge,
      ((canonicalSlowKappa / 2) *
              anchorMass (primeWeight B.sampleData.n) anchor -
            rowError -
            ((4 * pairCovarianceScale Eprofile) * totalWeight +
              2 * Eprofile +
              ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                CKernel) * invW) - R -
            ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              Cmarked ^ 2 * (∑ j : Band, B.harmonicMass j) / gamma)) *
          B.partition.data.bandNormSq q.1 ≤
        B.bandDPairing q
          (B.actualBandSchurLinearMap xi hgamma hgapNuisance q) := by
  have hfull := B.actualFull_bandCovariance_lower_canonicalKappa_of_profiles_and_row
    xi anchor hinterior hmass hEprofile hCKernel hW hTotal hInvW
    hrowReference hpair hsingle hKernel hrowPower
  intro q
  let F : B.sampleData.Sample → ℝ := B.bandRegressionScore q
  have hloss := B.nuisanceRegressionLoss_bandScore_le_of_marked
    xi hgamma hCmarked hgapNuisance hmarked q
  have hvariance := B.nuisanceResidualScore_variance_identity
    xi hgamma hgapNuisance F
  have hschur := B.actualBandSchur_quadratic_eq_residualVariance
    xi hgamma hgapNuisance q
  have hfullq := hfull q
  have hpairing :
      B.bandDPairing q
          (B.actualBandSchurLinearMap xi hgamma hgapNuisance q) =
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgapNuisance F)
          (B.nuisanceResidualScore xi hgamma hgapNuisance F) := by
    simpa only [bandDPairing, F] using hschur
  rw [hpairing, hvariance]
  dsimp only [F] at hfullq hloss ⊢
  have hband : 0 ≤ B.partition.data.bandNormSq q.1 :=
    B.partition.data.bandNormSq_nonneg q.1
  nlinarith

end Erdos390.Full.PaperBridgeFit.BridgeData

end
