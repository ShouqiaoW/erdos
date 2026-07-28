import Erdos390.Full.PaperBandQuadraticGeometry
import Erdos390.Full.PaperActualSquarefreeSlowLower
import Erdos390.Full.PaperActualSchurMarkedRow
import Erdos390.Full.PaperExactSchurTwoStageQuadratic

/-!
# Relative quadratic transfer for an arbitrary band coefficient

This is the quadratic-form half of the arithmetic bridge in Lemma 8.4.
Unlike the compensated specialization used in Lemma 8.6, the coefficient
below is an arbitrary prime vector (and will later be the exact physical
residual of a band vector).  A symmetric normalized prime-row estimate
controls its full-valuation/squarefree quadratic error in the reciprocal
prime square norm.  Signed squarefree-profile errors are put in the same
norm by a weighted Cauchy--Schwarz inequality.

No inverse, coercivity, or Schur-gap assertion is assumed in this file.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.PaperActualBandQuadraticTransfer

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open FiniteSignedQuadraticEntryTransfer
open PaperSquarefreeSlowQuadraticLower
open PrimeSquarefreeDirichletGeometry
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

/-- A literal `p * sum_r |VV-II| <= R` row controls every symmetric
quadratic coefficient in the reciprocal prime square norm. -/
theorem abs_subtypeFull_sub_squarefree_le_of_weightedRow
    (P : ArithmeticBandGeometry.Partition n W Band)
    (law : BoundedValuationLaw Omega M)
    (c : PrimeIndex n W → ℝ) {R : ℝ} (hR : 0 ≤ R)
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
    have hpne : (p.1 : ℝ) ≠ 0 := ne_of_gt hp
    apply (le_div_iff₀ hp).2
    calc
      (p.1 : ℝ) * ∑ r : PrimeIndex n W, |E p r| ≤ R := hrow p
      _ = (R * P.data.weight p) * (p.1 : ℝ) := by
        unfold Erdos390.Lemma84.WeightedBandData.weight
        field_simp [hpne]
  have hquad := P.data.symmetric_prime_row_quadratic_error E c R hsymm hrow'
  have hidentify :
      Erdos390.Lemma84.WeightedBandData.primeQuadratic P.data E c =
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
  simpa only [PaperBandQuadraticGeometry.primeCoefficientL2Sq_eq_data_primeNormSq
    P] using hquad

/-- Weighted Cauchy--Schwarz for reciprocal prime coefficients.  This is
the exact estimate needed to turn a product-reciprocal signed-profile error
into a relative `D`-form error, including the moving low band. -/
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

/-- All three signed squarefree-reference errors are relative to the
reciprocal prime square norm. -/
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
  have hInvWNonneg : 0 ≤ invW := (by positivity : 0 ≤ 1 / (W : ℝ)).trans hInvW
  have hSecond' : weightedL2SqSecond reciprocalWeight c ≤
      invW * weightedL2Sq reciprocalWeight c := by
    exact hSecondBase.trans (mul_le_mul_of_nonneg_right hInvW (by
      unfold weightedL2Sq
      apply Finset.sum_nonneg
      intro p hp
      exact mul_nonneg (by unfold reciprocalWeight; positivity) (sq_nonneg _)))
  have hL2id : weightedL2Sq reciprocalWeight c = primeCoefficientL2Sq c := by
    rfl
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

/-- The finite squarefree-reference gap, the signed profile comparison,
and the full/squarefree weighted row combine to give a genuine full-
valuation `D`-gap for every arithmetic raw-gauge band vector.  Every loss
is displayed as a coefficient of the same `D`-norm. -/
theorem exists_subtypeFull_band_lower_of_entry_and_row
    [Nonempty Band]
    (P : ArithmeticBandGeometry.Partition n W Band) (hn : 1 < n)
    (law : BoundedValuationLaw Omega M)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2)
    (anchor : Finset (PrimeIndex n W))
    (hinterior : ∀ p ∈ anchor,
      tPrime n p.1 ∈ Set.Icc epsilon (1 - epsilon))
    (hmass : 0 < FiniteAnchoredDirichletQuadratic.anchorMass
      (primeWeight n) anchor)
    {rowError epsilonOff epsilonDiag epsilonSecond totalWeight invW R : ℝ}
    (hOff : 0 ≤ epsilonOff) (hSecond : 0 ≤ epsilonSecond)
    (hR : 0 ≤ R) (hW : 0 < W)
    (hTotal : (∑ p : PrimeIndex n W, reciprocalWeight p) ≤ totalWeight)
    (hInvW : (1 / (W : ℝ)) ≤ invW)
    (hrowReference : ∀ p : PrimeIndex n W,
      |FiniteAnchoredDirichletQuadratic.rowResidual
          (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
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
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ q : PaperWeightedInverseExport.RawGaugeSpace P.mass P.center,
        ((kappa / 2) *
              FiniteAnchoredDirichletQuadratic.anchorMass
                (primeWeight n) anchor -
            rowError -
            (epsilonOff * totalWeight + epsilonDiag +
              epsilonSecond * invW) - R) *
              P.data.bandNormSq q.1 ≤
          subtypeFullQuadratic law
            (PaperBandQuadraticGeometry.liftBandCoefficient P q.1) := by
  obtain ⟨kappa, hkappa, href⟩ :=
    PaperBandQuadraticGeometry.exists_primeReference_band_lower
      P hn hepsilon hhalf anchor hinterior hmass hrowReference
  refine ⟨kappa, hkappa, ?_⟩
  intro q
  let c : PrimeIndex n W → ℝ :=
    PaperBandQuadraticGeometry.liftBandCoefficient P q.1
  let profileLoss : ℝ :=
    epsilonOff * totalWeight + epsilonDiag + epsilonSecond * invW
  have href' :
      ((kappa / 2) *
            FiniteAnchoredDirichletQuadratic.anchorMass
              (primeWeight n) anchor - rowError) *
          P.data.bandNormSq q.1 ≤ primeReferenceQuadratic n c := by
    simpa only [c] using href q
  have hsf := abs_squarefree_sub_reference_le_relative law c
    hOff hSecond hW hTotal hInvW hentry
  have hfull := abs_subtypeFull_sub_squarefree_le_of_weightedRow
    P law c hR hrowPower
  have hnorm : primeCoefficientL2Sq c = P.data.bandNormSq q.1 := by
    simpa only [c] using
      PaperBandQuadraticGeometry.primeCoefficientL2Sq_liftBandCoefficient P q.1
  have hsfLower :
      primeReferenceQuadratic n c - profileLoss * P.data.bandNormSq q.1 ≤
        subtypeSquarefreeQuadratic law c := by
    have h := (abs_le.mp hsf).1
    rw [hnorm] at h
    simpa only [profileLoss] using (show
      primeReferenceQuadratic n c - profileLoss * P.data.bandNormSq q.1 ≤
        subtypeSquarefreeQuadratic law c by linarith)
  have hfullLower :
      subtypeSquarefreeQuadratic law c - R * P.data.bandNormSq q.1 ≤
        subtypeFullQuadratic law c := by
    have h := (abs_le.mp hfull).1
    rw [hnorm] at h
    linarith
  dsimp only [c]
  have hband : 0 ≤ P.data.bandNormSq q.1 :=
    P.data.bandNormSq_nonneg q.1
  dsimp only [profileLoss] at hsfLower
  nlinarith

end Erdos390.Full.PaperActualBandQuadraticTransfer

namespace Erdos390.Full.PaperBridgeFit.BridgeData

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open FiniteSignedQuadraticEntryTransfer
open PaperSquarefreeSlowQuadraticLower
open PaperActualBandQuadraticTransfer
open PaperPrimePowerChamberError
open PaperWeightedInverseExport
open PrimeSquarefreeDirichletGeometry
open SquarefreeCovarianceReference

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : PaperBridgeFit.BridgeData Head Band)

/-- The arbitrary band-lift full quadratic is exactly the covariance of
the literal full-valuation band score. -/
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
        c p * ArithmeticModel.valuation p.1 (B.sampleData.value m) := by
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

/-- Finite actual-law full band gap, with all squarefree-profile,
prime-power, and row-residual losses explicit.  This is before the
head/physical nuisance Schur subtraction. -/
theorem exists_actualFull_bandCovariance_lower_of_profiles_and_row
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Set.Icc epsilon (1 - epsilon))
    (hmass : 0 < FiniteAnchoredDirichletQuadratic.anchorMass
      (primeWeight B.sampleData.n) anchor)
    {rowError Eprofile CKernel totalWeight invW R : ℝ}
    (hEprofile : 0 ≤ Eprofile) (hCKernel : 0 ≤ CKernel)
    (hR : 0 ≤ R) (hW : 0 < B.sampleData.W)
    (hTotal : (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        reciprocalWeight p) ≤ totalWeight)
    (hInvW : (1 / (B.sampleData.W : ℝ)) ≤ invW)
    (hrowReference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |FiniteAnchoredDirichletQuadratic.rowResidual
          (primeWeight B.sampleData.n) (primeDiagonal B.sampleData.n)
          (primeKernel B.sampleData.n) p| ≤
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
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ q : B.RawBandGauge,
        ((kappa / 2) *
              FiniteAnchoredDirichletQuadratic.anchorMass
                (primeWeight B.sampleData.n) anchor -
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
  obtain ⟨kappa, hkappa, hgap⟩ :=
    exists_subtypeFull_band_lower_of_entry_and_row
      B.partition B.n_gt_one (B.actualValuationLaw xi)
      hepsilon hhalf anchor hinterior hmass
      (mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hEprofile))
      (add_nonneg (sq_nonneg _) hCKernel) hR hW hTotal hInvW
      hrowReference hentry hrowPower
  refine ⟨kappa, hkappa, ?_⟩
  intro q
  rw [B.subtypeFullQuadratic_actual_eq_bandCovariance xi q] at hgap
  exact hgap q

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
  simpa only [Erdos390.Lemma84.WeightedBandData.bandNormSq,
    Erdos390.Lemma84.WeightedBandData.bandInner] using hcs

/-- A reciprocal marked nuisance family costs only
`card(Z) * Cmarked^2 * sum_j H_j / gamma` in the actual Schur quadratic
form.  No inverse center and hence no `1 / alpha_0` occurs. -/
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
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
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
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (B.harmonicMass_pos j).le (abs_nonneg _)
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

/-- Complete finite Schur `D`-gap for an arbitrary raw-gauge band vector.
The reference, signed-profile, prime-power, and nuisance losses are all
relative coefficients of the same arithmetic `D`-norm. -/
theorem exists_actualBandSchur_Dgap_of_profiles_rows_marked
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma Cmarked : ℝ}
    (hgamma : 0 < gamma) (hCmarked : 0 ≤ Cmarked)
    (hgapNuisance : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Set.Icc epsilon (1 - epsilon))
    (hmass : 0 < FiniteAnchoredDirichletQuadratic.anchorMass
      (primeWeight B.sampleData.n) anchor)
    {rowError Eprofile CKernel totalWeight invW R : ℝ}
    (hEprofile : 0 ≤ Eprofile) (hCKernel : 0 ≤ CKernel)
    (hR : 0 ≤ R) (hW : 0 < B.sampleData.W)
    (hTotal : (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        reciprocalWeight p) ≤ totalWeight)
    (hInvW : (1 / (B.sampleData.W : ℝ)) ≤ invW)
    (hrowReference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |FiniteAnchoredDirichletQuadratic.rowResidual
          (primeWeight B.sampleData.n) (primeDiagonal B.sampleData.n)
          (primeKernel B.sampleData.n) p| ≤
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
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ q : B.RawBandGauge,
        ((kappa / 2) *
              FiniteAnchoredDirichletQuadratic.anchorMass
                (primeWeight B.sampleData.n) anchor -
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
  obtain ⟨kappa, hkappa, hfull⟩ :=
    B.exists_actualFull_bandCovariance_lower_of_profiles_and_row
      xi hepsilon hhalf anchor hinterior hmass hEprofile hCKernel hR hW
      hTotal hInvW hrowReference hpair hsingle hKernel hrowPower
  refine ⟨kappa, hkappa, ?_⟩
  intro q
  let F : B.sampleData.Sample → ℝ := B.bandRegressionScore q
  have hloss := B.nuisanceRegressionLoss_bandScore_le_of_marked
    xi hgamma hCmarked hgapNuisance hmarked q
  have hvariance := B.nuisanceResidualScore_variance_identity
    xi hgamma hgapNuisance F
  have hschur := B.actualBandSchur_quadratic_eq_residualVariance
    xi hgamma hgapNuisance q
  have hfullq := hfull q
  change (B.tiltedLaw xi).covariance F F = _ - _ at hvariance
  rw [← hvariance] at hfullq
  rw [← hschur] at hfullq
  dsimp only [F] at hfullq hloss
  have hband : 0 ≤ B.partition.data.bandNormSq q.1 :=
    B.partition.data.bandNormSq_nonneg q.1
  nlinarith

end Erdos390.Full.PaperBridgeFit.BridgeData
