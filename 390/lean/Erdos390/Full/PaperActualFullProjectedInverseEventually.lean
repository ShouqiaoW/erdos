import Erdos390.Full.CanonicalEndpointWeightedInverseEventually
import Erdos390.Full.CanonicalEndpointCenterEnvelopeEventually
import Erdos390.Full.PaperActualFullProjectedInverseAssembly
import Erdos390.Full.PaperBridgeCanonicalPowerCorrectionTriangle
import Erdos390.Full.PaperBridgeCanonicalPhysicalPowerCorrectionEventually
import Erdos390.Full.PoissonDickmanKernelBounds

/-!
# Eventual inverse for the literal actual full projected operator

This file performs the two stable perturbations in the order used in
Section 8.4.  First the canonical arithmetic reference is perturbed to the
actual squarefree operator; then the proved full-versus-squarefree sharp row
is inserted.  The two perturbation radii and every inverse constant are
chosen before the ambient integer.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimeSums PaperWeightedInverseExport
open OmittedTiltPairChamber PaperPrimePowerChamberError

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Fixed reference-inverse constant obtained from the lower bound `width/2`
for the anchor cell. -/
def canonicalReferenceInverseConstant (kappa width : ℝ) : ℝ :=
  16 / (kappa * width)

/-- Common row radius reserved for each of the two Neumann perturbations. -/
def canonicalProjectedPerturbationRadius (C : ℝ) : ℝ :=
  1 / (8 * C)

theorem canonicalReferenceInverseConstant_pos
    {kappa width : ℝ} (hkappa : 0 < kappa) (hwidth : 0 < width) :
    0 < canonicalReferenceInverseConstant kappa width := by
  exact div_pos (by norm_num) (mul_pos hkappa hwidth)

/-- The varying inverse constant emitted by the literal interval mesh is
bounded by a constant depending only on the continuum gap and the fixed
anchor-cell width. -/
theorem canonical_varyingInverseConstant_le
    {kappa width anchorMass : ℝ}
    (hkappa : 0 < kappa) (hwidth : 0 < width)
    (hAnchor : width / 2 ≤ anchorMass) :
    (4 / (kappa * anchorMass)) /
        (1 - (4 / (kappa * anchorMass)) *
          (2 * (kappa * (width / 2) / 16))) ≤
      canonicalReferenceInverseConstant kappa width := by
  have hAnchorPos : 0 < anchorMass :=
    (half_pos hwidth).trans_le hAnchor
  have hkAnchor : 0 < kappa * anchorMass :=
    mul_pos hkappa hAnchorPos
  have hkWidth : 0 < kappa * width := mul_pos hkappa hwidth
  let base : ℝ := 4 / (kappa * anchorMass)
  let loss : ℝ := base * (2 * (kappa * (width / 2) / 16))
  have hbasePos : 0 < base := by
    dsimp only [base]
    exact div_pos (by norm_num) hkAnchor
  have hlossId : loss = width / (4 * anchorMass) := by
    dsimp only [loss, base]
    field_simp [ne_of_gt hkappa, ne_of_gt hAnchorPos]
    ring
  have hlossLe : loss ≤ 1 / 2 := by
    rw [hlossId]
    apply (div_le_iff₀ (mul_pos (by norm_num) hAnchorPos)).2
    nlinarith
  have hdenHalf : 1 / 2 ≤ 1 - loss := by linarith
  have hdenPos : 0 < 1 - loss := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hdenHalf
  have hbaseBound : base ≤ 8 / (kappa * width) := by
    dsimp only [base]
    apply (div_le_div_iff₀ hkAnchor hkWidth).2
    nlinarith [mul_nonneg hkappa.le (sub_nonneg.mpr hAnchor)]
  change base / (1 - loss) ≤ canonicalReferenceInverseConstant kappa width
  calc
    base / (1 - loss) ≤ base / (1 / 2) :=
      div_le_div_of_nonneg_left hbasePos.le (by norm_num) hdenHalf
    _ = 2 * base := by ring
    _ ≤ 2 * (8 / (kappa * width)) :=
      mul_le_mul_of_nonneg_left hbaseBound (by norm_num)
    _ = canonicalReferenceInverseConstant kappa width := by
      unfold canonicalReferenceInverseConstant
      ring

theorem canonicalProjectedPerturbationRadius_pos
    {C : ℝ} (hC : 0 < C) :
    0 < canonicalProjectedPerturbationRadius C := by
  exact div_pos (by norm_num) (mul_pos (by norm_num) hC)

theorem canonicalProjectedPerturbationRadius_first_small
    {C : ℝ} (hC : 0 < C) :
    C * (2 * canonicalProjectedPerturbationRadius C) < 1 := by
  unfold canonicalProjectedPerturbationRadius
  field_simp [ne_of_gt hC]
  norm_num

theorem canonicalProjectedPerturbationRadius_second_small
    {C : ℝ} (hC : 0 < C) :
    (C / (1 - C * (2 * canonicalProjectedPerturbationRadius C))) *
        (2 * canonicalProjectedPerturbationRadius C) < 1 := by
  unfold canonicalProjectedPerturbationRadius
  field_simp [ne_of_gt hC]
  norm_num

theorem canonicalProjectedPerturbation_finalConstant
    {C : ℝ} (hC : 0 < C) :
    (C / (1 - C * (2 * canonicalProjectedPerturbationRadius C))) /
        (1 - (C / (1 - C *
          (2 * canonicalProjectedPerturbationRadius C))) *
            (2 * canonicalProjectedPerturbationRadius C)) =
      2 * C := by
  unfold canonicalProjectedPerturbationRadius
  field_simp [ne_of_gt hC]
  ring

/-- The two already-audited residual rows (physical second tilt and guard
deletion) in the exact combination exported by the canonical prime-power
terminal. -/
def canonicalCombinedPowerCorrection
    (P : Head → HeadPattern.Pattern)
    (I : PaperGuardCensus.PhysicalIntervals)
    (Cmax : ℝ) (Cprom Cbank W : ℕ) (Acoef Aphys : ℝ)
    (n : ℕ) : ℝ :=
  physicalPowerCorrectionRowError
      (canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax n)
      (canonicalPhysicalPowerCorrectionConstant P I Cmax W Acoef) n W +
    guardPowerCorrectionWeightedMajorant Cprom Cbank
      (PaperStatisticNorm.valuationLogCoefficient Cmax W)
      (canonicalGuardPerturbationConstant P I
        (Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W)) n

omit [DecidableEq Head] in theorem canonicalCombinedPowerCorrection_nonneg
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern)
    (I : PaperGuardCensus.PhysicalIntervals)
    {Cmax Acoef Aphys : ℝ} {Cprom Cbank W n : ℕ}
    (hCmax : 1 ≤ Cmax)
    (hAphys : 0 ≤ Aphys) (hW : 1 < W) (hn : 1 < n) :
    0 ≤ canonicalCombinedPowerCorrection
      P I Cmax Cprom Cbank W Acoef Aphys n := by
  have hLpos : 0 < Scale.L n := Scale.L_pos hn
  have hlogCmax : 0 ≤ Real.log Cmax := Real.log_nonneg hCmax
  have hepsilon : 0 ≤
      canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax n := by
    unfold canonicalPhysicalPowerCorrectionEpsilon
    exact div_nonneg (mul_nonneg hAphys hlogCmax) hLpos.le
  have hG : 0 ≤
      canonicalPhysicalPowerCorrectionConstant P I Cmax W Acoef :=
    canonicalPhysicalPowerCorrectionConstant_nonneg P I Cmax W Acoef
  have hphysical : 0 ≤
      physicalPowerCorrectionRowError
        (canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax n)
        (canonicalPhysicalPowerCorrectionConstant P I Cmax W Acoef) n W :=
    physicalPowerCorrectionRowError_nonneg hepsilon hG
  have hCenv : 0 ≤
      PaperStatisticNorm.valuationLogCoefficient Cmax W :=
    PaperStatisticNorm.valuationLogCoefficient_nonneg hCmax hW
  have hD : 0 ≤ canonicalGuardPerturbationConstant P I
      (Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W) :=
    canonicalGuardPerturbationConstant_nonneg P I _
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hcensus : 0 ≤
      PaperGuardCensus.censusRatioMajorant Cprom Cbank n := by
    unfold PaperGuardCensus.censusRatioMajorant
    have hcoef : 0 ≤ (Cprom : ℝ) +
        3 * (Cbank : ℝ) * (Scale.L n + 2) := by positivity
    exact div_nonneg
      (mul_nonneg hcoef (Scale.y_pos hn0).le) (by positivity)
  have hguard : 0 ≤ guardPowerCorrectionWeightedMajorant Cprom Cbank
      (PaperStatisticNorm.valuationLogCoefficient Cmax W)
      (canonicalGuardPerturbationConstant P I
        (Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W)) n := by
    unfold guardPowerCorrectionWeightedMajorant
    exact mul_nonneg (Nat.cast_nonneg _)
      (PaperGuardCensus.guardPowerCorrectionRowError_nonneg
        (mul_nonneg hCenv hLpos.le) (mul_nonneg hD hcensus))
  unfold canonicalCombinedPowerCorrection
  exact add_nonneg hphysical hguard

/-- Uniform full-versus-squarefree row budget after inserting the canonical
reciprocal-centre envelope.  Its first term is the fixed-cutoff loss; the
other two terms vanish with `n`. -/
def canonicalFullSharpRemainder
    (epsilon combined : ℕ → ℝ)
    (Cpow Calpha K : ℝ) (W n : ℕ) : ℝ :=
  3 * Cpow * (K + 1) * (1 / (W : ℝ)) +
    3 * epsilon n *
      (K * (Calpha * Real.log (Scale.L n)) + 1) *
        (1 / (W : ℝ)) +
    combined n * (Calpha * Real.log (Scale.L n))

/-- The two sharp moving-low rates leave only the explicit fixed-cutoff
prime-power loss. -/
theorem tendsto_canonicalFullSharpRemainder
    (epsilon combined : ℕ → ℝ)
    (Cpow Calpha K : ℝ) (W : ℕ)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0))
    (hcombinedRate : Tendsto
      (fun n : ℕ ↦ combined n * Real.log (Scale.L n))
        atTop (nhds 0)) :
    Tendsto
      (canonicalFullSharpRemainder epsilon combined Cpow Calpha K W)
      atTop
      (nhds (3 * Cpow * (K + 1) * (1 / (W : ℝ)))) := by
  have hmiddleCore : Tendsto (fun n : ℕ ↦
      K * Calpha * (epsilon n * Real.log (Scale.L n)) + epsilon n)
      atTop (nhds 0) := by
    have hfirst : Tendsto (fun n : ℕ ↦
        (K * Calpha) *
          (epsilon n * Real.log (Scale.L n))) atTop (nhds 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hepsilonRate : Tendsto
          (fun n : ℕ ↦ (K * Calpha) *
            (epsilon n * Real.log (Scale.L n)))
            atTop (nhds ((K * Calpha) * 0)))
    simpa only [add_zero] using hfirst.add hepsilon
  have hmiddle : Tendsto (fun n : ℕ ↦
      3 * epsilon n *
        (K * (Calpha * Real.log (Scale.L n)) + 1) *
          (1 / (W : ℝ))) atTop (nhds 0) := by
    have hscaled : Tendsto (fun n : ℕ ↦
        (3 * (1 / (W : ℝ))) *
          (K * Calpha *
            (epsilon n * Real.log (Scale.L n)) + epsilon n))
        atTop (nhds 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hmiddleCore : Tendsto
          (fun n : ℕ ↦ (3 * (1 / (W : ℝ))) *
            (K * Calpha *
              (epsilon n * Real.log (Scale.L n)) + epsilon n))
            atTop (nhds ((3 * (1 / (W : ℝ))) * 0)))
    apply hscaled.congr'
    filter_upwards with n
    ring
  have hlast : Tendsto (fun n : ℕ ↦
      combined n * (Calpha * Real.log (Scale.L n)))
      atTop (nhds 0) := by
    have hscaled : Tendsto (fun n : ℕ ↦
        Calpha * (combined n * Real.log (Scale.L n)))
        atTop (nhds 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hcombinedRate : Tendsto
          (fun n : ℕ ↦
            Calpha * (combined n * Real.log (Scale.L n)))
              atTop (nhds (Calpha * 0)))
    apply hscaled.congr'
    filter_upwards with n
    ring
  have hconst : Tendsto (fun _n : ℕ ↦
      3 * Cpow * (K + 1) * (1 / (W : ℝ))) atTop
      (nhds (3 * Cpow * (K + 1) * (1 / (W : ℝ)))) :=
    tendsto_const_nhds
  simpa only [canonicalFullSharpRemainder, add_zero] using
    (hconst.add hmiddle).add hlast

/-- Insert the reciprocal-centre and reciprocal-prime-mass envelopes into
the literal full-versus-squarefree row.  This is deliberately a finite
inequality: all limiting statements remain outside this lemma. -/
theorem fullSharpRow_le_canonicalFullSharpRemainder
    [Nonempty Head]
    (xi : B.ParamSpace)
    (epsilon combined : ℕ → ℝ)
    {Cpow Calpha K : ℝ}
    (hCpow : 0 ≤ Cpow)
    (hepsilon : 0 ≤ epsilon B.sampleData.n)
    (hcombined : 0 ≤ combined B.sampleData.n)
    (hW : B.sampleData.W ≠ 0)
    (hBandT : bandTReciprocalSum B.sampleData.n B.sampleData.W ≤ K)
    (hcenterInv : ∀ i : Band,
      1 / B.partition.center i ≤
        Calpha * Real.log (Scale.L B.sampleData.n))
    (q : Band → ℝ) (i : Band)
    (hrow :
      |PrimePowerSharpBandTransfer.fullSharpRow
            (B.actualValuationLaw xi) B.partition q i -
          SquarefreeSharpBandTransfer.squarefreeSharpRow
            (B.actualValuationLaw xi) B.partition q i| ≤
        3 * Cpow *
              (bandTReciprocalSum B.sampleData.n B.sampleData.W + 1) *
              (1 / (B.sampleData.W : ℝ)) +
          3 * epsilon B.sampleData.n *
              (bandTReciprocalSum B.sampleData.n B.sampleData.W /
                    B.partition.center i + 1) *
              (1 / (B.sampleData.W : ℝ)) +
          combined B.sampleData.n / B.partition.center i) :
      |PrimePowerSharpBandTransfer.fullSharpRow
            (B.actualValuationLaw xi) B.partition q i -
          SquarefreeSharpBandTransfer.squarefreeSharpRow
            (B.actualValuationLaw xi) B.partition q i| ≤
        canonicalFullSharpRemainder epsilon combined Cpow Calpha K
          B.sampleData.W B.sampleData.n := by
  have hBandT0 : 0 ≤
      bandTReciprocalSum B.sampleData.n B.sampleData.W := by
    unfold bandTReciprocalSum
    apply Finset.sum_nonneg
    intro p hp
    exact div_nonneg (B.bandPrime_tPrime_pos ⟨p, hp⟩).le (by positivity)
  have hK0 : 0 ≤ K := hBandT0.trans hBandT
  have hcenterPos : 0 < B.partition.center i :=
    B.partition.center_pos B.n_gt_one i
  have hcenterInv' : (B.partition.center i)⁻¹ ≤
      Calpha * Real.log (Scale.L B.sampleData.n) := by
    simpa only [one_div] using hcenterInv i
  have hCL0 : 0 ≤ Calpha * Real.log (Scale.L B.sampleData.n) :=
    (one_div_pos.mpr hcenterPos).le.trans (hcenterInv i)
  have hWInv0 : 0 ≤ 1 / (B.sampleData.W : ℝ) := by positivity
  have hfirst :
      3 * Cpow *
            (bandTReciprocalSum B.sampleData.n B.sampleData.W + 1) *
            (1 / (B.sampleData.W : ℝ)) ≤
        3 * Cpow * (K + 1) * (1 / (B.sampleData.W : ℝ)) := by
    gcongr
  have hmiddleCore :
      bandTReciprocalSum B.sampleData.n B.sampleData.W /
            B.partition.center i + 1 ≤
        K * (Calpha * Real.log (Scale.L B.sampleData.n)) + 1 := by
    rw [div_eq_mul_inv]
    simpa only [add_comm] using add_le_add_right
      (mul_le_mul hBandT hcenterInv'
        (inv_nonneg.mpr hcenterPos.le) hK0) 1
  have hmiddle :
      3 * epsilon B.sampleData.n *
            (bandTReciprocalSum B.sampleData.n B.sampleData.W /
                  B.partition.center i + 1) *
            (1 / (B.sampleData.W : ℝ)) ≤
        3 * epsilon B.sampleData.n *
            (K * (Calpha * Real.log (Scale.L B.sampleData.n)) + 1) *
            (1 / (B.sampleData.W : ℝ)) := by
    gcongr
  have hlast :
      combined B.sampleData.n / B.partition.center i ≤
        combined B.sampleData.n *
          (Calpha * Real.log (Scale.L B.sampleData.n)) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hcenterInv' hcombined
  exact hrow.trans (by
    unfold canonicalFullSharpRemainder
    linarith)

/-- Literal equality transport for the squarefree profile estimate. -/
theorem abs_actual_squarefreeSharpRow_sub_equalPartitionArithmetic_le
    [Nonempty Head]
    (xi : B.ParamSpace)
    {P : ArithmeticBandGeometry.Partition
      B.sampleData.n B.sampleData.W Band}
    (hP : B.partition = P)
    (cert : PositiveCellTransfer.IntervalCertificate P)
    {Eprofile Calpha K CKernel : ℝ}
    (hEprofile : 0 ≤ Eprofile)
    (hW : 1 < B.sampleData.W)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p q 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p q 1 1)| ≤
        Eprofile * pairWeight p q 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel)
    (hBandT : bandTReciprocalSum B.sampleData.n B.sampleData.W ≤ K)
    (hcenterInv : ∀ i : Band,
      1 / P.center i ≤ Calpha * Real.log (Scale.L B.sampleData.n))
    (q : Band → ℝ) (hq : ∀ j, |q j| ≤ 1) (i : Band) :
    |SquarefreeSharpBandTransfer.squarefreeSharpRow
        (B.actualValuationLaw xi) B.partition q i -
      CompressedArithmeticOperator.arithmeticSharpOperator
        (y B.sampleData.n) cert.lower cert.upper P.center q i| ≤
      squarefreeSharpProfileRemainder
        (fun _n ↦ Eprofile) Calpha K CKernel
          B.sampleData.W B.sampleData.n := by
  subst P
  exact B.abs_actual_squarefreeSharpRow_sub_arithmetic_le_profileRemainder
    xi cert hEprofile hW hpair hsingle hKernel hBandT hcenterInv q hq i

/-- Deterministic two-stage inverse attachment.  This theorem keeps the two
Neumann smallness checks separate, so a later eventual theorem cannot hide a
circular choice of the full-valuation box. -/
theorem exists_actualFullProjectedEquiv_of_reference_of_unitSharpRows
    [Nonempty Head]
    (xi : B.ParamSpace)
    (cert : PositiveCellTransfer.IntervalCertificate B.partition)
    (referenceEquiv :
      SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
        SharpGaugeSpace B.partition.mass B.partition.center)
    (hreference : ∀ q, referenceEquiv q =
      ArithmeticGaugeStableInverse.projectedSharpCLM
        (CompressedArithmeticOperator.arithmeticDiagonal
          (y B.sampleData.n) cert.lower cert.upper)
        (CompressedArithmeticOperator.arithmeticKernel
          (y B.sampleData.n) cert.lower cert.upper)
        B.partition.center
        (MovingLowGaugeTransfer.sharpWeight
          B.partition.mass B.partition.center)
        (ne_of_gt (B.actualSharpWeightTotal_pos)) q)
    {C rSquare rFull : ℝ}
    (hC : 0 ≤ C) (hrSquare : 0 ≤ rSquare) (hrFull : 0 ≤ rFull)
    (hinv : ∀ v, ‖referenceEquiv.symm v‖ ≤ C * ‖v‖)
    (hsmallSquare : C * (2 * rSquare) < 1)
    (hrowSquare : ∀ q : Band → ℝ, (∀ j, |q j| ≤ 1) → ∀ i : Band,
      |SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        CompressedArithmeticOperator.arithmeticSharpOperator
          (y B.sampleData.n) cert.lower cert.upper
            B.partition.center q i| ≤ rSquare)
    (hsmallFull :
      (C / (1 - C * (2 * rSquare))) * (2 * rFull) < 1)
    (hrowFull : ∀ q : Band → ℝ, (∀ j, |q j| ≤ 1) → ∀ i : Band,
      |PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i| ≤ rFull) :
    ∃ actualEquiv :
      SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
        SharpGaugeSpace B.partition.mass B.partition.center,
      (∀ q, actualEquiv q = B.actualFullProjectedCLM xi q) ∧
      ∀ v, ‖actualEquiv.symm v‖ ≤
        ((C / (1 - C * (2 * rSquare))) /
          (1 - (C / (1 - C * (2 * rSquare))) * (2 * rFull))) * ‖v‖ := by
  obtain ⟨squarefreeEquiv, hsquarefree, hinvSquare⟩ :=
    B.exists_actualSquarefreeProjectedEquiv_of_reference
      xi cert referenceEquiv hreference hC hrSquare hinv
        hsmallSquare hrowSquare
  exact B.exists_actualFullProjectedEquiv_of_squarefree_of_unitSharpRows
    xi squarefreeEquiv hsquarefree
      (by
        have hden : 0 < 1 - C * (2 * rSquare) := sub_pos.mpr hsmallSquare
        exact div_nonneg hC hden.le)
      hrFull hinvSquare hsmallFull hrowFull

/-- Equality transport from an explicitly constructed canonical partition to
the partition stored in `BridgeData`.  Keeping this transport as a separate
lemma makes clear that no analytic comparison of two partitions is being
assumed: they must be literally equal. -/
theorem exists_actualFullProjectedEquiv_of_equal_referencePartition
    [Nonempty Head]
    (xi : B.ParamSpace)
    {P : ArithmeticBandGeometry.Partition
      B.sampleData.n B.sampleData.W Band}
    (hP : B.partition = P)
    (cert : PositiveCellTransfer.IntervalCertificate P)
    (referenceEquiv :
      SharpGaugeSpace P.mass P.center ≃L[ℝ]
        SharpGaugeSpace P.mass P.center)
    (hreference : ∀ q, referenceEquiv q =
      ArithmeticGaugeStableInverse.projectedSharpCLM
        (CompressedArithmeticOperator.arithmeticDiagonal
          (y B.sampleData.n) cert.lower cert.upper)
        (CompressedArithmeticOperator.arithmeticKernel
          (y B.sampleData.n) cert.lower cert.upper)
        P.center
        (MovingLowGaugeTransfer.sharpWeight P.mass P.center)
        (by
          change (∑ j, P.mass j * P.center j ^ 2) ≠ 0
          apply ne_of_gt
          apply Finset.sum_pos
          · intro j _hj
            exact mul_pos (P.data.mass_pos j)
              (sq_pos_of_pos (P.center_pos B.n_gt_one j))
          · exact ⟨B.lowBand, Finset.mem_univ _⟩) q)
    {C rSquare rFull : ℝ}
    (hC : 0 ≤ C) (hrSquare : 0 ≤ rSquare) (hrFull : 0 ≤ rFull)
    (hinv : ∀ v, ‖referenceEquiv.symm v‖ ≤ C * ‖v‖)
    (hsmallSquare : C * (2 * rSquare) < 1)
    (hrowSquare : ∀ q : Band → ℝ, (∀ j, |q j| ≤ 1) → ∀ i : Band,
      |SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        CompressedArithmeticOperator.arithmeticSharpOperator
          (y B.sampleData.n) cert.lower cert.upper P.center q i| ≤ rSquare)
    (hsmallFull :
      (C / (1 - C * (2 * rSquare))) * (2 * rFull) < 1)
    (hrowFull : ∀ q : Band → ℝ, (∀ j, |q j| ≤ 1) → ∀ i : Band,
      |PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i| ≤ rFull) :
    ∃ actualEquiv :
      SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
        SharpGaugeSpace B.partition.mass B.partition.center,
      (∀ q, actualEquiv q = B.actualFullProjectedCLM xi q) ∧
      ∀ v, ‖actualEquiv.symm v‖ ≤
        ((C / (1 - C * (2 * rSquare))) /
          (1 - (C / (1 - C * (2 * rSquare))) * (2 * rFull))) * ‖v‖ := by
  subst P
  exact B.exists_actualFullProjectedEquiv_of_reference_of_unitSharpRows
    xi cert referenceEquiv hreference hC hrSquare hrFull hinv
      hsmallSquare hrowSquare hsmallFull hrowFull

set_option maxHeartbeats 1600000 in
/-- End-to-end eventual inverse for the literal full-valuation projected
operator on the canonical moving-low partition.

The constants and mesh tolerance are fixed first.  Then a single cutoff is
chosen; only the final ambient threshold may depend on that cutoff.  After
that threshold, the hypotheses are exactly constructor equalities for the
sample and partition, together with the two preselected coefficient-box
bounds.  In particular no squarefree reference inverse, Lemma 7.5 bound, or
prime-power row estimate occurs among the hypotheses. -/
theorem exists_meshTolerance_cutoff_eventually_canonical_actualFullProjected_inverse
    [Nonempty Head]
    {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
    (hdelta : 0 < delta)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hhalf : epsilon < 1 / 2)
    (anchorCell : Fin M.cellCount)
    (hIdealLower : epsilon < M.lower anchorCell)
    (hIdealUpper : M.upper anchorCell ≤ 1 - epsilon)
    (Phead : Head → HeadPattern.Pattern)
    (I : PaperGuardCensus.PhysicalIntervals) (Cmax : ℝ)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (Cprom Cbank : ℕ)
    (ledger : ∀ n, PaperGuardCensus.Ledger n Cprom Cbank) :
    ∃ Cfull : ℝ, 0 < Cfull ∧ ∃ meshTol : ℝ, 0 < meshTol ∧
      ((delta < meshTol ∧
          ∀ k : Fin M.cellCount, M.width k < meshTol) →
        ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
          (∀ h, (Phead h).modulus ≤ W) →
          ∀ Acoef Aphys : ℝ, 0 ≤ Acoef → 0 ≤ Aphys →
          ∀ᶠ n : ℕ in atTop,
            ∀ (B : BridgeData Head (Fin (M.cellCount + 1)))
              (xi : B.ParamSpace),
              B.sampleData.n = n → B.sampleData.W = W →
              ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
                  physicalBound (I.lower .plus) B.sampleData.n)
                (hremaining : ∀ c : Cell Head,
                  (PaperGuardCensus.rawCell Phead I B.sampleData.n c \
                    (ledger B.sampleData.n).guards).Nonempty),
                B.sampleData = PaperGuardCensus.canonicalSampleData
                    (W := B.sampleData.W) Phead I
                      (ledger B.sampleData.n) hsep hremaining →
                (∃ (hWne : B.sampleData.W ≠ 0)
                    (S : RegularMeshPrimeCutoffs.ScaleSeparation
                      M B.sampleData.n B.sampleData.W),
                  B.partition =
                    RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                      M hdelta B.n_gt_one hWne S) →
                (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                  |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
                |xi MomentCoord.physical| ≤ Aphys →
                ∃ actualEquiv :
                  SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
                    SharpGaugeSpace B.partition.mass B.partition.center,
                  (∀ q, actualEquiv q = B.actualFullProjectedCLM xi q) ∧
                  ∀ v, ‖actualEquiv.symm v‖ ≤ Cfull * ‖v‖) := by
  obtain ⟨kappa, hkappa, meshTol, hmeshTol, hcanonicalInverse⟩ :=
    RegularMeshPrimeCutoffs.Mesh.exists_meshTolerance_cutoff_eventually_canonical_projected_inverse
        M hdelta hepsilon hhalf anchorCell hIdealLower hIdealUpper
  obtain ⟨Calpha, hCalpha, Wcenter, hcenterEvent⟩ :=
    RegularMeshPrimeCutoffs.Mesh.exists_cutoff_eventually_canonical_center_inverse_logL M hdelta
  obtain ⟨hCpow, hfullRowTerminal⟩ :=
    boxIndependent_canonicalRaw_fullSharp
      Phead I Cmax hlowerOne hupperMax Cprom Cbank ledger
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  obtain ⟨CKernel, hCKernel, hKernelBound⟩ :=
    PoissonDickmanKernelBounds.exists_covarianceKernel_abs_le_second
  let width : ℝ := M.width anchorCell
  let Cref : ℝ := canonicalReferenceInverseConstant kappa width
  let r : ℝ := canonicalProjectedPerturbationRadius Cref
  let Cfull : ℝ := 2 * Cref
  have hwidth : 0 < width := by
    dsimp only [width]
    exact M.width_pos hdelta anchorCell
  have hCref : 0 < Cref := by
    dsimp only [Cref]
    exact canonicalReferenceInverseConstant_pos hkappa hwidth
  have hr : 0 < r := by
    dsimp only [r]
    exact canonicalProjectedPerturbationRadius_pos hCref
  have hCfull : 0 < Cfull := by
    dsimp only [Cfull]
    positivity
  refine ⟨Cfull, hCfull, meshTol, hmeshTol, ?_⟩
  intro hmesh
  obtain ⟨_CRow, _hCRow, Winverse, hinverseEvent⟩ :=
    hcanonicalInverse hmesh
  let K : ℝ := 2 * Real.log 4
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hInvNat : Tendsto (fun W : ℕ ↦ 1 / (W : ℝ))
      atTop (nhds 0) := by
    have hinv : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    have h := hinv.comp tendsto_natCast_atTop_atTop
    simpa only [one_div] using h
  let squareTailConstant : ℝ :=
    (1 / DickmanBasic.rho DickmanBasic.U) ^ 2 + CKernel
  have hSquareTail : Tendsto (fun W : ℕ ↦
      squareTailConstant * (1 / (W : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hInvNat : Tendsto
        (fun W : ℕ ↦ squareTailConstant * (1 / (W : ℝ)))
          atTop (nhds (squareTailConstant * 0)))
  let fullTailConstant : ℝ := 3 * Cpow * (K + 1)
  have hFullTail : Tendsto (fun W : ℕ ↦
      fullTailConstant * (1 / (W : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hInvNat : Tendsto
        (fun W : ℕ ↦ fullTailConstant * (1 / (W : ℝ)))
          atTop (nhds (fullTailConstant * 0)))
  obtain ⟨Wsquare, hWsquare⟩ := eventually_atTop.1
    (hSquareTail.eventually (eventually_lt_nhds hr))
  obtain ⟨Wfull, hWfull⟩ := eventually_atTop.1
    (hFullTail.eventually (eventually_lt_nhds hr))
  let W₀ := max 2 (max Winverse (max Wcenter (max Wsquare Wfull)))
  refine ⟨W₀, ?_⟩
  intro W hWcutoff hmod
  have hWtwo : 2 ≤ W := (le_max_left 2 _).trans hWcutoff
  have hWone : 1 < W := by omega
  have hWne : W ≠ 0 := by omega
  have hWinverse : Winverse ≤ W := by
    exact ((le_max_left Winverse _).trans (le_max_right 2 _)).trans hWcutoff
  have hWcenter : Wcenter ≤ W := by
    exact ((le_max_left Wcenter (max Wsquare Wfull)).trans
      (le_max_right Winverse _)).trans ((le_max_right 2 _).trans hWcutoff)
  have hWsquare' : Wsquare ≤ W := by
    exact ((le_max_left Wsquare Wfull).trans
      (le_max_right Wcenter _)).trans
        ((le_max_right Winverse _).trans ((le_max_right 2 _).trans hWcutoff))
  have hWfull' : Wfull ≤ W := by
    exact ((le_max_right Wsquare Wfull).trans
      (le_max_right Wcenter _)).trans
        ((le_max_right Winverse _).trans ((le_max_right 2 _).trans hWcutoff))
  have hSquareTailLt :
      squareTailConstant * (1 / (W : ℝ)) < r := hWsquare W hWsquare'
  have hFullTailLt :
      fullTailConstant * (1 / (W : ℝ)) < r := hWfull W hWfull'
  intro Acoef Aphys hAcoef hAphys
  obtain ⟨profileError, hprofile0, hprofileT, hprofileRate,
      Nprofile, hprofile⟩ :=
    exists_boxIndependent_actual_component_signed_profiles
      Phead I Cmax hlowerOne hupperMax Cprom Cbank ledger
        W hWone
          (fun h p hp ↦
            PaperPrimePowerAuxiliaryPrime.headPrime_le_cutoff_of_modulus_le
              (Phead h) (hmod h) p hp)
          Acoef Aphys hAcoef hAphys
  obtain ⟨epsilon75, hepsilon0, hepsilonT, hepsilonRate,
      hcombinedRateRaw, Nfull, hfullRaw⟩ :=
    hfullRowTerminal W hWone
      (fun h p hp ↦
        PaperPrimePowerAuxiliaryPrime.headPrime_le_cutoff_of_modulus_le
          (Phead h) (hmod h) p hp)
      Acoef hAcoef Aphys hAphys
  let combined : ℕ → ℝ := fun n ↦
    canonicalCombinedPowerCorrection
      Phead I Cmax Cprom Cbank W Acoef Aphys n
  have hcombinedRate : Tendsto
      (fun n : ℕ ↦ combined n * Real.log (Scale.L n))
        atTop (nhds 0) := by
    simpa only [combined, canonicalCombinedPowerCorrection] using
      hcombinedRateRaw
  have hSquareRemainderT := tendsto_squarefreeSharpProfileRemainder
    profileError Calpha K CKernel W hprofileT hprofileRate
  have hSquareSmall : ∀ᶠ n : ℕ in atTop,
      squarefreeSharpProfileRemainder
        profileError Calpha K CKernel W n < r :=
    hSquareRemainderT.eventually (eventually_lt_nhds (by
      simpa only [squareTailConstant] using hSquareTailLt))
  have hFullRemainderT := tendsto_canonicalFullSharpRemainder
    epsilon75 combined Cpow Calpha K W
      hepsilonT hepsilonRate hcombinedRate
  have hFullSmall : ∀ᶠ n : ℕ in atTop,
      canonicalFullSharpRemainder
        epsilon75 combined Cpow Calpha K W n < r :=
    hFullRemainderT.eventually (eventually_lt_nhds (by
      simpa only [fullTailConstant] using hFullTailLt))
  have hInverse := hinverseEvent W hWinverse
  have hCenter := hcenterEvent W hWcenter
  have hCoverage :=
    RegularMeshPrimeCutoffs.Mesh.eventually_canonical_anchor_coverage
      M hdelta hWne anchorCell hIdealLower hIdealUpper
  have hBandT := eventually_bandTReciprocalSum_le W
  filter_upwards [hInverse, hCenter, hCoverage, hBandT,
    hSquareSmall, hFullSmall, eventually_ge_atTop Nprofile,
    eventually_ge_atTop Nfull] with n hInverseN hCenterN hCoverageN
      hBandTN hSquareN hFullN hnProfile hnFull
  intro B xi hBn hBW hsep hremaining hcanonical hpartition heta hphys
  subst n
  subst W
  obtain ⟨hWactual, hWTwoActual, hnInverse, SInverse,
      hInteriorLower, hInteriorUpper, referenceEquiv,
      hreference, hinvVarying⟩ := hInverseN
  obtain ⟨hnCoverage, hCoverageAll⟩ := hCoverageN
  obtain ⟨hWpartition, SPartition, hPartitionUser⟩ := hpartition
  let Pcanonical :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPartition
      M hdelta hnInverse hWactual SInverse
  let Ecanonical :=
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
      M hdelta hnInverse hWactual SInverse
  let IM := RegularMeshPrimeCutoffs.Mesh.canonicalIntervalMesh
    M hdelta hnInverse hWactual hWTwoActual SInverse
      epsilon anchorCell hInteriorLower hInteriorUpper
  have hPartitionCanonical : B.partition = Pcanonical := by
    exact hPartitionUser.trans (by rfl)
  have hAnchorLength : width / 2 ≤
      IM.length (RegularMeshPrimeCutoffs.Mesh.positiveBand M anchorCell) := by
    have hcov := (hCoverageAll SInverse).2.2
    simpa only [width, IM,
      RegularMeshPrimeCutoffs.Mesh.canonicalIntervalMesh] using hcov
  have hAnchorMass : width / 2 ≤ ∑ j, IM.anchor j := by
    have hsum : (∑ j, IM.anchor j) =
        IM.length (RegularMeshPrimeCutoffs.Mesh.positiveBand M anchorCell) := by
      unfold ContinuumCellGraph.IntervalMesh.anchor
      simp only [IM,
        RegularMeshPrimeCutoffs.Mesh.canonicalIntervalMesh,
        Finset.mem_singleton, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hsum]
    exact hAnchorLength
  let Cvary : ℝ :=
    (4 / (kappa * ∑ j, IM.anchor j)) /
      (1 - (4 / (kappa * ∑ j, IM.anchor j)) *
        (2 * (kappa * (M.width anchorCell / 2) / 16)))
  have hCvary : Cvary ≤ Cref := by
    dsimp only [Cvary, Cref, width]
    exact canonical_varyingInverseConstant_le hkappa
      (M.width_pos hdelta anchorCell) hAnchorMass
  have hinvReference : ∀ v, ‖referenceEquiv.symm v‖ ≤ Cref * ‖v‖ := by
    intro v
    exact (hinvVarying v).trans
      (mul_le_mul_of_nonneg_right hCvary (norm_nonneg v))
  have hPattern : B.sampleData.pattern = Phead := by
    rw [hcanonical]
    rfl
  have hLo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hHi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hGuards : B.sampleData.guards = (ledger B.sampleData.n).guards := by
    rw [hcanonical]
    rfl
  obtain ⟨hpair, hsingle⟩ := hprofile B xi hnProfile
    hPattern hLo hHi hGuards heta hphys rfl
  have hKernel : ∀ p ∈
      primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤
        CKernel := by
    intro p hp
    have ht0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
      B.n_gt_one hp
    have ht1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
      B.n_gt_one hp
    calc
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤
          CKernel * tPrime B.sampleData.n p :=
        hKernelBound _ ⟨ht0, ht1⟩ _ ⟨ht0, ht1⟩
      _ ≤ CKernel := by
        exact (mul_le_mul_of_nonneg_left ht1 hCKernel).trans_eq
          (mul_one CKernel)
  have hCenterCanonical : ∀ i : Fin (M.cellCount + 1),
      1 / Pcanonical.center i ≤
        Calpha * Real.log (Scale.L B.sampleData.n) := by
    intro i
    exact hCenterN hnInverse hWactual SInverse i
  have hSquareRow : ∀ q : Fin (M.cellCount + 1) → ℝ,
      (∀ j, |q j| ≤ 1) → ∀ i : Fin (M.cellCount + 1),
      |SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        CompressedArithmeticOperator.arithmeticSharpOperator
          (y B.sampleData.n) Ecanonical.lower Ecanonical.upper
            Pcanonical.center q i| ≤ r := by
    intro q hq i
    exact (B.abs_actual_squarefreeSharpRow_sub_equalPartitionArithmetic_le
      xi hPartitionCanonical Ecanonical
      (hprofile0 B.sampleData.n) (by omega) hpair hsingle hKernel
      hBandTN hCenterCanonical q hq i).trans hSquareN.le
  have hCenterActual : ∀ i : Fin (M.cellCount + 1),
      1 / B.partition.center i ≤
        Calpha * Real.log (Scale.L B.sampleData.n) := by
    intro i
    rw [hPartitionCanonical]
    exact hCenterCanonical i
  have hCmax : 1 ≤ Cmax :=
    (hlowerOne .minus).trans
      ((I.lower_lt_upper .minus).le.trans (hupperMax .minus))
  have hcombined0 : 0 ≤ combined B.sampleData.n := by
    dsimp only [combined]
    exact canonicalCombinedPowerCorrection_nonneg
      Phead I hCmax hAphys (by omega) B.n_gt_one
  have hrawFull := hfullRaw B xi hnFull rfl hsep hremaining
    hcanonical heta hphys
  have hFullRow : ∀ q : Fin (M.cellCount + 1) → ℝ,
      (∀ j, |q j| ≤ 1) → ∀ i : Fin (M.cellCount + 1),
      |PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i| ≤ r := by
    intro q hq i
    have hraw := hrawFull q hq i
    have hbounded := B.fullSharpRow_le_canonicalFullSharpRemainder
      xi epsilon75 combined hCpow.le (hepsilon0 B.sampleData.n)
        hcombined0 (by omega) hBandTN hCenterActual q i
        (by simpa only [combined, canonicalCombinedPowerCorrection] using hraw)
    exact hbounded.trans hFullN.le
  obtain ⟨actualEquiv, hactual, hinvActual⟩ :=
    B.exists_actualFullProjectedEquiv_of_equal_referencePartition
      xi hPartitionCanonical Ecanonical referenceEquiv hreference
      hCref.le hr.le hr.le hinvReference
      (canonicalProjectedPerturbationRadius_first_small hCref)
      hSquareRow
      (canonicalProjectedPerturbationRadius_second_small hCref)
      hFullRow
  refine ⟨actualEquiv, hactual, ?_⟩
  intro v
  have hbound := hinvActual v
  rw [canonicalProjectedPerturbation_finalConstant hCref] at hbound
  simpa only [Cfull] using hbound

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
