import Erdos390.Full.PaperExactTwoStageOrdinaryFast
import Erdos390.Full.OrdinaryRawInverseTransfer

/-!
# Ordinary raw-norm nuisance--Schur transfer

The sharp Schur estimate divides by the least band centre.  That loss is
appropriate for a sharp input, but it is spurious for the ordinary raw
supremum norm required by the fast solve.  Here both prime-band summations
are performed before projection.  The result depends on the total harmonic
mass, which is later paired with the genuinely vanishing marked rate; it has
no factor `1 / min alpha`.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry
open OrdinaryRawInverseTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Two covariance-vector estimates give an ordinary raw row bound for the
literal nuisance correction.  The projection loss is expressed only by the
displayed first-moment/centre-energy ratio. -/
theorem actualBandSchur_sub_full_norm_le_of_nuisanceCovarianceBounds_ordinary
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    {Csource Crow R : ℝ}
    (hCsource : 0 ≤ Csource) (hCrow : 0 ≤ Crow) (hR : 0 ≤ R)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      R * MovingLowGaugeTransfer.sharpWeightTotal
        B.harmonicMass B.bandCenter)
    (hsource : ∀ q : B.RawBandGauge,
      ‖B.nuisanceCovarianceVector xi (B.bandRegressionScore q)‖ ≤
        Csource * ‖q‖)
    (hband : ∀ i : Band,
      ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖ ≤
        Crow * B.harmonicMass i)
    (q : B.RawBandGauge) :
    ‖B.actualBandSchurLinearMap xi hgamma hgap q -
        B.actualBandFullLinearMap xi q‖ ≤
      ((1 + R) * ((Csource / gamma) * Crow)) * ‖q‖ := by
  let A : ℝ := (Csource / gamma) * Crow
  let z : EuclideanSpace ℝ (NuisanceCoord B.HeadIndex) :=
    B.nuisanceCoefficientOfScore xi hgamma hgap
      (B.bandRegressionScore q)
  let correction : Band → ℝ := fun i ↦
    B.normalizedBandCovarianceRow xi
      (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) i
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (div_nonneg hCsource hgamma.le) hCrow
  have hz : ‖z‖ ≤ (Csource / gamma) * ‖q‖ := by
    calc
      ‖z‖ ≤
          ‖B.nuisanceCovarianceVector xi
            (B.bandRegressionScore q)‖ / gamma :=
        B.nuisanceCoefficientOfScore_norm_le xi hgamma hgap _
      _ ≤ (Csource * ‖q‖) / gamma :=
        div_le_div_of_nonneg_right (hsource q) hgamma.le
      _ = (Csource / gamma) * ‖q‖ := by ring
  have hcorrection : ∀ i : Band, |correction i| ≤ A * ‖q‖ := by
    intro i
    have hH : 0 < B.harmonicMass i := B.harmonicMass_pos i
    change |B.normalizedBandCovarianceRow xi
      (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) i| ≤ _
    unfold normalizedBandCovarianceRow
    rw [B.covariance_marked_nuisanceScore_eq_inner,
      abs_div, abs_of_pos hH]
    have hinner := abs_real_inner_le_norm z
      (B.nuisanceCovarianceVector xi (B.bandScore i))
    calc
      |inner ℝ z (B.nuisanceCovarianceVector xi (B.bandScore i))| /
          B.harmonicMass i ≤
        (‖z‖ * ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖) /
          B.harmonicMass i :=
        div_le_div_of_nonneg_right hinner hH.le
      _ ≤ (((Csource / gamma) * ‖q‖) *
          (Crow * B.harmonicMass i)) / B.harmonicMass i := by
        apply div_le_div_of_nonneg_right _ hH.le
        exact mul_le_mul hz (hband i) (norm_nonneg _)
          (mul_nonneg (div_nonneg hCsource hgamma.le) (norm_nonneg q))
      _ = A * ‖q‖ := by
        dsimp only [A]
        field_simp [ne_of_gt hH]
  have hproject :
      ‖B.projectRawBandVector correction‖ ≤
        (1 + R) * (A * ‖q‖) :=
    B.projectRawBandVector_norm_le_of_moment_ratio
      correction (mul_nonneg hA (norm_nonneg q)) hR hcorrection hRatio
  rw [B.actualBandSchurLinearMap_eq_full_sub_nuisanceCorrection
    xi hgamma hgap q]
  simpa only [sub_sub_cancel_left, norm_neg, correction, z, A,
    mul_assoc] using hproject

/-- Ordinary raw Schur rate supplied by a reciprocal marked family.  In
contrast with `nuisanceMarkedSchurRate`, this has no least-centre divisor. -/
def nuisanceMarkedOrdinarySchurRate (Cmarked gamma R : ℝ) : ℝ :=
  let droot := Real.sqrt
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let totalMass := ∑ j : Band, B.harmonicMass j
  (1 + R) *
    (((droot * (Cmarked * totalMass)) / gamma) * (droot * Cmarked))

/-- The reciprocal marked-prime family closes the ordinary nuisance row
without using a lower bound for the moving centre. -/
theorem actualBandSchur_sub_full_norm_le_of_marked_ordinary
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    {Cmarked R : ℝ} (hCmarked : 0 ≤ Cmarked) (hR : 0 ≤ R)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      R * MovingLowGaugeTransfer.sharpWeightTotal
        B.harmonicMass B.bandCenter)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (q : B.RawBandGauge) :
    ‖B.actualBandSchurLinearMap xi hgamma hgap q -
        B.actualBandFullLinearMap xi q‖ ≤
      B.nuisanceMarkedOrdinarySchurRate Cmarked gamma R * ‖q‖ := by
  let droot : ℝ := Real.sqrt
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let totalMass : ℝ := ∑ j : Band, B.harmonicMass j
  let Csource : ℝ := droot * (Cmarked * totalMass)
  let Crow : ℝ := droot * Cmarked
  have htotalMass : 0 ≤ totalMass := by
    dsimp only [totalMass]
    exact Finset.sum_nonneg fun j _ ↦ (B.harmonicMass_pos j).le
  have hdroot : 0 ≤ droot := Real.sqrt_nonneg _
  have hCsource : 0 ≤ Csource :=
    mul_nonneg hdroot (mul_nonneg hCmarked htotalMass)
  have hCrow : 0 ≤ Crow := mul_nonneg hdroot hCmarked
  have hsource : ∀ q' : B.RawBandGauge,
      ‖B.nuisanceCovarianceVector xi (B.bandRegressionScore q')‖ ≤
        Csource * ‖q'‖ := by
    intro q'
    have h := B.nuisanceCovarianceVector_rawBandRegression_norm_le_of_marked
      xi hCmarked hmarked q'
    simpa only [Csource, droot, totalMass, mul_assoc] using h
  have hband : ∀ i : Band,
      ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖ ≤
        Crow * B.harmonicMass i := by
    intro i
    have h := B.nuisanceCovarianceVector_bandScore_norm_le_of_marked
      xi i hCmarked hmarked
    simpa only [Crow, droot, mul_assoc] using h
  have h := B.actualBandSchur_sub_full_norm_le_of_nuisanceCovarianceBounds_ordinary
    xi hgamma hgap hCsource hCrow hR hRatio hsource hband q
  simpa only [nuisanceMarkedOrdinarySchurRate, Csource, Crow,
    droot, totalMass] using h

/-- Once a literal Schur equivalence is known from the sharp argument, an
ordinary inverse estimate for the full raw operator and the just-proved raw
nuisance estimate give the ordinary inverse for the *same* equivalence. -/
theorem actualBandSchur_inverse_norm_le_of_full_ordinary
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    {C delta : ℝ} (hC : 0 ≤ C)
    (hsmall : C * delta ≤ 1 / 2)
    (hfull : ∀ q : B.RawBandGauge,
      ‖q‖ ≤ C * ‖B.actualBandFullLinearMap xi q‖)
    (herror : ∀ q : B.RawBandGauge,
      ‖B.actualBandSchurLinearMap xi hgamma hgap q -
          B.actualBandFullLinearMap xi q‖ ≤ delta * ‖q‖) :
    ∀ v, ‖e.symm v‖ ≤ (2 * C) * ‖v‖ := by
  apply inverse_norm_le_of_reference e
    (B.actualBandFullLinearMap xi) hC hsmall hfull
  intro q
  rw [he q, norm_sub_rev]
  exact herror q

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
