import Erdos390.Full.PaperActualTwoStageRegression
import Erdos390.Full.PaperEffectiveScoreBound
import Erdos390.Full.PaperVectorFieldSchur

/-!
# Exact identification of the main coordinates with the paper raw gauge

The ODE parameter space stores one coordinate for each concrete gauge-basis
vector and stores `w * lambda` in the slow coordinate.  Lemma 8.6 instead
writes the band coefficient as a vector in the arithmetic hyperplane
`sum_j H_j alpha_j q_j = 0`.  This file identifies these two descriptions
exactly, including the moving low coordinate.  No estimate is used.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The omitted low coordinate of an arithmetic raw-gauge vector is exactly
the weighted linear combination used by the concrete quotient basis.  This
is the finite identity which makes the paper's passage between intrinsic
gauge vectors and concrete coordinates invertible even for the moving low
cell. -/
theorem rawBandGauge_low_eq (q : B.RawBandGauge) :
    q.1 B.lowBand =
      -∑ j : B.GaugeIndex, B.lowRatio j * q.1 j.1 := by
  let d0 := B.harmonicMass B.lowBand * B.bandCenter B.lowBand
  have hd0 : d0 ≠ 0 := by
    exact ne_of_gt (mul_pos (B.harmonicMass_pos B.lowBand)
      (B.bandCenter_pos B.lowBand))
  have hq := q.2
  change (∑ j : Band,
    rawGaugeWeight B.harmonicMass B.bandCenter j * q.1 j) = 0 at hq
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun j : Band ↦
      rawGaugeWeight B.harmonicMass B.bandCenter j * q.1 j)
    B.lowBand] at hq
  simp only [rawGaugeWeight] at hq
  have hratio (j : B.GaugeIndex) :
      B.harmonicMass j.1 * B.bandCenter j.1 =
        d0 * B.lowRatio j := by
    unfold lowRatio d0
    exact (mul_div_cancel₀
      (B.harmonicMass j.1 * B.bandCenter j.1) hd0).symm
  simp_rw [hratio] at hq
  change d0 * q.1 B.lowBand +
      ∑ x : B.GaugeIndex, d0 * B.lowRatio x * q.1 x.1 = 0 at hq
  simp_rw [mul_assoc] at hq
  rw [← Finset.mul_sum] at hq
  have hsolve : q.1 B.lowBand =
      -(∑ j : B.GaugeIndex, B.lowRatio j * q.1 j.1) := by
    apply (mul_left_cancel₀ hd0)
    calc
      d0 * q.1 B.lowBand =
          -d0 * ∑ j : B.GaugeIndex, B.lowRatio j * q.1 j.1 := by
        linarith
      _ = d0 * -(∑ j : B.GaugeIndex,
          B.lowRatio j * q.1 j.1) := by ring
  exact hsolve

/-- The raw arithmetic-gauge vector represented by the gauge coordinates of
an actual main parameter. -/
def rawGaugeOfMain (u : B.MainSpace) : B.RawBandGauge := by
  refine ⟨fun j => B.bandParameter (B.mainEmbed u) j, ?_⟩
  change (∑ j : Band,
    rawGaugeWeight B.harmonicMass B.bandCenter j *
      B.bandParameter (B.mainEmbed u) j) = 0
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun j : Band =>
      rawGaugeWeight B.harmonicMass B.bandCenter j *
        B.bandParameter (B.mainEmbed u) j) B.lowBand]
  simp only [rawGaugeWeight, B.bandParameter_low,
    B.bandParameter_gauge, B.mainEmbed_gauge]
  have hden : B.harmonicMass B.lowBand * B.bandCenter B.lowBand ≠ 0 :=
    ne_of_gt (mul_pos (B.harmonicMass_pos B.lowBand)
      (B.bandCenter_pos B.lowBand))
  have hterm (j : B.GaugeIndex) :
      B.harmonicMass B.lowBand * B.bandCenter B.lowBand *
          (B.lowRatio j * u (MainCoord.gauge j)) =
        B.harmonicMass j.1 * B.bandCenter j.1 *
          u (MainCoord.gauge j) := by
    unfold lowRatio
    calc
      B.harmonicMass B.lowBand * B.bandCenter B.lowBand *
          ((B.harmonicMass j.1 * B.bandCenter j.1 /
              (B.harmonicMass B.lowBand * B.bandCenter B.lowBand)) *
            u (MainCoord.gauge j)) =
          (B.harmonicMass B.lowBand * B.bandCenter B.lowBand *
            ((B.harmonicMass j.1 * B.bandCenter j.1) /
              (B.harmonicMass B.lowBand * B.bandCenter B.lowBand))) *
            u (MainCoord.gauge j) := by ring
      _ = B.harmonicMass j.1 * B.bandCenter j.1 *
          u (MainCoord.gauge j) := by
        rw [mul_div_cancel₀ _ hden]
  rw [mul_neg, Finset.mul_sum]
  simp_rw [hterm]
  ring

@[simp] theorem rawGaugeOfMain_apply (u : B.MainSpace) (j : Band) :
    (B.rawGaugeOfMain u).1 j = B.bandParameter (B.mainEmbed u) j := rfl

@[simp] theorem rawGaugeOfMain_positive (u : B.MainSpace)
    (j : B.GaugeIndex) :
    (B.rawGaugeOfMain u).1 j.1 = u (MainCoord.gauge j) := by
  simp [rawGaugeOfMain]

@[simp] theorem rawGaugeOfMain_low (u : B.MainSpace) :
    (B.rawGaugeOfMain u).1 B.lowBand =
      -∑ j : B.GaugeIndex, B.lowRatio j * u (MainCoord.gauge j) := by
  simp [rawGaugeOfMain]

/-- The intrinsic arithmetic gauge together with the stored slow coordinate
is linearly equivalent to the actual `MainSpace` used by the exponential
family.  The inverse is the concrete basis from the paper; the low
coordinate is recovered by `rawBandGauge_low_eq`, not by a dimension or
mesh-dependent matrix inverse. -/
def mainRawSlowLinearEquiv :
    B.MainSpace ≃ₗ[ℝ] (B.RawBandGauge × ℝ) where
  toFun u := (B.rawGaugeOfMain u, u MainCoord.slow)
  invFun qr :=
    (EuclideanSpace.equiv (MainCoord B.GaugeIndex) ℝ).symm
      (fun c ↦ match c with
        | .gauge j => qr.1.1 j.1
        | .slow => qr.2)
  left_inv u := by
    apply (EuclideanSpace.equiv (MainCoord B.GaugeIndex) ℝ).injective
    funext c
    cases c with
    | gauge j => simp
    | slow => rfl
  right_inv qr := by
    apply Prod.ext
    · apply Subtype.ext
      funext j
      by_cases hj : j = B.lowBand
      · subst j
        rw [B.rawGaugeOfMain_low, B.rawBandGauge_low_eq]
        apply congrArg Neg.neg
        apply Finset.sum_congr rfl
        intro k hk
        rfl
      · let k : B.GaugeIndex := ⟨j, hj⟩
        change (B.rawGaugeOfMain _).1 k.1 = qr.1.1 j
        rw [B.rawGaugeOfMain_positive]
        change qr.1.1 j = qr.1.1 j
        rfl
    · rfl
  map_add' u v := by
    apply Prod.ext
    · apply Subtype.ext
      funext j
      exact B.bandParameter_add (B.mainEmbed u) (B.mainEmbed v) j
    · rfl
  map_smul' a u := by
    apply Prod.ext
    · apply Subtype.ext
      funext j
      exact B.bandParameter_smul a (B.mainEmbed u) j
    · rfl

@[simp] theorem mainRawSlowLinearEquiv_apply (u : B.MainSpace) :
    B.mainRawSlowLinearEquiv u =
      (B.rawGaugeOfMain u, u MainCoord.slow) := rfl

@[simp] theorem mainRawSlowLinearEquiv_symm_gauge
    (q : B.RawBandGauge) (s : ℝ) (j : B.GaugeIndex) :
    (B.mainRawSlowLinearEquiv.symm (q, s)) (MainCoord.gauge j) =
      q.1 j.1 := rfl

@[simp] theorem mainRawSlowLinearEquiv_symm_slow
    (q : B.RawBandGauge) (s : ℝ) :
    (B.mainRawSlowLinearEquiv.symm (q, s)) MainCoord.slow = s := rfl

/-- The raw-gauge band score is exactly the gauge-coordinate part of the
main exponential score. -/
theorem bandRegressionScore_rawGaugeOfMain
    (u : B.MainSpace) (m : B.sampleData.Sample) :
    B.bandRegressionScore (B.rawGaugeOfMain u) m =
      ∑ j : B.GaugeIndex,
        u (MainCoord.gauge j) * B.gaugeScore j m := by
  change (∑ j : Band,
      B.bandParameter (B.mainEmbed u) j * B.bandScore j m) = _
  simpa using B.sum_bandParameter_mul_bandScore_eq_gauge
    (B.mainEmbed u) m

/-- The slow coordinate of `MainSpace` is literally the stored coordinate
`w * lambda` in the full parameter space. -/
@[simp] theorem mainEmbed_effectivePrimeCoefficient
    (u : B.MainSpace)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    B.effectivePrimeCoefficient (B.mainEmbed u) p =
      (B.rawGaugeOfMain u).1 (B.partition.band p) +
        (u MainCoord.slow / B.w) * B.primeDeviation p := by
  rfl

/-- Nuisance coordinates do not alter any effective prime coefficient. -/
@[simp] theorem nuisanceEmbed_effectivePrimeCoefficient
    (z : B.NuisanceSpace)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    B.effectivePrimeCoefficient (B.nuisanceEmbed z) p = 0 := by
  unfold effectivePrimeCoefficient bandParameter
  by_cases h : B.partition.band p = B.lowBand
  · simp only [h, dite_true, B.nuisanceEmbed_gauge,
      B.nuisanceEmbed_slow, zero_div, zero_mul, add_zero]
    simp
  · simp [h]

/-- Exact effective prime coefficient of a Schur residual. -/
theorem schurResidual_effectivePrimeCoefficient
    (R : B.MainSpace → B.NuisanceSpace) (u : B.MainSpace)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    B.effectivePrimeCoefficient (B.schurResidual R u) p =
      (B.rawGaugeOfMain u).1 (B.partition.band p) +
        (u MainCoord.slow / B.w) * B.primeDeviation p := by
  rw [B.schurResidual_eq_sub]
  have hadd := B.effectivePrimeCoefficient_add
    (B.mainEmbed u) (-B.nuisanceEmbed (R u)) p
  have hneg := B.effectivePrimeCoefficient_smul (-1)
    (B.nuisanceEmbed (R u)) p
  rw [sub_eq_add_neg, hadd]
  change B.effectivePrimeCoefficient (B.mainEmbed u) p +
      B.effectivePrimeCoefficient (-B.nuisanceEmbed (R u)) p = _
  rw [show -B.nuisanceEmbed (R u) =
      (-1 : ℝ) • B.nuisanceEmbed (R u) by simp,
    hneg, B.nuisanceEmbed_effectivePrimeCoefficient]
  simp

/-- Exact nuisance block of a Schur residual. -/
@[simp] theorem nuisanceParameter_schurResidual
    (R : B.MainSpace → B.NuisanceSpace) (u : B.MainSpace) :
    B.nuisanceParameter (B.schurResidual R u) = -R u := by
  apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
  funext c
  cases c <;> simp [schurResidual, combine, nuisanceParameter]

/-- Exact stored slow coordinate of a Schur residual. -/
@[simp] theorem schurResidual_slow
    (R : B.MainSpace → B.NuisanceSpace) (u : B.MainSpace) :
    B.schurResidual R u MomentCoord.slow = u MainCoord.slow := by
  simp [schurResidual]

/-- Exact score represented by a main parameter in intrinsic raw-gauge and
stored-slow coordinates.  The factor `1 / w` is visible because the actual
`MainSpace` stores `w * lambda`. -/
theorem vectorScore_mainEmbed_eq_rawGauge_add_slow [Nonempty Head]
    (u : B.MainSpace) (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.score m (B.mainEmbed u) =
      B.bandRegressionScore (B.rawGaugeOfMain u) m +
        (u MainCoord.slow / B.w) * B.slowScore m := by
  rw [B.vectorScore_eq_effectivePrime_add_nuisance]
  have hnuisance : B.nuisanceParameter (B.mainEmbed u) = 0 := by
    apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
    funext c
    cases c <;> rfl
  rw [hnuisance, inner_zero_left, add_zero]
  simp_rw [B.mainEmbed_effectivePrimeCoefficient, add_mul]
  rw [Finset.sum_add_distrib]
  have hband := B.bandRegressionScore_eq_primeSum
    (B.rawGaugeOfMain u) m
  unfold bandRegressionCoefficient at hband
  rw [← hband]
  unfold slowScore
  rw [Finset.mul_sum]
  apply congrArg₂ (fun x y : ℝ ↦ x + y) rfl
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Exact score of a Schur residual.  This is the literal finite score on
which the band and marked covariance rows act. -/
theorem vectorScore_schurResidual_eq_rawGauge_slow_nuisance
    [Nonempty Head]
    (R : B.MainSpace → B.NuisanceSpace) (u : B.MainSpace)
    (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.score m (B.schurResidual R u) =
      B.bandRegressionScore (B.rawGaugeOfMain u) m +
        (u MainCoord.slow / B.w) * B.slowScore m -
          inner ℝ (R u) (B.nuisanceStatistic m) := by
  rw [B.vectorScore_eq_effectivePrime_add_nuisance,
    B.nuisanceParameter_schurResidual]
  simp_rw [B.schurResidual_effectivePrimeCoefficient, add_mul]
  rw [Finset.sum_add_distrib]
  have hband := B.bandRegressionScore_eq_primeSum
    (B.rawGaugeOfMain u) m
  unfold bandRegressionCoefficient at hband
  rw [← hband]
  unfold slowScore
  rw [inner_neg_left]
  have hslow :
      (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        u MainCoord.slow / B.w * B.primeDeviation p *
          ArithmeticModel.valuation p.1 (B.sampleData.value m)) =
        (u MainCoord.slow / B.w) *
          ∑ p : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation p *
              ArithmeticModel.valuation p.1 (B.sampleData.value m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [hslow]
  ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
