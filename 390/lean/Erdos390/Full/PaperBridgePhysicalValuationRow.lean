import Erdos390.Full.PaperBridgeNuisanceTiltFallback
import Erdos390.Full.PaperActualPrimePowerRelative

/-!
# The physical-log column through the residual bridge tilt

The medium-prime Stieltjes estimate in the paper gives a reciprocal-scale
bound for `Cov(v_p,R)` inside each structured cell.  The full bridge law has
one further physical tilt of size `O(1/L)`.  This file proves that the latter
operation preserves the `1/p` scale for the *full valuation* column.

The proof uses the actual bounded valuation and the fixed physical interval.
The artificial pointwise valuation cutoff cancels after normalization, so the
conclusion depends only on the reciprocal first moment.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PaperGuardCensus FiniteProbability
open PrimePowerCovariance PrimePowerCutoffCovariance
open ValuationCutoff LocalFugacityBounds

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The common endpoint is a strictly positive pointwise bound for every
actual valuation on every guarded bridge cell. -/
theorem valuation_le_sampleEndpoint
    (c : Cell Head) (p : ℕ) (m : B.sampleData.SampleAt c) :
    valuation p (m : ℕ) ≤ (B.sampleEndpoint : ℝ) := by
  have hmpos : 0 < (m : ℕ) := by
    let sample : B.sampleData.Sample := ⟨c, m⟩
    simpa only [sample, StructuredSampleData.value] using
      B.sampleData.value_pos sample
  have hmend : (m : ℕ) ≤ B.sampleEndpoint := by
    let sample : B.sampleData.Sample := ⟨c, m⟩
    simpa only [sample, StructuredSampleData.value] using
      B.sample_value_le_endpoint sample
  unfold valuation
  exact_mod_cast ((Nat.factorization_lt p hmpos.ne').le.trans hmend)

theorem sampleEndpoint_pos (c : Cell Head) : 0 < B.sampleEndpoint := by
  exact (B.cell_hi_pos c).trans_le (by
    cases c.2 <;> simp [sampleEndpoint])

/-- The arbitrary-divisor reciprocal fallback sums geometrically to a
reciprocal first moment for the genuine full valuation. -/
theorem cellMediumLaw_expect_valuation_le
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    {rho A : ℝ} {p : ℕ}
    (hp : p.Prime) (hA : 0 ≤ A) (hW : 1 < B.sampleData.W)
    (hrho : 0 < rho)
    (hcard : rho * (B.sampleData.hi c.2 : ℝ) ≤
      ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi r| ≤ A) :
    let G := Real.exp (2 * ((A / B.L) *
      (Real.log (B.sampleData.hi c.2 : ℝ) /
        Real.log (B.sampleData.W : ℝ)))) / rho
    (B.cellMediumLaw xi c).expect
        (fun m ↦ valuation p (m : ℕ)) ≤
      2 * G * (1 / (p : ℝ)) := by
  dsimp only
  let G := Real.exp (2 * ((A / B.L) *
    (Real.log (B.sampleData.hi c.2 : ℝ) /
      Real.log (B.sampleData.W : ℝ)))) / rho
  let law : BoundedValuationLaw (B.sampleData.SampleAt c)
      (B.sampleData.hi c.2) :=
    { probability := B.cellMediumLaw xi c
      value := fun m ↦ (m : ℕ)
      value_pos := fun m ↦ by
        let sample : B.sampleData.Sample := ⟨c, m⟩
        simpa only [sample, StructuredSampleData.value] using
          B.sampleData.value_pos sample
      value_le := fun m ↦ by
        let sample : B.sampleData.Sample := ⟨c, m⟩
        simpa only [sample, StructuredSampleData.value,
          StructuredSampleData.cellOf] using
          B.sampleData.value_le_hi sample }
  have hdecomp :
      (fun m : B.sampleData.SampleAt c ↦ valuation p (m : ℕ)) =
        fun m : B.sampleData.SampleAt c ↦ divInd p (m : ℕ) +
          ∑ k ∈ highExponents (valuationCutoff p (B.sampleData.hi c.2)),
            divInd (p ^ k) (m : ℕ) := by
    funext m
    change law.V p m = law.I p m +
      ∑ k ∈ highExponents (valuationCutoff p (B.sampleData.hi c.2)),
        law.Ip p k m
    rw [law.V_eq_I_add_J, J_eq_valuationCutoff_sum law hp]
  have hsingle (D : ℕ) (hD : 0 < D) :
      (B.cellMediumLaw xi c).expect (fun m ↦ divInd D (m : ℕ)) ≤
        G * (1 / (D : ℝ)) := by
    have hraw := B.cellMediumLaw_expect_divInd_le xi c
      hD hA hW hrho hcard heta
    dsimp only [G]
    calc
      _ ≤ Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) /
          (rho * (D : ℝ)) := hraw
      _ = Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) / rho *
          (1 / (D : ℝ)) := by ring
  have hG0 : 0 ≤ G :=
    div_nonneg (Real.exp_pos _).le hrho.le
  have htail :
      (∑ k ∈ highExponents (valuationCutoff p (B.sampleData.hi c.2)),
        (B.cellMediumLaw xi c).expect
          (fun m ↦ divInd (p ^ k) (m : ℕ))) ≤
        G * (2 / (p : ℝ) ^ 2) := by
    calc
      _ ≤ ∑ k ∈ highExponents
          (valuationCutoff p (B.sampleData.hi c.2)),
          G * (1 / ((p ^ k : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hsingle (p ^ k) (pow_pos hp.pos k)
      _ = G * (∑ k ∈ highExponents
          (valuationCutoff p (B.sampleData.hi c.2)),
          1 / ((p ^ k : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
      _ ≤ G * (2 / (p : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hG0
        simpa only [highExponents] using
          (sum_inv_pow_tail_le
            (p := p) (r := 1)
            (A := valuationCutoff p (B.sampleData.hi c.2)) hp.two_le)
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hexpectSum :
      (B.cellMediumLaw xi c).expect
          (fun m ↦ ∑ k ∈
            highExponents (valuationCutoff p (B.sampleData.hi c.2)),
              divInd (p ^ k) (m : ℕ)) =
        ∑ k ∈ highExponents (valuationCutoff p (B.sampleData.hi c.2)),
          (B.cellMediumLaw xi c).expect
            (fun m ↦ divInd (p ^ k) (m : ℕ)) := by
    let S := highExponents (valuationCutoff p (B.sampleData.hi c.2))
    change (B.cellMediumLaw xi c).expect
        (fun m ↦ ∑ k ∈ S, divInd (p ^ k) (m : ℕ)) =
      ∑ k ∈ S, (B.cellMediumLaw xi c).expect
        (fun m ↦ divInd (p ^ k) (m : ℕ))
    induction S using Finset.induction_on with
    | empty => simp [FiniteProbability.expect_zero]
    | @insert k S hk ih =>
        simp only [Finset.sum_insert hk]
        rw [(B.cellMediumLaw xi c).expect_add, ih]
  rw [hdecomp, (B.cellMediumLaw xi c).expect_add, hexpectSum]
  calc
    (B.cellMediumLaw xi c).expect (fun m ↦ divInd p (m : ℕ)) +
        ∑ k ∈ highExponents (valuationCutoff p (B.sampleData.hi c.2)),
          (B.cellMediumLaw xi c).expect
            (fun m ↦ divInd (p ^ k) (m : ℕ)) ≤
      G * (1 / (p : ℝ)) + G * (2 / (p : ℝ) ^ 2) :=
        add_le_add (hsingle p hp.pos) htail
    _ ≤ 2 * G * (1 / (p : ℝ)) := by
      have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
      field_simp [ne_of_gt hpPos]
      nlinarith

/-- A uniform reciprocal first moment for the medium-only component laws
passes to the literal globally tilted bridge law.  The only loss is the exact
density-ratio factor of the remaining physical tilt. -/
theorem tiltedLaw_expect_valuation_le_of_cellMedium
    [Nonempty Head]
    (xi : B.ParamSpace) {p : ℕ} {epsilon Aval : ℝ}
    (hscore : ∀ (c : Cell Head) (m : B.sampleData.SampleAt c),
      |B.cellPhysicalTiltScore xi c m| ≤ epsilon)
    (hmedium : ∀ c : Cell Head,
      (B.cellMediumLaw xi c).expect
        (fun m ↦ valuation p (m : ℕ)) ≤ Aval * (1 / (p : ℝ))) :
    (B.tiltedLaw xi).expect
        (fun m ↦ valuation p (B.sampleData.value m)) ≤
      Real.exp (2 * epsilon) * Aval * (1 / (p : ℝ)) := by
  rw [B.tiltedLaw_eq_tiltedSigmaMixture xi]
  apply FiniteProbability.sigmaMixture_expect_le_common
  intro c
  rw [B.guardedCell_fullTilt_eq_medium_physicalTilt xi c]
  have htilt := FiniteProbability.exponentialTilt_expect_le_exp_two_mul
    (B.cellMediumLaw xi c)
    (fun m ↦ valuation p (m : ℕ))
    (B.cellPhysicalTiltScore xi c) epsilon
    (fun m ↦ valuation_nonneg p (m : ℕ)) (hscore c)
  calc
    ((B.cellMediumLaw xi c).exponentialTilt
        (B.cellPhysicalTiltScore xi c)).expect
        (fun m ↦ valuation p (m : ℕ)) ≤
      Real.exp (2 * epsilon) *
        (B.cellMediumLaw xi c).expect
          (fun m ↦ valuation p (m : ℕ)) := htilt
    _ ≤ Real.exp (2 * epsilon) *
        (Aval * (1 / (p : ℝ))) :=
      mul_le_mul_of_nonneg_left (hmedium c) (Real.exp_pos _).le
    _ = Real.exp (2 * epsilon) * Aval * (1 / (p : ℝ)) := by ring

/-- A nonnegative marked statistic with a small first moment has small
covariance with every bounded nuisance coordinate.  This elementary estimate
handles both the physical coordinate and every fixed head coordinate at once;
it includes the between-cell covariance of the actual tilted mixture. -/
theorem abs_tiltedLaw_covariance_nuisanceCoord_le_of_expect
    [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    (c : NuisanceCoord B.HeadIndex) {K A : ℝ}
    (hK : 0 ≤ K)
    (hF0 : ∀ m, 0 ≤ F m)
    (hcoord : ∀ m, |B.nuisanceStatistic m c| ≤ K)
    (hEF : (B.tiltedLaw xi).expect F ≤ A) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m c) F| ≤ 2 * K * A := by
  let mu := B.tiltedLaw xi
  let H : B.sampleData.Sample → ℝ :=
    fun m ↦ B.nuisanceStatistic m c
  have hEF0 : 0 ≤ mu.expect F := mu.expect_nonneg F hF0
  have hEH : |mu.expect H| ≤ K := by
    unfold FiniteProbability.expect
    calc
      |∑ m, mu.mass m * H m| ≤ ∑ m, |mu.mass m * H m| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ m, mu.mass m * |H m| := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [abs_mul, abs_of_nonneg (mu.mass_nonneg m)]
      _ ≤ ∑ m, mu.mass m * K := by
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_left (hcoord m) (mu.mass_nonneg m)
      _ = K := by rw [← Finset.sum_mul, mu.mass_sum, one_mul]
  have hprod : |mu.expect (fun m ↦ H m * F m)| ≤ K * mu.expect F := by
    unfold FiniteProbability.expect
    calc
      |∑ m, mu.mass m * (H m * F m)| ≤
          ∑ m, |mu.mass m * (H m * F m)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ m, mu.mass m * (|H m| * F m) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [abs_mul, abs_mul, abs_of_nonneg (mu.mass_nonneg m),
          abs_of_nonneg (hF0 m)]
      _ ≤ ∑ m, mu.mass m * (K * F m) := by
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hcoord m) (hF0 m))
          (mu.mass_nonneg m)
      _ = K * ∑ m, mu.mass m * F m := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        ring
  change |mu.covariance H F| ≤ _
  unfold FiniteProbability.covariance
  calc
    |mu.expect (fun m ↦ H m * F m) - mu.expect H * mu.expect F| ≤
        |mu.expect (fun m ↦ H m * F m)| +
          |mu.expect H * mu.expect F| := abs_sub _ _
    _ ≤ K * mu.expect F + K * mu.expect F := by
      apply add_le_add hprod
      rw [abs_mul, abs_of_nonneg hEF0]
      exact mul_le_mul_of_nonneg_right hEH hEF0
    _ ≤ K * A + K * A := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hEF hK)
        (mul_le_mul_of_nonneg_left hEF hK)
    _ = 2 * K * A := by ring

/-- Every literal nuisance coordinate is uniformly bounded on the two fixed
physical intervals.  This coordinatewise version avoids an unnecessary
Euclidean-dimension factor in the marked-row estimate. -/
theorem abs_nuisanceStatistic_apply_le_fixedIntervals
    [Nonempty Head]
    (I : PhysicalIntervals) {U : ℝ}
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (m : B.sampleData.Sample) (c : NuisanceCoord B.HeadIndex) :
    |B.nuisanceStatistic m c| ≤ max (Real.log U) 3 := by
  cases c with
  | physical =>
      rw [B.nuisanceStatistic_physical]
      exact (B.abs_physicalScore_le_log_upperBound I
        hlowerOne hupperU hlo hhi m).trans (le_max_left _ _)
  | head h =>
      rw [B.nuisanceStatistic_head]
      exact (PaperStatisticNorm.BridgeData.abs_centeredHeadScore_le_three
        B h m).trans (le_max_right _ _)

/-- The paper's coordinatewise nuisance marked row follows from a uniform
reciprocal first moment in the medium-only cells.  It is a statement about the
actual global tilted law and therefore includes both within-cell and
between-cell covariance. -/
theorem abs_tiltedLaw_covariance_nuisance_valuation_le_of_cellMedium
    [Nonempty Head]
    (xi : B.ParamSpace) (I : PhysicalIntervals)
    {U epsilon Aval : ℝ} {p : ℕ}
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hscore : ∀ (c : Cell Head) (m : B.sampleData.SampleAt c),
      |B.cellPhysicalTiltScore xi c m| ≤ epsilon)
    (hmedium : ∀ c : Cell Head,
      (B.cellMediumLaw xi c).expect
        (fun m ↦ valuation p (m : ℕ)) ≤ Aval * (1 / (p : ℝ)))
    (c : NuisanceCoord B.HeadIndex) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m c)
      (fun m ↦ valuation p (B.sampleData.value m))| ≤
      (2 * max (Real.log U) 3 * (Real.exp (2 * epsilon) * Aval)) *
        (1 / (p : ℝ)) := by
  have hglobal := B.tiltedLaw_expect_valuation_le_of_cellMedium
    xi hscore hmedium
  have hK : 0 ≤ max (Real.log U) 3 :=
    (by norm_num : (0 : ℝ) ≤ 3).trans (le_max_right _ _)
  have hcov := B.abs_tiltedLaw_covariance_nuisanceCoord_le_of_expect
    xi (fun m ↦ valuation p (B.sampleData.value m)) c
    hK (fun m ↦ valuation_nonneg p (B.sampleData.value m))
    (fun m ↦ B.abs_nuisanceStatistic_apply_le_fixedIntervals
      I hlowerOne hupperU hlo hhi m c) hglobal
  calc
    |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p (B.sampleData.value m))| ≤
      2 * max (Real.log U) 3 *
        (Real.exp (2 * epsilon) * Aval * (1 / (p : ℝ))) := hcov
    _ = (2 * max (Real.log U) 3 * (Real.exp (2 * epsilon) * Aval)) *
        (1 / (p : ℝ)) := by ring

/-- Concrete guard-census/fugacity version of the nuisance marked row.  Every
hypothesis is an input already produced before Lemma 8.6: cell density,
effective-prime coefficient control, the fixed physical intervals, and one
uniform ceiling for the explicit reciprocal fallback factor. -/
theorem abs_tiltedLaw_covariance_nuisance_valuation_le_of_guardCensus
    [Nonempty Head]
    (xi : B.ParamSpace) (I : PhysicalIntervals)
    {U rho A Aphys Aval : ℝ} {p : ℕ}
    (hp : p.Prime) (hA : 0 ≤ A) (hW : 1 < B.sampleData.W)
    (hrho : 0 < rho)
    (hcard : ∀ c : Cell Head,
      rho * (B.sampleData.hi c.2 : ℝ) ≤
        ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi r| ≤ A)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hAval : ∀ c : Cell Head,
      2 * (Real.exp (2 * ((A / B.L) *
        (Real.log (B.sampleData.hi c.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ)))) / rho) ≤ Aval)
    (c : NuisanceCoord B.HeadIndex) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m c)
      (fun m ↦ valuation p (B.sampleData.value m))| ≤
      (2 * max (Real.log U) 3 *
        (Real.exp (2 * (Aphys * Real.log U / B.L)) * Aval)) *
          (1 / (p : ℝ)) := by
  let epsilon : ℝ := Aphys * Real.log U / B.L
  have hscore : ∀ (d : Cell Head) (m : B.sampleData.SampleAt d),
      |B.cellPhysicalTiltScore xi d m| ≤ epsilon := by
    intro d m
    simpa only [epsilon] using
      B.abs_cellPhysicalTiltScore_le_fixedIntervals xi d I
        hlowerOne hupperU hlo hhi hAphys m
  have hmedium : ∀ d : Cell Head,
      (B.cellMediumLaw xi d).expect
        (fun m ↦ valuation p (m : ℕ)) ≤ Aval * (1 / (p : ℝ)) := by
    intro d
    have hraw := B.cellMediumLaw_expect_valuation_le
      xi d hp hA hW hrho (hcard d) heta
    dsimp only at hraw
    exact hraw.trans
      (mul_le_mul_of_nonneg_right (hAval d) (by positivity))
  simpa only [epsilon] using
    B.abs_tiltedLaw_covariance_nuisance_valuation_le_of_cellMedium
      xi I hlowerOne hupperU hlo hhi hscore hmedium c

/-- The preceding guard-census theorem with its uniform cell ceiling chosen
explicitly from the common sample endpoint.  No supremum over cells remains
as a hypothesis. -/
theorem abs_tiltedLaw_covariance_nuisance_valuation_le_explicit
    [Nonempty Head]
    (xi : B.ParamSpace) (I : PhysicalIntervals)
    {U rho A Aphys : ℝ} {p : ℕ}
    (hp : p.Prime) (hA : 0 ≤ A) (hW : 1 < B.sampleData.W)
    (hrho : 0 < rho)
    (hcard : ∀ c : Cell Head,
      rho * (B.sampleData.hi c.2 : ℝ) ≤
        ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi r| ≤ A)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (c : NuisanceCoord B.HeadIndex) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m c)
      (fun m ↦ valuation p (B.sampleData.value m))| ≤
      (4 * max (Real.log U) 3 *
        (Real.exp (2 * (Aphys * Real.log U / B.L)) *
          (Real.exp (2 * ((A / B.L) *
            (Real.log (B.sampleEndpoint : ℝ) /
              Real.log (B.sampleData.W : ℝ)))) / rho))) *
        (1 / (p : ℝ)) := by
  let Gbar : ℝ := Real.exp (2 * ((A / B.L) *
    (Real.log (B.sampleEndpoint : ℝ) /
      Real.log (B.sampleData.W : ℝ)))) / rho
  have hlogW : 0 < Real.log (B.sampleData.W : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hW)
  have hAval : ∀ d : Cell Head,
      2 * (Real.exp (2 * ((A / B.L) *
        (Real.log (B.sampleData.hi d.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ)))) / rho) ≤ 2 * Gbar := by
    intro d
    have hhiEndNat : B.sampleData.hi d.2 ≤ B.sampleEndpoint := by
      cases d.2 <;> simp [sampleEndpoint]
    have hhiPosR : (0 : ℝ) < B.sampleData.hi d.2 := by
      exact_mod_cast B.cell_hi_pos d
    have hlog : Real.log (B.sampleData.hi d.2 : ℝ) ≤
        Real.log (B.sampleEndpoint : ℝ) := by
      exact Real.log_le_log hhiPosR (by exact_mod_cast hhiEndNat)
    have hratio :
        Real.log (B.sampleData.hi d.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ) ≤
          Real.log (B.sampleEndpoint : ℝ) /
            Real.log (B.sampleData.W : ℝ) :=
      div_le_div_of_nonneg_right hlog hlogW.le
    have hscale : 0 ≤ A / B.L := div_nonneg hA B.L_pos.le
    have hexp : Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleData.hi d.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) ≤
        Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleEndpoint : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hratio hscale) (by norm_num)
    dsimp only [Gbar]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hexp hrho.le) (by norm_num)
  have hraw :=
    B.abs_tiltedLaw_covariance_nuisance_valuation_le_of_guardCensus
      xi I hp hA hW hrho hcard heta hlowerOne hupperU hlo hhi hAphys
      hAval c
  dsimp only [Gbar] at hraw
  convert hraw using 1
  all_goals ring

/-- Uniform family form consumed by the two-stage Lemma 8.6 assembly. -/
theorem nuisanceMarkedRows_le_explicit
    [Nonempty Head]
    (xi : B.ParamSpace) (I : PhysicalIntervals)
    {U rho A Aphys : ℝ}
    (hA : 0 ≤ A) (hW : 1 < B.sampleData.W)
    (hrho : 0 < rho)
    (hcard : ∀ c : Cell Head,
      rho * (B.sampleData.hi c.2 : ℝ) ≤
        ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi r| ≤ A)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys) :
    ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
      (4 * max (Real.log U) 3 *
        (Real.exp (2 * (Aphys * Real.log U / B.L)) *
          (Real.exp (2 * ((A / B.L) *
            (Real.log (B.sampleEndpoint : ℝ) /
              Real.log (B.sampleData.W : ℝ)))) / rho))) *
        (1 / (p.1 : ℝ)) := by
  intro c p
  exact B.abs_tiltedLaw_covariance_nuisance_valuation_le_explicit
    xi I (prime_of_mem_primeBand p.2) hA hW hrho hcard heta
    hlowerOne hupperU hlo hhi hAphys c

/-- A small physical residual tilt changes the *full valuation* expectation
at relative reciprocal scale.  The proof normalizes by the actual finite
cell endpoint, applies the marked small-tilt estimate, and then cancels that
endpoint exactly; hence no artificial pointwise cutoff remains in the
conclusion. -/
theorem abs_guardedCell_fullTilt_expect_valuation_sub_medium_le
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    {epsilon Aval : ℝ} {p : ℕ}
    (hp : 0 < p) (hepsilon0 : 0 ≤ epsilon) (hAval0 : 0 ≤ Aval)
    (hscore : ∀ m : B.sampleData.SampleAt c,
      |B.cellPhysicalTiltScore xi c m| ≤ epsilon)
    (hVexpect : (B.cellMediumLaw xi c).expect
      (fun m ↦ valuation p (m : ℕ)) ≤ Aval / (p : ℝ))
    (hsmall : 8 * epsilon ≤ 1) :
    |((B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)).expect
          (fun m ↦ valuation p (m : ℕ)) -
        (B.cellMediumLaw xi c).expect
          (fun m ↦ valuation p (m : ℕ))| ≤
      8 * epsilon * (Aval / (p : ℝ)) := by
  let M : ℝ := B.sampleEndpoint
  let V : B.sampleData.SampleAt c → ℝ :=
    fun m ↦ valuation p (m : ℕ)
  let A : B.sampleData.SampleAt c → ℝ := fun m ↦ V m / M
  let a : ℝ := Aval / (p : ℝ)
  have hM : 0 < M := by
    dsimp only [M]
    exact_mod_cast B.sampleEndpoint_pos c
  have hV0 : ∀ m, 0 ≤ V m := fun m ↦ valuation_nonneg p (m : ℕ)
  have hVM : ∀ m, V m ≤ M := by
    intro m
    simpa only [V, M] using B.valuation_le_sampleEndpoint c p m
  have hA0 : ∀ m, 0 ≤ A m := fun m ↦ div_nonneg (hV0 m) hM.le
  have hA1 : ∀ m, A m ≤ 1 := by
    intro m
    exact (div_le_one hM).2 (hVM m)
  have ha0 : 0 ≤ a := div_nonneg hAval0 (by exact_mod_cast hp.le)
  have hAexpect : (B.cellMediumLaw xi c).expect A ≤ a / M := by
    have hscale : A = fun m ↦ (1 / M) * V m := by
      funext m
      dsimp only [A]
      ring
    rw [hscale, (B.cellMediumLaw xi c).expect_smul]
    calc
      (1 / M) * (B.cellMediumLaw xi c).expect V =
          (B.cellMediumLaw xi c).expect V / M := by ring
      _ ≤ a / M := div_le_div_of_nonneg_right
        (by simpa only [V, a] using hVexpect) hM.le
  have hsmallTwo : 2 * epsilon < 1 := by nlinarith
  have hraw :=
    FiniteProbability.abs_exponentialTilt_expect_sub_expect_le_smallTiltLoss
      (B.cellMediumLaw xi c) A (B.cellPhysicalTiltScore xi c)
      hA0 hA1 hepsilon0 hsmallTwo hscore hAexpect
  rw [← B.guardedCell_fullTilt_eq_medium_physicalTilt xi c] at hraw
  have hloss : smallTiltLoss epsilon ≤ 8 * epsilon :=
    smallTiltLoss_le_eight_mul hepsilon0 hsmall
  have hfactor0 : 0 ≤ a / M := div_nonneg ha0 hM.le
  have hscaled :
      |((B.guardedCellProbability c).exponentialTilt
            (sigmaCellScore (B.scaledBridgeScore xi) c)).expect A -
          (B.cellMediumLaw xi c).expect A| ≤
        8 * epsilon * (a / M) :=
    hraw.trans (mul_le_mul_of_nonneg_right hloss hfactor0)
  have hExpect (mu : FiniteProbability (B.sampleData.SampleAt c)) :
      mu.expect A = (1 / M) * mu.expect V := by
    have hscale : A = fun m ↦ (1 / M) * V m := by
      funext m
      dsimp only [A]
      ring
    rw [hscale, mu.expect_smul]
  rw [hExpect, hExpect] at hscaled
  have hdiv :
      |((B.guardedCellProbability c).exponentialTilt
            (sigmaCellScore (B.scaledBridgeScore xi) c)).expect V -
          (B.cellMediumLaw xi c).expect V| / M ≤
        (8 * epsilon * a) / M := by
    calc
      |((B.guardedCellProbability c).exponentialTilt
            (sigmaCellScore (B.scaledBridgeScore xi) c)).expect V -
          (B.cellMediumLaw xi c).expect V| / M =
          |(1 / M) *
              ((B.guardedCellProbability c).exponentialTilt
                (sigmaCellScore (B.scaledBridgeScore xi) c)).expect V -
            (1 / M) * (B.cellMediumLaw xi c).expect V| := by
        rw [show |((B.guardedCellProbability c).exponentialTilt
              (sigmaCellScore (B.scaledBridgeScore xi) c)).expect V -
            (B.cellMediumLaw xi c).expect V| / M =
          |(((B.guardedCellProbability c).exponentialTilt
              (sigmaCellScore (B.scaledBridgeScore xi) c)).expect V -
            (B.cellMediumLaw xi c).expect V) / M| by
              rw [abs_div, abs_of_pos hM]]
        apply congrArg abs
        field_simp [ne_of_gt hM]
      _ ≤ 8 * epsilon * (a / M) := hscaled
      _ = (8 * epsilon * a) / M := by ring
  have hmain := (div_le_div_iff_of_pos_right hM).mp hdiv
  simpa only [V, a] using hmain

/-- Pairwise component-mean agreement survives the physical residual tilt
at the same reciprocal scale.  Both endpoint losses are included, so the
constant is exactly `16 * epsilon * Aval / p` in addition to the medium-law
pairwise error. -/
theorem abs_guardedCell_fullTilt_expect_valuation_sub_other_le
    [Nonempty Head]
    (xi : B.ParamSpace) (c c' : Cell Head)
    {epsilon Aval meanError : ℝ} {p : ℕ}
    (hp : 0 < p) (hepsilon0 : 0 ≤ epsilon) (hAval0 : 0 ≤ Aval)
    (hscore : ∀ (d : Cell Head) (m : B.sampleData.SampleAt d),
      |B.cellPhysicalTiltScore xi d m| ≤ epsilon)
    (hVexpect : ∀ d : Cell Head, (B.cellMediumLaw xi d).expect
      (fun m ↦ valuation p (m : ℕ)) ≤ Aval / (p : ℝ))
    (hsmall : 8 * epsilon ≤ 1)
    (hmediumPair :
      |(B.cellMediumLaw xi c).expect
          (fun m ↦ valuation p (m : ℕ)) -
        (B.cellMediumLaw xi c').expect
          (fun m ↦ valuation p (m : ℕ))| ≤ meanError) :
    |((B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)).expect
          (fun m ↦ valuation p (m : ℕ)) -
        ((B.guardedCellProbability c').exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c')).expect
          (fun m ↦ valuation p (m : ℕ))| ≤
      meanError + 16 * epsilon * (Aval / (p : ℝ)) := by
  let Fc : ℝ :=
    ((B.guardedCellProbability c).exponentialTilt
      (sigmaCellScore (B.scaledBridgeScore xi) c)).expect
      (fun m ↦ valuation p (m : ℕ))
  let Mc : ℝ := (B.cellMediumLaw xi c).expect
    (fun m ↦ valuation p (m : ℕ))
  let Fc' : ℝ :=
    ((B.guardedCellProbability c').exponentialTilt
      (sigmaCellScore (B.scaledBridgeScore xi) c')).expect
      (fun m ↦ valuation p (m : ℕ))
  let Mc' : ℝ := (B.cellMediumLaw xi c').expect
    (fun m ↦ valuation p (m : ℕ))
  have hc : |Fc - Mc| ≤ 8 * epsilon * (Aval / (p : ℝ)) := by
    simpa only [Fc, Mc] using
      B.abs_guardedCell_fullTilt_expect_valuation_sub_medium_le
        xi c hp hepsilon0 hAval0 (hscore c) (hVexpect c) hsmall
  have hc' : |Fc' - Mc'| ≤ 8 * epsilon * (Aval / (p : ℝ)) := by
    simpa only [Fc', Mc'] using
      B.abs_guardedCell_fullTilt_expect_valuation_sub_medium_le
        xi c' hp hepsilon0 hAval0 (hscore c') (hVexpect c') hsmall
  change |Fc - Fc'| ≤ _
  calc
    |Fc - Fc'| = |(Fc - Mc) + (Mc - Mc') + (Mc' - Fc')| := by
      congr 1
      ring
    _ ≤ |Fc - Mc| + |Mc - Mc'| + |Mc' - Fc'| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ 8 * epsilon * (Aval / (p : ℝ)) + meanError +
        8 * epsilon * (Aval / (p : ℝ)) := by
      exact add_le_add
        (add_le_add hc (by simpa only [Mc, Mc'] using hmediumPair))
        (by simpa only [abs_sub_comm] using hc')
    _ = meanError + 16 * epsilon * (Aval / (p : ℝ)) := by ring

/-- The physical residual tilt changes `Cov(v_p,R)` by `O(1/(pL))`, with
all constants explicit.  The hypothesis `hVexpect` is the reciprocal first
moment supplied by the marked-cell estimate for the medium law. -/
theorem abs_guardedCell_fullTilt_covariance_valuation_physical_sub_medium_le
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (I : PhysicalIntervals) {U Aphys Aval : ℝ} {p : ℕ}
    (hp : 0 < p)
    (hAphys0 : 0 ≤ Aphys) (hAval0 : 0 ≤ Aval)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hVexpect : (B.cellMediumLaw xi c).expect
      (fun m ↦ valuation p (m : ℕ)) ≤ Aval / (p : ℝ))
    (hsmall : 8 * (Aphys * Real.log U / B.L) ≤ 1) :
    |((B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance
          (fun m ↦ valuation p (m : ℕ))
          (fun m ↦ B.physicalScore ⟨c, m⟩) -
        (B.cellMediumLaw xi c).covariance
          (fun m ↦ valuation p (m : ℕ))
          (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
      32 * Real.log U * (Aphys * Real.log U / B.L) *
        (Aval / (p : ℝ)) := by
  let K : ℝ := Real.log U
  let epsilon : ℝ := Aphys * K / B.L
  let V : B.sampleData.SampleAt c → ℝ :=
    fun m ↦ valuation p (m : ℕ)
  let R : B.sampleData.SampleAt c → ℝ :=
    fun m ↦ B.physicalScore ⟨c, m⟩
  let R' : B.sampleData.SampleAt c → ℝ := fun m ↦ R m / K
  let a : ℝ := Aval / (p : ℝ)
  have hU : 1 < U :=
    (hlowerOne .minus).trans_lt
      ((I.lower_lt_upper .minus).trans_le (hupperU .minus))
  have hK : 0 < K := by
    exact Real.log_pos hU
  have hEndpoint : (0 : ℝ) < B.sampleEndpoint := by
    exact_mod_cast B.sampleEndpoint_pos c
  have hV0 : ∀ m, 0 ≤ V m := fun m ↦ valuation_nonneg p (m : ℕ)
  have hVupper : ∀ m, V m ≤ (B.sampleEndpoint : ℝ) :=
    fun m ↦ B.valuation_le_sampleEndpoint c p m
  have hR0 : ∀ m, 0 ≤ R m := by
    intro m
    have hlower := B.log_lower_lt_physicalScore I hlo ⟨c, m⟩
    exact (Real.log_nonneg (hlowerOne c.2)).trans hlower.le
  have hRK : ∀ m, R m ≤ K := by
    intro m
    exact (B.physicalScore_le_log_upper I hhi ⟨c, m⟩).trans
      (Real.log_le_log
        ((I.lower_pos c.2).trans (I.lower_lt_upper c.2))
        (hupperU c.2))
  have hR'0 : ∀ m, 0 ≤ R' m := fun m ↦
    div_nonneg (hR0 m) hK.le
  have hR'1 : ∀ m, R' m ≤ 1 := by
    intro m
    exact (div_le_one hK).2 (hRK m)
  have hepsilon0 : 0 ≤ epsilon := by
    exact div_nonneg (mul_nonneg hAphys0 (Real.log_nonneg hU.le)) B.L_pos.le
  have hscore : ∀ m, |B.cellPhysicalTiltScore xi c m| ≤ epsilon := by
    simpa only [epsilon, K] using
      B.abs_cellPhysicalTiltScore_le_fixedIntervals
        xi c I hlowerOne hupperU hlo hhi hAphys
  have ha0 : 0 ≤ a := div_nonneg hAval0 (by exact_mod_cast hp.le)
  have hVexpect' : (B.cellMediumLaw xi c).expect V ≤ a := by
    simpa only [V, a] using hVexpect
  have hR'expect : (B.cellMediumLaw xi c).expect R' ≤ 1 := by
    calc
      (B.cellMediumLaw xi c).expect R' ≤
          (B.cellMediumLaw xi c).expect (fun _ ↦ (1 : ℝ)) :=
        (B.cellMediumLaw xi c).expect_mono R' _ hR'1
      _ = 1 := by
        unfold FiniteProbability.expect
        rw [← Finset.sum_mul, (B.cellMediumLaw xi c).mass_sum, one_mul]
  have hVR'expect : (B.cellMediumLaw xi c).expect
      (fun m ↦ V m * R' m) ≤ a := by
    calc
      (B.cellMediumLaw xi c).expect (fun m ↦ V m * R' m) ≤
          (B.cellMediumLaw xi c).expect V := by
        apply (B.cellMediumLaw xi c).expect_mono
        intro m
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (hR'1 m) (hV0 m)
      _ ≤ a := hVexpect'
  have hraw :=
    FiniteProbability.abs_exponentialTilt_covariance_sub_covariance_le_eight_mul_left_bounded
        (B.cellMediumLaw xi c) V R' (B.cellPhysicalTiltScore xi c)
        hEndpoint hV0 hVupper hR'0 hR'1 hepsilon0
        (by simpa only [epsilon, K] using hsmall) hscore
        hVexpect' hR'expect hVR'expect
  rw [← B.guardedCell_fullTilt_eq_medium_physicalTilt xi c] at hraw
  have hcov (mu : FiniteProbability (B.sampleData.SampleAt c)) :
      mu.covariance V R' = (1 / K) * mu.covariance V R := by
    rw [show R' = fun m ↦ (1 / K) * R m by
      funext m
      dsimp only [R']
      ring]
    exact mu.covariance_smul_right (1 / K) V R
  rw [hcov, hcov] at hraw
  have hdiv :
      |((B.guardedCellProbability c).exponentialTilt
            (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance V R -
          (B.cellMediumLaw xi c).covariance V R| / K ≤
        32 * epsilon * a := by
    calc
      |((B.guardedCellProbability c).exponentialTilt
            (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance V R -
          (B.cellMediumLaw xi c).covariance V R| / K =
          |(1 / K) *
              ((B.guardedCellProbability c).exponentialTilt
                (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance V R -
            (1 / K) * (B.cellMediumLaw xi c).covariance V R| := by
        rw [show |((B.guardedCellProbability c).exponentialTilt
              (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance V R -
            (B.cellMediumLaw xi c).covariance V R| / K =
          |(((B.guardedCellProbability c).exponentialTilt
              (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance V R -
            (B.cellMediumLaw xi c).covariance V R) / K| by
              rw [abs_div, abs_of_pos hK]]
        apply congrArg abs
        field_simp [ne_of_gt hK]
      _ ≤ 8 * epsilon * (a + 3 * a * 1) := hraw
      _ = 32 * epsilon * a := by ring
  have hmain :
      |((B.guardedCellProbability c).exponentialTilt
            (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance V R -
          (B.cellMediumLaw xi c).covariance V R| ≤
        32 * K * epsilon * a := by
    have hmul := (div_le_iff₀ hK).mp hdiv
    nlinarith
  simpa only [V, R, epsilon, K, a] using hmain

/-- The full-tilt cell covariance bound obtained by combining the medium-law
Stieltjes row with the preceding residual-tilt stability theorem.  The
coefficient of `1 / (p L)` is displayed exactly, with no hidden dependence on
the later tilt box. -/
theorem abs_guardedCell_fullTilt_covariance_valuation_physical_le_of_medium
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (I : PhysicalIntervals) {U Aphys Aval Cmedium : ℝ} {p : ℕ}
    (hp : 0 < p)
    (hAphys0 : 0 ≤ Aphys) (hAval0 : 0 ≤ Aval)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hVexpect : (B.cellMediumLaw xi c).expect
      (fun m ↦ valuation p (m : ℕ)) ≤ Aval / (p : ℝ))
    (hsmall : 8 * (Aphys * Real.log U / B.L) ≤ 1)
    (hmedium :
      |(B.cellMediumLaw xi c).covariance
        (fun m ↦ valuation p (m : ℕ))
        (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
          (Cmedium / B.L) * (1 / (p : ℝ))) :
    |((B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance
          (fun m ↦ valuation p (m : ℕ))
          (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
      ((Cmedium + 32 * Real.log U * Aphys * Real.log U * Aval) / B.L) *
        (1 / (p : ℝ)) := by
  let full : ℝ :=
    ((B.guardedCellProbability c).exponentialTilt
      (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance
      (fun m ↦ valuation p (m : ℕ))
      (fun m ↦ B.physicalScore ⟨c, m⟩)
  let medium : ℝ := (B.cellMediumLaw xi c).covariance
    (fun m ↦ valuation p (m : ℕ))
    (fun m ↦ B.physicalScore ⟨c, m⟩)
  have htilt :=
    B.abs_guardedCell_fullTilt_covariance_valuation_physical_sub_medium_le
      xi c I hp hAphys0 hAval0 hlowerOne hupperU hlo hhi hAphys
      hVexpect hsmall
  have htriangle : |full| ≤ |full - medium| + |medium| := by
    have h := abs_add_le (full - medium) medium
    simpa only [sub_add_cancel] using h
  calc
    |full| ≤ |full - medium| + |medium| := htriangle
    _ ≤ 32 * Real.log U * (Aphys * Real.log U / B.L) *
          (Aval / (p : ℝ)) +
        (Cmedium / B.L) * (1 / (p : ℝ)) :=
      add_le_add (by simpa only [full, medium] using htilt) hmedium
    _ = ((Cmedium + 32 * Real.log U * Aphys * Real.log U * Aval) / B.L) *
        (1 / (p : ℝ)) := by ring

/-- Uniform family form of the two preceding residual-tilt attachments.
The only analytic inputs left are the medium-law Stieltjes covariance and
medium-law pairwise valuation profile.  The resulting full-tilt cell
covariance and pairwise mean comparison share one explicit structural
coefficient. -/
theorem fullTiltCellProfiles_of_medium_stieltjes
    [Nonempty Head]
    (xi : B.ParamSpace) (I : PhysicalIntervals)
    {U Aphys Aval Ccov Cmean : ℝ}
    (hAphys0 : 0 ≤ Aphys) (hAval0 : 0 ≤ Aval)
    (hCcov : 0 ≤ Ccov) (hCmean : 0 ≤ Cmean)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hVexpect : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c : Cell Head),
      (B.cellMediumLaw xi c).expect
        (fun m ↦ valuation p.1 (m : ℕ)) ≤ Aval / (p.1 : ℝ))
    (hsmall : 8 * (Aphys * Real.log U / B.L) ≤ 1)
    (hmediumCov : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c : Cell Head),
      |(B.cellMediumLaw xi c).covariance
        (fun m ↦ valuation p.1 (m : ℕ))
        (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
          (Ccov / B.L) * (1 / (p.1 : ℝ)))
    (hmediumPair : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c c' : Cell Head),
      |(B.cellMediumLaw xi c).expect
          (fun m ↦ valuation p.1 (m : ℕ)) -
        (B.cellMediumLaw xi c').expect
          (fun m ↦ valuation p.1 (m : ℕ))| ≤
        (Cmean / B.L) * (1 / (p.1 : ℝ))) :
    let Cfull := Ccov + Cmean +
      32 * Real.log U * Aphys * Real.log U * Aval +
      16 * Aphys * Real.log U * Aval
    (∀ (p : BandPrime B.sampleData.n B.sampleData.W) (c : Cell Head),
      |((B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance
          (fun m ↦ valuation p.1 (m : ℕ))
          (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
        (Cfull / B.L) * (1 / (p.1 : ℝ))) ∧
    (∀ (p : BandPrime B.sampleData.n B.sampleData.W) (c c' : Cell Head),
      |((B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)).expect
          (fun m ↦ valuation p.1 (m : ℕ)) -
        ((B.guardedCellProbability c').exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c')).expect
          (fun m ↦ valuation p.1 (m : ℕ))| ≤
        (Cfull / B.L) * (1 / (p.1 : ℝ))) := by
  dsimp only
  let Cfull : ℝ := Ccov + Cmean +
    32 * Real.log U * Aphys * Real.log U * Aval +
    16 * Aphys * Real.log U * Aval
  have hU : 1 < U :=
    (hlowerOne .minus).trans_lt
      ((I.lower_lt_upper .minus).trans_le (hupperU .minus))
  have hlogU : 0 ≤ Real.log U := (Real.log_pos hU).le
  have hscore : ∀ (c : Cell Head) (m : B.sampleData.SampleAt c),
      |B.cellPhysicalTiltScore xi c m| ≤
        Aphys * Real.log U / B.L := by
    intro c m
    exact B.abs_cellPhysicalTiltScore_le_fixedIntervals
      xi c I hlowerOne hupperU hlo hhi hAphys m
  constructor
  · intro p c
    have hp : 0 < p.1 := (prime_of_mem_primeBand p.2).pos
    have hraw :=
      B.abs_guardedCell_fullTilt_covariance_valuation_physical_le_of_medium
        xi c I hp hAphys0 hAval0 hlowerOne hupperU hlo hhi hAphys
        (hVexpect p c) hsmall (hmediumCov p c)
    have hnum :
        Ccov + 32 * Real.log U * Aphys * Real.log U * Aval ≤ Cfull := by
      dsimp only [Cfull]
      have hrest : 0 ≤ Cmean + 16 * Aphys * Real.log U * Aval := by
        positivity
      linarith
    have hpR : (0 : ℝ) < p.1 := by exact_mod_cast hp
    exact hraw.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hnum B.L_pos.le)
      (one_div_nonneg.mpr hpR.le))
  · intro p c c'
    have hp : 0 < p.1 := (prime_of_mem_primeBand p.2).pos
    let epsilon : ℝ := Aphys * Real.log U / B.L
    have hepsilon0 : 0 ≤ epsilon := by
      dsimp only [epsilon]
      exact div_nonneg (mul_nonneg hAphys0 hlogU) B.L_pos.le
    have hraw := B.abs_guardedCell_fullTilt_expect_valuation_sub_other_le
      xi c c' hp hepsilon0 hAval0 hscore (hVexpect p)
      (by simpa only [epsilon] using hsmall) (hmediumPair p c c')
    have hrewrite :
        (Cmean / B.L) * (1 / (p.1 : ℝ)) +
            16 * epsilon * (Aval / (p.1 : ℝ)) =
          ((Cmean + 16 * Aphys * Real.log U * Aval) / B.L) *
            (1 / (p.1 : ℝ)) := by
      dsimp only [epsilon]
      ring
    rw [hrewrite] at hraw
    have hnum : Cmean + 16 * Aphys * Real.log U * Aval ≤ Cfull := by
      dsimp only [Cfull]
      have hrest :
          0 ≤ Ccov + 32 * Real.log U * Aphys * Real.log U * Aval := by
        positivity
      linarith
    have hpR : (0 : ℝ) < p.1 := by exact_mod_cast hp
    exact hraw.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hnum B.L_pos.le)
      (one_div_nonneg.mpr hpR.le))

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
