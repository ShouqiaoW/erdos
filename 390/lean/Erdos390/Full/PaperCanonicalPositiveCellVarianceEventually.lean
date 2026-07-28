import Erdos390.Full.PaperCanonicalActualMomentBoundsEventually

/-!
# Positive-cell variance on an arbitrary regular relative mesh

The moving low cell alone controls the paper scale only when the positive
relative width is no larger than the low endpoint.  This file supplies the
missing complementary estimate: the sum of the literal within-cell prime
variances in the positive cells is bounded below by a fixed multiple of the
square of the actual common mesh ratio.  The proof first identifies the
finite prime moments with three unconditional PNT quadratures and then
passes to the exact continuum cell variance.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer KernelPrimeQuadrature PrimeBandQuadrature
open PrimeCoordinateSecondMoment MovingLowMomentQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- Exact continuum variance of one positive logarithmic cell for the
harmonic measure `dt/t`. -/
def idealPositiveBandVariance (k : Fin M.cellCount) : ℝ :=
  (M.upper k ^ 2 - M.lower k ^ 2) / 2 -
    M.width k ^ 2 / M.cellHarmonicMass k

/-- The first two positive terms of the symmetric power series for
`log (1+r)` already retain the cubic information needed for variance. -/
theorem twoTerm_log_one_add_lower :
    2 * (M.ratio / (M.ratio + 2)) +
        (2 / 3 : ℝ) * (M.ratio / (M.ratio + 2)) ^ 3 ≤
      Real.log (1 + M.ratio) := by
  let f : ℕ → ℝ := fun k ↦
    2 * (1 / (2 * (k : ℝ) + 1)) *
      (M.ratio / (M.ratio + 2)) ^ (2 * k + 1)
  have hs : HasSum f (Real.log (1 + M.ratio)) := by
    simpa only [f] using Real.hasSum_log_one_add M.ratio_pos.le
  have hsum := hs.summable.sum_le_tsum (Finset.range 2) (fun k hk ↦ by
    dsimp only [f]
    have hden : 0 ≤ 2 * (k : ℝ) + 1 := by positivity
    have hbase : 0 ≤ M.ratio / (M.ratio + 2) :=
      div_nonneg M.ratio_pos.le (by linarith [M.ratio_pos])
    exact mul_nonneg (mul_nonneg (by norm_num) (one_div_nonneg.mpr hden))
      (pow_nonneg hbase _))
  rw [hs.tsum_eq] at hsum
  norm_num [f, Finset.sum_range_succ] at hsum
  convert hsum using 1

/-- Cubic lower bound for the continuum variance in one geometric cell.
The numerical constant is deliberately coarse and uniform. -/
theorem lower_sq_mul_ratio_cube_div_le_idealPositiveBandVariance
    (hdelta : 0 < delta) (hratioOne : M.ratio ≤ 1)
    (k : Fin M.cellCount) :
    M.lower k ^ 2 * M.ratio ^ 3 / 28 ≤
      idealPositiveBandVariance M k := by
  let r : ℝ := M.ratio
  let a : ℝ := M.lower k
  let x : ℝ := r / (r + 2)
  let H₀ : ℝ := 2 * x + (2 / 3 : ℝ) * x ^ 3
  have hr : 0 < r := M.ratio_pos
  have hra : r ≤ 1 := hratioOne
  have ha : 0 < a := M.lower_pos hdelta k
  have hx : 0 < x := by
    dsimp only [x, r]
    exact div_pos M.ratio_pos (by linarith [M.ratio_pos])
  have hH₀ : 0 < H₀ := by
    dsimp only [H₀]
    positivity
  have hH₀le : H₀ ≤ Real.log (1 + r) := by
    simpa only [H₀, x, r] using twoTerm_log_one_add_lower M
  have hlog : 0 < Real.log (1 + r) :=
    Real.log_pos (by linarith [hr])
  have hquot : r ^ 2 / Real.log (1 + r) ≤ r ^ 2 / H₀ :=
    div_le_div_of_nonneg_left (sq_nonneg r) hH₀ hH₀le
  have hformula :
      r + r ^ 2 / 2 - r ^ 2 / H₀ =
        r ^ 3 * (r + 2) / (8 * (r ^ 2 + 3 * r + 3)) := by
    dsimp only [H₀, x]
    have hr2 : r + 2 ≠ 0 := by linarith
    have hpoly : r ^ 2 + 3 * r + 3 ≠ 0 := by nlinarith [sq_nonneg r]
    field_simp [hr2, hpoly]
    ring
  have hrsq : r ^ 2 ≤ r := by nlinarith [mul_nonneg hr.le (by linarith : 0 ≤ 1 - r)]
  have hpolyUpper : r ^ 2 + 3 * r + 3 ≤ 7 := by linarith
  have hdenPos : 0 < 8 * (r ^ 2 + 3 * r + 3) := by
    positivity
  have hcoarse : r ^ 3 / 28 ≤
      r ^ 3 * (r + 2) / (8 * (r ^ 2 + 3 * r + 3)) := by
    rw [le_div_iff₀ hdenPos]
    have hrCube : 0 ≤ r ^ 3 := by positivity
    nlinarith
  have hscalar : r ^ 3 / 28 ≤
      r + r ^ 2 / 2 - r ^ 2 / Real.log (1 + r) := by
    have hH₀scalar : r ^ 3 / 28 ≤
        r + r ^ 2 / 2 - r ^ 2 / H₀ := hcoarse.trans_eq hformula.symm
    linarith
  have hupper : M.upper k = a * (1 + r) := by
    dsimp only [a, r]
    unfold RegularRelativeMesh.Mesh.upper RegularRelativeMesh.Mesh.lower
    exact M.endpoint_succ k.1
  have hwidth : M.width k = r * a := by
    dsimp only [r, a]
    exact M.width_eq_ratio_mul_lower k
  have hmass : M.cellHarmonicMass k = Real.log (1 + r) := by
    simpa only [r] using M.cellHarmonicMass_eq_log_one_add_ratio hdelta k
  rw [idealPositiveBandVariance, hupper, hwidth, hmass]
  have haSq : 0 ≤ a ^ 2 := sq_nonneg a
  calc
    a ^ 2 * r ^ 3 / 28 = a ^ 2 * (r ^ 3 / 28) := by ring
    _ ≤ a ^ 2 *
        (r + r ^ 2 / 2 - r ^ 2 / Real.log (1 + r)) :=
      mul_le_mul_of_nonneg_left hscalar haSq
    _ = ((a * (1 + r)) ^ 2 - a ^ 2) / 2 -
        (r * a) ^ 2 / Real.log (1 + r) := by ring

/-- The squared endpoint increments telescope over the entire positive
mesh, just as the ordinary widths do. -/
theorem sum_upper_sq_sub_lower_sq :
    ∑ k : Fin M.cellCount, (M.upper k ^ 2 - M.lower k ^ 2) =
      1 - delta ^ 2 := by
  change (∑ k : Fin M.cellCount,
      (fun i : ℕ ↦ M.endpoint (i + 1) ^ 2 - M.endpoint i ^ 2) k.1) =
    1 - delta ^ 2
  calc
    (∑ k : Fin M.cellCount,
        (fun i : ℕ ↦ M.endpoint (i + 1) ^ 2 - M.endpoint i ^ 2) k.1) =
        ∑ k ∈ Finset.range M.cellCount,
          (M.endpoint (k + 1) ^ 2 - M.endpoint k ^ 2) :=
      Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ M.endpoint (i + 1) ^ 2 - M.endpoint i ^ 2)
          M.cellCount
    _ = 1 - delta ^ 2 := by
      have htel := Finset.sum_range_sub
        (fun i : ℕ ↦ M.endpoint i ^ 2) M.cellCount
      rw [M.endpoint_cellCount, M.endpoint_zero] at htel
      norm_num at htel
      rw [Finset.sum_sub_distrib]
      exact htel

/-- Summing the one-cell cubic estimate gives a quadratic lower bound in
the actual common mesh ratio. -/
theorem ratio_sq_div_le_sum_idealPositiveBandVariance
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (1 : ℝ) / 2)
    (hratioOne : M.ratio ≤ 1) :
    M.ratio ^ 2 / 112 ≤
      ∑ k : Fin M.cellCount, idealPositiveBandVariance M k := by
  have hcell (k : Fin M.cellCount) :
      M.lower k ^ 2 * M.ratio ^ 3 / 28 =
        (M.ratio ^ 2 / (28 * (M.ratio + 2))) *
          (M.upper k ^ 2 - M.lower k ^ 2) := by
    have hupper : M.upper k = M.lower k * (1 + M.ratio) := by
      unfold RegularRelativeMesh.Mesh.upper RegularRelativeMesh.Mesh.lower
      exact M.endpoint_succ k.1
    rw [hupper]
    have hden : M.ratio + 2 ≠ 0 := by linarith [M.ratio_pos]
    field_simp [hden]
    ring
  have hsumLower :
      (∑ k : Fin M.cellCount,
          M.lower k ^ 2 * M.ratio ^ 3 / 28) ≤
        ∑ k : Fin M.cellCount, idealPositiveBandVariance M k := by
    exact Finset.sum_le_sum fun k hk ↦
      lower_sq_mul_ratio_cube_div_le_idealPositiveBandVariance
        M hdelta hratioOne k
  have hsumIdentity :
      (∑ k : Fin M.cellCount,
          M.lower k ^ 2 * M.ratio ^ 3 / 28) =
        M.ratio ^ 2 * (1 - delta ^ 2) /
          (28 * (M.ratio + 2)) := by
    calc
      (∑ k : Fin M.cellCount,
          M.lower k ^ 2 * M.ratio ^ 3 / 28) =
          ∑ k : Fin M.cellCount,
            (M.ratio ^ 2 / (28 * (M.ratio + 2))) *
              (M.upper k ^ 2 - M.lower k ^ 2) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hcell k
      _ = (M.ratio ^ 2 / (28 * (M.ratio + 2))) *
          (∑ k : Fin M.cellCount,
            (M.upper k ^ 2 - M.lower k ^ 2)) := by
        rw [Finset.mul_sum]
      _ = M.ratio ^ 2 * (1 - delta ^ 2) /
          (28 * (M.ratio + 2)) := by
        rw [sum_upper_sq_sub_lower_sq M]
        ring
  have hdeltaSq : delta ^ 2 ≤ (1 : ℝ) / 4 := by
    nlinarith [sq_nonneg delta]
  have hdenPos : 0 < 28 * (M.ratio + 2) := by
    exact mul_pos (by norm_num) (by linarith [M.ratio_pos])
  have hcoarse : M.ratio ^ 2 / 112 ≤
      M.ratio ^ 2 * (1 - delta ^ 2) /
        (28 * (M.ratio + 2)) := by
    rw [le_div_iff₀ hdenPos]
    have hrSq : 0 ≤ M.ratio ^ 2 := sq_nonneg _
    nlinarith
  rw [← hsumIdentity] at hcoarse
  exact hcoarse.trans hsumLower

/-- The three literal prime sums attached to a positive canonical cell.
They are defined without choosing a proof of scale separation, so their
limits can be stated as ordinary sequences. -/
def canonicalPositiveMassValue (n W : ℕ) (k : Fin M.cellCount) : ℝ :=
  PrimeSums.fullReciprocalSum (fullCutoff M n W (k.1 + 2)) -
    PrimeSums.fullReciprocalSum (fullCutoff M n W (k.1 + 1))

def canonicalPositiveFirstValue (n W : ℕ) (k : Fin M.cellCount) : ℝ :=
  (PrimeSums.fullLogReciprocalSum (fullCutoff M n W (k.1 + 2)) -
      PrimeSums.fullLogReciprocalSum (fullCutoff M n W (k.1 + 1))) /
    Real.log (y n)

def canonicalPositiveSecondValue (n W : ℕ) (k : Fin M.cellCount) : ℝ :=
  fullWeightedReciprocalSum squareCoordinate (y n)
      (fullCutoff M n W (k.1 + 2)) -
    fullWeightedReciprocalSum squareCoordinate (y n)
      (fullCutoff M n W (k.1 + 1))

def canonicalPositiveVarianceValue (n W : ℕ) (k : Fin M.cellCount) : ℝ :=
  canonicalPositiveSecondValue M n W k -
    canonicalPositiveFirstValue M n W k ^ 2 /
      canonicalPositiveMassValue M n W k

/-- Endpoint second moment before applying the prime quadrature. -/
def positiveContinuumSecond (n W : ℕ) (k : Fin M.cellCount) : ℝ :=
  (cutoffCoordinate M n W (k.1 + 2) ^ 2 -
    cutoffCoordinate M n W (k.1 + 1) ^ 2) / 2

private theorem tendsto_of_abs_sub_le
    {f g e : ℕ → ℝ} {a : ℝ}
    (hg : Tendsto g atTop (nhds a)) (he : Tendsto e atTop (nhds 0))
    (hbound : ∀ᶠ n : ℕ in atTop, |f n - g n| ≤ e n) :
    Tendsto f atTop (nhds a) := by
  have habs : Tendsto (fun n ↦ |f n - g n|) atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun n ↦ abs_nonneg _))
      hbound he
  have hdiff : Tendsto (fun n ↦ f n - g n) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by
      simpa only [Real.norm_eq_abs] using habs)
  have hadd := hdiff.add hg
  simpa only [sub_add_cancel, zero_add] using hadd

theorem tendsto_positiveContinuumSecond
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ positiveContinuumSecond M n W k) atTop
      (nhds ((M.upper k ^ 2 - M.lower k ^ 2) / 2)) := by
  have hLower := (tendsto_positive_lowerCoordinate M hdelta W k).pow 2
  have hUpper := (tendsto_positive_upperCoordinate M hdelta W k).pow 2
  simpa only [positiveContinuumSecond] using
    (hUpper.sub hLower).div_const (2 : ℝ)

theorem tendsto_positiveSecondError_zero
    (C : ℝ) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      3 * C /
        (Real.log (y n) ^ 2 *
          Real.log (fullCutoff M n W (k.1 + 1) : ℝ)))
      atTop (nhds 0) := by
  have hInvY : Tendsto (fun n : ℕ ↦ (Real.log (y n))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_y_atTop
  have hLowerReal : Tendsto (fun n : ℕ ↦
      (fullCutoff M n W (k.1 + 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_positive_lowerCutoff_atTop M (by
        have hdelta : 0 < delta := by
          have hbase : 0 < (1 + M.ratio) ^ M.cellCount :=
            pow_pos (by linarith [M.ratio_pos]) M.cellCount
          nlinarith [M.lastEndpoint]
        exact hdelta) W k)
  have hInvA : Tendsto (fun n : ℕ ↦
      (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hLowerReal)
  have hMain :=
    ((tendsto_const_nhds : Tendsto (fun _n : ℕ ↦ 3 * C) atTop
      (nhds (3 * C))).mul (hInvY.pow 2)).mul hInvA
  convert hMain using 1 <;> ring

/-- Literal reciprocal mass in a fixed positive cell converges to its
harmonic continuum mass. -/
theorem tendsto_canonicalPositiveMassValue
    (hdelta : 0 < delta) {W : ℕ}
    (hW : canonicalMassQuadratureCutoff ≤ W)
    (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ canonicalPositiveMassValue M n W k) atTop
      (nhds (M.cellHarmonicMass k)) := by
  have hMain : Tendsto (fun n : ℕ ↦
      endpointContinuumMass M n W (positiveBand M k)) atTop
      (nhds (M.cellHarmonicMass k)) := by
    have hEq : M.cellHarmonicMass k =
        Real.log (M.upper k) - Real.log (M.lower k) := by
      unfold RegularRelativeMesh.Mesh.cellHarmonicMass
      rw [Real.log_div
        (ne_of_gt ((M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k)))
        (ne_of_gt (M.lower_pos hdelta k))]
    rw [hEq]
    exact tendsto_positive_endpointContinuumMass M hdelta W k
  have hError := tendsto_positive_massError_zero M hdelta W
    canonicalMassQuadratureConstant k
  have hBound : ∀ᶠ n : ℕ in atTop,
      |canonicalPositiveMassValue M n W k -
        endpointContinuumMass M n W (positiveBand M k)| ≤
          5 * canonicalMassQuadratureConstant /
            Real.log (fullCutoff M n W (k.1 + 1) : ℝ) ^ 3 := by
    filter_upwards [eventually_gt_atTop 1,
      eventually_scaleSeparation M hdelta W] with n hn S
    have hmono := fullCutoff_monotone M hdelta hn
      (W_le_first_fullCutoff M S)
    have hA : canonicalMassQuadratureCutoff ≤
        fullCutoff M n W (k.1 + 1) :=
      hW.trans ((W_le_first_fullCutoff M S).trans
        (hmono (by omega : 1 ≤ k.1 + 1)))
    have hAY : fullCutoff M n W (k.1 + 1) ≤
        fullCutoff M n W (k.1 + 2) := hmono (by omega)
    have hq := canonicalMassQuadratureBound
      (fullCutoff M n W (k.1 + 1))
      (fullCutoff M n W (k.1 + 2)) hA hAY
    simpa only [canonicalPositiveMassValue, endpointContinuumMass,
      positiveBand, Fin.val_succ] using hq
  exact tendsto_of_abs_sub_le hMain hError hBound

/-- Literal first logarithmic prime moment in a fixed positive cell
converges to the cell width. -/
theorem tendsto_canonicalPositiveFirstValue
    (hdelta : 0 < delta) {W : ℕ}
    (hWtwo : 2 ≤ W)
    (hW : fullLogReciprocalSumUniformCutoff ≤ W)
    (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ canonicalPositiveFirstValue M n W k) atTop
      (nhds (M.width k)) := by
  have hMain := tendsto_positive_endpointContinuumMoment M hdelta W k
  have hError := tendsto_positive_endpointMomentError_zero M hdelta
    fullLogReciprocalSumUniformConstant W k
  have hBound : ∀ᶠ n : ℕ in atTop,
      |canonicalPositiveFirstValue M n W k -
        endpointContinuumMoment M n W (positiveBand M k)| ≤
          endpointMomentError M fullLogReciprocalSumUniformConstant
            n W (positiveBand M k) := by
    filter_upwards [eventually_gt_atTop 1,
      eventually_scaleSeparation M hdelta W] with n hn S
    have hWne : W ≠ 0 := by omega
    have hq :=
      abs_canonical_mass_mul_center_sub_endpointContinuumMoment_le
        M hdelta hn hWne S fullLogReciprocalSumUniform_bound hW
          (positiveBand M k)
    let P := canonicalPartition M hdelta hn hWne S
    let E := canonicalCertificate M hdelta hn hWne S
    have hfirst : P.mass (positiveBand M k) *
        P.center (positiveBand M k) =
          canonicalPositiveFirstValue M n W k := by
      rw [E.mass_mul_center_eq_fullLogReciprocalSum_sub]
      rfl
    change |P.mass (positiveBand M k) * P.center (positiveBand M k) -
      endpointContinuumMoment M n W (positiveBand M k)| ≤
        endpointMomentError M fullLogReciprocalSumUniformConstant
          n W (positiveBand M k) at hq
    rw [hfirst] at hq
    exact hq
  exact tendsto_of_abs_sub_le hMain hError hBound

/-- Literal second logarithmic prime moment in a fixed positive cell
converges to the corresponding continuum second moment. -/
theorem tendsto_canonicalPositiveSecondValue
    (hdelta : 0 < delta) {W : ℕ}
    (hW : canonicalSecondMomentCutoff ≤ W)
    (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ canonicalPositiveSecondValue M n W k) atTop
      (nhds ((M.upper k ^ 2 - M.lower k ^ 2) / 2)) := by
  have hMain := tendsto_positiveContinuumSecond M hdelta W k
  have hError := tendsto_positiveSecondError_zero M
    canonicalSecondMomentConstant W k
  have hBound : ∀ᶠ n : ℕ in atTop,
      |canonicalPositiveSecondValue M n W k -
        positiveContinuumSecond M n W k| ≤
          3 * canonicalSecondMomentConstant /
            (Real.log (y n) ^ 2 *
              Real.log (fullCutoff M n W (k.1 + 1) : ℝ)) := by
    filter_upwards [eventually_gt_atTop 1,
      eventually_scaleSeparation M hdelta W] with n hn S
    have hmono := fullCutoff_monotone M hdelta hn
      (W_le_first_fullCutoff M S)
    have hA : canonicalSecondMomentCutoff ≤
        fullCutoff M n W (k.1 + 1) :=
      hW.trans ((W_le_first_fullCutoff M S).trans
        (hmono (by omega : 1 ≤ k.1 + 1)))
    have hAY : fullCutoff M n W (k.1 + 1) ≤
        fullCutoff M n W (k.1 + 2) := hmono (by omega)
    have hq := canonicalSecondMomentBound (y n) (y_gt_one hn)
      (fullCutoff M n W (k.1 + 1))
      (fullCutoff M n W (k.1 + 2)) hA hAY
    simpa only [canonicalPositiveSecondValue, positiveContinuumSecond,
      cutoffCoordinate] using hq
  exact tendsto_of_abs_sub_le hMain hError hBound

/-- The exact prime-sum variance of a fixed positive cell converges to its
continuum harmonic variance. -/
theorem tendsto_canonicalPositiveVarianceValue
    (hdelta : 0 < delta) {W : ℕ}
    (hW : canonicalActualMomentCutoff ≤ W)
    (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ canonicalPositiveVarianceValue M n W k) atTop
      (nhds (idealPositiveBandVariance M k)) := by
  have hW8 : 8 ≤ W :=
    (le_max_left 8 (max canonicalMassQuadratureCutoff
      (max fullLogReciprocalSumUniformCutoff
        canonicalSecondMomentCutoff))).trans hW
  have hMassCutoff : canonicalMassQuadratureCutoff ≤ W :=
    ((le_max_left canonicalMassQuadratureCutoff
      (max fullLogReciprocalSumUniformCutoff canonicalSecondMomentCutoff)).trans
      (le_max_right 8 (max canonicalMassQuadratureCutoff
        (max fullLogReciprocalSumUniformCutoff
          canonicalSecondMomentCutoff)))).trans hW
  have hFirstCutoff : fullLogReciprocalSumUniformCutoff ≤ W :=
    ((le_max_left fullLogReciprocalSumUniformCutoff
      canonicalSecondMomentCutoff).trans
      ((le_max_right canonicalMassQuadratureCutoff
        (max fullLogReciprocalSumUniformCutoff canonicalSecondMomentCutoff)).trans
        (le_max_right 8 (max canonicalMassQuadratureCutoff
          (max fullLogReciprocalSumUniformCutoff
            canonicalSecondMomentCutoff))))).trans hW
  have hSecondCutoff : canonicalSecondMomentCutoff ≤ W :=
    ((le_max_right fullLogReciprocalSumUniformCutoff
      canonicalSecondMomentCutoff).trans
      ((le_max_right canonicalMassQuadratureCutoff
        (max fullLogReciprocalSumUniformCutoff canonicalSecondMomentCutoff)).trans
        (le_max_right 8 (max canonicalMassQuadratureCutoff
          (max fullLogReciprocalSumUniformCutoff
            canonicalSecondMomentCutoff))))).trans hW
  have hMass := tendsto_canonicalPositiveMassValue M hdelta hMassCutoff k
  have hFirst := tendsto_canonicalPositiveFirstValue M hdelta
    (by omega : 2 ≤ W) hFirstCutoff k
  have hSecond := tendsto_canonicalPositiveSecondValue M hdelta
    hSecondCutoff k
  have hMassPos : 0 < M.cellHarmonicMass k :=
    M.cellHarmonicMass_pos hdelta k
  have hQuot := (hFirst.pow 2).div hMass (ne_of_gt hMassPos)
  simpa only [canonicalPositiveVarianceValue, idealPositiveBandVariance]
    using hSecond.sub hQuot

/-- Summed convergence over the finite positive mesh. -/
theorem tendsto_sum_canonicalPositiveVarianceValue
    (hdelta : 0 < delta) {W : ℕ}
    (hW : canonicalActualMomentCutoff ≤ W) :
    Tendsto (fun n : ℕ ↦
      ∑ k : Fin M.cellCount, canonicalPositiveVarianceValue M n W k)
      atTop (nhds (∑ k : Fin M.cellCount,
        idealPositiveBandVariance M k)) := by
  exact tendsto_finset_sum Finset.univ (fun k hk ↦
    tendsto_canonicalPositiveVarianceValue M hdelta hW k)

/-- The actual prime-sum positive variance eventually retains half of the
uniform continuum lower bound. -/
theorem eventually_ratio_sq_div_le_sum_canonicalPositiveVarianceValue
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (1 : ℝ) / 2)
    (hratioOne : M.ratio ≤ 1) {W : ℕ}
    (hW : canonicalActualMomentCutoff ≤ W) :
    ∀ᶠ n : ℕ in atTop,
      M.ratio ^ 2 / 224 ≤
        ∑ k : Fin M.cellCount,
          canonicalPositiveVarianceValue M n W k := by
  have hLimit := tendsto_sum_canonicalPositiveVarianceValue M hdelta hW
  have hIdeal := ratio_sq_div_le_sum_idealPositiveBandVariance M hdelta
    hdeltaHalf hratioOne
  have hStrict : M.ratio ^ 2 / 224 <
      ∑ k : Fin M.cellCount, idealPositiveBandVariance M k := by
    have hrSqPos : 0 < M.ratio ^ 2 := sq_pos_of_pos M.ratio_pos
    exact (by nlinarith : M.ratio ^ 2 / 224 < M.ratio ^ 2 / 112).trans_le
      hIdeal
  exact hLimit.eventually (eventually_ge_nhds hStrict)

/-- Identification of the prime-sum proxy with the literal variance of a
canonical positive band. -/
theorem canonical_bandVariance_positive_eq_value
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n) (hWne : W ≠ 0)
    (S : ScaleSeparation M n W) (k : Fin M.cellCount) :
    let P := canonicalPartition M hdelta hn hWne S
    P.bandVariance (positiveBand M k) =
      canonicalPositiveVarianceValue M n W k := by
  let P := canonicalPartition M hdelta hn hWne S
  let E := canonicalCertificate M hdelta hn hWne S
  dsimp only
  have hMass : P.mass (positiveBand M k) =
      canonicalPositiveMassValue M n W k := by
    rw [E.mass_eq_fullReciprocalSum_sub]
    rfl
  have hFirst : P.mass (positiveBand M k) *
      P.center (positiveBand M k) =
        canonicalPositiveFirstValue M n W k := by
    rw [E.mass_mul_center_eq_fullLogReciprocalSum_sub]
    rfl
  have hSecond : P.bandSecondMoment (positiveBand M k) =
      canonicalPositiveSecondValue M n W k := by
    rw [P.bandSecondMoment_eq_fullWeightedReciprocalSum_sub E]
    rfl
  rw [P.bandVariance_eq_second_sub_mass_center_sq, hSecond]
  unfold canonicalPositiveVarianceValue
  rw [← hMass, ← hFirst]
  have hMassNe : P.mass (positiveBand M k) ≠ 0 :=
    ne_of_gt (P.data.mass_pos (positiveBand M k))
  field_simp [hMassNe]

/-- Paper-order eventual form of the literal positive-cell variance lower.
The global cutoff is fixed before the mesh; only the ambient threshold may
depend on the fixed mesh. -/
theorem canonicalPositiveVarianceCutoff_eventually
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (1 : ℝ) / 2)
    (hratioOne : M.ratio ≤ 1) :
    ∀ W : ℕ, canonicalActualMomentCutoff ≤ W →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∀ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            M.ratio ^ 2 / 224 ≤
              ∑ k : Fin M.cellCount,
                P.bandVariance (positiveBand M k) := by
  intro W hW
  have hValue :=
    eventually_ratio_sq_div_le_sum_canonicalPositiveVarianceValue
      M hdelta hdeltaHalf hratioOne hW
  have hWne : W ≠ 0 := by
    have hW8 : 8 ≤ W :=
      (le_max_left 8 (max canonicalMassQuadratureCutoff
        (max fullLogReciprocalSumUniformCutoff
          canonicalSecondMomentCutoff))).trans hW
    omega
  filter_upwards [hValue, eventually_gt_atTop 1] with n hValueN hn
  refine ⟨hWne, hn, ?_⟩
  intro S
  let P := canonicalPartition M hdelta hn hWne S
  calc
    M.ratio ^ 2 / 224 ≤
        ∑ k : Fin M.cellCount,
          canonicalPositiveVarianceValue M n W k := hValueN
    _ = ∑ k : Fin M.cellCount,
        P.bandVariance (positiveBand M k) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact (canonical_bandVariance_positive_eq_value M hdelta hn hWne S k).symm

/-- The fixed interior prime mass gives a mesh-independent lower floor for
the literal arithmetic centre energy. -/
theorem one_div_64_le_centerEnergy_of_canonical_anchor
    {n W : ℕ} (hdelta : 0 < delta)
    (hn : 1 < n) (hWne : W ≠ 0) (S : ScaleSeparation M n W)
    (anchors : Finset (Fin M.cellCount))
    (hinterior : ∀ p ∈ canonicalPrimeAnchorSet M
        (canonicalPartition M hdelta hn hWne S) anchors,
      tPrime n p.1 ∈ Set.Icc ((1 : ℝ) / 8) (1 - (1 : ℝ) / 8))
    (hAnchorMass : (1 : ℝ) / 8 ≤
      FiniteAnchoredDirichletQuadratic.anchorMass
        (PrimeSquarefreeDirichletGeometry.primeWeight n)
        (canonicalPrimeAnchorSet M
          (canonicalPartition M hdelta hn hWne S) anchors)) :
    (1 : ℝ) / 64 ≤
      (canonicalPartition M hdelta hn hWne S).centerEnergy := by
  let P := canonicalPartition M hdelta hn hWne S
  have hEnergy := epsilon_mul_anchorMass_le_centerEnergy M P hn
    (by norm_num : (0 : ℝ) ≤ 1 / 8) anchors hinterior
  calc
    (1 : ℝ) / 64 = (1 / 8 : ℝ) * (1 / 8 : ℝ) := by norm_num
    _ ≤ (1 / 8 : ℝ) *
        FiniteAnchoredDirichletQuadratic.anchorMass
          (PrimeSquarefreeDirichletGeometry.primeWeight n)
          (canonicalPrimeAnchorSet M P anchors) := by
      exact mul_le_mul_of_nonneg_left hAnchorMass (by norm_num)
    _ ≤ P.centerEnergy := hEnergy

/-- Interior prime mass forces the center energy to dominate the within-cell
variance whenever the actual mesh scale is sufficiently small.  This form is
uniform for independent `delta` and `eta`. -/
theorem variance_le_centerEnergy_of_canonical_anchor_of_actualScale
    {n W : ℕ} (hdelta : 0 < delta)
    (hscaleSmall : delta + M.ratio ≤ (1 : ℝ) / 16)
    (hn : 1 < n) (hWne : W ≠ 0) (S : ScaleSeparation M n W)
    (anchors : Finset (Fin M.cellCount))
    (hinterior : ∀ p ∈ canonicalPrimeAnchorSet M
        (canonicalPartition M hdelta hn hWne S) anchors,
      tPrime n p.1 ∈ Set.Icc ((1 : ℝ) / 8) (1 - (1 : ℝ) / 8))
    (hAnchorMass : (1 : ℝ) / 8 ≤
      FiniteAnchoredDirichletQuadratic.anchorMass
        (PrimeSquarefreeDirichletGeometry.primeWeight n)
        (canonicalPrimeAnchorSet M
          (canonicalPartition M hdelta hn hWne S) anchors))
    (hVarUpper :
      (canonicalPartition M hdelta hn hWne S).variance ≤
        4 * (delta + M.ratio) ^ 2) :
    (canonicalPartition M hdelta hn hWne S).variance ≤
      (canonicalPartition M hdelta hn hWne S).centerEnergy := by
  let P := canonicalPartition M hdelta hn hWne S
  have hEnergyFloor : (1 : ℝ) / 64 ≤ P.centerEnergy := by
    exact one_div_64_le_centerEnergy_of_canonical_anchor M hdelta
      hn hWne S anchors hinterior hAnchorMass
  have hscaleNonneg : 0 ≤ delta + M.ratio :=
    (add_pos hdelta M.ratio_pos).le
  have hSmallVar : 4 * (delta + M.ratio) ^ 2 ≤ (1 : ℝ) / 64 := by
    nlinarith
  exact hVarUpper.trans (hSmallVar.trans hEnergyFloor)

end Mesh

end Erdos390.Full.RegularMeshPrimeCutoffs
