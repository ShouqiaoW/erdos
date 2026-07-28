import Erdos390.Full.RegularRelativeMesh

/-!
# Moment budgets for the regular relative mesh

This is the elementary continuum census behind the arithmetic estimates in
Lemma 8.6.  The moving-low cell provides the quadratic lower bound, while the
geometric positive cells have total `L¹` cost at most their common relative
width and total quadratic cost at most its square.
-/

open scoped BigOperators

namespace Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- Continuum harmonic mass `integral dt/t` of a positive cell. -/
def cellHarmonicMass (k : Fin M.cellCount) : ℝ :=
  Real.log (M.upper k / M.lower k)

/-- Deterministic positive-cell `L¹` envelope. -/
def positiveL1Budget : ℝ :=
  ∑ k : Fin M.cellCount, M.width k * M.cellHarmonicMass k

/-- Deterministic positive-cell quadratic envelope. -/
def positiveVarianceBudget : ℝ :=
  ∑ k : Fin M.cellCount, M.width k ^ 2 * M.cellHarmonicMass k

theorem upper_div_lower_eq_one_add_ratio
    (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.upper k / M.lower k = 1 + M.ratio := by
  rw [show M.upper k = M.lower k * (1 + M.ratio) by
    unfold upper lower
    exact M.endpoint_succ k.1]
  field_simp [ne_of_gt (M.lower_pos hdelta k)]

theorem cellHarmonicMass_eq_log_one_add_ratio
    (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.cellHarmonicMass k = Real.log (1 + M.ratio) := by
  unfold cellHarmonicMass
  rw [M.upper_div_lower_eq_one_add_ratio hdelta k]

theorem cellHarmonicMass_pos
    (hdelta : 0 < delta) (k : Fin M.cellCount) :
    0 < M.cellHarmonicMass k := by
  rw [M.cellHarmonicMass_eq_log_one_add_ratio hdelta k]
  exact Real.log_pos (by linarith [M.ratio_pos])

theorem cellHarmonicMass_le_ratio
    (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.cellHarmonicMass k ≤ M.ratio := by
  rw [M.cellHarmonicMass_eq_log_one_add_ratio hdelta k]
  have h := Real.log_le_sub_one_of_pos (by linarith [M.ratio_pos] :
    0 < 1 + M.ratio)
  linarith

theorem lower_le_one (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.lower k ≤ 1 :=
  (M.lower_lt_upper hdelta k).le.trans (M.upper_le_one hdelta k)

theorem width_le_ratio (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.width k ≤ M.ratio := by
  rw [M.width_eq_ratio_mul_lower]
  nlinarith [M.ratio_pos, M.lower_pos hdelta k,
    M.lower_le_one hdelta k]

theorem positiveL1Budget_le_ratio_mul_one_sub_delta
    (hdelta : 0 < delta) :
    M.positiveL1Budget ≤ M.ratio * (1 - delta) := by
  unfold positiveL1Budget
  calc
    (∑ k : Fin M.cellCount,
        M.width k * M.cellHarmonicMass k) ≤
        ∑ k : Fin M.cellCount, M.width k * M.ratio := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left
        (M.cellHarmonicMass_le_ratio hdelta k)
        (M.width_pos hdelta k).le
    _ = M.ratio * (∑ k : Fin M.cellCount, M.width k) := by
      rw [← Finset.sum_mul]
      ring
    _ = M.ratio * (1 - delta) := by
      rw [M.sum_width_eq_one_sub_delta]

theorem positiveL1Budget_le_ratio
    (hdelta : 0 < delta) :
    M.positiveL1Budget ≤ M.ratio := by
  calc
    M.positiveL1Budget ≤ M.ratio * (1 - delta) :=
      M.positiveL1Budget_le_ratio_mul_one_sub_delta hdelta
    _ ≤ M.ratio := by
      nlinarith [M.ratio_pos]

theorem positiveVarianceBudget_le_ratio_sq_mul_one_sub_delta
    (hdelta : 0 < delta) :
    M.positiveVarianceBudget ≤ M.ratio ^ 2 * (1 - delta) := by
  unfold positiveVarianceBudget
  calc
    (∑ k : Fin M.cellCount,
        M.width k ^ 2 * M.cellHarmonicMass k) ≤
        ∑ k : Fin M.cellCount, M.ratio ^ 2 * M.width k := by
      apply Finset.sum_le_sum
      intro k hk
      have hw0 := (M.width_pos hdelta k).le
      have hwle := M.width_le_ratio hdelta k
      have hmle := M.cellHarmonicMass_le_ratio hdelta k
      have hratio0 := M.ratio_pos.le
      calc
        M.width k ^ 2 * M.cellHarmonicMass k ≤
            M.width k ^ 2 * M.ratio :=
          mul_le_mul_of_nonneg_left hmle (sq_nonneg _)
        _ = M.width k * (M.width k * M.ratio) := by ring
        _ ≤ M.width k * (M.ratio * M.ratio) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hwle hratio0) hw0
        _ = M.ratio ^ 2 * M.width k := by ring
    _ = M.ratio ^ 2 * (∑ k : Fin M.cellCount, M.width k) := by
      rw [← Finset.mul_sum]
    _ = M.ratio ^ 2 * (1 - delta) := by
      rw [M.sum_width_eq_one_sub_delta]

theorem positiveVarianceBudget_le_ratio_sq
    (hdelta : 0 < delta) :
    M.positiveVarianceBudget ≤ M.ratio ^ 2 := by
  calc
    M.positiveVarianceBudget ≤ M.ratio ^ 2 * (1 - delta) :=
      M.positiveVarianceBudget_le_ratio_sq_mul_one_sub_delta hdelta
    _ ≤ M.ratio ^ 2 := by
      nlinarith [sq_nonneg M.ratio]

end Mesh

/-- Continuum harmonic mass of the moving-low cell `[t₀,delta]`. -/
def lowHarmonicMass (t₀ delta : ℝ) : ℝ := Real.log (delta / t₀)

/-- Continuum first moment of the moving-low cell. -/
def lowFirstMoment (t₀ delta : ℝ) : ℝ := delta - t₀

/-- Continuum second moment of the moving-low cell. -/
def lowSecondMoment (t₀ delta : ℝ) : ℝ :=
  (delta ^ 2 - t₀ ^ 2) / 2

/-- Exact continuum centered variance of the moving-low cell. -/
def lowVariance (t₀ delta : ℝ) : ℝ :=
  lowSecondMoment t₀ delta -
    lowFirstMoment t₀ delta ^ 2 / lowHarmonicMass t₀ delta

theorem lowHarmonicMass_pos {t₀ delta : ℝ}
    (ht₀ : 0 < t₀) (htδ : t₀ < delta) :
    0 < lowHarmonicMass t₀ delta := by
  unfold lowHarmonicMass
  exact Real.log_pos ((lt_div_iff₀ ht₀).2 (by simpa using htδ))

/-- Once the moving lower endpoint is at most half of `delta` and the
harmonic mass is at least eight, the low cell alone contributes a fixed
multiple of `delta²`. -/
theorem quarter_delta_sq_le_lowVariance
    {t₀ delta : ℝ} (ht₀ : 0 < t₀) (hdelta : 0 < delta)
    (ht₀Half : t₀ ≤ delta / 2)
    (hMass : 8 ≤ lowHarmonicMass t₀ delta) :
    delta ^ 2 / 4 ≤ lowVariance t₀ delta := by
  have htδ : t₀ < delta := by linarith
  have hHpos := lowHarmonicMass_pos ht₀ htδ
  have hmoment0 : 0 ≤ lowFirstMoment t₀ delta := by
    unfold lowFirstMoment
    linarith
  have hmomentLe : lowFirstMoment t₀ delta ≤ delta := by
    unfold lowFirstMoment
    linarith
  have hmomentSq : lowFirstMoment t₀ delta ^ 2 ≤ delta ^ 2 := by
    exact (sq_le_sq₀ hmoment0 hdelta.le).2 hmomentLe
  have hquot : lowFirstMoment t₀ delta ^ 2 /
      lowHarmonicMass t₀ delta ≤ delta ^ 2 / 8 := by
    rw [div_le_iff₀ hHpos]
    have hright : delta ^ 2 ≤
        delta ^ 2 / 8 * lowHarmonicMass t₀ delta := by
      nlinarith [sq_nonneg delta]
    exact hmomentSq.trans hright
  have htSq : t₀ ^ 2 ≤ delta ^ 2 / 4 := by
    have hsq := (sq_le_sq₀ ht₀.le (div_nonneg hdelta.le (by norm_num))).2
      ht₀Half
    nlinarith
  unfold lowVariance lowSecondMoment
  linarith

theorem lowVariance_le_half_delta_sq
    {t₀ delta : ℝ} (ht₀ : 0 < t₀) (htδ : t₀ < delta) :
    lowVariance t₀ delta ≤ delta ^ 2 / 2 := by
  have hHpos := lowHarmonicMass_pos ht₀ htδ
  have hquot : 0 ≤ lowFirstMoment t₀ delta ^ 2 /
      lowHarmonicMass t₀ delta := div_nonneg (sq_nonneg _) hHpos.le
  unfold lowVariance lowSecondMoment
  nlinarith [sq_nonneg t₀]

/-- Exact-centering envelope for the low-cell `L¹` cost. -/
def lowL1Budget (t₀ delta : ℝ) : ℝ :=
  2 * lowFirstMoment t₀ delta

theorem lowL1Budget_le_two_delta
    {t₀ delta : ℝ} (ht₀ : 0 ≤ t₀) :
    lowL1Budget t₀ delta ≤ 2 * delta := by
  unfold lowL1Budget lowFirstMoment
  linarith

/-- With the requested positive relative width chosen no larger than
`delta`, the paper scale `w=delta+rho` is controlled by the low-cell
variance. -/
theorem combined_scale_bounds
    {t₀ delta : ℝ} (M : Mesh delta delta)
    (ht₀ : 0 < t₀) (hdelta : 0 < delta)
    (ht₀Half : t₀ ≤ delta / 2)
    (hMass : 8 ≤ lowHarmonicMass t₀ delta) :
    let w := delta + M.ratio
    w ^ 2 / 16 ≤ lowVariance t₀ delta ∧
      lowL1Budget t₀ delta + M.positiveL1Budget ≤ 3 * w := by
  dsimp only
  have hrho0 := M.ratio_pos.le
  have hrhoDelta := M.ratio_le_eta
  have hwSq : (delta + M.ratio) ^ 2 ≤ 4 * delta ^ 2 := by
    nlinarith
  constructor
  · have hlow := quarter_delta_sq_le_lowVariance
      ht₀ hdelta ht₀Half hMass
    nlinarith
  · have hlow := lowL1Budget_le_two_delta (delta := delta) ht₀.le
    have hpositive := M.positiveL1Budget_le_ratio hdelta
    linarith

end

end Erdos390.Full.RegularRelativeMesh
