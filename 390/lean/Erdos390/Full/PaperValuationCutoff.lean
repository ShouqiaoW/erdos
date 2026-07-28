import Erdos390.Full.ValuationCutoff
import Erdos390.Full.PaperTiltSmallness

/-!
# Paper-scale bounds for the logarithmic valuation cutoff

At the physical scale `m ≤ C n` and for `W < p ≤ n^(2/9)`, the exact local
cutoff is `O(L / log W)`.  This turns every restored coefficient tail into
`L⁻¹ p^{-r}` with an exponential constant depending on the already fixed
box and cutoff, while leaving the leading prime-power constant independent
of that box.
-/

open Filter Topology

namespace Erdos390.Full.PaperValuationCutoff

open ArithmeticModel Scale
open ValuationCutoff LocalFugacityBounds

noncomputable section

/-- The logarithmic valuation-cutoff estimate only needs a positive physical
upper endpoint.  The older `1 ≤ C` formulation below is retained as a
compatibility wrapper, but that normalization is not part of the paper's
cell hypotheses. -/
theorem eventually_valuationCutoff_div_L_le_of_pos
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W,
      (valuationCutoff p (physicalBound C n) : ℝ) / L n ≤
        2 / Real.log (W : ℝ) := by
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hCevent : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop C)
  have hInvCevent : ∀ᶠ n : ℕ in atTop, 1 / C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop (1 / C))
  filter_upwards [hCevent, hInvCevent, Filter.eventually_gt_atTop 1]
    with n hCn hInvCn hn
  intro p hpBand
  have hL : 0 < L n := L_pos hn
  have hlogW : 0 < Real.log (W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  have hpPrime : p.Prime := prime_of_mem_primeBand hpBand
  have hpW : W < p := cutoff_lt_of_mem_primeBand hpBand
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hpPrime.one_lt)
  have hlogWp : Real.log (W : ℝ) ≤ Real.log (p : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast hW.le)
    exact_mod_cast hpW.le
  have hOneMul : (1 : ℝ) ≤ C * (n : ℝ) := by
    have h := (div_le_iff₀ hC).mp hInvCn
    simpa [mul_comm] using h
  have hphysOne : 1 ≤ physicalBound C n := by
    unfold physicalBound
    apply Nat.le_floor
    exact_mod_cast hOneMul
  have hM : 0 < physicalBound C n := lt_of_lt_of_le Nat.zero_lt_one hphysOne
  have hphysCast : (physicalBound C n : ℝ) ≤ C * (n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hC.le (by positivity))
  have hCnSq : C * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hlogPhys : Real.log (physicalBound C n : ℝ) ≤ 2 * L n := by
    have hleSq : (physicalBound C n : ℝ) ≤ (n : ℝ) ^ 2 :=
      hphysCast.trans hCnSq
    have hlog := Real.log_le_log (by exact_mod_cast hM) hleSq
    rw [Real.log_pow] at hlog
    simpa [L] using hlog
  have hlogPhys0 : 0 ≤ Real.log (physicalBound C n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hphysOne)
  have hcut := cast_valuationCutoff_le_log_ratio hpPrime.one_lt hM
  have hratio :
      Real.log (physicalBound C n : ℝ) / Real.log (p : ℝ) ≤
        (2 * L n) / Real.log (W : ℝ) := by
    calc
      _ ≤ Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ) :=
        div_le_div_of_nonneg_left hlogPhys0 hlogW hlogWp
      _ ≤ (2 * L n) / Real.log (W : ℝ) :=
        div_le_div_of_nonneg_right hlogPhys hlogW.le
  calc
    (valuationCutoff p (physicalBound C n) : ℝ) / L n ≤
        (Real.log (physicalBound C n : ℝ) / Real.log (p : ℝ)) / L n :=
      div_le_div_of_nonneg_right hcut hL.le
    _ ≤ ((2 * L n) / Real.log (W : ℝ)) / L n :=
      div_le_div_of_nonneg_right hratio hL.le
    _ = 2 / Real.log (W : ℝ) := by
      field_simp [hL.ne', hlogW.ne']

/-- Uniform logarithmic size of every actual local valuation cutoff. -/
theorem eventually_valuationCutoff_div_L_le
    (C : ℝ) (W : ℕ) (hC : 1 ≤ C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W,
      (valuationCutoff p (physicalBound C n) : ℝ) / L n ≤
        2 / Real.log (W : ℝ) := by
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hCevent : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop C)
  filter_upwards [hCevent, Filter.eventually_gt_atTop 1] with n hCn hn
  intro p hpBand
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hL : 0 < L n := L_pos hn
  have hlogW : 0 < Real.log (W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  have hpPrime : p.Prime := prime_of_mem_primeBand hpBand
  have hpW : W < p := cutoff_lt_of_mem_primeBand hpBand
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hpPrime.one_lt)
  have hlogWp : Real.log (W : ℝ) ≤ Real.log (p : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast hW.le)
    exact_mod_cast hpW.le
  have hphysLower : n ≤ physicalBound C n := by
    unfold physicalBound
    apply Nat.le_floor
    exact_mod_cast (show (n : ℝ) ≤ C * (n : ℝ) by
      nlinarith [show (0 : ℝ) ≤ n by positivity])
  have hM : 0 < physicalBound C n := hnpos.trans_le hphysLower
  have hphysCast : (physicalBound C n : ℝ) ≤ C * (n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg (le_trans zero_le_one hC) (by positivity))
  have hCnSq : C * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hlogPhys : Real.log (physicalBound C n : ℝ) ≤ 2 * L n := by
    have hleSq : (physicalBound C n : ℝ) ≤ (n : ℝ) ^ 2 :=
      hphysCast.trans hCnSq
    have hlog := Real.log_le_log (by exact_mod_cast hM) hleSq
    rw [Real.log_pow] at hlog
    simpa [L] using hlog
  have hlogPhys0 : 0 ≤ Real.log (physicalBound C n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hphysLower.trans' (by omega : 1 ≤ n))
  have hcut := cast_valuationCutoff_le_log_ratio hpPrime.one_lt hM
  have hratio :
      Real.log (physicalBound C n : ℝ) / Real.log (p : ℝ) ≤
        (2 * L n) / Real.log (W : ℝ) := by
    calc
      _ ≤ Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ) :=
        div_le_div_of_nonneg_left hlogPhys0 hlogW hlogWp
      _ ≤ (2 * L n) / Real.log (W : ℝ) :=
        div_le_div_of_nonneg_right hlogPhys hlogW.le
  calc
    (valuationCutoff p (physicalBound C n) : ℝ) / L n ≤
        (Real.log (physicalBound C n : ℝ) / Real.log (p : ℝ)) / L n :=
      div_le_div_of_nonneg_right hcut hL.le
    _ ≤ ((2 * L n) / Real.log (W : ℝ)) / L n :=
      div_le_div_of_nonneg_right hratio hL.le
    _ = 2 / Real.log (W : ℝ) := by
      field_simp [hL.ne', hlogW.ne']

/-- The exponential part of every local coefficient is bounded by a single
fixed box/cutoff constant. -/
theorem eventually_cutoff_exp_le
    (B C : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 1 ≤ C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W,
      Real.exp
          (B * (valuationCutoff p (physicalBound C n) : ℝ) / L n) ≤
        Real.exp (2 * B / Real.log (W : ℝ)) := by
  filter_upwards [eventually_valuationCutoff_div_L_le C W hC hW]
    with n hcut
  intro p hp
  apply Real.exp_le_exp.mpr
  calc
    B * (valuationCutoff p (physicalBound C n) : ℝ) / L n =
        B * ((valuationCutoff p (physicalBound C n) : ℝ) / L n) := by
      ring
    _ ≤ B * (2 / Real.log (W : ℝ)) :=
      mul_le_mul_of_nonneg_left (hcut p hp) hB
    _ = 2 * B / Real.log (W : ℝ) := by ring

/-- Uniform paper-scale pointwise coefficient tail. -/
theorem eventually_coefficientTail_le
    (B C : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 1 ≤ C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ eta : ℝ,
      |eta| ≤ B → ∀ r : ℕ,
      coefficientTail p (valuationCutoff p (physicalBound C n)) r eta (L n) ≤
        ((2 * B / L n) * Real.exp (2 * B / Real.log (W : ℝ))) *
          (((r : ℝ) + 1) / (p : ℝ) ^ r) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hBLEvent : ∀ᶠ n : ℕ in atTop, B ≤ L n :=
    hLTop.eventually (eventually_ge_atTop B)
  filter_upwards [eventually_valuationCutoff_div_L_le C W hC hW,
    hBLEvent, Filter.eventually_gt_atTop 1] with n hcut hBL hn
  intro p hpBand eta heta r
  have hL : 0 < L n := L_pos hn
  have hp2 : 2 ≤ p := (prime_of_mem_primeBand hpBand).two_le
  have hcut' := hcut p hpBand
  have hexponent :
      B * (valuationCutoff p (physicalBound C n) : ℝ) / L n ≤
        2 * B / Real.log (W : ℝ) := by
    calc
      B * (valuationCutoff p (physicalBound C n) : ℝ) / L n =
          B * ((valuationCutoff p (physicalBound C n) : ℝ) / L n) := by
        ring
      _ ≤ B * (2 / Real.log (W : ℝ)) :=
        mul_le_mul_of_nonneg_left hcut' hB
      _ = 2 * B / Real.log (W : ℝ) := by ring
  have hraw := coefficientTail_le (A := valuationCutoff p (physicalBound C n))
    hp2 hB hL hBL heta (r := r)
  have hcoef : 0 ≤ 2 * B / L n := by positivity
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hcoef)
    (by positivity))

/-- Positive-endpoint version of `eventually_coefficientTail_le`. -/
theorem eventually_coefficientTail_le_of_pos
    (B C : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ eta : ℝ,
      |eta| ≤ B → ∀ r : ℕ,
      coefficientTail p (valuationCutoff p (physicalBound C n)) r eta (L n) ≤
        ((2 * B / L n) * Real.exp (2 * B / Real.log (W : ℝ))) *
          (((r : ℝ) + 1) / (p : ℝ) ^ r) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hBLEvent : ∀ᶠ n : ℕ in atTop, B ≤ L n :=
    hLTop.eventually (eventually_ge_atTop B)
  filter_upwards [eventually_valuationCutoff_div_L_le_of_pos C W hC hW,
    hBLEvent, Filter.eventually_gt_atTop 1] with n hcut hBL hn
  intro p hpBand eta heta r
  have hL : 0 < L n := L_pos hn
  have hp2 : 2 ≤ p := (prime_of_mem_primeBand hpBand).two_le
  have hcut' := hcut p hpBand
  have hexponent :
      B * (valuationCutoff p (physicalBound C n) : ℝ) / L n ≤
        2 * B / Real.log (W : ℝ) := by
    calc
      B * (valuationCutoff p (physicalBound C n) : ℝ) / L n =
          B * ((valuationCutoff p (physicalBound C n) : ℝ) / L n) := by
        ring
      _ ≤ B * (2 / Real.log (W : ℝ)) :=
        mul_le_mul_of_nonneg_left hcut' hB
      _ = 2 * B / Real.log (W : ℝ) := by ring
  have hraw := coefficientTail_le (A := valuationCutoff p (physicalBound C n))
    hp2 hB hL hBL heta (r := r)
  have hcoef : 0 ≤ 2 * B / L n := by positivity
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hcoef)
    (by positivity))

/-- Aggregate local restoration error for all higher powers. -/
theorem eventually_sum_coefficientTail_le
    (B C : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 1 ≤ C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ eta : ℝ,
      |eta| ≤ B → ∀ R : ℕ,
      (∑ r ∈ Finset.Icc 2 R,
          coefficientTail p (valuationCutoff p (physicalBound C n)) r
            eta (L n)) ≤
        8 * ((2 * B / L n) *
          Real.exp (2 * B / Real.log (W : ℝ))) / (p : ℝ) ^ 2 := by
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hBLEvent : ∀ᶠ n : ℕ in atTop, B ≤ L n :=
    hLTop.eventually (eventually_ge_atTop B)
  filter_upwards [eventually_cutoff_exp_le B C W hB hC hW,
    hBLEvent, Filter.eventually_gt_atTop 1] with n hexp hBL hn
  intro p hpBand eta heta R
  have hL : 0 < L n := L_pos hn
  have hp2 : 2 ≤ p := (prime_of_mem_primeBand hpBand).two_le
  have hraw := sum_coefficientTail_le
    (A := valuationCutoff p (physicalBound C n)) (R := R)
    hp2 hB hL hBL heta
  have hcoef : 0 ≤ 8 * (2 * B / L n) := by positivity
  calc
    _ ≤ 8 * ((2 * B / L n) *
          Real.exp
            (B * (valuationCutoff p (physicalBound C n) : ℝ) / L n)) /
        (p : ℝ) ^ 2 := hraw
    _ ≤ 8 * ((2 * B / L n) *
          Real.exp (2 * B / Real.log (W : ℝ))) / (p : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        8 * ((2 * B / L n) *
            Real.exp
              (B * (valuationCutoff p (physicalBound C n) : ℝ) / L n)) =
            (8 * (2 * B / L n)) *
              Real.exp
                (B * (valuationCutoff p (physicalBound C n) : ℝ) / L n) := by
          ring
        _ ≤ (8 * (2 * B / L n)) *
              Real.exp (2 * B / Real.log (W : ℝ)) :=
          mul_le_mul_of_nonneg_left (hexp p hpBand) hcoef
        _ = 8 * ((2 * B / L n) *
              Real.exp (2 * B / Real.log (W : ℝ))) := by
          ring

/-- Aggregate local restoration error with the exact diagonal `(2r-3)`
weight. -/
theorem eventually_sum_diagonalWeight_coefficientTail_le
    (B C : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 1 ≤ C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ eta : ℝ,
      |eta| ≤ B → ∀ R : ℕ,
      (∑ r ∈ Finset.Icc 2 R,
          ((2 * r - 3 : ℕ) : ℝ) *
            coefficientTail p (valuationCutoff p (physicalBound C n)) r
              eta (L n)) ≤
        ((2 * B / L n) *
          Real.exp (2 * B / Real.log (W : ℝ))) *
            (quadraticHalfMass / (p : ℝ) ^ 2) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hBLEvent : ∀ᶠ n : ℕ in atTop, B ≤ L n :=
    hLTop.eventually (eventually_ge_atTop B)
  filter_upwards [eventually_cutoff_exp_le B C W hB hC hW,
    hBLEvent, Filter.eventually_gt_atTop 1] with n hexp hBL hn
  intro p hpBand eta heta R
  have hL : 0 < L n := L_pos hn
  have hp2 : 2 ≤ p := (prime_of_mem_primeBand hpBand).two_le
  have hraw := sum_diagonalWeight_coefficientTail_le
    (A := valuationCutoff p (physicalBound C n)) (R := R)
    hp2 hB hL hBL heta
  have hcoef : 0 ≤ 2 * B / L n := by positivity
  have hmass : 0 ≤ quadraticHalfMass / (p : ℝ) ^ 2 := by
    exact div_nonneg quadraticHalfMass_nonneg (by positivity)
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hexp p hpBand) hcoef) hmass)

end

end Erdos390.Full.PaperValuationCutoff
