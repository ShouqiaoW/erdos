import Erdos390.Full.PaperMediumNuisanceInputReduction
import Erdos390.Full.PrimeSums

/-!
# A closed rate bound for the raw moving-prefix Taylor polynomial

The finite Taylor theorem records its normalization and remainder terms in
`rawTiltPrefixTaylorBound`.  For the asymptotic application we only need a
simple domination by the marked first moment `RFone` and by `MF * a`.
This file proves that domination with a fixed numerical constant, so the
subsequent rate argument does not have to re-expand the polynomial.
-/

open Filter Topology

namespace Erdos390.Full

open ArithmeticModel Scale PrimeSums

noncomputable section

namespace FiniteProbability

/-- On the score-small box `0 ≤ a ≤ 1`, every nonlinear normalization
term is controlled by `128 (RFone + MF*a)`.  The two supplied covariance
inputs remain additive and are not enlarged. -/
theorem rawTiltPrefixTaylorBound_le_add_128
    {a MF RFone Czero Cthird : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hMF : 0 ≤ MF) (hRFone : 0 ≤ RFone) :
    rawTiltPrefixTaylorBound a MF RFone Czero Cthird ≤
      Czero + Cthird + 128 * (RFone + MF * a) := by
  let X : ℝ := RFone + MF * a
  let CF : ℝ := RFone + MF * a
  let CG : ℝ := 2 * a
  let EF : ℝ := 2 * (RFone + CF * a + (MF + CF) * a)
  let EG : ℝ := 2 * (a + CG * a + (1 + CG) * a)
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hCF : CF = X := by rfl
  have hCG0 : 0 ≤ CG := by dsimp only [CG]; positivity
  have hCG2 : CG ≤ 2 := by dsimp only [CG]; linarith
  have hEF0 : 0 ≤ EF := by dsimp only [EF, CF]; positivity
  have hEG0 : 0 ≤ EG := by dsimp only [EG, CG]; positivity
  have hXa : X * a ≤ X := by
    exact mul_le_of_le_one_right hX ha1
  have hMFa : MF * a ≤ X := by
    dsimp only [X]
    linarith
  have hEF : EF ≤ 6 * X := by
    have hid : EF = 2 * (X + 2 * X * a) := by
      dsimp only [EF, CF, X]
      ring
    rw [hid]
    nlinarith
  have haSq : a ^ 2 ≤ a := by
    nlinarith [mul_nonneg ha (sub_nonneg.mpr ha1)]
  have hEG : EG ≤ 12 * a := by
    have hid : EG = 4 * a + 8 * a ^ 2 := by
      dsimp only [EG, CG]
      ring
    rw [hid]
    nlinarith
  have hCF_CG : CF * CG ≤ 2 * X := by
    rw [hCF]
    exact (mul_le_mul_of_nonneg_left hCG2 hX).trans_eq (by ring)
  have hMF_CF_EG : (MF + CF) * EG ≤ 24 * X := by
    have hsum0 : 0 ≤ MF + CF := by
      dsimp only [CF]
      positivity
    calc
      (MF + CF) * EG ≤ (MF + CF) * (12 * a) :=
        mul_le_mul_of_nonneg_left hEG hsum0
      _ = 12 * (MF * a + X * a) := by rw [hCF]; ring
      _ ≤ 12 * (X + X) := by gcongr
      _ = 24 * X := by ring
  have hOneCG : 1 + CG ≤ 3 := by linarith
  have hOneCG_EF : (1 + CG) * EF ≤ 18 * X := by
    have hOneCG0 : 0 ≤ 1 + CG := by linarith
    calc
      (1 + CG) * EF ≤ 3 * EF :=
        mul_le_mul_of_nonneg_right hOneCG hEF0
      _ ≤ 3 * (6 * X) := mul_le_mul_of_nonneg_left hEF (by norm_num)
      _ = 18 * X := by ring
  have hEF_EG : EF * EG ≤ 72 * X := by
    calc
      EF * EG ≤ (6 * X) * (12 * a) :=
        mul_le_mul hEF hEG hEG0 (by positivity)
      _ = 72 * (X * a) := by ring
      _ ≤ 72 * X := mul_le_mul_of_nonneg_left hXa (by norm_num)
  unfold rawTiltPrefixTaylorBound
  dsimp only
  change Czero + Cthird + CF * CG + EF +
      (MF + CF) * EG + (1 + CG) * EF + EF * EG ≤
    Czero + Cthird + 128 * X
  linarith

/-- Row-normalized form of the preceding polynomial estimate.  This is the
exact algebra used after the un-tilted and third-cumulant estimates have
been written as `epsilon/p` rows. -/
theorem rawTiltPrefixTaylorBound_le_row
    {a MF RFone Czero Cthird epsilonZero epsilonThird nonlinear : ℝ}
    {p : ℕ}
    (hp : 0 < p)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hMF : 0 ≤ MF) (hRFone : 0 ≤ RFone)
    (hzero : Czero ≤ epsilonZero / (p : ℝ))
    (hthird : Cthird ≤ epsilonThird / (p : ℝ))
    (hnonlinear : (p : ℝ) * (128 * (RFone + MF * a)) ≤ nonlinear) :
    rawTiltPrefixTaylorBound a MF RFone Czero Cthird ≤
      (epsilonZero + epsilonThird + nonlinear) / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hnonlinear' : 128 * (RFone + MF * a) ≤ nonlinear / (p : ℝ) := by
    apply (le_div_iff₀ hpR).2
    simpa only [mul_comm] using hnonlinear
  calc
    rawTiltPrefixTaylorBound a MF RFone Czero Cthird ≤
        Czero + Cthird + 128 * (RFone + MF * a) :=
      rawTiltPrefixTaylorBound_le_add_128 ha ha1 hMF hRFone
    _ ≤ epsilonZero / (p : ℝ) + epsilonThird / (p : ℝ) +
        nonlinear / (p : ℝ) :=
      add_le_add (add_le_add hzero hthird) hnonlinear'
    _ = (epsilonZero + epsilonThird + nonlinear) / (p : ℝ) := by ring

/-- Addition preserves the precise one-harmonic-loss rate required at the
moving low band. -/
theorem tendsto_sum_three_mul_logL_zero
    (epsilonZero epsilonThird nonlinear : ℕ → ℝ)
    (hzero : Tendsto (fun n ↦ epsilonZero n * Real.log (L n))
      atTop (nhds 0))
    (hthird : Tendsto (fun n ↦ epsilonThird n * Real.log (L n))
      atTop (nhds 0))
    (hnonlinear : Tendsto (fun n ↦ nonlinear n * Real.log (L n))
      atTop (nhds 0)) :
    Tendsto (fun n ↦
      (epsilonZero n + epsilonThird n + nonlinear n) * Real.log (L n))
      atTop (nhds 0) := by
  have hsum := (hzero.add hthird).add hnonlinear
  simpa only [zero_add, add_mul] using hsum

/-- A prime-uniform scalar majorant for the nonlinear part of the Taylor
row after inserting the elementary band bound
`sum_{W<p≤y} 1/p ≤ 12 log L`. -/
def rawTiltNonlinearRateMajorant (B c : ℝ) (n : ℕ) : ℝ :=
  let H := 12 * Real.log (L n)
  128 *
    ((B / L n) * (1 / c) *
        (4 * H + PrimePowerTaylorLedger.positivePrimePowerLcmConstant) +
      (2 / c) * ((B / L n) * ((2 / c) * H)))

/-- The literal nonlinear Taylor row, multiplied by its row prime, is
eventually bounded by `rawTiltNonlinearRateMajorant`.  The assertion is
uniform in every positive prime and therefore in the entire moving band. -/
theorem eventually_rawTiltNonlinear_row_le
    (B c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℕ, 0 < p →
      let H := bandReciprocalSum n W
      let a := (B / L n) * ((2 / c) * H)
      let MF := 2 / (c * (p : ℝ))
      let RFone := (B / L n) * (1 / c) *
        ((4 * H + PrimePowerTaylorLedger.positivePrimePowerLcmConstant) /
          (p : ℝ))
      (p : ℝ) * (128 * (RFone + MF * a)) ≤
        rawTiltNonlinearRateMajorant B c n := by
  filter_upwards [eventually_bandReciprocalSum_le_logL W,
    Filter.eventually_gt_atTop 2] with n hband hn
  intro p hp
  dsimp only
  have hL : 0 < L n := L_pos (by omega)
  have hlog : 0 ≤ Real.log (L n) := by
    apply Real.log_nonneg
    have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 3 ≤ n by omega)
    have hnCast : (Real.exp 1 : ℝ) ≤ (n : ℝ) :=
      Real.exp_one_lt_three.le.trans h3
    exact (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < n)).2
      (by simpa only [L] using hnCast)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hH0 : 0 ≤ bandReciprocalSum n W := by
    unfold bandReciprocalSum
    positivity
  have hHstar0 : 0 ≤ 12 * Real.log (L n) := by positivity
  have hcoef1 : 0 ≤ (B / L n) * (1 / c) := by positivity
  have hcoef2 : 0 ≤ (2 / c) * (B / L n) * (2 / c) := by positivity
  have heq :
      (p : ℝ) *
          (128 *
            ((B / L n) * (1 / c) *
                ((4 * bandReciprocalSum n W +
                    PrimePowerTaylorLedger.positivePrimePowerLcmConstant) /
                  (p : ℝ)) +
              (2 / (c * (p : ℝ))) *
                ((B / L n) *
                  ((2 / c) * bandReciprocalSum n W)))) =
        128 *
          ((B / L n) * (1 / c) *
              (4 * bandReciprocalSum n W +
                PrimePowerTaylorLedger.positivePrimePowerLcmConstant) +
            (2 / c) * ((B / L n) *
              ((2 / c) * bandReciprocalSum n W))) := by
    field_simp [hpR.ne', hc.ne', hL.ne']
  rw [heq]
  unfold rawTiltNonlinearRateMajorant
  dsimp only
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hcoef1
    gcongr
  · calc
      (2 / c) *
          ((B / L n) * ((2 / c) * bandReciprocalSum n W)) =
          ((2 / c) * (B / L n) * (2 / c)) *
            bandReciprocalSum n W := by ring
      _ ≤ ((2 / c) * (B / L n) * (2 / c)) *
          (12 * Real.log (L n)) :=
        mul_le_mul_of_nonneg_left hband hcoef2
      _ = (2 / c) *
          ((B / L n) * ((2 / c) * (12 * Real.log (L n)))) := by ring

/-- The nonlinear Taylor row survives the additional moving-low harmonic
loss. -/
theorem tendsto_rawTiltNonlinearRateMajorant_mul_logL_zero
    (B c : ℝ) :
    Tendsto (fun n : ℕ ↦
      rawTiltNonlinearRateMajorant B c n * Real.log (L n))
      atTop (nhds 0) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto
      (fun n : ℕ ↦ Real.log (L n) ^ 2 / L n) atTop (nhds 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hone : Tendsto
      (fun n : ℕ ↦ Real.log (L n) / L n) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  let A₁ : ℝ := 128 * (48 * B / c + 48 * B / c ^ 2)
  let A₂ : ℝ := 128 *
    (B / c * PrimePowerTaylorLedger.positivePrimePowerLcmConstant)
  have hlimit : Tendsto (fun n : ℕ ↦
      A₁ * (Real.log (L n) ^ 2 / L n) +
        A₂ * (Real.log (L n) / L n)) atTop (nhds 0) := by
    simpa only [mul_zero, zero_add] using
      (tendsto_const_nhds.mul hsq).add (tendsto_const_nhds.mul hone)
  apply hlimit.congr'
  filter_upwards [Filter.eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  unfold rawTiltNonlinearRateMajorant
  dsimp only
  dsimp only [A₁, A₂]
  ring

end FiniteProbability

end

end Erdos390.Full
