import Erdos390.Full.FiniteProbabilityFixedBoxTaylor
import Erdos390.Full.PaperRawTiltTaylorRate

/-!
# Closed raw-prefix Taylor rate for an arbitrary fixed score box

This is the quantitative replacement for the former unit-score-box
restriction.  The domination constant may depend on the fixed score bound
`K`, but it is independent of `n`, the moving prime, and the prime cutoff.
-/

open Filter Topology

namespace Erdos390.Full

open ArithmeticModel Scale PrimeSums

noncomputable section

namespace FiniteProbability

/-- Fixed scalar multiplying the marked first-moment ledger. -/
def fixedBoxTaylorDominationConstant (K : ℝ) : ℝ :=
  let D := fixedBoxQuadraticConstant K
  let A := 2 * D * (3 * K + 1)
  let G := 2 * D * (4 * K + 2)
  2 + 4 * A + 2 * G + A * G

theorem fixedBoxTaylorDominationConstant_nonneg
    {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ fixedBoxTaylorDominationConstant K := by
  unfold fixedBoxTaylorDominationConstant
  dsimp only
  have hD : 0 ≤ fixedBoxQuadraticConstant K :=
    zero_le_one.trans (one_le_fixedBoxQuadraticConstant hK)
  positivity

/-- Every nonlinear term in the arbitrary-box Taylor polynomial is bounded
by one fixed multiple of `RFone + MF*a`. -/
theorem rawTiltPrefixTaylorBoundFixedBox_le
    {K a MF RFone Czero Cthird : ℝ}
    (hK : 0 ≤ K) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hMF : 0 ≤ MF) (hRFone : 0 ≤ RFone) :
    rawTiltPrefixTaylorBoundFixedBox K a MF RFone Czero Cthird ≤
      Czero + Cthird +
        fixedBoxTaylorDominationConstant K * (RFone + MF * a) := by
  let D := fixedBoxQuadraticConstant K
  let X := RFone + MF * a
  let CF := RFone + MF * a
  let CG := 2 * a
  let Rone := K * a
  let RF := K * RFone
  let EF := 2 * D * (RF + CF * a + (MF + CF) * Rone)
  let EG := 2 * D * (Rone + CG * a + (1 + CG) * Rone)
  let A := 2 * D * (3 * K + 1)
  let Gc := 2 * D * (4 * K + 2)
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact zero_le_one.trans (one_le_fixedBoxQuadraticConstant hK)
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hCF : CF = X := rfl
  have hCG0 : 0 ≤ CG := by dsimp only [CG]; positivity
  have hCG2 : CG ≤ 2 := by dsimp only [CG]; linarith
  have hRone0 : 0 ≤ Rone := by dsimp only [Rone]; positivity
  have hRF0 : 0 ≤ RF := by dsimp only [RF]; positivity
  have hEF0 : 0 ≤ EF := by dsimp only [EF]; positivity
  have hEG0 : 0 ≤ EG := by dsimp only [EG]; positivity
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hGc0 : 0 ≤ Gc := by dsimp only [Gc]; positivity
  have hXa : X * a ≤ X := mul_le_of_le_one_right hX ha1
  have hMFa : MF * a ≤ X := by dsimp only [X]; linarith
  have hRFoneX : RFone ≤ X := by
    dsimp only [X]
    linarith [mul_nonneg hMF ha]
  have hKRF : RF ≤ K * X := by
    dsimp only [RF]
    exact mul_le_mul_of_nonneg_left hRFoneX hK
  have hsumKa : (MF + X) * (K * a) ≤ 2 * K * X := by
    calc
      (MF + X) * (K * a) = K * (MF * a + X * a) := by ring
      _ ≤ K * (X + X) := by gcongr
      _ = 2 * K * X := by ring
  have hEF : EF ≤ A * X := by
    have hinside : RF + CF * a + (MF + CF) * Rone ≤
        (3 * K + 1) * X := by
      rw [hCF]
      dsimp only [Rone]
      calc
        RF + X * a + (MF + X) * (K * a) ≤
            K * X + X + 2 * K * X := by linarith
        _ = (3 * K + 1) * X := by ring
    calc
      EF = 2 * D * (RF + CF * a + (MF + CF) * Rone) := rfl
      _ ≤ 2 * D * ((3 * K + 1) * X) := by gcongr
      _ = A * X := by dsimp only [A]; ring
  have haSq : a ^ 2 ≤ a := by
    nlinarith [mul_nonneg ha (sub_nonneg.mpr ha1)]
  have hEG : EG ≤ Gc * a := by
    have hinside : Rone + CG * a + (1 + CG) * Rone ≤
        (4 * K + 2) * a := by
      dsimp only [Rone, CG]
      have hKa : 0 ≤ K * a := mul_nonneg hK ha
      have htwoa : 0 ≤ 2 * a := by positivity
      calc
        K * a + (2 * a) * a + (1 + 2 * a) * (K * a) ≤
            K * a + 2 * a + 3 * (K * a) := by
          have hlast : (1 + 2 * a) * (K * a) ≤ 3 * (K * a) := by
            exact mul_le_mul_of_nonneg_right (by linarith) hKa
          nlinarith
        _ = (4 * K + 2) * a := by ring
    calc
      EG = 2 * D * (Rone + CG * a + (1 + CG) * Rone) := rfl
      _ ≤ 2 * D * ((4 * K + 2) * a) := by gcongr
      _ = Gc * a := by dsimp only [Gc]; ring
  have hCF_CG : CF * CG ≤ 2 * X := by
    rw [hCF]
    exact (mul_le_mul_of_nonneg_left hCG2 hX).trans_eq (by ring)
  have hMF_CF_EG : (MF + CF) * EG ≤ 2 * Gc * X := by
    rw [hCF]
    have hsum0 : 0 ≤ MF + X := add_nonneg hMF hX
    calc
      (MF + X) * EG ≤ (MF + X) * (Gc * a) :=
        mul_le_mul_of_nonneg_left hEG hsum0
      _ = Gc * (MF * a + X * a) := by ring
      _ ≤ Gc * (X + X) := by gcongr
      _ = 2 * Gc * X := by ring
  have hOneCG : 1 + CG ≤ 3 := by linarith
  have hOneCG_EF : (1 + CG) * EF ≤ 3 * A * X := by
    have hOneCG0 : 0 ≤ 1 + CG := by positivity
    calc
      (1 + CG) * EF ≤ 3 * EF :=
        mul_le_mul_of_nonneg_right hOneCG hEF0
      _ ≤ 3 * (A * X) := mul_le_mul_of_nonneg_left hEF (by norm_num)
      _ = 3 * A * X := by ring
  have hEF_EG : EF * EG ≤ A * Gc * X := by
    calc
      EF * EG ≤ (A * X) * (Gc * a) :=
        mul_le_mul hEF hEG hEG0 (mul_nonneg hA0 hX)
      _ = A * Gc * (X * a) := by ring
      _ ≤ A * Gc * X :=
        mul_le_mul_of_nonneg_left hXa (mul_nonneg hA0 hGc0)
  unfold rawTiltPrefixTaylorBoundFixedBox
  dsimp only
  change Czero + Cthird + CF * CG + EF +
      (MF + CF) * EG + (1 + CG) * EF + EF * EG ≤
    Czero + Cthird + fixedBoxTaylorDominationConstant K * X
  unfold fixedBoxTaylorDominationConstant
  dsimp only
  change _ ≤ Czero + Cthird + (2 + 4 * A + 2 * Gc + A * Gc) * X
  nlinarith

/-- Row-normalized version of the fixed-box polynomial domination. -/
theorem rawTiltPrefixTaylorBoundFixedBox_le_row
    {K a MF RFone Czero Cthird epsilonZero epsilonThird nonlinear : ℝ}
    {p : ℕ}
    (hp : 0 < p) (hK : 0 ≤ K) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hMF : 0 ≤ MF) (hRFone : 0 ≤ RFone)
    (hzero : Czero ≤ epsilonZero / (p : ℝ))
    (hthird : Cthird ≤ epsilonThird / (p : ℝ))
    (hnonlinear : (p : ℝ) *
      (fixedBoxTaylorDominationConstant K * (RFone + MF * a)) ≤ nonlinear) :
    rawTiltPrefixTaylorBoundFixedBox K a MF RFone Czero Cthird ≤
      (epsilonZero + epsilonThird + nonlinear) / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hnonlinear' :
      fixedBoxTaylorDominationConstant K * (RFone + MF * a) ≤
        nonlinear / (p : ℝ) := by
    apply (le_div_iff₀ hpR).2
    simpa only [mul_comm] using hnonlinear
  calc
    rawTiltPrefixTaylorBoundFixedBox K a MF RFone Czero Cthird ≤
        Czero + Cthird +
          fixedBoxTaylorDominationConstant K * (RFone + MF * a) :=
      rawTiltPrefixTaylorBoundFixedBox_le hK ha ha1 hMF hRFone
    _ ≤ epsilonZero / (p : ℝ) + epsilonThird / (p : ℝ) +
        nonlinear / (p : ℝ) :=
      add_le_add (add_le_add hzero hthird) hnonlinear'
    _ = (epsilonZero + epsilonThird + nonlinear) / (p : ℝ) := by ring

/-- Fixed-box nonlinear majorant obtained by rescaling the already proved
unit-box scalar ledger. -/
def rawTiltFixedBoxNonlinearRateMajorant
    (K B c : ℝ) (n : ℕ) : ℝ :=
  (fixedBoxTaylorDominationConstant K / 128) *
    rawTiltNonlinearRateMajorant B c n

theorem eventually_rawTiltFixedBoxNonlinear_row_le
    (K B c : ℝ) (W : ℕ) (hK : 0 ≤ K) (hB : 0 ≤ B) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℕ, 0 < p →
      let H := bandReciprocalSum n W
      let a := (B / L n) * ((2 / c) * H)
      let MF := 2 / (c * (p : ℝ))
      let RFone := (B / L n) * (1 / c) *
        ((4 * H + PrimePowerTaylorLedger.positivePrimePowerLcmConstant) /
          (p : ℝ))
      (p : ℝ) *
          (fixedBoxTaylorDominationConstant K * (RFone + MF * a)) ≤
        rawTiltFixedBoxNonlinearRateMajorant K B c n := by
  filter_upwards [eventually_rawTiltNonlinear_row_le B c W hB hc] with n hn
  intro p hp
  dsimp only
  have hC : 0 ≤ fixedBoxTaylorDominationConstant K :=
    fixedBoxTaylorDominationConstant_nonneg hK
  have hscale : 0 ≤ fixedBoxTaylorDominationConstant K / 128 := by positivity
  have hraw := hn p hp
  dsimp only at hraw
  calc
    (p : ℝ) * (fixedBoxTaylorDominationConstant K *
        ((B / L n) * (1 / c) *
            ((4 * bandReciprocalSum n W +
                PrimePowerTaylorLedger.positivePrimePowerLcmConstant) /
              (p : ℝ)) +
          (2 / (c * (p : ℝ))) *
            ((B / L n) * ((2 / c) * bandReciprocalSum n W)))) =
      (fixedBoxTaylorDominationConstant K / 128) *
        ((p : ℝ) * (128 *
          ((B / L n) * (1 / c) *
              ((4 * bandReciprocalSum n W +
                  PrimePowerTaylorLedger.positivePrimePowerLcmConstant) /
                (p : ℝ)) +
            (2 / (c * (p : ℝ))) *
              ((B / L n) * ((2 / c) * bandReciprocalSum n W))))) := by ring
    _ ≤ (fixedBoxTaylorDominationConstant K / 128) *
        rawTiltNonlinearRateMajorant B c n :=
      mul_le_mul_of_nonneg_left hraw hscale
    _ = rawTiltFixedBoxNonlinearRateMajorant K B c n := rfl

theorem tendsto_rawTiltFixedBoxNonlinearRateMajorant_mul_logL_zero
    (K B c : ℝ) :
    Tendsto (fun n : ℕ ↦
      rawTiltFixedBoxNonlinearRateMajorant K B c n * Real.log (L n))
      atTop (nhds 0) := by
  have hraw := tendsto_rawTiltNonlinearRateMajorant_mul_logL_zero B c
  have hconst : Tendsto
      (fun _n : ℕ ↦ fixedBoxTaylorDominationConstant K / 128)
      atTop (nhds (fixedBoxTaylorDominationConstant K / 128)) :=
    tendsto_const_nhds
  have hmul := hconst.mul hraw
  simpa only [rawTiltFixedBoxNonlinearRateMajorant, mul_zero, mul_assoc]
    using hmul

end FiniteProbability

end

end Erdos390.Full
