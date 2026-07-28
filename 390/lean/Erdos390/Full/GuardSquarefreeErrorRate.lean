import Erdos390.Full.GuardDeletionSquarefreeProfiles
import Erdos390.Full.PaperGuardDeletionRows

/-!
# Vanishing rate of the squarefree guard error

The reciprocal guard conversion costs `y²`.  Since the concrete ledger has
`O(y log n)` guards and each raw cell has positive linear density, the final
cost is `O((log n)/n^(1/3))`; it still vanishes after multiplication by
`log log n`.  This file proves that rate with the literal scales.
-/

open Filter Topology

namespace Erdos390.Full.GuardSquarefreeErrorRate

open ArithmeticModel Scale PaperGuardCensus
open GuardDeletionSquarefreeProfiles

noncomputable section

private theorem tendsto_inv_nat_rpow_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ 1 / (n : ℝ) ^ a) atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (0 : ℝ) / x ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (0 : ℝ) ha).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  simp only [Function.comp_apply, Real.rpow_zero]

private theorem tendsto_L_div_nat_rpow_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ L n / (n : ℝ) ^ a) atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (1 : ℝ) / x ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ) ha).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  simp only [Function.comp_apply, L, Real.rpow_one]

private theorem tendsto_L_sq_div_nat_rpow_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ L n ^ 2 / (n : ℝ) ^ a) atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (2 : ℝ) / x ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) ha).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  change Tendsto
    (fun n : ℕ ↦ Real.log (n : ℝ) ^ (2 : ℝ) / (n : ℝ) ^ a)
      atTop (nhds 0) at hnat
  simpa [L, Real.rpow_natCast] using hnat

private theorem y_cube_div_nat_eq_inv_rpow {n : ℕ} (hn : 0 < n) :
    y n ^ 3 / (n : ℝ) = 1 / (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpow :
      ((n : ℝ) ^ (2 / 9 : ℝ)) ^ 3 *
          (n : ℝ) ^ (1 / 3 : ℝ) = (n : ℝ) := by
    calc
      ((n : ℝ) ^ (2 / 9 : ℝ)) ^ 3 *
          (n : ℝ) ^ (1 / 3 : ℝ) =
        (((n : ℝ) ^ (2 / 9 : ℝ) *
            (n : ℝ) ^ (2 / 9 : ℝ)) *
          ((n : ℝ) ^ (2 / 9 : ℝ) *
            (n : ℝ) ^ (1 / 3 : ℝ))) := by ring
      _ = (n : ℝ) ^ ((2 / 9 : ℝ) + 2 / 9) *
          (n : ℝ) ^ ((2 / 9 : ℝ) + 1 / 3) := by
        rw [Real.rpow_add hnR, Real.rpow_add hnR]
      _ = (n : ℝ) ^ (((2 / 9 : ℝ) + 2 / 9) +
          ((2 / 9 : ℝ) + 1 / 3)) := by
        rw [← Real.rpow_add hnR]
      _ = (n : ℝ) := by norm_num [Real.rpow_one]
  unfold y
  field_simp [(Real.rpow_pos_of_pos hnR (1 / 3 : ℝ)).ne', hnR.ne']
  nlinarith

private theorem census_mul_y_sq_expansion
    (Cprom Cbank n : ℕ) (hn : 0 < n) :
    censusRatioMajorant Cprom Cbank n * y n ^ 2 =
      (Cprom : ℝ) * (1 / (n : ℝ) ^ (1 / 3 : ℝ)) +
        3 * (Cbank : ℝ) *
          (L n / (n : ℝ) ^ (1 / 3 : ℝ) +
            2 * (1 / (n : ℝ) ^ (1 / 3 : ℝ))) := by
  rw [censusRatioMajorant]
  rw [show
    (((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) * y n /
        (n : ℝ)) * y n ^ 2 =
      ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) *
        (y n ^ 3 / (n : ℝ)) by ring]
  rw [y_cube_div_nat_eq_inv_rpow hn]
  ring

/-- The concrete census still vanishes after the reciprocal `y²` conversion. -/
theorem tendsto_censusRatioMajorant_mul_y_sq_zero (Cprom Cbank : ℕ) :
    Tendsto (fun n : ℕ ↦ censusRatioMajorant Cprom Cbank n * y n ^ 2)
      atTop (nhds 0) := by
  let a : ℝ := 1 / 3
  have ha : 0 < a := by norm_num [a]
  have hzero := tendsto_inv_nat_rpow_zero a ha
  have hlog := tendsto_L_div_nat_rpow_zero a ha
  have hsum : Tendsto
      (fun n : ℕ ↦
        (Cprom : ℝ) * (1 / (n : ℝ) ^ a) +
          3 * (Cbank : ℝ) *
            (L n / (n : ℝ) ^ a + 2 * (1 / (n : ℝ) ^ a)))
      atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using
      (hzero.const_mul (Cprom : ℝ)).add
        ((hlog.add (hzero.const_mul 2)).const_mul (3 * (Cbank : ℝ)))
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simpa only [a] using (census_mul_y_sq_expansion Cprom Cbank n hn).symm

/-- The unweighted census ratio itself tends to zero.  This follows from
the stronger `y²`-weighted estimate because `1 ≤ y²` eventually. -/
theorem tendsto_censusRatioMajorant_zero (Cprom Cbank : ℕ) :
    Tendsto (censusRatioMajorant Cprom Cbank) atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_
    (tendsto_censusRatioMajorant_mul_y_sq_zero Cprom Cbank)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    unfold censusRatioMajorant
    have hL : 0 ≤ L n := Real.log_nonneg (by exact_mod_cast hn)
    have hcoef : 0 ≤
        (Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2) := by positivity
    exact div_nonneg
      (mul_nonneg hcoef (Scale.y_pos hn).le) (by positivity)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hyOne : (1 : ℝ) ≤ y n := by
      unfold y
      exact Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
    have hySq : (1 : ℝ) ≤ y n ^ 2 := by nlinarith
    have hcensus0 : 0 ≤ censusRatioMajorant Cprom Cbank n := by
      unfold censusRatioMajorant
      have hL : 0 ≤ L n := Real.log_nonneg (by exact_mod_cast hn)
      have hcoef : 0 ≤
          (Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2) := by positivity
      exact div_nonneg
        (mul_nonneg hcoef (Scale.y_pos hn).le) (by positivity)
    calc
      censusRatioMajorant Cprom Cbank n =
          censusRatioMajorant Cprom Cbank n * 1 := by ring
      _ ≤ censusRatioMajorant Cprom Cbank n * y n ^ 2 :=
        mul_le_mul_of_nonneg_left hySq hcensus0

/-- The same error survives the extra moving-low harmonic loss
`log (L n)`. -/
theorem tendsto_censusRatioMajorant_mul_y_sq_mul_logL_zero
    (Cprom Cbank : ℕ) :
    Tendsto (fun n : ℕ ↦
      censusRatioMajorant Cprom Cbank n * y n ^ 2 * Real.log (L n))
      atTop (nhds 0) := by
  let a : ℝ := 1 / 3
  have ha : 0 < a := by norm_num [a]
  have hlog := tendsto_L_div_nat_rpow_zero a ha
  have hlogSq := tendsto_L_sq_div_nat_rpow_zero a ha
  let upper : ℕ → ℝ := fun n ↦
    (Cprom : ℝ) * (L n / (n : ℝ) ^ a) +
      3 * (Cbank : ℝ) *
        (L n ^ 2 / (n : ℝ) ^ a +
          2 * (L n / (n : ℝ) ^ a))
  have hupper : Tendsto upper atTop (nhds 0) := by
    dsimp only [upper]
    simpa only [mul_zero, add_zero] using
      (hlog.const_mul (Cprom : ℝ)).add
        ((hlogSq.add (hlog.const_mul 2)).const_mul (3 * (Cbank : ℝ)))
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLge : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ L n :=
    hLTop.eventually (eventually_ge_atTop 1)
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_gt_atTop 0, hLge] with n hn hLn
    rw [census_mul_y_sq_expansion Cprom Cbank n hn]
    exact mul_nonneg (by positivity) (Real.log_nonneg hLn)
  · filter_upwards [eventually_gt_atTop 0, hLge] with n hn hLn
    have hlogL : Real.log (L n) ≤ L n :=
      (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hLn)).trans (by linarith)
    rw [census_mul_y_sq_expansion Cprom Cbank n hn]
    dsimp only [upper, a]
    have hbase0 : 0 ≤
        (Cprom : ℝ) * (1 / (n : ℝ) ^ (1 / 3 : ℝ)) +
          3 * (Cbank : ℝ) *
            (L n / (n : ℝ) ^ (1 / 3 : ℝ) +
              2 * (1 / (n : ℝ) ^ (1 / 3 : ℝ))) := by
      positivity
    calc
      ((Cprom : ℝ) * (1 / (n : ℝ) ^ (1 / 3 : ℝ)) +
            3 * (Cbank : ℝ) *
              (L n / (n : ℝ) ^ (1 / 3 : ℝ) +
                2 * (1 / (n : ℝ) ^ (1 / 3 : ℝ)))) * Real.log (L n) ≤
          ((Cprom : ℝ) * (1 / (n : ℝ) ^ (1 / 3 : ℝ)) +
            3 * (Cbank : ℝ) *
              (L n / (n : ℝ) ^ (1 / 3 : ℝ) +
                2 * (1 / (n : ℝ) ^ (1 / 3 : ℝ)))) * L n :=
        mul_le_mul_of_nonneg_left hlogL hbase0
      _ = (Cprom : ℝ) * (L n / (n : ℝ) ^ (1 / 3 : ℝ)) +
          3 * (Cbank : ℝ) *
            (L n ^ 2 / (n : ℝ) ^ (1 / 3 : ℝ) +
              2 * (L n / (n : ℝ) ^ (1 / 3 : ℝ))) := by ring

/-- Multiplication by fixed cell/box constants preserves both vanishing
statements. -/
theorem tendsto_guardRateMajorant_zero
    (Cprom Cbank : ℕ) (constant : ℝ) :
    Tendsto (fun n : ℕ ↦ constant *
      (censusRatioMajorant Cprom Cbank n * y n ^ 2))
      atTop (nhds 0) := by
  simpa only [mul_zero] using
    (tendsto_const_nhds.mul
      (tendsto_censusRatioMajorant_mul_y_sq_zero Cprom Cbank))

theorem tendsto_guardRateMajorant_mul_logL_zero
    (Cprom Cbank : ℕ) (constant : ℝ) :
    Tendsto (fun n : ℕ ↦ constant *
      (censusRatioMajorant Cprom Cbank n * y n ^ 2) * Real.log (L n))
      atTop (nhds 0) := by
  have hc : Tendsto (fun _n : ℕ ↦ constant) atTop (nhds constant) :=
    tendsto_const_nhds
  have h := hc.mul
    (tendsto_censusRatioMajorant_mul_y_sq_mul_logL_zero Cprom Cbank)
  simpa only [mul_zero, mul_assoc] using h

/-- The literal squarefree deletion error of a concrete raw cell is bounded
by the preceding universal vanishing rate. -/
theorem guardSquarefreeError_rawCell_le_rateMajorant
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    {n Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (c : PaperBridgeFit.Cell Head) (hn : 1 ≤ n)
    (hdensity :
      PaperScaleMarkedCell.paperCellDensity (P c.1)
          (I.lower c.2) (I.upper c.2) * (n : ℝ) / 2 ≤
        (rawCell P I n c).card)
    (K : ℝ) :
    guardSquarefreeError (rawCell P I n c) G.guards K n ≤
      (4 * Real.exp (2 * K) /
          PaperScaleMarkedCell.paperCellDensity (P c.1)
            (I.lower c.2) (I.upper c.2)) *
        (censusRatioMajorant Cprom Cbank n * y n ^ 2) := by
  let density := PaperScaleMarkedCell.paperCellDensity (P c.1)
    (I.lower c.2) (I.upper c.2)
  have hdensityPos : 0 < density :=
    PaperScaleMarkedCell.paperCellDensity_pos (P c.1) (I.lower_lt_upper c.2)
  have hratio := guard_card_div_rawCell_le P I G c hn hdensity
  have hratio0 : 0 ≤ (G.guards.card : ℝ) /
      ((rawCell P I n c).card : ℝ) := by positivity
  have hcensus0 : 0 ≤ censusRatioMajorant Cprom Cbank n := by
    unfold censusRatioMajorant
    have hL : 0 ≤ L n := Real.log_nonneg (by exact_mod_cast hn)
    have hnR : 0 ≤ (n : ℝ) := by positivity
    have hcoef : 0 ≤
        (Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2) := by positivity
    exact div_nonneg (mul_nonneg hcoef (Scale.y_pos (by omega : 0 < n)).le) hnR
  have hmajor0 : 0 ≤
      2 * censusRatioMajorant Cprom Cbank n / density :=
    div_nonneg (mul_nonneg (by norm_num) hcensus0) hdensityPos.le
  have hyNat : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (Scale.y_pos (by omega : 0 < n)).le
  have hyNat0 : 0 ≤ (yNat n : ℝ) := by positivity
  have hy0 : 0 ≤ y n := (Scale.y_pos (by omega : 0 < n)).le
  have hySq : (yNat n : ℝ) ^ 2 ≤ y n ^ 2 :=
    (sq_le_sq₀ hyNat0 hy0).2 hyNat
  unfold guardSquarefreeError
  rw [show 2 * (Real.exp (2 * K) * (G.guards.card : ℝ) /
        ((rawCell P I n c).card : ℝ)) * (yNat n : ℝ) ^ 2 =
      2 * Real.exp (2 * K) *
        ((G.guards.card : ℝ) / ((rawCell P I n c).card : ℝ)) *
          (yNat n : ℝ) ^ 2 by ring]
  calc
    2 * Real.exp (2 * K) *
          ((G.guards.card : ℝ) / ((rawCell P I n c).card : ℝ)) *
          (yNat n : ℝ) ^ 2 ≤
        2 * Real.exp (2 * K) *
          (2 * censusRatioMajorant Cprom Cbank n / density) *
          (yNat n : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio
          (mul_nonneg (by norm_num) (Real.exp_pos _).le))
        (sq_nonneg _)
    _ ≤ 2 * Real.exp (2 * K) *
          (2 * censusRatioMajorant Cprom Cbank n / density) * y n ^ 2 :=
      mul_le_mul_of_nonneg_left hySq
        (mul_nonneg
          (mul_nonneg (by norm_num) (Real.exp_pos _).le) hmajor0)
    _ = (4 * Real.exp (2 * K) / density) *
          (censusRatioMajorant Cprom Cbank n * y n ^ 2) := by ring
    _ = _ := by rfl

/-- For a fixed score box, the concrete ledger has exponentially tilted
mass at most one half in every raw head/physical cell eventually. -/
theorem eventually_exp_two_mul_guardRatio_rawCell_le_half
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ c : PaperBridgeFit.Cell Head,
      Real.exp (2 * K) * ((G n).guards.card : ℝ) /
        ((rawCell P I n c).card : ℝ) ≤ (1 : ℝ) / 2 := by
  have hdensity := eventually_rawCell_density P I
  have hsmall : ∀ᶠ n : ℕ in atTop, ∀ c : PaperBridgeFit.Cell Head,
      (2 * Real.exp (2 * K) /
          PaperScaleMarkedCell.paperCellDensity (P c.1)
            (I.lower c.2) (I.upper c.2)) *
        censusRatioMajorant Cprom Cbank n ≤ (1 : ℝ) / 2 := by
    rw [Filter.eventually_all]
    intro c
    let constant := 2 * Real.exp (2 * K) /
      PaperScaleMarkedCell.paperCellDensity (P c.1)
        (I.lower c.2) (I.upper c.2)
    have hconst : Tendsto (fun _n : ℕ ↦ constant) atTop (nhds constant) :=
      tendsto_const_nhds
    have ht := hconst.mul
      (tendsto_censusRatioMajorant_zero Cprom Cbank)
    have ht0 : Tendsto (fun n : ℕ ↦
        (2 * Real.exp (2 * K) /
          PaperScaleMarkedCell.paperCellDensity (P c.1)
            (I.lower c.2) (I.upper c.2)) *
          censusRatioMajorant Cprom Cbank n) atTop (nhds 0) := by
      simpa only [constant, mul_zero] using ht
    exact ht0.eventually (eventually_le_nhds (by norm_num))
  filter_upwards [hdensity, hsmall, eventually_gt_atTop 0] with
      n hdens hsmalln hn c
  have hratio := guard_card_div_rawCell_le P I (G n) c
    (by omega : 1 ≤ n) (hdens c)
  have hexp0 : 0 ≤ Real.exp (2 * K) := (Real.exp_pos _).le
  calc
    Real.exp (2 * K) * ((G n).guards.card : ℝ) /
        ((rawCell P I n c).card : ℝ) =
      Real.exp (2 * K) *
        (((G n).guards.card : ℝ) / ((rawCell P I n c).card : ℝ)) := by ring
    _ ≤ Real.exp (2 * K) *
        (2 * censusRatioMajorant Cprom Cbank n /
          PaperScaleMarkedCell.paperCellDensity (P c.1)
            (I.lower c.2) (I.upper c.2)) :=
      mul_le_mul_of_nonneg_left hratio hexp0
    _ = (2 * Real.exp (2 * K) /
          PaperScaleMarkedCell.paperCellDensity (P c.1)
            (I.lower c.2) (I.upper c.2)) *
        censusRatioMajorant Cprom Cbank n := by ring
    _ ≤ (1 : ℝ) / 2 := hsmalln c

/-- After deleting the concrete guard ledger, every fixed head/physical cell
still retains a fixed positive fraction of its proved raw density.  The
constant `1/4` is uniform over the finite family of cells and is stated at
the literal finite-`n` cardinality level. -/
theorem eventually_guarded_rawCell_density
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank) :
    ∀ᶠ n : ℕ in atTop, ∀ c : PaperBridgeFit.Cell Head,
      PaperScaleMarkedCell.paperCellDensity (P c.1)
          (I.lower c.2) (I.upper c.2) * (n : ℝ) / 4 ≤
        ((rawCell P I n c \ (G n).guards).card : ℝ) := by
  have hdensity := eventually_rawCell_density P I
  have hguardRatio :=
    eventually_exp_two_mul_guardRatio_rawCell_le_half
      P I Cprom Cbank G 0
  filter_upwards [hdensity, hguardRatio, eventually_gt_atTop 0] with
      n hdens hratio hn c
  let density := PaperScaleMarkedCell.paperCellDensity (P c.1)
    (I.lower c.2) (I.upper c.2)
  let S := rawCell P I n c
  let R := S \ (G n).guards
  have hdensityPos : 0 < density := by
    exact PaperScaleMarkedCell.paperCellDensity_pos
      (P c.1) (I.lower_lt_upper c.2)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hSpos : (0 : ℝ) < (S.card : ℝ) := by
    have hmain : 0 < density * (n : ℝ) / 2 := by positivity
    exact hmain.trans_le (by simpa only [density, S] using hdens c)
  have hratio' : ((G n).guards.card : ℝ) / (S.card : ℝ) ≤
      (1 : ℝ) / 2 := by
    have hc := hratio c
    norm_num at hc
    simpa only [S] using hc
  have hguard : ((G n).guards.card : ℝ) ≤ (S.card : ℝ) / 2 := by
    have := (div_le_iff₀ hSpos).mp hratio'
    nlinarith
  have hcardNat : S.card ≤ R.card + (G n).guards.card := by
    simpa only [R] using
      (Finset.card_le_card_sdiff_add_card
        (s := S) (t := (G n).guards))
  have hcardReal : (S.card : ℝ) ≤ (R.card : ℝ) +
      ((G n).guards.card : ℝ) := by exact_mod_cast hcardNat
  have hraw : density * (n : ℝ) / 2 ≤ (S.card : ℝ) := by
    simpa only [density, S] using hdens c
  have : density * (n : ℝ) / 4 ≤ (R.card : ℝ) := by
    nlinarith
  simpa only [density, S, R] using this

/-- Endpoint-normalized form of `eventually_guarded_rawCell_density`.  Each
fixed cell gets the explicit positive density
`paperCellDensity/(4*upper)`; no minimum over a varying family is used. -/
theorem eventually_guarded_rawCell_endpoint_density
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank) :
    ∀ᶠ n : ℕ in atTop, ∀ c : PaperBridgeFit.Cell Head,
      let rho := PaperScaleMarkedCell.paperCellDensity (P c.1)
        (I.lower c.2) (I.upper c.2) / (4 * I.upper c.2)
      0 < rho ∧
        rho * (physicalBound (I.upper c.2) n : ℝ) ≤
          ((rawCell P I n c \ (G n).guards).card : ℝ) := by
  have hdensity := eventually_guarded_rawCell_density P I Cprom Cbank G
  filter_upwards [hdensity] with n hdens c
  let density := PaperScaleMarkedCell.paperCellDensity (P c.1)
    (I.lower c.2) (I.upper c.2)
  let upper := I.upper c.2
  let rho := density / (4 * upper)
  have hdensityPos : 0 < density := by
    exact PaperScaleMarkedCell.paperCellDensity_pos
      (P c.1) (I.lower_lt_upper c.2)
  have hupperPos : 0 < upper := by
    exact (I.lower_pos c.2).trans (I.lower_lt_upper c.2)
  have hrho : 0 < rho := by
    exact div_pos hdensityPos (mul_pos (by norm_num) hupperPos)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hbound : (physicalBound upper n : ℝ) ≤ upper * (n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hupperPos.le hn0)
  have hscaled : rho * (physicalBound upper n : ℝ) ≤
      density * (n : ℝ) / 4 := by
    calc
      rho * (physicalBound upper n : ℝ) ≤ rho * (upper * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hbound hrho.le
      _ = density * (n : ℝ) / 4 := by
        dsimp only [rho]
        field_simp [hupperPos.ne']
  refine ⟨hrho, hscaled.trans ?_⟩
  simpa only [density, upper] using hdens c

/-- One common guard-profile error for the fixed finite family of all
head/physical cells. -/
def canonicalGuardSquarefreeError
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    {Cprom Cbank : ℕ} (G : ∀ n, Ledger n Cprom Cbank)
    (K : ℝ) (n : ℕ) : ℝ :=
  ∑ c : PaperBridgeFit.Cell Head,
    guardSquarefreeError (rawCell P I n c) (G n).guards K n

theorem canonicalGuardSquarefreeError_nonneg
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    {Cprom Cbank : ℕ} (G : ∀ n, Ledger n Cprom Cbank)
    (K : ℝ) (n : ℕ) :
    0 ≤ canonicalGuardSquarefreeError P I G K n := by
  unfold canonicalGuardSquarefreeError
  exact Finset.sum_nonneg fun c hc ↦
    guardSquarefreeError_nonneg _ _ _ _

/-- The family-aggregated reciprocal guard error tends to zero. -/
theorem tendsto_canonicalGuardSquarefreeError_zero
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    {Cprom Cbank : ℕ} (G : ∀ n, Ledger n Cprom Cbank) (K : ℝ) :
    Tendsto (canonicalGuardSquarefreeError P I G K) atTop (nhds 0) := by
  have hcell (c : PaperBridgeFit.Cell Head) : Tendsto
      (fun n : ℕ ↦ guardSquarefreeError
        (rawCell P I n c) (G n).guards K n) atTop (nhds 0) := by
    let constant := 4 * Real.exp (2 * K) /
      PaperScaleMarkedCell.paperCellDensity (P c.1)
        (I.lower c.2) (I.upper c.2)
    have hupper := tendsto_guardRateMajorant_zero Cprom Cbank constant
    have hdensity := eventually_rawCell_density P I
    refine squeeze_zero' ?_ ?_ hupper
    · filter_upwards with n
      exact guardSquarefreeError_nonneg _ _ _ _
    · filter_upwards [hdensity, eventually_gt_atTop 0] with n hdens hn
      simpa only [constant] using
        guardSquarefreeError_rawCell_le_rateMajorant
          P I (G n) c (by omega : 1 ≤ n) (hdens c) K
  have hsum := tendsto_finset_sum
    (Finset.univ : Finset (PaperBridgeFit.Cell Head))
    (fun c hc ↦ hcell c)
  simpa only [canonicalGuardSquarefreeError,
    Finset.sum_const_zero] using hsum

/-- The same family error remains negligible after the moving-low harmonic
loss. -/
theorem tendsto_canonicalGuardSquarefreeError_mul_logL_zero
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    {Cprom Cbank : ℕ} (G : ∀ n, Ledger n Cprom Cbank) (K : ℝ) :
    Tendsto (fun n : ℕ ↦
      canonicalGuardSquarefreeError P I G K n * Real.log (L n))
      atTop (nhds 0) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog0 : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (L n) :=
    (hLTop.eventually (eventually_ge_atTop 1)).mono fun n hn ↦
      Real.log_nonneg hn
  have hcell (c : PaperBridgeFit.Cell Head) : Tendsto
      (fun n : ℕ ↦ guardSquarefreeError
          (rawCell P I n c) (G n).guards K n * Real.log (L n))
        atTop (nhds 0) := by
    let constant := 4 * Real.exp (2 * K) /
      PaperScaleMarkedCell.paperCellDensity (P c.1)
        (I.lower c.2) (I.upper c.2)
    have hupper :=
      tendsto_guardRateMajorant_mul_logL_zero Cprom Cbank constant
    have hdensity := eventually_rawCell_density P I
    refine squeeze_zero' ?_ ?_ hupper
    · filter_upwards [hlog0] with n hlog
      exact mul_nonneg (guardSquarefreeError_nonneg _ _ _ _) hlog
    · filter_upwards [hdensity, eventually_gt_atTop 0, hlog0]
        with n hdens hn hlog
      have hn1 : 1 ≤ n := by omega
      have hguard := guardSquarefreeError_rawCell_le_rateMajorant
        (Head := Head) P I (G n) c hn1 (hdens c) K
      have hguard' : guardSquarefreeError
          (rawCell P I n c) (G n).guards K n ≤
        constant * (censusRatioMajorant Cprom Cbank n * y n ^ 2) := by
        simpa only [constant] using hguard
      exact mul_le_mul_of_nonneg_right hguard' hlog
  have hsum := tendsto_finset_sum
    (Finset.univ : Finset (PaperBridgeFit.Cell Head))
    (fun c hc ↦ hcell c)
  have hsum0 : Tendsto (fun n : ℕ ↦
      ∑ c : PaperBridgeFit.Cell Head,
        guardSquarefreeError (rawCell P I n c) (G n).guards K n *
          Real.log (L n)) atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using hsum
  apply hsum0.congr'
  filter_upwards with n
  unfold canonicalGuardSquarefreeError
  rw [Finset.sum_mul]

end

end Erdos390.Full.GuardSquarefreeErrorRate
