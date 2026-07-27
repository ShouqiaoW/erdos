import Erdos536.PrimeBandProfileConcrete
import Erdos536.PrimeBandCollision

/-!
# Concrete endpoint data for the delayed quadratic profile

This file chooses a logarithmic checked horizon for the polynomial-cutoff
quadratic band and packages the rank lower bounds consumed by the
collision argument.
-/

open scoped BigOperators
open Finset Filter Topology Set

noncomputable section

namespace Erdos536

open PrimeSums
open PrimeBandTimeChange

/-- A slope just below two.  The small gap leaves room for the polynomial
cutoff, while the profile slope still gives rank decay faster than
`T⁻²`. -/
def quadraticDelayedProfileHorizonSlope : ℝ := 199 / 100

/-- The concrete delayed-profile horizon. -/
noncomputable def quadraticDelayedProfileHorizon (T : ℕ) : ℕ :=
  ⌊quadraticDelayedProfileHorizonSlope * Real.log (T : ℝ)⌋₊

/-- Last real depth in the concrete delayed grid. -/
noncomputable def quadraticDelayedProfileEndpointDepth (T : ℕ) : ℝ :=
  quadraticDelayedProfileDepth (quadraticDelayedProfileHorizon T)

/-- Number of visible pivot ranks forced at horizon `H`. -/
def quadraticDelayedPivotCount (H : ℕ) : ℕ :=
  3 * quadraticDelayedProfileThreshold H

/-- The first delayed check whose three visible-label thresholds force
rank `i`. -/
def quadraticDelayedPivotCheck (i : ℕ) : ℕ :=
  (25 * (i / 3) + 7) / 8

/-- Deterministic normalized-weight lower bound at pivot rank `i`. -/
def quadraticDelayedPivotLower (i : ℕ) : ℝ :=
  depthCoordinate
    (quadraticDelayedProfileDepth (quadraticDelayedPivotCheck i))

theorem quadraticDelayedPivotLower_pos (i : ℕ) :
    0 < quadraticDelayedPivotLower i :=
  depthCoordinate_pos _

theorem quadraticDelayedPivotCheck_forces_rank (i : ℕ) :
    i <
      quadraticDelayedPivotCount
        (quadraticDelayedPivotCheck i) := by
  unfold quadraticDelayedPivotCount
    quadraticDelayedProfileThreshold
    quadraticDelayedPivotCheck
  omega

theorem quadraticDelayedPivotCheck_cast_le (i : ℕ) :
    (quadraticDelayedPivotCheck i : ℝ) ≤
      (25 / 24 : ℝ) * (i : ℝ) + 1 := by
  have hfirst :
      8 * quadraticDelayedPivotCheck i ≤
        25 * (i / 3) + 7 := by
    unfold quadraticDelayedPivotCheck
    exact Nat.mul_div_le _ _
  have hsecond : 3 * (i / 3) ≤ i :=
    by simpa only [mul_comm] using Nat.div_mul_le_self i 3
  have hfirstR :
      (8 : ℝ) * quadraticDelayedPivotCheck i ≤
        25 * ((i / 3 : ℕ) : ℝ) + 7 := by
    exact_mod_cast hfirst
  have hsecondR :
      (3 : ℝ) * ((i / 3 : ℕ) : ℝ) ≤ (i : ℝ) := by
    exact_mod_cast hsecond
  nlinarith

theorem quadraticDelayedPivotCheck_le_of_lt_count
    {i H : ℕ} (hi : i < quadraticDelayedPivotCount H) :
    quadraticDelayedPivotCheck i ≤ H := by
  unfold quadraticDelayedPivotCount
    quadraticDelayedProfileThreshold at hi
  unfold quadraticDelayedPivotCheck
  omega

private theorem exp_twenty_one_twentieth_lt_three :
    Real.exp (21 / 20 : ℝ) < 3 := by
  have hsmall :
      Real.exp (1 / 20 : ℝ) ≤
        1 / (1 - (1 / 20 : ℝ)) :=
    Real.exp_bound_div_one_sub_of_interval
      (by norm_num) (by norm_num)
  calc
    Real.exp (21 / 20 : ℝ) =
        Real.exp 1 * Real.exp (1 / 20 : ℝ) := by
      rw [show (21 / 20 : ℝ) = 1 + 1 / 20 by norm_num,
        Real.exp_add]
    _ < (2.7182818286 : ℝ) *
        Real.exp (1 / 20 : ℝ) :=
      mul_lt_mul_of_pos_right Real.exp_one_lt_d9
        (Real.exp_pos _)
    _ ≤ (2.7182818286 : ℝ) *
        (1 / (1 - (1 / 20 : ℝ))) :=
      mul_le_mul_of_nonneg_left hsmall (by norm_num)
    _ < 3 := by norm_num

private theorem twenty_one_twentieth_lt_log_three :
    (21 / 20 : ℝ) < Real.log 3 := by
  exact (Real.lt_log_iff_exp_lt (by norm_num)).2
    exp_twenty_one_twentieth_lt_three

/-- Every index up to the concrete horizon belongs to the valid natural
check set, eventually in `T`. -/
theorem eventually_quadraticDelayedProfileHorizon_checks :
    ∀ᶠ T : ℕ in atTop, ∀ k ≤ quadraticDelayedProfileHorizon T,
      k ∈ quadraticDelayedProfileChecks T
        (quadraticDelayedProfileHorizon T) := by
  let B : ℝ := quadraticDelayedProfileDepth 0
  have hrpow :
      Tendsto
        (fun T : ℕ => (T : ℝ) ^ (1 / 200 : ℝ))
        atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200)).comp
      tendsto_natCast_atTop_atTop
  have hlarge :
      ∀ᶠ T : ℕ in atTop,
        1200 * Real.exp B ≤ (T : ℝ) ^ (1 / 200 : ℝ) :=
    hrpow.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge, eventually_ge_atTop 1] with
      T hlargeT hT
  have hTR : (0 : ℝ) < T := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hlogNonneg : 0 ≤ Real.log (T : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hT)
  have hHorizon :
      (quadraticDelayedProfileHorizon T : ℝ) ≤
        quadraticDelayedProfileHorizonSlope *
          Real.log (T : ℝ) := by
    exact Nat.floor_le
      (mul_nonneg
        (by norm_num [quadraticDelayedProfileHorizonSlope])
        hlogNonneg)
  have hlog :=
    Real.log_natCast_le_rpow_div T
      (show (0 : ℝ) < 1 / 200 by norm_num)
  have hlarge' :
      (1200 : ℝ) ≤
        Real.exp (-B) * (T : ℝ) ^ (1 / 200 : ℝ) := by
    calc
      (1200 : ℝ) =
          Real.exp (-B) * (1200 * Real.exp B) := by
        symm
        calc
          Real.exp (-B) * (1200 * Real.exp B) =
              1200 * (Real.exp (-B) * Real.exp B) := by ring
          _ = 1200 := by
            rw [← Real.exp_add]
            simp
      _ ≤ Real.exp (-B) *
          (T : ℝ) ^ (1 / 200 : ℝ) :=
        mul_le_mul_of_nonneg_left hlargeT (Real.exp_nonneg _)
  have hdom :
      6 * Real.log (T : ℝ) ≤
        Real.exp (-B) * (T : ℝ) ^ (1 / 100 : ℝ) := by
    have hlog' :
        6 * Real.log (T : ℝ) ≤
          1200 * (T : ℝ) ^ (1 / 200 : ℝ) := by
      norm_num at hlog ⊢
      nlinarith
    calc
      6 * Real.log (T : ℝ) ≤
          1200 * (T : ℝ) ^ (1 / 200 : ℝ) :=
        hlog'
      _ ≤ (Real.exp (-B) *
              (T : ℝ) ^ (1 / 200 : ℝ)) *
            (T : ℝ) ^ (1 / 200 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hlarge'
          (Real.rpow_nonneg (by positivity) _)
      _ = Real.exp (-B) *
          (T : ℝ) ^ (1 / 100 : ℝ) := by
        calc
          (Real.exp (-B) * (T : ℝ) ^ (1 / 200 : ℝ)) *
              (T : ℝ) ^ (1 / 200 : ℝ) =
            Real.exp (-B) *
              ((T : ℝ) ^ (1 / 200 : ℝ) *
                (T : ℝ) ^ (1 / 200 : ℝ)) := by ring
          _ = Real.exp (-B) *
              (T : ℝ) ^
                ((1 / 200 : ℝ) + (1 / 200 : ℝ)) := by
            rw [Real.rpow_add hTR]
          _ = Real.exp (-B) *
              (T : ℝ) ^ (1 / 100 : ℝ) := by norm_num
  have hdepthEq :
      quadraticDelayedProfileDepth
          (quadraticDelayedProfileHorizon T) =
        B + (quadraticDelayedProfileHorizon T : ℝ) := by
    dsimp [B]
    unfold quadraticDelayedProfileDepth
    push_cast
    ring
  have hcoordinate :
      Real.exp
          (-B - quadraticDelayedProfileHorizonSlope *
            Real.log (T : ℝ)) ≤
        depthCoordinate
          (quadraticDelayedProfileDepth
            (quadraticDelayedProfileHorizon T)) := by
    unfold depthCoordinate
    rw [Real.exp_le_exp, hdepthEq]
    linarith
  have hscale :
      Real.exp (-B) * (T : ℝ) ^ (1 / 100 : ℝ) =
        ((T ^ 2 : ℕ) : ℝ) *
          Real.exp
            (-B - quadraticDelayedProfileHorizonSlope *
              Real.log (T : ℝ)) := by
    calc
      Real.exp (-B) * (T : ℝ) ^ (1 / 100 : ℝ) =
          Real.exp (-B) *
            Real.exp (Real.log (T : ℝ) * (1 / 100 : ℝ)) := by
        rw [Real.rpow_def_of_pos hTR]
      _ = Real.exp
          (-B + Real.log (T : ℝ) * (1 / 100 : ℝ)) := by
        rw [← Real.exp_add]
      _ = Real.exp (2 * Real.log (T : ℝ)) *
          Real.exp
            (-B - quadraticDelayedProfileHorizonSlope *
              Real.log (T : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        unfold quadraticDelayedProfileHorizonSlope
        ring
      _ = ((T ^ 2 : ℕ) : ℝ) *
          Real.exp
            (-B - quadraticDelayedProfileHorizonSlope *
              Real.log (T : ℝ)) := by
        have hT2 :
            Real.exp (2 * Real.log (T : ℝ)) =
              ((T ^ 2 : ℕ) : ℝ) := by
          calc
            Real.exp (2 * Real.log (T : ℝ)) =
                Real.exp (Real.log (T : ℝ)) ^ 2 := by
              simpa only [Nat.cast_ofNat] using
                Real.exp_nat_mul (Real.log (T : ℝ)) 2
            _ = (T : ℝ) ^ 2 := by rw [Real.exp_log hTR]
            _ = ((T ^ 2 : ℕ) : ℝ) := by norm_num
        rw [hT2]
  have hinner :
      6 * Real.log (T : ℝ) ≤
        ((T ^ 2 : ℕ) : ℝ) *
          depthCoordinate
            (quadraticDelayedProfileDepth
              (quadraticDelayedProfileHorizon T)) := by
    calc
      6 * Real.log (T : ℝ) ≤
          Real.exp (-B) * (T : ℝ) ^ (1 / 100 : ℝ) :=
        hdom
      _ = ((T ^ 2 : ℕ) : ℝ) *
          Real.exp
            (-B - quadraticDelayedProfileHorizonSlope *
              Real.log (T : ℝ)) :=
        hscale
      _ ≤ ((T ^ 2 : ℕ) : ℝ) *
          depthCoordinate
            (quadraticDelayedProfileDepth
              (quadraticDelayedProfileHorizon T)) :=
        mul_le_mul_of_nonneg_left hcoordinate (by positivity)
  have hrealCutoff :
      (quadraticLowerCutoff T : ℝ) ≤
        Real.exp
          (((T ^ 2 : ℕ) : ℝ) *
            depthCoordinate
              (quadraticDelayedProfileDepth
                (quadraticDelayedProfileHorizon T))) := by
    calc
      (quadraticLowerCutoff T : ℝ) = (T : ℝ) ^ 6 := by
        simp [quadraticLowerCutoff, Nat.cast_pow]
      _ = Real.exp (6 * Real.log (T : ℝ)) := by
        symm
        calc
          Real.exp (6 * Real.log (T : ℝ)) =
              Real.exp (Real.log (T : ℝ)) ^ 6 := by
            simpa only [Nat.cast_ofNat] using
              Real.exp_nat_mul (Real.log (T : ℝ)) 6
          _ = (T : ℝ) ^ 6 := by rw [Real.exp_log hTR]
      _ ≤ Real.exp
          (((T ^ 2 : ℕ) : ℝ) *
            depthCoordinate
              (quadraticDelayedProfileDepth
                (quadraticDelayedProfileHorizon T))) :=
        Real.exp_le_exp.mpr hinner
  have hcutoff :
      quadraticLowerCutoff T ≤
        expEndpoint
          (depthCoordinate
            (quadraticDelayedProfileDepth
              (quadraticDelayedProfileHorizon T))) (T ^ 2) := by
    unfold expEndpoint
    exact_mod_cast hrealCutoff.trans (Nat.le_ceil _)
  intro k hk
  rw [mem_quadraticDelayedProfileChecks]
  constructor
  · omega
  · apply hcutoff.trans
    apply expEndpoint_mono
    apply depthCoordinate_antitone
    unfold quadraticDelayedProfileDepth
    exact_mod_cast (show
      76 + quadraticDelayedProfileGap + k ≤
        76 + quadraticDelayedProfileGap +
          quadraticDelayedProfileHorizon T by omega)

/-- Endpoint rank decay at the concrete horizon, with unit constant. -/
theorem eventually_quadraticDelayedPivotCount_decay
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ T : ℕ in atTop,
      (1 / 3 : ℝ) ^
          quadraticDelayedPivotCount
            (quadraticDelayedProfileHorizon T) ≤
        eta / ((T ^ 2 : ℕ) : ℝ) := by
  let delta : ℝ :=
    (24 / 25 : ℝ) * quadraticDelayedProfileHorizonSlope *
        Real.log 3 - 2
  have hdelta : 0 < delta := by
    dsimp [delta, quadraticDelayedProfileHorizonSlope]
    nlinarith [twenty_one_twentieth_lt_log_three]
  have hlogTop :
      Tendsto (fun T : ℕ => Real.log (T : ℝ))
        atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmargin :
      ∀ᶠ T : ℕ in atTop,
        -Real.log eta + (24 / 25 : ℝ) * Real.log 3 ≤
          delta * Real.log (T : ℝ) :=
    (hlogTop.const_mul_atTop hdelta).eventually
      (eventually_ge_atTop _)
  filter_upwards [hmargin, eventually_ge_atTop 1] with
      T hmarginT hT
  let H := quadraticDelayedProfileHorizon T
  let K := quadraticDelayedPivotCount H
  have hTR : (0 : ℝ) < T := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hHlower :
      quadraticDelayedProfileHorizonSlope *
            Real.log (T : ℝ) - 1 <
        (H : ℝ) := by
    have hfloor :=
      Nat.lt_floor_add_one
        (quadraticDelayedProfileHorizonSlope *
          Real.log (T : ℝ))
    change
      quadraticDelayedProfileHorizonSlope *
          Real.log (T : ℝ) <
        (H : ℝ) + 1 at hfloor
    linarith
  have hdiv :
      8 * H <
        25 * quadraticDelayedProfileThreshold H := by
    unfold quadraticDelayedProfileThreshold
    omega
  have hdivR :
      (8 : ℝ) * H <
        25 * quadraticDelayedProfileThreshold H := by
    exact_mod_cast hdiv
  have hK :
      (24 / 25 : ℝ) * (H : ℝ) < (K : ℝ) := by
    dsimp [K, quadraticDelayedPivotCount]
    push_cast
    nlinarith
  have hKaffine :
      (24 / 25 : ℝ) *
            quadraticDelayedProfileHorizonSlope *
            Real.log (T : ℝ) -
          24 / 25 <
        (K : ℝ) := by
    calc
      (24 / 25 : ℝ) *
              quadraticDelayedProfileHorizonSlope *
              Real.log (T : ℝ) -
            24 / 25 =
          (24 / 25 : ℝ) *
            (quadraticDelayedProfileHorizonSlope *
              Real.log (T : ℝ) - 1) := by ring
      _ < (24 / 25 : ℝ) * (H : ℝ) :=
        mul_lt_mul_of_pos_left hHlower (by norm_num)
      _ < (K : ℝ) := hK
  have hlogThree : 0 < Real.log 3 :=
    Real.log_pos (by norm_num)
  have hKmul :=
    mul_lt_mul_of_pos_right hKaffine hlogThree
  have hexponent :
      -(K : ℝ) * Real.log 3 ≤
        Real.log eta - 2 * Real.log (T : ℝ) := by
    dsimp [delta, quadraticDelayedProfileHorizonSlope] at hmarginT
    dsimp [quadraticDelayedProfileHorizonSlope] at hKmul
    ring_nf at hmarginT hKmul ⊢
    nlinarith
  have hleft :
      (1 / 3 : ℝ) ^ K =
        Real.exp (-(K : ℝ) * Real.log 3) := by
    calc
      (1 / 3 : ℝ) ^ K = (3 : ℝ)⁻¹ ^ K := by
        rw [one_div]
      _ = Real.exp (-Real.log 3) ^ K := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      _ = Real.exp ((K : ℝ) * (-Real.log 3)) :=
        (Real.exp_nat_mul (-Real.log 3) K).symm
      _ = Real.exp (-(K : ℝ) * Real.log 3) := by ring
  have hTtwo :
      Real.exp (2 * Real.log (T : ℝ)) =
        ((T ^ 2 : ℕ) : ℝ) := by
    calc
      Real.exp (2 * Real.log (T : ℝ)) =
          Real.exp (Real.log (T : ℝ)) ^ 2 := by
        simpa only [Nat.cast_ofNat] using
          Real.exp_nat_mul (Real.log (T : ℝ)) 2
      _ = (T : ℝ) ^ 2 := by rw [Real.exp_log hTR]
      _ = ((T ^ 2 : ℕ) : ℝ) := by norm_num
  have hright :
      Real.exp
          (Real.log eta - 2 * Real.log (T : ℝ)) =
        eta / ((T ^ 2 : ℕ) : ℝ) := by
    rw [Real.exp_sub, Real.exp_log heta, hTtwo]
  dsimp [K, H] at hleft ⊢
  rw [hleft, ← hright]
  exact Real.exp_le_exp.mpr hexponent

/-- Collision-facing endpoint package.  The last depth is in the concrete
grid, its threshold is positive, and the three-visible-label endpoint
decay has unit constant. -/
theorem eventually_quadraticDelayedProfileEndpointData
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ T : ℕ in atTop,
      quadraticDelayedProfileEndpointDepth T ∈
          quadraticDelayedProfileDepths T
            (quadraticDelayedProfileHorizon T) ∧
        1 ≤ quadraticDelayedProfileThresholdAtDepth
          (quadraticDelayedProfileEndpointDepth T) ∧
        (1 / 3 : ℝ) ^
            (3 * quadraticDelayedProfileThresholdAtDepth
              (quadraticDelayedProfileEndpointDepth T)) ≤
          eta / ((T ^ 2 : ℕ) : ℝ) := by
  filter_upwards [
      eventually_quadraticDelayedProfileHorizon_checks,
      eventually_quadraticDelayedPivotCount_decay heta] with
      T hchecksT hdecayT
  have hlast :
      quadraticDelayedProfileHorizon T ∈
        quadraticDelayedProfileChecks T
          (quadraticDelayedProfileHorizon T) :=
    hchecksT _ le_rfl
  constructor
  · rw [mem_quadraticDelayedProfileDepths]
    exact
      ⟨quadraticDelayedProfileHorizon T, hlast, rfl⟩
  constructor
  · rw [quadraticDelayedProfileEndpointDepth,
      quadraticDelayedProfileThresholdAtDepth_eq]
    exact quadraticDelayedProfileThreshold_pos _
  · simpa only [
      quadraticDelayedProfileEndpointDepth,
      quadraticDelayedProfileThresholdAtDepth_eq,
      quadraticDelayedPivotCount] using hdecayT

/-- A fixed geometric majorant for the pivot rank series. -/
noncomputable def quadraticDelayedPivotSeriesBound : ℝ :=
  Real.exp
      (quadraticDelayedProfileDepth 0 + 1) /
    (3 * (1 - Real.exp (25 / 24) / 3))

theorem quadraticDelayedPivotSeriesBound_nonneg :
    0 ≤ quadraticDelayedPivotSeriesBound := by
  have hexp :
      Real.exp (25 / 24 : ℝ) < 3 := by
    exact
      (Real.exp_lt_exp.mpr
        (show (25 / 24 : ℝ) < 21 / 20 by norm_num)).trans
        exp_twenty_one_twentieth_lt_three
  have hratio :
      Real.exp (25 / 24 : ℝ) / 3 < 1 :=
    (div_lt_one (by norm_num)).2 hexp
  unfold quadraticDelayedPivotSeriesBound
  apply div_nonneg (Real.exp_nonneg _)
  exact mul_nonneg (by norm_num) (sub_nonneg.mpr hratio.le)

private theorem pivotRankDecay_div_quadraticDelayedPivotLower_le
    (i : ℕ) :
    pivotRankDecay i / quadraticDelayedPivotLower i ≤
      (Real.exp (quadraticDelayedProfileDepth 0 + 1) / 3) *
        (Real.exp (25 / 24 : ℝ) / 3) ^ i := by
  let B : ℝ := quadraticDelayedProfileDepth 0
  have hdepthEq :
      quadraticDelayedProfileDepth (quadraticDelayedPivotCheck i) =
        B + (quadraticDelayedPivotCheck i : ℝ) := by
    dsimp [B]
    unfold quadraticDelayedProfileDepth
    push_cast
    ring
  have hdepth :
      quadraticDelayedProfileDepth (quadraticDelayedPivotCheck i) ≤
        B + 1 + (25 / 24 : ℝ) * (i : ℝ) := by
    rw [hdepthEq]
    linarith [quadraticDelayedPivotCheck_cast_le i]
  have hexp :
      Real.exp
          (quadraticDelayedProfileDepth
            (quadraticDelayedPivotCheck i)) ≤
        Real.exp (B + 1 + (25 / 24 : ℝ) * (i : ℝ)) :=
    Real.exp_le_exp.mpr hdepth
  have hellInv :
      (quadraticDelayedPivotLower i)⁻¹ =
        Real.exp
          (quadraticDelayedProfileDepth
            (quadraticDelayedPivotCheck i)) := by
    unfold quadraticDelayedPivotLower depthCoordinate
    simpa only [neg_neg] using
      (Real.exp_neg
        (-quadraticDelayedProfileDepth
          (quadraticDelayedPivotCheck i))).symm
  calc
    pivotRankDecay i / quadraticDelayedPivotLower i =
        pivotRankDecay i *
          Real.exp
            (quadraticDelayedProfileDepth
              (quadraticDelayedPivotCheck i)) := by
      rw [div_eq_mul_inv, hellInv]
    _ ≤ pivotRankDecay i *
          Real.exp (B + 1 + (25 / 24 : ℝ) * (i : ℝ)) :=
      mul_le_mul_of_nonneg_left hexp (pivotRankDecay_nonneg i)
    _ = (Real.exp (quadraticDelayedProfileDepth 0 + 1) / 3) *
        (Real.exp (25 / 24 : ℝ) / 3) ^ i := by
      have hexpi :
          Real.exp ((25 / 24 : ℝ) * (i : ℝ)) =
            Real.exp (25 / 24 : ℝ) ^ i := by
        simpa only [mul_comm] using
          Real.exp_nat_mul (25 / 24 : ℝ) i
      unfold pivotRankDecay
      dsimp [B]
      rw [show
          quadraticDelayedProfileDepth 0 + 1 +
              (25 / 24 : ℝ) * (i : ℝ) =
            (quadraticDelayedProfileDepth 0 + 1) +
              (25 / 24 : ℝ) * (i : ℝ) by ring,
        Real.exp_add, hexpi, pow_succ]
      simp only [div_eq_mul_inv, mul_pow]
      ring

theorem quadraticDelayedPivotRankSeries_le (K : ℕ) :
    pivotRankSeries quadraticDelayedPivotLower K ≤
      quadraticDelayedPivotSeriesBound := by
  let A : ℝ :=
    Real.exp (quadraticDelayedProfileDepth 0 + 1) / 3
  let q : ℝ := Real.exp (25 / 24 : ℝ) / 3
  have hq0 : 0 < q := by
    dsimp [q]
    positivity
  have hexp :
      Real.exp (25 / 24 : ℝ) < 3 := by
    exact
      (Real.exp_lt_exp.mpr
        (show (25 / 24 : ℝ) < 21 / 20 by norm_num)).trans
        exp_twenty_one_twentieth_lt_three
  have hq1 : q < 1 := by
    dsimp [q]
    exact (div_lt_one (by norm_num)).2 hexp
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hgeom :
      (∑ i ∈ Finset.range K, q ^ i) ≤
        1 / (1 - q) := by
    simpa only [Nat.Ico_zero_eq_range, pow_zero,
      one_div] using
      (geom_sum_Ico_le_of_lt_one
        (m := 0) (n := K) hq0.le hq1)
  calc
    pivotRankSeries quadraticDelayedPivotLower K ≤
        ∑ i ∈ Finset.range K, A * q ^ i := by
      unfold pivotRankSeries
      apply Finset.sum_le_sum
      intro i _hi
      dsimp [A, q]
      exact
        pivotRankDecay_div_quadraticDelayedPivotLower_le i
    _ = A * ∑ i ∈ Finset.range K, q ^ i := by
      rw [Finset.mul_sum]
    _ ≤ A * (1 - q)⁻¹ := by
      simpa only [one_div] using
        mul_le_mul_of_nonneg_left hgeom hA
    _ = quadraticDelayedPivotSeriesBound := by
      dsimp [A, q]
      unfold quadraticDelayedPivotSeriesBound
      have hden :
          1 - Real.exp (25 / 24 : ℝ) / 3 ≠ 0 := by
        exact ne_of_gt (sub_pos.mpr (by
          exact (div_lt_one (by norm_num)).2 hexp))
      field_simp [hden]

end Erdos536
