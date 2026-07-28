import Erdos390.WholePaper.PrimeLayerCounts

/-!
# Prime counting at asymptotically linear moving endpoints

The moving layers use endpoints which differ from fixed multiples of `n` by
`O(n / log n)`.  This file packages the needed consequence of the safe PNT:
any natural endpoint `m n` with `m n / n → a > 0` has
`π(m n) / (n / log n) → a`.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper.SafePrimeCounting

noncomputable section

private theorem movingEndpoint_cast_tendsto_atTop
    {m : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hm : Tendsto (fun n : ℕ ↦ (m n : ℝ) / (n : ℝ)) atTop (nhds a)) :
    Tendsto (fun n : ℕ ↦ (m n : ℝ)) atTop atTop := by
  have hratio :
      ∀ᶠ n : ℕ in atTop, a / 2 ≤ (m n : ℝ) / (n : ℝ) :=
    hm.eventually (eventually_ge_nhds (half_lt_self ha))
  have hbase :
      Tendsto (fun n : ℕ ↦ (a / 2) * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (half_pos ha)
  apply tendsto_atTop_mono' atTop _ hbase
  filter_upwards [hratio, eventually_gt_atTop 0] with n hnRatio hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact (le_div_iff₀ hnR).mp hnRatio

private theorem movingEndpoint_log_ratio_tendsto_one
    {m : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hm : Tendsto (fun n : ℕ ↦ (m n : ℝ) / (n : ℝ)) atTop (nhds a)) :
    Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) / Real.log (m n : ℝ))
      atTop (nhds 1) := by
  let u : ℕ → ℝ := fun n ↦ (m n : ℝ) / (n : ℝ)
  have hu : Tendsto u atTop (nhds a) := hm
  have hlogu : Tendsto (fun n ↦ Real.log (u n)) atTop (nhds (Real.log a)) :=
    (Real.continuousAt_log ha.ne').tendsto.comp hu
  have hlogn : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    tendsto_log_natCast_atTop
  have hsmall : Tendsto
      (fun n : ℕ ↦ Real.log (u n) / Real.log (n : ℝ))
      atTop (nhds 0) := by
    simpa using hlogu.div_atTop hlogn
  have hden : Tendsto
      (fun n : ℕ ↦ 1 + Real.log (u n) / Real.log (n : ℝ))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hsmall
  have hinv : Tendsto
      (fun n : ℕ ↦
        1 / (1 + Real.log (u n) / Real.log (n : ℝ)))
      atTop (nhds 1) := by
    have hnum : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    convert hnum.div hden (by norm_num : (1 : ℝ) ≠ 0) using 1
    norm_num
  apply hinv.congr'
  have huPos : ∀ᶠ n : ℕ in atTop, 0 < u n :=
    hu.eventually (eventually_gt_nhds ha)
  have hmTop := movingEndpoint_cast_tendsto_atTop ha hm
  filter_upwards [huPos, eventually_gt_atTop 1,
      hmTop.eventually (eventually_gt_atTop 1)] with n hun hn hmn
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hmPos : (0 : ℝ) < m n := by exact_mod_cast (lt_trans zero_lt_one hmn)
  have hlogn : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  have hlogm : Real.log (m n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hmn)).ne'
  have humul : u n * (n : ℝ) = (m n : ℝ) := by
    dsimp [u]
    field_simp
  rw [← humul, Real.log_mul hun.ne' hnPos.ne']
  field_simp
  ring

private theorem movingMainTerm_normalized_tendsto
    {m : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hm : Tendsto (fun n : ℕ ↦ (m n : ℝ) / (n : ℝ)) atTop (nhds a)) :
    Tendsto
      (fun n : ℕ ↦
        ((m n : ℝ) / Real.log (m n : ℝ)) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds a) := by
  have hprod := hm.mul (movingEndpoint_log_ratio_tendsto_one ha hm)
  have hprod' : Tendsto
      (fun n : ℕ ↦
        ((m n : ℝ) / (n : ℝ)) *
          (Real.log (n : ℝ) / Real.log (m n : ℝ)))
      atTop (nhds a) := by
    simpa only [mul_one] using hprod
  apply hprod'.congr'
  have hmTop := movingEndpoint_cast_tendsto_atTop ha hm
  filter_upwards [eventually_gt_atTop 1,
      hmTop.eventually (eventually_gt_atTop 1)] with n hn hmn
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))
  have hm0 : (m n : ℝ) ≠ 0 := by
    exact ne_of_gt (lt_trans zero_lt_one hmn)
  have hlogn : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  have hlogm : Real.log (m n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hmn)).ne'
  field_simp

/-- Prime counting at an arbitrary asymptotically linear moving endpoint. -/
theorem primeCounting_movingEndpoint_normalized_tendsto
    {m : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hm : Tendsto (fun n : ℕ ↦ (m n : ℝ) / (n : ℝ)) atTop (nhds a)) :
    Tendsto
      (fun n : ℕ ↦
        (Nat.primeCounting (m n) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds a) := by
  have hmTop := movingEndpoint_cast_tendsto_atTop ha hm
  have hpnt0 := primeCounting_real_isEquivalent.comp_tendsto hmTop
  have hpnt :
      (fun n : ℕ ↦ (Nat.primeCounting (m n) : ℝ)) ~[atTop]
        (fun n : ℕ ↦ (m n : ℝ) / Real.log (m n : ℝ)) := by
    refine (hpnt0.congr_left ?_).congr_right ?_
    · exact Eventually.of_forall fun n ↦ by
        simp [Function.comp_apply, Nat.floor_natCast]
    · exact Eventually.of_forall fun _ ↦ rfl
  have hmain := movingMainTerm_normalized_tendsto ha hm
  have hdenNe :
      ∀ᶠ n : ℕ in atTop,
        (m n : ℝ) / Real.log (m n : ℝ) ≠ 0 := by
    filter_upwards [hmTop.eventually (eventually_gt_atTop 1)] with n hmn
    exact div_ne_zero (by positivity)
      (Real.log_pos (by exact_mod_cast hmn)).ne'
  have hpntRatio := (isEquivalent_iff_tendsto_one hdenNe).mp hpnt
  have hmul := hpntRatio.mul hmain
  have hmul' : Tendsto
      (fun n : ℕ ↦
        ((Nat.primeCounting (m n) : ℝ) /
            ((m n : ℝ) / Real.log (m n : ℝ))) *
          (((m n : ℝ) / Real.log (m n : ℝ)) /
            ((n : ℝ) / Real.log (n : ℝ))))
      atTop (nhds a) := by
    simpa only [one_mul] using hmul
  apply hmul'.congr'
  filter_upwards [eventually_gt_atTop 1,
      hmTop.eventually (eventually_gt_atTop 1)] with n hn hmn
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))
  have hm0 : (m n : ℝ) ≠ 0 := by
    exact ne_of_gt (lt_trans zero_lt_one hmn)
  have hlogn : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  have hlogm : Real.log (m n : ℝ) ≠ 0 :=
    (Real.log_pos hmn).ne'
  change
    ((Nat.primeCounting (m n) : ℝ) /
        ((m n : ℝ) / Real.log (m n : ℝ))) *
        (((m n : ℝ) / Real.log (m n : ℝ)) /
          ((n : ℝ) / Real.log (n : ℝ))) =
      (Nat.primeCounting (m n) : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))
  field_simp [hm0, hlogm]

end

end Erdos390.WholePaper.SafePrimeCounting
