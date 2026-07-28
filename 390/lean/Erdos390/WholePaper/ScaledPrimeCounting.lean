import Erdos390.WholePaper.SafePrimeCounting

/-!
# Prime counting at fixed positive dilates

This is the uniformity-free fixed-scale consequence needed for each of the
thirteen lower-bound layers.  Moving endpoints will later be sandwiched
between fixed dilates.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper.SafePrimeCounting

theorem tendsto_log_natCast_atTop :
    Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_log_natCast_div_log_const_mul (a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun n : ℕ =>
        Real.log (n : ℝ) / Real.log (a * (n : ℝ)))
      atTop (nhds 1) := by
  have hsmall : Tendsto
      (fun n : ℕ => Real.log a / Real.log (n : ℝ))
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_natCast_atTop
  have hden : Tendsto
      (fun n : ℕ => 1 + Real.log a / Real.log (n : ℝ))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hsmall
  have hinv : Tendsto
      (fun n : ℕ => 1 / (1 + Real.log a / Real.log (n : ℝ)))
      atTop (nhds 1) := by
    have hnum : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    convert hnum.div hden (by norm_num : (1 : ℝ) ≠ 0) using 1
    norm_num
  apply hinv.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hlogn : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  rw [Real.log_mul ha.ne' hnR.ne']
  field_simp
  ring

theorem div_log_const_mul_isEquivalent (a : ℝ) (ha : 0 < a) :
    (fun n : ℕ =>
      (a * (n : ℝ)) / Real.log (a * (n : ℝ))) ~[atTop]
      (fun n : ℕ =>
        (a * (n : ℝ)) / Real.log (n : ℝ)) := by
  have hscaleTop :
      Tendsto (fun n : ℕ => a * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop ha
  have htargetNe :
      ∀ᶠ n : ℕ in atTop,
        (a * (n : ℝ)) / Real.log (n : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    exact div_ne_zero (mul_ne_zero ha.ne' hnR.ne')
      (Real.log_pos (by exact_mod_cast hn)).ne'
  apply (isEquivalent_iff_tendsto_one htargetNe).mpr
  apply (tendsto_log_natCast_div_log_const_mul a ha).congr'
  filter_upwards [eventually_gt_atTop 1,
      hscaleTop.eventually (eventually_gt_atTop 1)] with n hn han
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hlogn : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  have hlogaN : Real.log (a * (n : ℝ)) ≠ 0 := (Real.log_pos han).ne'
  have han0 : a * (n : ℝ) ≠ 0 := mul_ne_zero ha.ne' hnR.ne'
  change Real.log (n : ℝ) / Real.log (a * (n : ℝ)) =
    ((a * (n : ℝ)) / Real.log (a * (n : ℝ))) /
      ((a * (n : ℝ)) / Real.log (n : ℝ))
  field_simp

/-- For each fixed `a>0`, the count of primes up to `a n` has the expected
`a n / log n` asymptotic. -/
theorem primeCounting_const_mul_nat_isEquivalent (a : ℝ) (ha : 0 < a) :
    (fun n : ℕ =>
      (Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ)) ~[atTop]
      (fun n : ℕ =>
        (a * (n : ℝ)) / Real.log (n : ℝ)) := by
  have hscaleTop :
      Tendsto (fun n : ℕ => a * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop ha
  exact (primeCounting_real_isEquivalent.comp_tendsto hscaleTop).trans
    (div_log_const_mul_isEquivalent a ha)

end Erdos390.WholePaper.SafePrimeCounting
