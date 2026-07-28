import Erdos390.WholePaper.Definitions

/-!
# Equivalence of the two main asymptotic targets

The paper states its main result both as an additive small-`o` expansion and
as a normalized limit.  This file proves that the two exact Lean target
propositions are equivalent.  It does not prove that either target holds.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

noncomputable section

private theorem eventually_secondOrderScale_ne_zero :
    ∀ᶠ n : ℕ in atTop, secondOrderScale n ≠ 0 := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnOne : 1 < n := lt_of_lt_of_le (by norm_num) hn
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hnOne)
  have hlogPos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hnOne)
  exact div_ne_zero hnPos.ne' hlogPos.ne'

private theorem mainError_div_secondOrderScale_eq {n : ℕ} (hn : 2 ≤ n) :
    mainError n / secondOrderScale n =
      (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) /
          (n : ℝ) - C0 := by
  have hnOne : 1 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hnOne))
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hnOne)).ne'
  simp only [mainError, secondOrderScale]
  field_simp [hnR, hlog]
  ring

private theorem eventually_mainError_ratio_eq :
    (fun n : ℕ ↦ mainError n / secondOrderScale n) =ᶠ[atTop]
      (fun n : ℕ ↦
        (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) /
            (n : ℝ) - C0) := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact mainError_div_secondOrderScale_eq hn

/-- The two displays in the paper's main theorem are mathematically
equivalent, with the exact totalized definitions used in this project. -/
theorem mainAsymptotic_iff_mainNormalizedLimit :
    MainAsymptotic ↔ MainNormalizedLimit := by
  constructor
  · intro h
    have hratio :
        Tendsto (fun n : ℕ ↦ mainError n / secondOrderScale n)
          atTop (nhds 0) :=
      (show mainError =o[atTop] secondOrderScale from h).tendsto_div_nhds_zero
    have hsub :
        Tendsto
          (fun n : ℕ ↦
            (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) /
                (n : ℝ) - C0)
          atTop (nhds 0) :=
      hratio.congr' eventually_mainError_ratio_eq
    exact (tendsto_sub_nhds_zero_iff.mp hsub : MainNormalizedLimit)
  · intro h
    have hsub :
        Tendsto
          (fun n : ℕ ↦
            (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) /
                (n : ℝ) - C0)
          atTop (nhds 0) :=
      tendsto_sub_nhds_zero_iff.mpr h
    have hratio :
        Tendsto (fun n : ℕ ↦ mainError n / secondOrderScale n)
          atTop (nhds 0) :=
      hsub.congr' eventually_mainError_ratio_eq.symm
    apply (isLittleO_iff_tendsto' ?_).mpr hratio
    filter_upwards [eventually_secondOrderScale_ne_zero] with n hn hzero
    exact (hn hzero).elim

end

end Erdos390.WholePaper
