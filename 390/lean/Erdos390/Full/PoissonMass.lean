import Erdos390.Full.ConditionedPoisson
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Almost-sure finiteness of the scale-invariant Poisson mass

The shell construction in `ConditionedPoisson` is an honest probability
space, but the infinite total was initially only an `ENNReal` random
variable.  Here we prove that its expectation is finite and hence that the
total is finite almost surely.  This is a prerequisite for a genuine
exact-total bridge and is not assumed as part of a process interface.
-/

open Filter Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace Erdos390.Full.PoissonMass

open MeasureTheory ProbabilityTheory Real
open ConditionedPoisson

/-- The Poisson count has its declared mean, proved from the PMF recurrence. -/
lemma lintegral_count_poisson (r : ℝ≥0) :
    (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂poissonMeasure r) = (r : ℝ≥0∞) := by
  rw [poissonMeasure, lintegral_countable']
  have hsingle (n : ℕ) :
      (poissonPMF r).toMeasure {n} = poissonPMF r n :=
    (poissonPMF r).toMeasure_apply_singleton n (measurableSet_singleton n)
  simp_rw [hsingle]
  change (∑' n : ℕ, (n : ℝ≥0∞) * poissonPMF r n) = (r : ℝ≥0∞)
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  simp_rw [poissonPMF_succ_size_bias]
  rw [ENNReal.tsum_mul_left, PMF.tsum_coe]
  simp

lemma lintegral_count_shellLaw :
    (∫⁻ omega : Sample, (omega.1 : ℝ≥0∞) ∂shellLaw) = 1 := by
  have hfst : MeasurePreserving Prod.fst shellLaw (poissonMeasure 1) :=
    measurePreserving_fst
  rw [hfst.lintegral_comp (by fun_prop)]
  exact lintegral_count_poisson 1

/-- Under one shell law, every auxiliary logarithmic coordinate belongs to
the unit interval almost surely, simultaneously for all indices. -/
lemma shellLaw_ae_all_coordinates :
    ∀ᵐ omega ∂shellLaw, ∀ i : ℕ, omega.2 i ∈ Ioc (0 : ℝ) 1 := by
  have hcoord (i : ℕ) :
      ∀ᵐ omega ∂shellLaw, omega.2 i ∈ Ioc (0 : ℝ) 1 := by
    have hsnd : MeasurePreserving Prod.snd shellLaw coordinateLaw :=
      measurePreserving_snd
    have heval : MeasurePreserving (Function.eval i) coordinateLaw unitLaw :=
      measurePreserving_eval_infinitePi (fun _ : ℕ ↦ unitLaw) i
    exact (heval.comp hsnd).quasiMeasurePreserving.tendsto_ae unitLaw_ae_mem
  exact ae_all_iff.mpr hcoord

private lemma shellMassTerm_le (k i : ℕ) (omega : Sample)
    (hcoord : ∀ j : ℕ, omega.2 j ∈ Ioc (0 : ℝ) 1) :
    shellMassTerm k i omega ≤
      if i < omega.1 then ENNReal.ofReal (exp (-(k : ℝ))) else 0 := by
  unfold shellMassTerm
  split_ifs with hi
  · apply ENNReal.ofReal_le_ofReal
    exact (shellAtom_bounds k (hcoord i)).2
  · rfl

private lemma tsum_cutoff_const (N : ℕ) (c : ℝ≥0∞) :
    (∑' i : ℕ, if i < N then c else 0) = (N : ℝ≥0∞) * c := by
  rw [tsum_eq_sum (s := Finset.range N) (by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [if_neg hi])]
  calc
    (∑ i ∈ Finset.range N, if i < N then c else 0) =
        ∑ _i ∈ Finset.range N, c := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [if_pos (Finset.mem_range.mp hi)]
    _ = (N : ℝ≥0∞) * c := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Pointwise shell-mass bound on the full-measure coordinate event. -/
lemma shellMass_le_count_mul (k : ℕ) :
    ∀ᵐ omega ∂shellLaw,
      shellMass k omega ≤
        (omega.1 : ℝ≥0∞) * ENNReal.ofReal (exp (-(k : ℝ))) := by
  filter_upwards [shellLaw_ae_all_coordinates] with omega hcoord
  unfold shellMass
  calc
    (∑' i : ℕ, shellMassTerm k i omega) ≤
        ∑' i : ℕ,
          if i < omega.1 then ENNReal.ofReal (exp (-(k : ℝ))) else 0 := by
      exact ENNReal.tsum_le_tsum fun i ↦ shellMassTerm_le k i omega hcoord
    _ = (omega.1 : ℝ≥0∞) * ENNReal.ofReal (exp (-(k : ℝ))) :=
      tsum_cutoff_const omega.1 _

/-- The expected mass in shell `k` is at most `e^{-k}`. -/
lemma lintegral_shellMass_le (k : ℕ) :
    (∫⁻ omega, shellMass k omega ∂shellLaw) ≤
      ENNReal.ofReal (exp (-(k : ℝ))) := by
  calc
    (∫⁻ omega, shellMass k omega ∂shellLaw) ≤
        ∫⁻ omega, (omega.1 : ℝ≥0∞) *
          ENNReal.ofReal (exp (-(k : ℝ))) ∂shellLaw :=
      lintegral_mono_ae (shellMass_le_count_mul k)
    _ = (∫⁻ omega, (omega.1 : ℝ≥0∞) ∂shellLaw) *
          ENNReal.ofReal (exp (-(k : ℝ))) := by
      rw [lintegral_mul_const]
      fun_prop
    _ = ENNReal.ofReal (exp (-(k : ℝ))) := by
      rw [lintegral_count_shellLaw, one_mul]

private def geometricRatio : ℝ≥0∞ :=
  ENNReal.ofReal (exp (-1))

private lemma geometricRatio_lt_one : geometricRatio < 1 := by
  rw [geometricRatio, ENNReal.ofReal_lt_one]
  rw [exp_lt_one_iff]
  norm_num

private lemma geometricRatio_ne_top : geometricRatio ≠ ∞ := by
  unfold geometricRatio
  exact ENNReal.ofReal_ne_top

private lemma ofReal_exp_neg_nat_eq_pow (k : ℕ) :
    ENNReal.ofReal (exp (-(k : ℝ))) = geometricRatio ^ k := by
  unfold geometricRatio
  rw [← ENNReal.ofReal_pow (le_of_lt (exp_pos (-1)))]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

private lemma tsum_exp_neg_nat_ne_top :
    (∑' k : ℕ, ENNReal.ofReal (exp (-(k : ℝ)))) ≠ ∞ := by
  simp_rw [ofReal_exp_neg_nat_eq_pow]
  rw [ENNReal.tsum_geometric]
  apply ENNReal.inv_ne_top.mpr
  intro hzero
  exact (not_le_of_gt geometricRatio_lt_one)
    (tsub_eq_zero_iff_le.mp hzero)

/-- Each shell coordinate has the declared shell law under the global product
measure. -/
lemma lintegral_shellMass_global (k : ℕ) :
    (∫⁻ omega, shellMass k (omega k) ∂globalLaw) =
      ∫⁻ eta, shellMass k eta ∂shellLaw := by
  have heval : MeasurePreserving (Function.eval k) globalLaw shellLaw :=
    measurePreserving_eval_infinitePi (fun _ : ℕ ↦ shellLaw) k
  exact heval.lintegral_comp (measurable_shellMass k)

/-- Finite expectation for the actual infinite total mass. -/
lemma lintegral_globalTotalMass_ne_top :
    (∫⁻ omega, globalTotalMass omega ∂globalLaw) ≠ ∞ := by
  have hle : (∫⁻ omega, globalTotalMass omega ∂globalLaw) ≤
      ∑' k : ℕ, ENNReal.ofReal (exp (-(k : ℝ))) := by
    change (∫⁻ omega, ∑' k : ℕ, shellMass k (omega k) ∂globalLaw) ≤ _
    rw [lintegral_tsum]
    · apply ENNReal.tsum_le_tsum
      intro k
      rw [lintegral_shellMass_global]
      exact lintegral_shellMass_le k
    · intro k
      have heval : Measurable (fun omega : GlobalSample ↦ omega k) :=
        measurable_pi_apply k
      exact ((measurable_shellMass k).comp heval).aemeasurable
  exact ne_top_of_le_ne_top tsum_exp_neg_nat_ne_top hle

/-- The scale-invariant Poisson sum is finite almost surely. -/
lemma globalTotalMass_ae_lt_top :
    ∀ᵐ omega ∂globalLaw, globalTotalMass omega < ∞ :=
  ae_lt_top measurable_globalTotalMass lintegral_globalTotalMass_ne_top

end Erdos390.Full.PoissonMass
