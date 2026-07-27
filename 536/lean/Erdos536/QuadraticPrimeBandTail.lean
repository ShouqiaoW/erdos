import Erdos536.PrimeBandBase
import Erdos536.QuadraticPrimeBand
import Erdos536.PrimeBandTimeChange

/-!
# Deep normalized-weight tails on the quadratic prime band

At normalized scale `T²`, primes of depth greater than `R` have total
one-label logarithmic first moment asymptotic to at most `exp (-R) / 3`.
The proof embeds the relevant part of the corrected quadratic band into
the broad band already treated in `PrimeBandTimeChange`.
-/

open scoped BigOperators Nat.Prime
open Filter Topology

noncomputable section

namespace Erdos536

open PrimeSums
open PrimeBandTimeChange

/-- The part of the quadratic band strictly beyond normalized depth `R`. -/
noncomputable def quadraticDeepPrimeBand
    (T : ℕ) (a R : ℝ) : Finset ℕ :=
  (quadraticPrimeBand T a).filter fun p ↦
    R < normalizedLogDepth ((T ^ 2 : ℕ) : ℝ) p

@[simp]
theorem mem_quadraticDeepPrimeBand
    {T p : ℕ} {a R : ℝ} :
    p ∈ quadraticDeepPrimeBand T a R ↔
      p ∈ quadraticPrimeBand T a ∧
        R < normalizedLogDepth ((T ^ 2 : ℕ) : ℝ) p := by
  simp [quadraticDeepPrimeBand]

/-- Deep quadratic-band primes lie in the corresponding broad tail. -/
theorem quadraticDeepPrimeBand_subset_broad
    {T : ℕ} (hT : 0 < T) {a R : ℝ}
    (hsquare : T ^ 2 ≤ quadraticLowerCutoff T) :
    quadraticDeepPrimeBand T a R ⊆
      broadPrimeBand (T ^ 2) (depthCoordinate R) := by
  intro p hp
  have hpDeep := mem_quadraticDeepPrimeBand.mp hp
  have hpBand := mem_quadraticPrimeBand.mp hpDeep.1
  have hN : 0 < T ^ 2 := pow_pos hT _
  have hNR : (0 : ℝ) < (T ^ 2 : ℕ) := by
    exact_mod_cast hN
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast hpBand.1.pos
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hpBand.1.one_lt)
  have hu :
      0 < normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p := by
    unfold normalizedLogWeight
    exact div_pos hlogp hNR
  have hlogu :
      Real.log
          (normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p) <
        -R := by
    unfold normalizedLogDepth at hpDeep
    linarith [hpDeep.2]
  have huUpper :
      normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p <
        depthCoordinate R := by
    unfold depthCoordinate
    have hexp := Real.exp_lt_exp.mpr hlogu
    simpa only [Real.exp_log hu] using hexp
  have hlogUpper :
      Real.log (p : ℝ) <
        ((T ^ 2 : ℕ) : ℝ) * depthCoordinate R := by
    unfold normalizedLogWeight at huUpper
    simpa only [mul_comm] using
      (div_lt_iff₀ hNR).mp huUpper
  have hpUpperReal :
      (p : ℝ) <
        Real.exp
          (((T ^ 2 : ℕ) : ℝ) * depthCoordinate R) := by
    calc
      (p : ℝ) = Real.exp (Real.log (p : ℝ)) :=
        (Real.exp_log hpR).symm
      _ < _ := Real.exp_lt_exp.mpr hlogUpper
  have hpUpper :
      p ≤ expEndpoint (depthCoordinate R) (T ^ 2) := by
    have hceil :
        (p : ℝ) ≤
          (expEndpoint (depthCoordinate R) (T ^ 2) : ℝ) :=
      hpUpperReal.le.trans (Nat.le_ceil _)
    exact_mod_cast hceil
  apply mem_broadPrimeBand.mpr
  exact
    ⟨hpBand.1,
      hsquare.trans_lt hpBand.2.1,
      hpUpper⟩

/-- The expected normalized weight of one specified active label on the
deep part of the corrected quadratic band. -/
noncomputable def quadraticDeepOneLabelMean
    (T : ℕ) (a R : ℝ) : ℝ :=
  ∑ p ∈ quadraticDeepPrimeBand T a R,
    reciprocalBernoulli p / 3 *
      normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p

theorem eventually_quadraticDeepOneLabelMean_le
    (a R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℕ in atTop,
      quadraticDeepOneLabelMean T a R ≤
        (depthCoordinate R + ε) / 3 := by
  have hpow :
      Tendsto (fun T : ℕ => T ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have htail :=
    hpow.eventually
      (eventually_deepTailShiftedLogMoment_le R hε)
  have hendpointBase :
      ∀ᶠ N : ℕ in atTop,
        N ≤ expEndpoint (depthCoordinate R) N := by
    have hgrowth :
        Tendsto
          (fun x : ℝ =>
            Real.exp (depthCoordinate R * x) / x ^ (1 : ℝ))
          atTop atTop :=
      tendsto_exp_mul_div_rpow_atTop
        1 (depthCoordinate R) (depthCoordinate_pos R)
    have hnat := hgrowth.comp tendsto_natCast_atTop_atTop
    filter_upwards [
      hnat.eventually (eventually_ge_atTop (1 : ℝ)),
      eventually_gt_atTop 0] with N hratio hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hratio' :
        (1 : ℝ) ≤
          Real.exp
              (depthCoordinate R * (N : ℝ)) / (N : ℝ) := by
      simpa only [Function.comp_apply, Real.rpow_one] using hratio
    have hexp :
        (N : ℝ) ≤
          Real.exp ((N : ℝ) * depthCoordinate R) := by
      have h := (le_div_iff₀ hNR).mp hratio'
      calc
        (N : ℝ) ≤
            Real.exp
              (depthCoordinate R * (N : ℝ)) := by
          simpa only [one_mul] using h
        _ = _ := by
          congr 1
          ring
    exact_mod_cast hexp.trans (Nat.le_ceil _)
  have hendpoint := hpow.eventually hendpointBase
  filter_upwards [
    htail, hendpoint, eventually_ge_atTop 1] with
      T htailT hendpointT hT
  have hsquare :
      T ^ 2 ≤ quadraticLowerCutoff T :=
    quadraticScale_le_lowerCutoff hT
  have hN : 0 < T ^ 2 := pow_pos hT _
  have hNR : (0 : ℝ) < (T ^ 2 : ℕ) := by
    exact_mod_cast hN
  have hsubset :=
    quadraticDeepPrimeBand_subset_broad
      (a := a) (R := R) hT hsquare
  have hsum :
      quadraticDeepOneLabelMean T a R ≤
        broadBandShiftedLogMoment
            (T ^ 2) (depthCoordinate R) / 3 := by
    rw [deepTailShiftedLogMoment_eq_sum
      R hendpointT]
    unfold quadraticDeepOneLabelMean
    calc
      (∑ p ∈ quadraticDeepPrimeBand T a R,
          reciprocalBernoulli p / 3 *
            normalizedLogWeight
              ((T ^ 2 : ℕ) : ℝ) p) =
        ∑ p ∈ quadraticDeepPrimeBand T a R,
          (Real.log (p : ℝ) / ((p : ℝ) + 1)) /
            ((T ^ 2 : ℕ) : ℝ) / 3 := by
          apply Finset.sum_congr rfl
          intro p _hp
          unfold reciprocalBernoulli normalizedLogWeight
          ring
      _ ≤
        ∑ p ∈ broadPrimeBand
              (T ^ 2) (depthCoordinate R),
          (Real.log (p : ℝ) / ((p : ℝ) + 1)) /
            ((T ^ 2 : ℕ) : ℝ) / 3 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro p hpBroad _hpDeep
          have hpPrime :=
            (mem_broadPrimeBand.mp hpBroad).1
          have hpLog :
              0 ≤ Real.log (p : ℝ) :=
            Real.log_nonneg (by
              exact_mod_cast hpPrime.one_le)
          positivity
      _ =
        ((∑ p ∈ broadPrimeBand
              (T ^ 2) (depthCoordinate R),
            Real.log (p : ℝ) / ((p : ℝ) + 1)) /
              ((T ^ 2 : ℕ) : ℝ)) / 3 := by
          rw [Finset.sum_div, Finset.sum_div]
  exact hsum.trans (div_le_div_of_nonneg_right
    htailT (by norm_num))

/-- A small exact numerical bound used for the depth-`75` tail. -/
theorem exp_neg_seventyFive_lt :
    Real.exp (-75) < (1 / 10000 : ℝ) := by
  have hexp :
      (10000 : ℝ) < Real.exp 75 := by
    refine lt_of_lt_of_le ?_
      (Real.sum_le_exp_of_nonneg (by norm_num) 4)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [Real.exp_neg]
  simpa only [one_div] using
    one_div_lt_one_div_of_lt (by norm_num) hexp

/-- Concrete one-label mean bound below normalized depth `75`. -/
theorem eventually_quadraticDeepOneLabelMean_le_one_div_fifteenThousand
    (a : ℝ) :
    ∀ᶠ T : ℕ in atTop,
      quadraticDeepOneLabelMean T a 75 ≤
        (1 / 15000 : ℝ) := by
  have htail :=
    eventually_quadraticDeepOneLabelMean_le
      a 75 (show (0 : ℝ) < 1 / 10000 by norm_num)
  filter_upwards [htail] with T htailT
  unfold depthCoordinate at htailT
  have hexp := exp_neg_seventyFive_lt
  linarith

end Erdos536
