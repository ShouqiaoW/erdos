import Erdos390.Full.TwoLocalRestorationBound

/-!
# Paper-scale stability of the two-local normalizer

The exact restoration quotient is useful only after its denominator is shown
uniformly away from zero.  This file performs that quantifier step at the
actual paper scale.  The fallback density-ratio constant is first bounded by
a fixed `B,W,c` ceiling, and the two coefficient tails then tend uniformly to
zero over the moving prime band.
-/

open Filter Topology

namespace Erdos390.Full.PaperTwoLocalRestorationBound

open ArithmeticModel Scale LocalFugacityBounds PaperValuationCutoff
open ValuationCutoff
open TwoLocalRestorationBound

noncomputable section

/-- The exact reciprocal-event constant produced by the arbitrary-modulus
omitted-tilt fallback at the paper endpoint. -/
def paperPairFallbackConstant (B C c : ℝ) (W n : ℕ) : ℝ :=
  Real.exp (2 * ((B / L n) *
    (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ)))) / c

/-- A fixed ceiling for the preceding constant. -/
def paperPairFallbackCeiling (B c : ℝ) (W : ℕ) : ℝ :=
  Real.exp (4 * B / Real.log (W : ℝ)) / c

theorem paperPairFallbackConstant_nonneg (B C c : ℝ) (W n : ℕ)
    (hc : 0 ≤ c) :
    0 ≤ paperPairFallbackConstant B C c W n := by
  unfold paperPairFallbackConstant
  positivity

theorem paperPairFallbackCeiling_pos (B c : ℝ) (W : ℕ) (hc : 0 < c) :
    0 < paperPairFallbackCeiling B c W := by
  unfold paperPairFallbackCeiling
  positivity

/-- The moving physical endpoint contributes no `n`-dependent loss to the
fallback density-ratio constant. -/
theorem eventually_paperPairFallbackConstant_le
    (B C c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 0 < C)
    (hc : 0 < c) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop,
      paperPairFallbackConstant B C c W n ≤
        paperPairFallbackCeiling B c W := by
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hCevent : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop C)
  have hInvCevent : ∀ᶠ n : ℕ in atTop, 1 / C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop (1 / C))
  filter_upwards [hCevent, hInvCevent, Filter.eventually_gt_atTop 1]
    with n hCn hInvCn hn
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hL : 0 < L n := L_pos hn
  have hlogW : 0 < Real.log (W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  have hphysLower : 1 ≤ physicalBound C n := by
    unfold physicalBound
    apply Nat.le_floor
    have hOne : (1 : ℝ) ≤ C * (n : ℝ) := by
      have := (div_le_iff₀ hC).mp hInvCn
      simpa [mul_comm] using this
    exact_mod_cast hOne
  have hphysPos : 0 < physicalBound C n :=
    lt_of_lt_of_le Nat.zero_lt_one hphysLower
  have hphysCast : (physicalBound C n : ℝ) ≤ C * (n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hC.le (by positivity))
  have hCnSq : C * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hlogPhys : Real.log (physicalBound C n : ℝ) ≤ 2 * L n := by
    have hleSq : (physicalBound C n : ℝ) ≤ (n : ℝ) ^ 2 :=
      hphysCast.trans hCnSq
    have hlog := Real.log_le_log (by exact_mod_cast hphysPos) hleSq
    rw [Real.log_pow] at hlog
    simpa [L] using hlog
  have hK : 2 * ((B / L n) *
      (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) ≤
      4 * B / Real.log (W : ℝ) := by
    calc
      _ ≤ 2 * ((B / L n) *
          ((2 * L n) / Real.log (W : ℝ))) := by gcongr
      _ = 4 * B / Real.log (W : ℝ) := by
        field_simp [hL.ne', hlogW.ne']
        ring
  unfold paperPairFallbackConstant paperPairFallbackCeiling
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hK) hc.le

/-- Uniformly over both moving band primes and all local coefficients in the
fixed box, the actual two-local normalizer error is eventually at most one
half. -/
theorem eventually_pairRestorationError_zero_le_half
    (B C c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 0 < C)
    (hc : 0 < c) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      ∀ etaP etaQ : ℝ, |etaP| ≤ B → |etaQ| ≤ B →
      pairRestorationError p q
        (valuationCutoff p (physicalBound C n))
        (valuationCutoff q (physicalBound C n)) 0 0 etaP etaQ (L n)
        (paperPairFallbackConstant B C c W n) ≤ 1 / 2 := by
  let k : ℕ → ℝ := fun n ↦
    (2 * B / L n) * Real.exp (2 * B / Real.log (W : ℝ))
  let G0 : ℝ := paperPairFallbackCeiling B c W
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hInv : Tendsto (fun n : ℕ ↦ (L n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hLTop
  have hkT : Tendsto k atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦
        (2 * B) * Real.exp (2 * B / Real.log (W : ℝ))) atTop
        (𝓝 ((2 * B) * Real.exp (2 * B / Real.log (W : ℝ)))) :=
      tendsto_const_nhds
    have hmul := hconst.mul hInv
    rw [show k = fun n : ℕ ↦
        ((2 * B) * Real.exp (2 * B / Real.log (W : ℝ))) * (L n)⁻¹ by
      funext n
      dsimp only [k]
      ring]
    simpa using hmul
  have hmajorT : Tendsto (fun n ↦ G0 * (2 * k n + (k n) ^ 2))
      atTop (𝓝 0) := by
    have hpoly : Tendsto (fun n ↦ 2 * k n + (k n) ^ 2) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hkT).add (hkT.pow 2)
    simpa using tendsto_const_nhds.mul hpoly
  have hmajorHalf : ∀ᶠ n : ℕ in atTop,
      G0 * (2 * k n + (k n) ^ 2) ≤ 1 / 2 :=
    hmajorT (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_paperPairFallbackConstant_le B C c W
      hB hC hc hW,
    eventually_coefficientTail_le_of_pos B C W hB hC hW,
    hmajorHalf, Filter.eventually_gt_atTop 1] with n hG hcoef hhalf hn
  intro p hpBand q hqBand etaP etaQ hetaP hetaQ
  let G := paperPairFallbackConstant B C c W n
  let dp := coefficientTail p (valuationCutoff p (physicalBound C n))
    0 etaP (L n)
  let dq := coefficientTail q (valuationCutoff q (physicalBound C n))
    0 etaQ (L n)
  have hdp0 : 0 ≤ dp := coefficientTail_nonneg _ _ _ _ _
  have hdq0 : 0 ≤ dq := coefficientTail_nonneg _ _ _ _ _
  have hk0 : 0 ≤ k n := by
    dsimp only [k]
    have hL := L_pos hn
    positivity
  have hdp : dp ≤ k n := by
    have h := hcoef p hpBand etaP hetaP 0
    simpa only [dp, k, Nat.cast_zero, zero_add, pow_zero, div_one, mul_one]
      using h
  have hdq : dq ≤ k n := by
    have h := hcoef q hqBand etaQ hetaQ 0
    simpa only [dq, k, Nat.cast_zero, zero_add, pow_zero, div_one, mul_one]
      using h
  have hG0 : 0 ≤ G := paperPairFallbackConstant_nonneg B C c W n hc.le
  have hG00 : 0 ≤ G0 := (paperPairFallbackCeiling_pos B c W hc).le
  have hG' : G ≤ G0 := by simpa only [G, G0] using hG
  have herr : G * dp + G * dq + G * dp * dq ≤ 1 / 2 := by
    calc
      G * dp + G * dq + G * dp * dq ≤
        G0 * dp + G0 * dq + G0 * dp * dq := by
        exact add_le_add_three
          (mul_le_mul_of_nonneg_right hG' hdp0)
          (mul_le_mul_of_nonneg_right hG' hdq0)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hG' hdp0) hdq0)
      _ ≤ G0 * k n + G0 * k n + G0 * (k n) * (k n) := by
        exact add_le_add_three
          (mul_le_mul_of_nonneg_left hdp hG00)
          (mul_le_mul_of_nonneg_left hdq hG00)
          (mul_le_mul
            (mul_le_mul_of_nonneg_left hdp hG00) hdq
            hdq0 (mul_nonneg hG00 hk0))
      _ = G0 * (2 * k n + (k n) ^ 2) := by ring
      _ ≤ 1 / 2 := hhalf
  simpa [pairRestorationError, G, dp, dq] using herr

end

end Erdos390.Full.PaperTwoLocalRestorationBound
