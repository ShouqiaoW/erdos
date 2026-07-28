import Erdos390.Full.PaperRawPrefixThirdCumulantFallback
import Erdos390.Full.PrimeSums

/-!
# The raw valuation-score third-cumulant row

For the nuisance moving-prefix row, the score itself supplies one factor
`L⁻¹`.  Consequently the unconditional reciprocal divisor fallback is
already strong enough: after summing the moving prime band, its coefficient
is `O(log L / L)`, and hence still vanishes after multiplication by the one
additional `log L` required by the sharp norm.  This avoids an unnecessary
second chamber/tail splice in Lemma 8.6.
-/

open scoped BigOperators

namespace Erdos390.Full

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability ValuationScoreDomination
open PrimePowerTaylorLedger LocalFugacityBounds PrimeSums

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

/-- A reciprocal divisor expectation bound, summed over the exact finite
valuation-score expansion, gives a full-valuation third-cumulant row.  The
same-prime lcm contribution is retained by the literal finite lcm ledger;
no independence assertion is used. -/
theorem abs_covarianceThirdCentered_valuation_prefix_valuationScore_fallback_le
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (pref : Omega → ℝ) (P : Finset ℕ) (eta : ℕ → ℝ)
    (M p : ℕ) {B G L : ℝ}
    (hpP : p ∈ P) (hB : 0 ≤ B) (hG : 0 ≤ G) (hL : 0 < L)
    (hprime : ∀ q ∈ P, q.Prime)
    (hvaluePos : ∀ omega, 0 < value omega)
    (hvalueLe : ∀ omega, value omega ≤ M)
    (heta : ∀ q ∈ P, |eta q| ≤ B)
    (hpref0 : ∀ omega, 0 ≤ pref omega)
    (hpref1 : ∀ omega, pref omega ≤ 1)
    (hdiv : ∀ D : ℕ, 0 < D →
      mu.expect (fun omega ↦ divInd D (value omega)) ≤ G / (D : ℝ)) :
    |mu.covarianceThirdCentered
        (fun omega ↦ valuation p (value omega)) pref
        (fun omega ↦ valuationScore P eta L (value omega))| ≤
      (B / L) *
        (((8 * G + 16 * G ^ 2) * (∑ q ∈ P, 1 / (q : ℝ)) +
          2 * G * positivePrimePowerLcmConstant) / (p : ℝ)) := by
  have hp := hprime p hpP
  have hF : (fun omega ↦ valuation p (value omega)) =
      fun omega ↦ ∑ r ∈ positiveExponents M,
        divInd (p ^ r) (value omega) := by
    funext omega
    exact valuation_eq_sum_divInd_of_le hp (hvaluePos omega) (hvalueLe omega)
  have hS : (fun omega ↦ valuationScore P eta L (value omega)) =
      fun omega ↦ ∑ q ∈ P, ∑ s ∈ positiveExponents M,
        (eta q / L) * divInd (q ^ s) (value omega) := by
    funext omega
    exact valuationScore_eq_indicator_sum_of_le P eta L hprime
      (hvaluePos omega) (hvalueLe omega)
  have hcomponent (r q s : ℕ) (hq : q ∈ P) :
      |mu.covarianceThirdCentered
          (fun omega ↦ divInd (p ^ r) (value omega)) pref
          (fun omega ↦ divInd (q ^ s) (value omega))| ≤
        2 * G / (Nat.lcm (p ^ r) (q ^ s) : ℝ) +
          4 * G ^ 2 /
            (((p ^ r : ℕ) : ℝ) * ((q ^ s : ℕ) : ℝ)) := by
    have hpr : 0 < p ^ r := pow_pos hp.pos r
    have hqs : 0 < q ^ s := pow_pos (hprime q hq).pos s
    have hraw :=
      mu.abs_covarianceThirdCentered_divInd_prefix_divInd_fallback_le
        value pref hpr hqs hG hpref0 hpref1 hdiv
    calc
      _ ≤ 2 * G / (Nat.lcm (p ^ r) (q ^ s) : ℝ) +
          (G / ((q ^ s : ℕ) : ℝ)) *
            (2 * G / ((p ^ r : ℕ) : ℝ)) +
          (G / ((p ^ r : ℕ) : ℝ)) *
            (2 * G / ((q ^ s : ℕ) : ℝ)) := hraw
      _ = 2 * G / (Nat.lcm (p ^ r) (q ^ s) : ℝ) +
          4 * G ^ 2 /
            (((p ^ r : ℕ) : ℝ) * ((q ^ s : ℕ) : ℝ)) := by
        ring
  rw [hF, hS, mu.covarianceThirdCentered_sum_left]
  simp_rw [mu.covarianceThirdCentered_sum_score,
    mu.covarianceThirdCentered_smul_score]
  calc
    |∑ r ∈ positiveExponents M, ∑ q ∈ P,
        ∑ s ∈ positiveExponents M,
          eta q / L *
            mu.covarianceThirdCentered
              (fun omega ↦ divInd (p ^ r) (value omega)) pref
              (fun omega ↦ divInd (q ^ s) (value omega))| ≤
      ∑ r ∈ positiveExponents M, ∑ q ∈ P,
        ∑ s ∈ positiveExponents M,
          |eta q / L *
            mu.covarianceThirdCentered
              (fun omega ↦ divInd (p ^ r) (value omega)) pref
              (fun omega ↦ divInd (q ^ s) (value omega))| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun r hr ↦
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun q hq ↦
              Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ r ∈ positiveExponents M, ∑ q ∈ P,
        ∑ s ∈ positiveExponents M,
          (B / L) *
            (2 * G / (Nat.lcm (p ^ r) (q ^ s) : ℝ) +
              4 * G ^ 2 /
                (((p ^ r : ℕ) : ℝ) * ((q ^ s : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro s hs
      rw [abs_mul, abs_div, abs_of_pos hL]
      exact mul_le_mul
        (div_le_div_of_nonneg_right (heta q hq) hL.le)
        (hcomponent r q s hq) (abs_nonneg _)
        (div_nonneg hB hL.le)
    _ = (B / L) *
        (2 * G *
            (∑ r ∈ positiveExponents M, ∑ q ∈ P,
              ∑ s ∈ positiveExponents M,
                1 / (Nat.lcm (p ^ r) (q ^ s) : ℝ)) +
          4 * G ^ 2 *
            (∑ r ∈ positiveExponents M, ∑ q ∈ P,
              ∑ s ∈ positiveExponents M,
                1 /
                  (((p ^ r : ℕ) : ℝ) * ((q ^ s : ℕ) : ℝ)))) := by
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      ring
    _ ≤ (B / L) *
        (2 * G *
            ((4 * (∑ q ∈ P, 1 / (q : ℝ)) +
              positivePrimePowerLcmConstant) / (p : ℝ)) +
          4 * G ^ 2 *
            ((2 / (p : ℝ)) *
              (2 * (∑ q ∈ P, 1 / (q : ℝ))))) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hB hL.le)
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hG)
        have hledger :=
          sum_positiveExponents_primePowerModuli_inv_lcm_le
            P M p hpP hprime
        have hrewrite :
            (∑ r ∈ positiveExponents M, ∑ q ∈ P,
              ∑ s ∈ positiveExponents M,
                1 / (Nat.lcm (p ^ r) (q ^ s) : ℝ)) =
              ∑ r ∈ positiveExponents M,
                ∑ a ∈ primePowerModuli P M,
                  1 / (Nat.lcm (p ^ r) a : ℝ) := by
          apply Finset.sum_congr rfl
          intro r hr
          unfold primePowerModuli
          rw [Finset.sum_image]
          · rw [Finset.sum_product]
          · intro a ha b hb hab
            exact primePowerMap_injective hprime ha hb hab
        rw [hrewrite]
        exact hledger
      · apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (by norm_num) (sq_nonneg G))
        let Hp : ℝ := ∑ r ∈ positiveExponents M,
          1 / ((p ^ r : ℕ) : ℝ)
        let U : ℝ := ∑ q ∈ P, ∑ s ∈ positiveExponents M,
          1 / ((q ^ s : ℕ) : ℝ)
        have hprod :
            (∑ r ∈ positiveExponents M, ∑ q ∈ P,
              ∑ s ∈ positiveExponents M,
                1 /
                  (((p ^ r : ℕ) : ℝ) * ((q ^ s : ℕ) : ℝ))) =
              Hp * U := by
          dsimp only [Hp, U]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          ring
        rw [hprod]
        have hHp : Hp ≤ 2 / (p : ℝ) := by
          dsimp only [Hp]
          exact sum_inv_prime_powers_le p M hp.two_le
        have hU : U ≤ 2 * (∑ q ∈ P, 1 / (q : ℝ)) := by
          dsimp only [U]
          have hraw := sum_inv_primePowerModuli_le P M hprime
          rw [sum_inv_primePowerModuli_eq P M hprime] at hraw
          exact hraw
        exact mul_le_mul hHp hU (by dsimp only [U]; positivity)
          (by positivity)
    _ = (B / L) *
        (((8 * G + 16 * G ^ 2) * (∑ q ∈ P, 1 / (q : ℝ)) +
          2 * G * positivePrimePowerLcmConstant) / (p : ℝ)) := by
      ring

end FiniteProbability

namespace PaperRawPrefixThirdCumulantRow

/-- Prime-uniform coefficient of the reciprocal third-cumulant row after
replacing the literal band harmonic sum by `12 log L`. -/
def rawThirdCumulantRateMajorant (B G : ℝ) (n : ℕ) : ℝ :=
  (B / L n) *
    ((8 * G + 16 * G ^ 2) * (12 * Real.log (L n)) +
      2 * G * positivePrimePowerLcmConstant)

/-- The exact finite coefficient in the raw-cell theorem is eventually
bounded by the explicit rate majorant, uniformly in the chosen cutoff
`W`. -/
theorem eventually_rawThirdCumulantCoefficient_le
    (B G : ℝ) (W : ℕ) (hB : 0 ≤ B) (hG : 0 ≤ G) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (B / L n) *
          ((8 * G + 16 * G ^ 2) * bandReciprocalSum n W +
            2 * G * positivePrimePowerLcmConstant) ≤
        rawThirdCumulantRateMajorant B G n := by
  filter_upwards [eventually_bandReciprocalSum_le_logL W,
    Filter.eventually_gt_atTop 1] with n hband hn
  have hcoef : 0 ≤ B / L n := div_nonneg hB (L_pos hn).le
  have hHG : 0 ≤ 8 * G + 16 * G ^ 2 := by positivity
  unfold rawThirdCumulantRateMajorant
  exact mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hband hHG) le_rfl) hcoef

/-- The reciprocal third-cumulant coefficient survives the additional
moving-low harmonic loss `log L`. -/
theorem tendsto_rawThirdCumulantRateMajorant_mul_logL_zero
    (B G : ℝ) :
    Filter.Tendsto (fun n : ℕ ↦
      rawThirdCumulantRateMajorant B G n * Real.log (L n))
      Filter.atTop (nhds 0) := by
  have hLTop : Filter.Tendsto L Filter.atTop Filter.atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq : Filter.Tendsto
      (fun n : ℕ ↦ Real.log (L n) ^ 2 / L n)
      Filter.atTop (nhds 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hone : Filter.Tendsto
      (fun n : ℕ ↦ Real.log (L n) / L n)
      Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  let A₁ : ℝ := 12 * B * (8 * G + 16 * G ^ 2)
  let A₂ : ℝ := 2 * B * G * positivePrimePowerLcmConstant
  have hlimit : Filter.Tendsto (fun n : ℕ ↦
      A₁ * (Real.log (L n) ^ 2 / L n) +
        A₂ * (Real.log (L n) / L n))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero, zero_add] using
      (tendsto_const_nhds.mul hsq).add (tendsto_const_nhds.mul hone)
  apply hlimit.congr'
  filter_upwards [Filter.eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  unfold rawThirdCumulantRateMajorant
  dsimp only [A₁, A₂]
  field_simp [hL.ne']

/-- Raw-cell specialization, simultaneous in the band prime, coefficient
box, and moving prefix.  Only the already proved reciprocal cell-density
fallback is used. -/
theorem exists_uniform_rawCell_valuationScore_thirdCumulant_bound
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) :
    ∃ G : ℝ, 0 < G ∧ ∃ N₀ : ℕ, ∀ {n W p k : ℕ}
      {B : ℝ} (eta : ℕ → ℝ),
      N₀ ≤ n → p ∈ primeBand n W → 0 ≤ B →
      (∀ q ∈ primeBand n W, |eta q| ≤ B) →
      let S := structuredCell H (physicalBound A n) (physicalBound C n)
        (yNat n)
      ∀ hS : S.Nonempty,
        |(uniformOnFinset S hS).covarianceThirdCentered
            (fun m : S ↦ valuation p (m : ℕ))
            (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)
            (fun m : S ↦ valuationScore (primeBand n W) eta (L n)
              (m : ℕ))| ≤
          (B / L n) *
            (((8 * G + 16 * G ^ 2) *
                (∑ q ∈ primeBand n W, 1 / (q : ℝ)) +
              2 * G * positivePrimePowerLcmConstant) / (p : ℝ)) := by
  obtain ⟨G, hG, Ndiv, hdiv⟩ :=
    PaperRawPrefixThirdCumulantFallback.exists_uniform_rawCell_divInd_fallback
      H hA hAC hC
  refine ⟨G, hG, max 2 Ndiv, ?_⟩
  intro n W p k B eta hN hpBand hB heta
  have hn : 1 < n := by omega
  have hNdiv : Ndiv ≤ n := by omega
  let M := physicalBound C n
  let S := structuredCell H (physicalBound A n) M (yNat n)
  change ∀ hS : S.Nonempty, _
  intro hS
  let mu := uniformOnFinset S hS
  let pref : S → ℝ := fun m ↦ if (m : ℕ) ≤ k then 1 else 0
  have hvaluePos : ∀ m : S, 0 < (m : ℕ) := by
    intro m
    exact pos_of_mem_smoothInterval (mem_structuredCell.mp m.property).1
  have hvalueLe : ∀ m : S, (m : ℕ) ≤ M := by
    intro m
    exact (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1
  have hpref0 : ∀ m : S, 0 ≤ pref m := by
    intro m
    dsimp only [pref]
    split_ifs <;> norm_num
  have hpref1 : ∀ m : S, pref m ≤ 1 := by
    intro m
    dsimp only [pref]
    split_ifs <;> norm_num
  have hdivAll (D : ℕ) (hD : 0 < D) :
      mu.expect (fun m : S ↦ divInd D (m : ℕ)) ≤ G / (D : ℝ) := by
    simpa only [S, M, mu] using hdiv hNdiv hS D hD
  have hraw :=
    mu.abs_covarianceThirdCentered_valuation_prefix_valuationScore_fallback_le
      (fun m : S ↦ (m : ℕ)) pref (primeBand n W) eta M p
      hpBand hB hG.le (L_pos hn)
      (fun q hq ↦ prime_of_mem_primeBand hq)
      hvaluePos hvalueLe heta hpref0 hpref1 hdivAll
  simpa only [S, M, mu, pref] using hraw

end PaperRawPrefixThirdCumulantRow

end

end Erdos390.Full
