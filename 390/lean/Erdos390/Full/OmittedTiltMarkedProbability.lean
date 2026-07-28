import Erdos390.Full.PaperScaleMarkedCell
import Erdos390.Full.PaperTiltSmallness

/-!
# Actual omitted-score marked probabilities

This module joins the paper-scale structured-cell count to the genuine
finite valuation tilt.  The local forced primes are omitted from the score,
so their marked modulus is coprime to every score prime.  No marked-number
asymptotic or normalization estimate remains as an input.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.OmittedTiltMarkedProbability

open ArithmeticModel Scale PrimeSums
open StructuredCells HeadPattern
open DivisibilityMomentBounds FiniteProbability
open PaperScaleMarkedCell PaperTiltSmallness ValuationScoreDomination
open DickmanBasic

noncomputable section

/-- The explicit common majorant for every omitted-score subset of the
moving prime band. -/
def omittedTiltMajorant (B C c : ℝ) (W n : ℕ) : ℝ :=
  Real.exp
      ((B / L n) *
        (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) *
    (B / L n) * ((2 / c) * bandReciprocalSum n W)

theorem eventually_omittedTiltMajorant_nonneg
    (B C c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ omittedTiltMajorant B C c W n := by
  filter_upwards [Filter.eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  have hband : 0 ≤ bandReciprocalSum n W := by
    unfold bandReciprocalSum
    positivity
  unfold omittedTiltMajorant
  exact mul_nonneg
    (mul_nonneg (Real.exp_pos _).le (div_nonneg hB hL.le))
    (mul_nonneg (div_nonneg (by norm_num) hc.le) hband)

/-- For fixed cutoff and box, the exact omitted-score normalizer majorant
tends to zero. -/
theorem tendsto_omittedTiltMajorant_zero
    (B C c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 0 < C)
    (hc : 0 < c) (hW : 1 < W) :
    Tendsto (omittedTiltMajorant B C c W) atTop (𝓝 0) := by
  let Kbound : ℝ := 2 * B / Real.log (W : ℝ)
  let small : ℕ → ℝ := fun n ↦
    (B / L n) * ((2 / c) * bandReciprocalSum n W)
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ ↦ Real.log (L n) / L n)
      atTop (𝓝 0) := by
    exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hmajor : Tendsto
      (fun n : ℕ ↦ (24 * B / c) * (Real.log (L n) / L n))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hratio)
  have hsmallNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ small n := by
    filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    have hL : 0 < L n := L_pos hn
    have hband : 0 ≤ bandReciprocalSum n W := by
      unfold bandReciprocalSum
      positivity
    dsimp only [small]
    exact mul_nonneg (div_nonneg hB hL.le)
      (mul_nonneg (div_nonneg (by norm_num) hc.le) hband)
  have hsmallMajor : ∀ᶠ n : ℕ in atTop,
      small n ≤ (24 * B / c) * (Real.log (L n) / L n) := by
    filter_upwards [eventually_bandReciprocalSum_le_logL W,
      Filter.eventually_gt_atTop 1] with n hband hn
    have hL : 0 < L n := L_pos hn
    have hcoef : 0 ≤ (B / L n) * (2 / c) := by positivity
    dsimp only [small]
    calc
      (B / L n) * ((2 / c) * bandReciprocalSum n W) =
          ((B / L n) * (2 / c)) * bandReciprocalSum n W := by ring
      _ ≤ ((B / L n) * (2 / c)) * (12 * Real.log (L n)) :=
        mul_le_mul_of_nonneg_left hband hcoef
      _ = (24 * B / c) * (Real.log (L n) / L n) := by ring
  have hsmallT : Tendsto small atTop (𝓝 0) :=
    squeeze_zero' hsmallNonneg hsmallMajor hmajor
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hCevent : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop C)
  have hInvCevent : ∀ᶠ n : ℕ in atTop, 1 / C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop (1 / C))
  have hexpBound : ∀ᶠ n : ℕ in atTop,
      Real.exp
          ((B / L n) *
            (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) ≤
        Real.exp Kbound := by
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
    apply Real.exp_le_exp.mpr
    calc
      (B / L n) *
          (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ)) ≤
        (B / L n) * ((2 * L n) / Real.log (W : ℝ)) := by gcongr
      _ = Kbound := by
        dsimp only [Kbound]
        field_simp [hL.ne', hlogW.ne']
  have hupperT : Tendsto (fun n : ℕ ↦ Real.exp Kbound * small n)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hsmallT
  have hmajorNonneg := eventually_omittedTiltMajorant_nonneg B C c W hB hc
  have hmajorLe : ∀ᶠ n : ℕ in atTop,
      omittedTiltMajorant B C c W n ≤ Real.exp Kbound * small n := by
    filter_upwards [hexpBound, hsmallNonneg] with n hexp hsmall
    calc
      omittedTiltMajorant B C c W n =
          Real.exp
              ((B / L n) *
                (Real.log (physicalBound C n : ℝ) /
                  Real.log (W : ℝ))) * small n := by
        unfold omittedTiltMajorant
        dsimp only [small]
        ring
      _ ≤ Real.exp Kbound * small n :=
        mul_le_mul_of_nonneg_right hexp hsmall
  exact squeeze_zero' hmajorNonneg hmajorLe hupperT

/-- A single nonnegative remainder combining the untilted marked-count
error and the omitted-score normalization error. -/
def omittedTiltRemainder (K B C c : ℝ) (W n : ℕ) : ℝ :=
  |K / L n| +
    2 * |omittedTiltMajorant B C c W n| *
      (1 + 1 / rho DickmanBasic.U + |K / L n|)

theorem omittedTiltRemainder_nonneg (K B C c : ℝ) (W n : ℕ) :
    0 ≤ omittedTiltRemainder K B C c W n := by
  unfold omittedTiltRemainder
  have hU : 0 ≤ 1 / rho DickmanBasic.U := one_div_nonneg.mpr rho_U_pos.le
  positivity

theorem tendsto_omittedTiltRemainder_zero
    (K B C c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 0 < C)
    (hc : 0 < c) (hW : 1 < W) :
    Tendsto (omittedTiltRemainder K B C c W) atTop (𝓝 0) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hKL : Tendsto (fun n : ℕ ↦ K / L n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hLTop
  have hmaj := tendsto_omittedTiltMajorant_zero B C c W hB hC hc hW
  have hbracket : Tendsto
      (fun n : ℕ ↦ 1 + 1 / rho DickmanBasic.U + |K / L n|)
      atTop (𝓝 (1 + 1 / rho DickmanBasic.U)) := by
    simpa using tendsto_const_nhds.add hKL.abs
  have hprod : Tendsto
      (fun n : ℕ ↦ 2 * |omittedTiltMajorant B C c W n| *
        (1 + 1 / rho DickmanBasic.U + |K / L n|))
      atTop (𝓝 0) := by
    have htwo : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (𝓝 2) :=
      tendsto_const_nhds
    have := (htwo.mul hmaj.abs).mul hbracket
    simpa using this
  change Tendsto
    (fun n : ℕ ↦ |K / L n| +
      2 * |omittedTiltMajorant B C c W n| *
        (1 + 1 / rho DickmanBasic.U + |K / L n|)) atTop (𝓝 0)
  simpa using hKL.abs.add hprod

/-! ## The actual omitted-score marked law -/

/-- Uniform marked probability under the genuine finite valuation tilt after
omitting every prime dividing the forced modulus.  The same nonnegative
remainder works for every subset of the moving band, every coefficient vector
in the fixed box, and every admissible four-mark modulus. -/
theorem exists_uniform_omittedTilt_divInd_paper_bound
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 1 ≤ C) (B : ℝ) (W : ℕ) (hB : 0 ≤ B) (hW : 1 < W) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧ Tendsto epsilon atTop (𝓝 0) ∧
      ∃ N₀ : ℕ, ∀ {n D : ℕ} (P : Finset ℕ) (eta : ℕ → ℝ),
        N₀ ≤ n → 0 < D → D ≤ yNat n ^ 4 →
        D ∈ Nat.smoothNumbers (yNat n + 1) →
        Nat.Coprime D H.modulus →
        P ⊆ primeBand n W →
        (∀ p ∈ P, Nat.Coprime D p) →
        (∀ p ∈ P, |eta p| ≤ B) →
        let S := structuredCell H (physicalBound A n) (physicalBound C n)
          (yNat n)
        S.Nonempty ∧ ∀ hS : S.Nonempty,
          |((uniformOnFinset S hS).exponentialTilt
                (fun m : S ↦ valuationScore P eta (L n) m)).expect
                (fun m : S ↦ divInd D m) -
              paperDivisibilityMain n D| ≤
            epsilon n / (D : ℝ) := by
  obtain ⟨K, hK, Nbase, hbaseAll⟩ :=
    exists_uniform_uniformAverage_divInd_paper_bound H hA hAC
  obtain ⟨Ndensity, hdensityAll⟩ :=
    exists_structuredCell_density_lower_bound H hA hAC
  let density : ℝ := paperCellDensity H A C
  have hdensity : 0 < density := paperCellDensity_pos H hAC
  let c : ℝ := density / (2 * C)
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hc : 0 < c := div_pos hdensity (mul_pos (by norm_num) hCpos)
  let epsilon : ℕ → ℝ := omittedTiltRemainder K B C c W
  have hepsilon0 : ∀ n, 0 ≤ epsilon n := by
    intro n
    exact omittedTiltRemainder_nonneg K B C c W n
  have hepsilonT : Tendsto epsilon atTop (𝓝 0) := by
    exact tendsto_omittedTiltRemainder_zero K B C c W hB hCpos hc hW
  have hcompEvent :=
    eventually_abs_actual_valuationTilt_divInd_sub_average_le
      B C c W hB hCpos hc hW
  have hmajorT := tendsto_omittedTiltMajorant_zero B C c W hB hCpos hc hW
  have hmajorHalf : ∀ᶠ n : ℕ in atTop,
      omittedTiltMajorant B C c W n ≤ 1 / 2 :=
    hmajorT (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨Ncomp, hNcomp⟩ := Filter.eventually_atTop.mp hcompEvent
  have hhalfReady : ∀ᶠ n : ℕ in atTop,
      1 < n ∧ omittedTiltMajorant B C c W n ≤ 1 / 2 := by
    filter_upwards [Filter.eventually_gt_atTop 1, hmajorHalf] with n hn hhalf
    exact ⟨hn, hhalf⟩
  obtain ⟨Nhalf, hNhalf⟩ := Filter.eventually_atTop.mp hhalfReady
  let N₀ := max Nbase (max Ndensity (max Ncomp Nhalf))
  refine ⟨epsilon, hepsilon0, hepsilonT, N₀, ?_⟩
  intro n D P eta hN hD hD4 hDsmooth hDhead hP hDcop heta
  have hNbase : Nbase ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hNdensity : Ndensity ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hNcomp' : Ncomp ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hNhalf' : Nhalf ≤ n := by
    dsimp only [N₀] at hN
    omega
  obtain ⟨hn, hmajorHalfN⟩ := hNhalf n hNhalf'
  have hcompAll := hNcomp n hNcomp'
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hL : 0 < L n := L_pos hn
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  let S := structuredCell H (physicalBound A n) (physicalBound C n)
    (yNat n)
  obtain ⟨hSnonempty, hbase⟩ :=
    hbaseAll hNbase hD hD4 hDsmooth hDhead
  have hcellDensity := hdensityAll hNdensity
  have hMcast : (physicalBound C n : ℝ) ≤ C * (n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hCpos.le hnR.le)
  have hcard : c * (physicalBound C n : ℝ) ≤ (S.card : ℝ) := by
    calc
      c * (physicalBound C n : ℝ) ≤ c * (C * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hMcast hc.le
      _ = density * (n : ℝ) / 2 := by
        dsimp only [c]
        field_simp [hCpos.ne']
      _ ≤ (S.card : ℝ) := by
        simpa only [S, density] using hcellDensity
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    exact pos_of_mem_smoothInterval (mem_structuredCell.mp hm).1
  have hSle : ∀ m ∈ S, m ≤ physicalBound C n := by
    intro m hm
    exact (mem_smoothInterval.mp (mem_structuredCell.mp hm).1).2.1
  refine ⟨by simpa only [S] using hSnonempty, ?_⟩
  intro hS
  have hS' : S.Nonempty := hS
  have hcomp := hcompAll S P eta D hP hS' hD hcard hSpos hSle hDcop heta
  let T : ℝ := ∑ a ∈ primePowerModuli P (physicalBound C n),
    1 / (a : ℝ)
  let g : ℝ := Real.exp ((B / L n) *
    (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ)))
  let delta : ℝ := g * (B / L n) * ((1 / c) * T)
  let avg : ℝ := uniformAverage S (divInd D)
  let main : ℝ := paperDivisibilityMain n D
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact prime_of_mem_primeBand (hP hp)
  have hTbound : T ≤ 2 * bandReciprocalSum n W := by
    dsimp only [T]
    have hpow := sum_inv_primePowerModuli_le P (physicalBound C n) hprime
    have hPsum : (∑ p ∈ P, 1 / (p : ℝ)) ≤ bandReciprocalSum n W := by
      unfold bandReciprocalSum
      exact Finset.sum_le_sum_of_subset_of_nonneg hP
        (fun p hpBand hpNotP ↦ by positivity)
    exact hpow.trans (mul_le_mul_of_nonneg_left hPsum (by norm_num))
  have hT0 : 0 ≤ T := by
    dsimp only [T]
    positivity
  have hdelta0 : 0 ≤ delta := by
    dsimp only [delta, g]
    positivity
  have hdeltaMajor : delta ≤ omittedTiltMajorant B C c W n := by
    have hfactor : 0 ≤ g * (B / L n) * (1 / c) := by
      dsimp only [g]
      positivity
    calc
      delta = (g * (B / L n) * (1 / c)) * T := by
        dsimp only [delta]
        ring
      _ ≤ (g * (B / L n) * (1 / c)) *
          (2 * bandReciprocalSum n W) :=
        mul_le_mul_of_nonneg_left hTbound hfactor
      _ = omittedTiltMajorant B C c W n := by
        unfold omittedTiltMajorant
        dsimp only [g]
        ring
  have hdeltaHalf : delta ≤ 1 / 2 := hdeltaMajor.trans hmajorHalfN
  have hdenpos : 0 < 1 - delta := by linarith
  have hmainBounds := paperDivisibilityMain_nonneg_le hn hD hD4
  have havg0 : 0 ≤ avg := by
    dsimp only [avg, uniformAverage]
    apply div_nonneg
    · exact Finset.sum_nonneg fun m hm ↦ divInd_nonneg D m
    · positivity
  have havgUpper : avg ≤
      1 / (rho DickmanBasic.U * (D : ℝ)) +
        K / ((D : ℝ) * L n) := by
    have hbaseUpper : avg ≤ main + K / ((D : ℝ) * L n) := by
      have habs : avg - main ≤ K / ((D : ℝ) * L n) :=
        (le_abs_self (avg - main)).trans (by
          simpa only [avg, main, S] using hbase)
      linarith
    dsimp only [main] at hbaseUpper
    linarith [hmainBounds.2]
  have hcomp' :
      |((uniformOnFinset S hS).exponentialTilt
            (fun m : S ↦ valuationScore P eta (L n) m)).expect
            (fun m : S ↦ divInd D m) - avg| ≤
        (delta * (1 / (D : ℝ) + avg)) / (1 - delta) := by
    dsimp only [T, g, delta, avg]
    convert hcomp using 1
    ring
  have hsumUpper : 1 / (D : ℝ) + avg ≤
      (1 + 1 / rho DickmanBasic.U + K / L n) / (D : ℝ) := by
    calc
      1 / (D : ℝ) + avg ≤
          1 / (D : ℝ) +
            (1 / (rho DickmanBasic.U * (D : ℝ)) +
              K / ((D : ℝ) * L n)) := by linarith [havgUpper]
      _ = (1 + 1 / rho DickmanBasic.U + K / L n) / (D : ℝ) := by ring
  have hbracket0 : 0 ≤
      (1 + 1 / rho DickmanBasic.U + K / L n) / (D : ℝ) := by
    have : 0 ≤ 1 / rho DickmanBasic.U := one_div_nonneg.mpr rho_U_pos.le
    positivity
  have hnum : delta * (1 / (D : ℝ) + avg) ≤
      omittedTiltMajorant B C c W n *
        ((1 + 1 / rho DickmanBasic.U + K / L n) / (D : ℝ)) := by
    calc
      delta * (1 / (D : ℝ) + avg) ≤
          delta * ((1 + 1 / rho DickmanBasic.U + K / L n) /
            (D : ℝ)) := mul_le_mul_of_nonneg_left hsumUpper hdelta0
      _ ≤ omittedTiltMajorant B C c W n *
          ((1 + 1 / rho DickmanBasic.U + K / L n) /
            (D : ℝ)) := mul_le_mul_of_nonneg_right hdeltaMajor hbracket0
  have hinvden : 1 / (1 - delta) ≤ 2 := by
    apply (div_le_iff₀ hdenpos).2
    linarith
  have htiltBase :
      |((uniformOnFinset S hS).exponentialTilt
            (fun m : S ↦ valuationScore P eta (L n) m)).expect
            (fun m : S ↦ divInd D m) - avg| ≤
        2 * omittedTiltMajorant B C c W n *
          (1 + 1 / rho DickmanBasic.U + K / L n) / (D : ℝ) := by
    refine hcomp'.trans ?_
    calc
      delta * (1 / (D : ℝ) + avg) / (1 - delta) =
          (delta * (1 / (D : ℝ) + avg)) * (1 / (1 - delta)) := by ring
      _ ≤ (omittedTiltMajorant B C c W n *
          ((1 + 1 / rho DickmanBasic.U + K / L n) / (D : ℝ))) *
            (1 / (1 - delta)) :=
        mul_le_mul_of_nonneg_right hnum (one_div_nonneg.mpr hdenpos.le)
      _ ≤ (omittedTiltMajorant B C c W n *
          ((1 + 1 / rho DickmanBasic.U + K / L n) / (D : ℝ))) * 2 :=
        mul_le_mul_of_nonneg_left hinvden
          (mul_nonneg (hdelta0.trans hdeltaMajor) hbracket0)
      _ = 2 * omittedTiltMajorant B C c W n *
          (1 + 1 / rho DickmanBasic.U + K / L n) / (D : ℝ) := by ring
  have htriangle :
      |((uniformOnFinset S hS).exponentialTilt
            (fun m : S ↦ valuationScore P eta (L n) m)).expect
            (fun m : S ↦ divInd D m) - main| ≤
        |((uniformOnFinset S hS).exponentialTilt
            (fun m : S ↦ valuationScore P eta (L n) m)).expect
            (fun m : S ↦ divInd D m) - avg| + |avg - main| := by
    exact abs_sub_le _ _ _
  have hmajor0 : 0 ≤ omittedTiltMajorant B C c W n :=
    hdelta0.trans hdeltaMajor
  have hKL0 : 0 ≤ K / L n := div_nonneg hK.le hL.le
  calc
    |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ valuationScore P eta (L n) m)).expect
          (fun m : S ↦ divInd D m) - paperDivisibilityMain n D| ≤
      |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ valuationScore P eta (L n) m)).expect
          (fun m : S ↦ divInd D m) - avg| + |avg - main| := by
        simpa only [main] using htriangle
    _ ≤ 2 * omittedTiltMajorant B C c W n *
          (1 + 1 / rho DickmanBasic.U + K / L n) / (D : ℝ) +
        K / ((D : ℝ) * L n) := by
      apply add_le_add htiltBase
      simpa only [avg, main, S] using hbase
    _ = epsilon n / (D : ℝ) := by
      dsimp only [epsilon, omittedTiltRemainder]
      rw [abs_of_nonneg hmajor0, abs_of_nonneg hKL0]
      ring

end

end Erdos390.Full.OmittedTiltMarkedProbability
