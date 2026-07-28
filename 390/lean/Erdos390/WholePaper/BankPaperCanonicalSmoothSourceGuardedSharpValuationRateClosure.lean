import Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedRateClosure
import Erdos390.Full.PaperRawTiltedValuationMeanRows
import Erdos390.Full.PaperRawPrefixThirdCumulantFallback
import Erdos390.Full.PaperCanonicalTiltedPrefixRows

/-!
# Sharp valuation-rate ingredients for the smooth source

This file begins the analytic lift left explicit by
`BankPaperCanonicalSmoothSourceGuardedRateClosure`.

The first theorem below is the sharp un-tilted full-valuation profile for one
fixed raw structured cell.  It is obtained only from already proved inputs:

* the common `paperDivisibilityMain` law through `yNat n ^ 4`;
* the arbitrary-divisor reciprocal fallback;
* the finite prime-power tail identity; and
* the sharp conversion of the `yNat n ^ 4` tail to `1 / (p * L n)`.

No full-valuation comparison is assumed.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.Scale
open Erdos390.Full.HeadPattern
open Erdos390.Full.StructuredCells
open Erdos390.Full.FiniteProbability
open Erdos390.Full.PrimePowerCovariance
open Erdos390.Full.PrimePowerCutoffCovariance
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.PaperMovingPrefixMarkedCell
open Erdos390.Full.PaperPrimePowerTailRate
open Erdos390.Full.PaperRawPrefixThirdCumulantFallback
open Erdos390.Full.PaperRawTiltedValuationMeanRows
open Erdos390.Full.LocalFugacityBounds
open Erdos390.Full.ValuationScoreDomination
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.GuardedUniformCell
open Erdos390.Full.GuardDeletionSquarefreeProfiles
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.PaperCanonicalTiltedPrefixRows

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## Fixed raw structured cells -/

/-- The genuine full valuation on one fixed raw structured cell has the
common truncated Dickman profile with the sharp `1 / (p * L)` error.

The returned nonemptiness witness is produced by the marked-cell theorem;
it is not an additional premise. -/
theorem
    exists_uniform_rawStructuredCell_valuation_mean_profile_paperRate
    (P : Pattern) {A C : Real}
    (hA : 0 < A) (hAC : A < C) (hC : 0 < C)
    (W : Nat) (_hW : 1 < W)
    (hHeadLe : ∀ q ∈ P.primes, q ≤ W) :
    ∃ Cval : Real, 0 < Cval ∧ ∃ N₀ : Nat,
      ∀ {n p : Nat}, N₀ ≤ n → p ∈ primeBand n W →
        let S := structuredCell P
          (physicalBound A n) (physicalBound C n) (yNat n)
        let Kcut := Nat.log p (yNat n ^ 4)
        ∃ hS : S.Nonempty,
          |(uniformOnFinset S hS).expect
                (fun m ↦ valuation p (m : Nat)) -
            ∑ k ∈ positiveExponents Kcut,
              paperDivisibilityMain n (p ^ k)| ≤
            Cval / ((p : Real) * L n) := by
  obtain ⟨K, hK, Nprofile, hprofile⟩ :=
    PaperScaleMarkedCell.exists_uniform_uniformAverage_divInd_paper_bound
      P hA hAC
  obtain ⟨G, hG, Nfallback, hfallback⟩ :=
    PaperRawPrefixThirdCumulantFallback.exists_uniform_rawCell_divInd_fallback
      P hA hAC hC
  have htailSharp :=
    PaperPrimePowerTailRate.eventually_mul_two_div_yNat_pow_four_le_sharp
  have hgood : ∀ᶠ n : Nat in atTop,
      (∀ p : Nat, 0 < p → p ≤ yNat n → ∀ H : Real, 0 ≤ H →
        H * (2 / ((yNat n ^ 4 : Nat) : Real)) ≤
          ((2 * H) / L n) * (1 / (p : Real))) ∧
      1 < n := by
    filter_upwards [htailSharp, Filter.eventually_gt_atTop 1]
      with n htail hn
    exact ⟨htail, hn⟩
  obtain ⟨Ngood, hNgood⟩ := Filter.eventually_atTop.mp hgood
  let Cval : Real := 2 * K + 2 * G
  have hCval : 0 < Cval := by
    dsimp only [Cval]
    positivity
  refine ⟨Cval, hCval, max Nprofile (max Nfallback Ngood), ?_⟩
  intro n p hN hpBand
  dsimp only
  have hNprofile : Nprofile ≤ n := by omega
  have hNfallback : Nfallback ≤ n := by omega
  have hNgoodBound : Ngood ≤ n := by omega
  obtain ⟨htailSharpN, hn⟩ := hNgood n hNgoodBound
  have hp := prime_of_mem_primeBand hpBand
  have hpR : (0 : Real) < p := by exact_mod_cast hp.pos
  have hpY : p ≤ yNat n := le_yNat_of_mem_primeBand hpBand
  have hp4 : p ≤ yNat n ^ 4 :=
    hpY.trans (Nat.le_pow (by omega : 0 < 4))
  have hpSmooth : p ∈ Nat.smoothNumbers (yNat n + 1) :=
    Nat.mem_smoothNumbers_of_lt hp.pos (Nat.lt_succ_of_le hpY)
  have hpHead : Nat.Coprime p P.modulus :=
    PaperPrimePowerAuxiliaryPrime.coprime_modulus_of_mem_primeBand_of_headSupport
      P hHeadLe hpBand
  let S := structuredCell P
    (physicalBound A n) (physicalBound C n) (yNat n)
  let Kcut : Nat := Nat.log p (yNat n ^ 4)
  let main : Nat → Real := fun k ↦
    paperDivisibilityMain n (p ^ k)
  let mainSum : Real := ∑ k ∈ positiveExponents Kcut, main k
  have hprofileP :=
    hprofile (n := n) (d := p) hNprofile hp.pos hp4 hpSmooth hpHead
  have hS : S.Nonempty := by
    simpa only [S] using hprofileP.1
  refine ⟨hS, ?_⟩
  let mu := uniformOnFinset S hS
  let trunc : S → Real := fun m ↦
    ∑ k ∈ positiveExponents Kcut, divInd (p ^ k) (m : Nat)
  let tail : S → Real := fun m ↦ valuation p (m : Nat) - trunc m
  have hprofilePower (k : Nat)
      (hk : k ∈ positiveExponents Kcut) :
      |mu.expect (fun m ↦ divInd (p ^ k) (m : Nat)) - main k| ≤
        K / (((p ^ k : Nat) : Real) * L n) := by
    have hkLe : k ≤ Kcut := (mem_positiveExponents.mp hk).2
    have hY4pos : 0 < yNat n ^ 4 :=
      pow_pos (hp.pos.trans_le hpY) 4
    have hpK : p ^ Kcut ≤ yNat n ^ 4 :=
      Nat.pow_log_le_self p hY4pos.ne'
    have hpk4 : p ^ k ≤ yNat n ^ 4 :=
      (Nat.pow_le_pow_right hp.pos hkLe).trans hpK
    have hpkSmooth := StructuredCells.pow_mem_smoothNumbers hpSmooth k
    have hpkHead := hpHead.pow_left k
    have hraw :=
      (hprofile (n := n) (d := p ^ k) hNprofile
        (pow_pos hp.pos k) hpk4 hpkSmooth hpkHead).2
    rw [OmittedScoreCell.uniform_expect_eq_uniformAverage]
    simpa only [S, mu, main] using hraw
  have hdiv (D : Nat) (hD : 0 < D) :
      mu.expect (fun m ↦ divInd D (m : Nat)) ≤
        G * (1 / (D : Real)) := by
    have hraw := hfallback hNfallback hS D hD
    simpa only [S, mu, div_eq_mul_inv, one_mul] using hraw
  have hvaluePos : ∀ m : S, 0 < (m : Nat) := by
    intro m
    exact pos_of_mem_smoothInterval (mem_structuredCell.mp m.property).1
  have hvalueLe : ∀ m : S, (m : Nat) ≤ physicalBound C n := by
    intro m
    exact
      (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1
  have htailRaw :=
    PaperRawTiltedValuationMeanRows.PrimePowerTail.abs_expect_valuation_sub_cutoff_le_of_divisor_fallback_unrestricted
        mu (fun m : S ↦ (m : Nat)) hp hvaluePos hvalueLe hG.le hdiv
        (Kcut := Kcut)
  have hpowNat : yNat n ^ 4 < p ^ (Kcut + 1) := by
    simpa only [Kcut, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self hp.one_lt (yNat n ^ 4)
  have hpow : ((yNat n ^ 4 : Nat) : Real) ≤
      (p : Real) ^ (Kcut + 1) := by
    exact_mod_cast hpowNat.le
  have hY4real : (0 : Real) < (yNat n ^ 4 : Nat) := by
    exact_mod_cast pow_pos (hp.pos.trans_le hpY) 4
  have hrecip : 2 / (p : Real) ^ (Kcut + 1) ≤
      2 / ((yNat n ^ 4 : Nat) : Real) :=
    div_le_div_of_nonneg_left (by norm_num) hY4real hpow
  have htail :
      |mu.expect tail| ≤ ((2 * G) / L n) * (1 / (p : Real)) := by
    have hfirst :
        |mu.expect (fun m ↦
            valuation p (m : Nat) -
              ∑ k ∈ positiveExponents Kcut,
                divInd (p ^ k) (m : Nat))| ≤
          G * (2 / (p : Real) ^ (Kcut + 1)) := by
      exact htailRaw
    calc
      |mu.expect tail| ≤
          G * (2 / (p : Real) ^ (Kcut + 1)) := by
        simpa only [tail, trunc] using hfirst
      _ ≤ G * (2 / ((yNat n ^ 4 : Nat) : Real)) :=
        mul_le_mul_of_nonneg_left hrecip hG.le
      _ ≤ ((2 * G) / L n) * (1 / (p : Real)) :=
        htailSharpN p hp.pos hpY G hG.le
  have hsumReciprocal :
      (∑ k ∈ positiveExponents Kcut,
          1 / (((p ^ k : Nat) : Real))) ≤
        2 / (p : Real) :=
    sum_inv_prime_powers_le p Kcut hp.two_le
  have htruncExpand :
      mu.expect trunc =
        ∑ k ∈ positiveExponents Kcut,
          mu.expect (fun m ↦ divInd (p ^ k) (m : Nat)) := by
    exact
      PrimePowerCutoffCovariance.FiniteProbability.expect_sum mu
        (positiveExponents Kcut)
        (fun k m ↦ divInd (p ^ k) (m : Nat))
  have htrunc :
      |mu.expect trunc - mainSum| ≤
        ((2 * K) / L n) * (1 / (p : Real)) := by
    rw [htruncExpand]
    dsimp only [mainSum]
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ k ∈ positiveExponents Kcut,
          (mu.expect (fun m ↦ divInd (p ^ k) (m : Nat)) - main k)| ≤
        ∑ k ∈ positiveExponents Kcut,
          |mu.expect (fun m ↦ divInd (p ^ k) (m : Nat)) - main k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ positiveExponents Kcut,
          K / (((p ^ k : Nat) : Real) * L n) := by
        exact Finset.sum_le_sum fun k hk ↦ hprofilePower k hk
      _ = (K / L n) *
          (∑ k ∈ positiveExponents Kcut,
            1 / (((p ^ k : Nat) : Real))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring
      _ ≤ (K / L n) * (2 / (p : Real)) := by
        exact mul_le_mul_of_nonneg_left hsumReciprocal
          (div_nonneg hK.le (L_pos hn).le)
      _ = ((2 * K) / L n) * (1 / (p : Real)) := by ring
  have hexpect :
      mu.expect (fun m ↦ valuation p (m : Nat)) =
        mu.expect trunc + mu.expect tail := by
    have hpoint : (fun m : S ↦ (valuation p (m : Nat) : Real)) =
        fun m ↦ trunc m + tail m := by
      funext m
      dsimp only [tail]
      ring
    rw [hpoint, mu.expect_add]
  change
    |mu.expect (fun m ↦ valuation p (m : Nat)) - mainSum| ≤
      Cval / ((p : Real) * L n)
  rw [hexpect]
  calc
    |mu.expect trunc + mu.expect tail - mainSum| =
        |(mu.expect trunc - mainSum) + mu.expect tail| := by ring_nf
    _ ≤ |mu.expect trunc - mainSum| + |mu.expect tail| :=
      abs_add_le _ _
    _ ≤ ((2 * K) / L n) * (1 / (p : Real)) +
        ((2 * G) / L n) * (1 / (p : Real)) :=
      add_le_add htrunc htail
    _ = Cval / ((p : Real) * L n) := by
      dsimp only [Cval]
      field_simp [hpR.ne', (L_pos hn).ne']

/-- Fixed finitely many raw cells admit one common sharp valuation-profile
constant and one common threshold.  The Dickman main sum is independent of
the cell index, which is the essential input for the later barycentric
mixture. -/
theorem
    exists_uniform_fixedFinite_rawStructuredCell_valuation_mean_profiles_paperRate
    {CellIndex : Type*} [Fintype CellIndex] [Nonempty CellIndex]
    (H : CellIndex → Pattern) (A C : CellIndex → Real)
    (hA : ∀ c, 0 < A c) (hAC : ∀ c, A c < C c)
    (hC : ∀ c, 0 < C c)
    (W : Nat) (hW : 1 < W)
    (hHeadLe : ∀ c, ∀ q ∈ (H c).primes, q ≤ W) :
    ∃ Cval : Real, 0 < Cval ∧ ∃ N₀ : Nat,
      ∀ {n p : Nat}, N₀ ≤ n → p ∈ primeBand n W →
        let Kcut := Nat.log p (yNat n ^ 4)
        ∀ c : CellIndex,
          let S := structuredCell (H c)
            (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
          ∃ hS : S.Nonempty,
            |(uniformOnFinset S hS).expect
                  (fun m ↦ valuation p (m : Nat)) -
              ∑ k ∈ positiveExponents Kcut,
                paperDivisibilityMain n (p ^ k)| ≤
              Cval / ((p : Real) * L n) := by
  classical
  have hcell : ∀ c : CellIndex,
      ∃ Cval : Real, 0 < Cval ∧ ∃ N₀ : Nat,
        ∀ {n p : Nat}, N₀ ≤ n → p ∈ primeBand n W →
          let S := structuredCell (H c)
            (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
          let Kcut := Nat.log p (yNat n ^ 4)
          ∃ hS : S.Nonempty,
            |(uniformOnFinset S hS).expect
                  (fun m ↦ valuation p (m : Nat)) -
              ∑ k ∈ positiveExponents Kcut,
                paperDivisibilityMain n (p ^ k)| ≤
              Cval / ((p : Real) * L n) := by
    intro c
    exact
      exists_uniform_rawStructuredCell_valuation_mean_profile_paperRate
        (H c) (hA c) (hAC c) (hC c) W hW (hHeadLe c)
  choose Ccell hCcell Ncell hrate using hcell
  let Cval : Real := ∑ c : CellIndex, Ccell c
  let N₀ : Nat := 2 + ∑ c : CellIndex, Ncell c
  have hCcell0 (c : CellIndex) : 0 ≤ Ccell c := (hCcell c).le
  let c₀ : CellIndex := Classical.choice (inferInstance : Nonempty CellIndex)
  have hCval : 0 < Cval := by
    have hsingle : Ccell c₀ ≤ Cval := by
      dsimp only [Cval]
      exact Finset.single_le_sum
        (fun c _hc ↦ hCcell0 c) (Finset.mem_univ c₀)
    exact (hCcell c₀).trans_le hsingle
  refine ⟨Cval, hCval, N₀, ?_⟩
  intro n p hN hpBand
  dsimp only
  intro c
  have hNc : Ncell c ≤ n := by
    have hle : Ncell c ≤ N₀ := by
      dsimp only [N₀]
      have hsingle :
          Ncell c ≤ ∑ d : CellIndex, Ncell d :=
        Finset.single_le_sum
          (fun d _hd ↦ Nat.zero_le (Ncell d)) (Finset.mem_univ c)
      omega
    exact hle.trans hN
  have hraw := hrate c hNc hpBand
  rcases hraw with ⟨hS, hbound⟩
  refine ⟨hS, hbound.trans ?_⟩
  have hCcellLe : Ccell c ≤ Cval := by
    dsimp only [Cval]
    exact Finset.single_le_sum
      (fun d _hd ↦ hCcell0 d) (Finset.mem_univ c)
  have hden0 : 0 ≤ (p : Real) * L n := by
    exact mul_nonneg (by positivity) (L_pos (by omega)).le
  exact div_le_div_of_nonneg_right hCcellLe hden0

/-! ## Literal guard deletion -/

/-- Tilting by the identically-zero score does not change an expectation.
This small identity lets the general conditional-deletion theorem be used
without replacing the literal uniform laws by unnamed equivalent laws. -/
theorem finiteProbability_exponentialTilt_zero_expect
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (F : Omega → Real) :
    (mu.exponentialTilt (fun _ ↦ 0)).expect F = mu.expect F := by
  have hpartition :
      mu.expPartition (fun _ ↦ 0) = 1 := by
    unfold FiniteProbability.expPartition FiniteProbability.expect
    simp only [Real.exp_zero, mul_one]
    exact mu.mass_sum
  rw [mu.exponentialTilt_expect_eq, hpartition, div_one]
  apply congrArg mu.expect
  funext omega
  simp

/-- Quantitative deletion of a literal finset from an un-tilted uniform
law.  The conclusion is obtained from the general conditional-law theorem;
the surviving law is reindexed exactly as `uniformOnFinset (S \ G)`. -/
theorem
    abs_uniformOnFinset_sdiff_expect_sub_uniformOnFinset_expect_le
    (S G : Finset Nat) (hS : S.Nonempty) (hR : (S \ G).Nonempty)
    (F : Nat → Real) {KF : Real} (hKF : 0 ≤ KF)
    (hF : ∀ m ∈ S, |F m| ≤ KF)
    (hsmallCensus :
      (G.card : Real) / (S.card : Real) ≤ (1 : Real) / 2) :
    |(uniformOnFinset (S \ G) hR).expect (fun m ↦ F (m : Nat)) -
        (uniformOnFinset S hS).expect (fun m ↦ F (m : Nat))| ≤
      4 * KF * ((G.card : Real) / (S.card : Real)) := by
  let score : S → Real := fun _ ↦ 0
  have hscore : ∀ m : S, |score m| ≤ (0 : Real) := by
    intro m
    simp only [score, abs_zero, le_refl]
  have hFsub : ∀ m : S, |F (m : Nat)| ≤ KF := by
    intro m
    exact hF m m.property
  have hsmallCensus' :
      Real.exp (2 * (0 : Real)) * (G.card : Real) /
          (S.card : Real) ≤ (1 : Real) / 2 := by
    simpa using hsmallCensus
  obtain ⟨hsmall, hdiff⟩ :=
    GuardedUniformCell.exists_deleteGuards_expect_bound
      S G hS score 0 hscore (fun m : S ↦ F (m : Nat))
        hKF hFsub hsmallCensus'
  have hreindex :=
    deleteGuards_tilted_uniform_expect_remaining_eq
      S G hS hR score hsmall (fun m : S ↦ F (m : Nat))
  have hremainingZero :
      ((uniformOnFinset (S \ G) hR).exponentialTilt
          (fun z ↦ score (remainingEmbedding S G z))).expect
            (fun z ↦ F ((remainingEmbedding S G z : S) : Nat)) =
        (uniformOnFinset (S \ G) hR).expect
          (fun z ↦ F (z : Nat)) := by
    have hzero :=
      finiteProbability_exponentialTilt_zero_expect
        (uniformOnFinset (S \ G) hR) (fun z ↦ F (z : Nat))
    simpa only [score, remainingEmbedding_value] using hzero
  have hrawZero :
      ((uniformOnFinset S hS).exponentialTilt score).expect
          (fun m ↦ F (m : Nat)) =
        (uniformOnFinset S hS).expect (fun m ↦ F (m : Nat)) := by
    simpa only [score] using
      finiteProbability_exponentialTilt_zero_expect
        (uniformOnFinset S hS) (fun m ↦ F (m : Nat))
  rw [hreindex, hremainingZero, hrawZero] at hdiff
  simpa using hdiff

/-! ## The concrete guard ledger at the stronger `1 / L` rate -/

private theorem sharp_y_cube_div_nat_eq_inv_rpow
    {n : Nat} (hn : 0 < n) :
    y n ^ 3 / (n : Real) = 1 / (n : Real) ^ (1 / 3 : Real) := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hpow :
      ((n : Real) ^ (2 / 9 : Real)) ^ 3 *
          (n : Real) ^ (1 / 3 : Real) = (n : Real) := by
    calc
      ((n : Real) ^ (2 / 9 : Real)) ^ 3 *
          (n : Real) ^ (1 / 3 : Real) =
        (((n : Real) ^ (2 / 9 : Real) *
            (n : Real) ^ (2 / 9 : Real)) *
          ((n : Real) ^ (2 / 9 : Real) *
            (n : Real) ^ (1 / 3 : Real))) := by ring
      _ = (n : Real) ^ ((2 / 9 : Real) + 2 / 9) *
          (n : Real) ^ ((2 / 9 : Real) + 1 / 3) := by
        rw [Real.rpow_add hnR, Real.rpow_add hnR]
      _ = (n : Real) ^ (((2 / 9 : Real) + 2 / 9) +
          ((2 / 9 : Real) + 1 / 3)) := by
        rw [← Real.rpow_add hnR]
      _ = (n : Real) := by norm_num [Real.rpow_one]
  unfold y
  field_simp [(Real.rpow_pos_of_pos hnR (1 / 3 : Real)).ne', hnR.ne']
  nlinarith

private theorem sharp_census_mul_y_sq_expansion
    (Cprom Cbank n : Nat) (hn : 0 < n) :
    censusRatioMajorant Cprom Cbank n * y n ^ 2 =
      (Cprom : Real) * (1 / (n : Real) ^ (1 / 3 : Real)) +
        3 * (Cbank : Real) *
          (L n / (n : Real) ^ (1 / 3 : Real) +
            2 * (1 / (n : Real) ^ (1 / 3 : Real))) := by
  rw [censusRatioMajorant]
  rw [show
    (((Cprom : Real) + 3 * (Cbank : Real) * (L n + 2)) * y n /
        (n : Real)) * y n ^ 2 =
      ((Cprom : Real) + 3 * (Cbank : Real) * (L n + 2)) *
        (y n ^ 3 / (n : Real)) by ring]
  rw [sharp_y_cube_div_nat_eq_inv_rpow hn]
  ring

/-- The concrete reciprocal guard majorant is in fact `o(1 / L)`.
The older public theorem retained only the weaker moving-low
`o(1 / log L)` consequence. -/
theorem tendsto_censusRatioMajorant_mul_y_sq_mul_L_zero_sharp
    (Cprom Cbank : Nat) :
    Tendsto (fun n : Nat ↦
      censusRatioMajorant Cprom Cbank n * y n ^ 2 * L n)
      atTop (nhds 0) := by
  let a : Real := 1 / 3
  have ha : 0 < a := by norm_num [a]
  have hlog :
      Tendsto (fun n : Nat ↦ L n / (n : Real) ^ a)
        atTop (nhds 0) := by
    have hreal : Tendsto
        (fun x : Real ↦ Real.log x ^ (1 : Real) / x ^ a)
        atTop (nhds 0) :=
      (isLittleO_log_rpow_rpow_atTop (1 : Real) ha).tendsto_div_nhds_zero
    have hnat := hreal.comp tendsto_natCast_atTop_atTop
    apply hnat.congr'
    filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    simp only [Function.comp_apply, L, Real.rpow_one]
  have hlogSq :
      Tendsto (fun n : Nat ↦ L n ^ 2 / (n : Real) ^ a)
        atTop (nhds 0) := by
    have hreal : Tendsto
        (fun x : Real ↦ Real.log x ^ (2 : Real) / x ^ a)
        atTop (nhds 0) :=
      (isLittleO_log_rpow_rpow_atTop (2 : Real) ha).tendsto_div_nhds_zero
    have hnat := hreal.comp tendsto_natCast_atTop_atTop
    change Tendsto
      (fun n : Nat ↦ Real.log (n : Real) ^ (2 : Real) /
        (n : Real) ^ a) atTop (nhds 0) at hnat
    simpa [L, Real.rpow_natCast] using hnat
  let upper : Nat → Real := fun n ↦
    (Cprom : Real) * (L n / (n : Real) ^ a) +
      3 * (Cbank : Real) *
        (L n ^ 2 / (n : Real) ^ a +
          2 * (L n / (n : Real) ^ a))
  have hupper : Tendsto upper atTop (nhds 0) := by
    dsimp only [upper]
    simpa only [mul_zero, add_zero] using
      (hlog.const_mul (Cprom : Real)).add
        ((hlogSq.add (hlog.const_mul 2)).const_mul
          (3 * (Cbank : Real)))
  apply hupper.congr'
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  rw [sharp_census_mul_y_sq_expansion Cprom Cbank n hn]
  dsimp only [upper, a]
  ring

/-- Fixed multiplicative constants preserve the stronger concrete guard
rate. -/
theorem tendsto_guardRateMajorant_mul_L_zero_sharp
    (Cprom Cbank : Nat) (constant : Real) :
    Tendsto (fun n : Nat ↦ constant *
      (censusRatioMajorant Cprom Cbank n * y n ^ 2) * L n)
      atTop (nhds 0) := by
  have hc : Tendsto (fun _n : Nat ↦ constant)
      atTop (nhds constant) := tendsto_const_nhds
  have h := hc.mul
    (tendsto_censusRatioMajorant_mul_y_sq_mul_L_zero_sharp
      Cprom Cbank)
  simpa only [mul_zero, mul_assoc] using h

/-- The family-aggregated literal guard error is also `o(1 / L)`. -/
theorem tendsto_canonicalGuardSquarefreeError_mul_L_zero_sharp
    {Head : Type*} [Fintype Head]
    (P : Head → Pattern) (I : PaperGuardCensus.PhysicalIntervals)
    {Cprom Cbank : Nat}
    (G : ∀ n, PaperGuardCensus.Ledger n Cprom Cbank) (Kscore : Real) :
    Tendsto (fun n : Nat ↦
      GuardSquarefreeErrorRate.canonicalGuardSquarefreeError
          P I G Kscore n * L n)
      atTop (nhds 0) := by
  have hL0 : ∀ᶠ n : Nat in atTop, 0 ≤ L n := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    exact Real.log_nonneg (by exact_mod_cast hn)
  have hcell (c : PaperBridgeFit.Cell Head) :
      Tendsto (fun n : Nat ↦
        GuardDeletionSquarefreeProfiles.guardSquarefreeError
            (PaperGuardCensus.rawCell P I n c) (G n).guards
              Kscore n * L n)
        atTop (nhds 0) := by
    let constant := 4 * Real.exp (2 * Kscore) /
      PaperScaleMarkedCell.paperCellDensity (P c.1)
        (I.lower c.2) (I.upper c.2)
    have hupper :=
      tendsto_guardRateMajorant_mul_L_zero_sharp
        Cprom Cbank constant
    have hdensity := PaperGuardCensus.eventually_rawCell_density P I
    refine squeeze_zero' ?_ ?_ hupper
    · filter_upwards [hL0] with n hLn
      exact mul_nonneg
        (GuardDeletionSquarefreeProfiles.guardSquarefreeError_nonneg
          _ _ _ _) hLn
    · filter_upwards [hdensity, Filter.eventually_gt_atTop 0, hL0]
        with n hdens hn hLn
      have hguard :=
        GuardSquarefreeErrorRate.guardSquarefreeError_rawCell_le_rateMajorant
          P I (G n) c (by omega : 1 ≤ n) (hdens c) Kscore
      have hguard' :
          GuardDeletionSquarefreeProfiles.guardSquarefreeError
              (PaperGuardCensus.rawCell P I n c) (G n).guards
                Kscore n ≤
            constant *
              (censusRatioMajorant Cprom Cbank n * y n ^ 2) := by
        simpa only [constant] using hguard
      exact mul_le_mul_of_nonneg_right hguard' hLn
  have hsum := tendsto_finset_sum
    (Finset.univ : Finset (PaperBridgeFit.Cell Head))
    (fun c _hc ↦ hcell c)
  have hsum0 : Tendsto (fun n : Nat ↦
      ∑ c : PaperBridgeFit.Cell Head,
        GuardDeletionSquarefreeProfiles.guardSquarefreeError
            (PaperGuardCensus.rawCell P I n c) (G n).guards
              Kscore n * L n)
      atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using hsum
  apply hsum0.congr'
  filter_upwards with n
  unfold GuardSquarefreeErrorRate.canonicalGuardSquarefreeError
  rw [Finset.sum_mul]

/-- After deletion of the concrete canonical guard ledger, every fixed
head/physical cell retains the same common full-valuation profile with an
explicit `1 / (p * L)` error.  This is the sharp un-tilted counterpart of
the older tilted `epsilon(n) / p` component theorem. -/
theorem
    exists_uniform_guardedRawCell_valuation_mean_profiles_paperRate
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    (W : Nat) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ q ∈ (P h).primes, q ≤ W) :
    ∃ Cval : Real, 0 < Cval ∧ ∃ N₀ : Nat,
      ∀ {n p : Nat}, N₀ ≤ n → p ∈ primeBand n W →
        let Kcut := Nat.log p (yNat n ^ 4)
        ∀ c : Cell Head,
          ∀ hremaining :
            (rawCell P I n c \ (G n).guards).Nonempty,
            |(uniformOnFinset
                  (rawCell P I n c \ (G n).guards) hremaining).expect
                  (fun m ↦ valuation p (m : Nat)) -
              ∑ k ∈ positiveExponents Kcut,
                paperDivisibilityMain n (p ^ k)| ≤
              Cval / ((p : Real) * L n) := by
  let H : Cell Head → Pattern := fun c ↦ P c.1
  let Alower : Cell Head → Real := fun c ↦ I.lower c.2
  let Cupper : Cell Head → Real := fun c ↦ I.upper c.2
  obtain ⟨Craw, hCraw, Nraw, hraw⟩ :=
    exists_uniform_fixedFinite_rawStructuredCell_valuation_mean_profiles_paperRate
      H Alower Cupper
      (fun c ↦ I.lower_pos c.2)
      (fun c ↦ I.lower_lt_upper c.2)
      (fun c ↦ (I.lower_pos c.2).trans (I.lower_lt_upper c.2))
      W hW (fun c ↦ hHeadLe c.1)
  have hsmallEvent :=
    eventually_exp_two_mul_guardRatio_rawCell_le_half
      P I Cprom Cbank G 0
  have henvEvent :=
    eventually_valuationEnvelope_bounds (Head := Head) I W hW
  have hrowEnvEvent :=
    eventually_bandPrime_mul_valuationEnvelope_le_yNat_sq
      (Head := Head) I W hW
  have hguardRate :=
    tendsto_canonicalGuardSquarefreeError_mul_L_zero_sharp
      P I G 0
  have hguardSmall : ∀ᶠ n : Nat in atTop,
      canonicalGuardSquarefreeError P I G 0 n * L n ≤ 1 :=
    hguardRate.eventually (eventually_le_nhds (by norm_num))
  have hAll : ∀ᶠ n : Nat in atTop,
      (∀ c : Cell Head,
        ((G n).guards.card : Real) /
          ((rawCell P I n c).card : Real) ≤ (1 : Real) / 2) ∧
      (∀ c : Cell Head,
        0 ≤ valuationEnvelope I n W c ∧
          valuationEnvelope I n W c ≤
            (2 / Real.log (W : Real)) * L n) ∧
      (∀ (c : Cell Head) (p : BandPrime n W),
        (p.1 : Real) * valuationEnvelope I n W c ≤
          (yNat n : Real) ^ 2) ∧
      canonicalGuardSquarefreeError P I G 0 n * L n ≤ 1 ∧
      1 < n := by
    filter_upwards [hsmallEvent, henvEvent, hrowEnvEvent, hguardSmall,
      Filter.eventually_gt_atTop 1] with
      n hsmallN henvN hrowEnvN hguardN hn
    have hsmallN' : ∀ c : Cell Head,
        ((G n).guards.card : Real) /
          ((rawCell P I n c).card : Real) ≤ (1 : Real) / 2 := by
      intro c
      have hc := hsmallN c
      norm_num at hc
      simpa using hc
    exact ⟨hsmallN', henvN, hrowEnvN, hguardN, hn⟩
  obtain ⟨Nevent, hNevent⟩ := Filter.eventually_atTop.mp hAll
  let Cval : Real := Craw + 2
  have hCval : 0 < Cval := by
    dsimp only [Cval]
    linarith
  refine ⟨Cval, hCval, max Nraw Nevent, ?_⟩
  intro n p hN hpBand
  dsimp only
  intro c hremaining
  have hNraw : Nraw ≤ n := by omega
  have hNeventBound : Nevent ≤ n := by omega
  obtain ⟨hsmallN, henvN, hrowEnvN, hguardN, hn⟩ :=
    hNevent n hNeventBound
  have hp := prime_of_mem_primeBand hpBand
  have hpR : (0 : Real) < p := by exact_mod_cast hp.pos
  have hL : 0 < L n := L_pos hn
  have hrawCell := hraw (n := n) (p := p) hNraw hpBand c
  rcases hrawCell with ⟨hS, hrawBound⟩
  let S := rawCell P I n c
  let KA := valuationEnvelope I n W c
  have hKA : 0 ≤ KA := by
    exact (henvN c).1
  have hvaluation : ∀ m ∈ S, |valuation p m| ≤ KA := by
    intro m hm
    rw [abs_of_nonneg (valuation_nonneg p m)]
    let pBand : BandPrime n W := ⟨p, hpBand⟩
    let mRaw : rawCell P I n c :=
      ⟨m, by simpa only [S] using hm⟩
    exact (rawCell_valuation_le_total P I pBand c mRaw).trans
      (by
        simpa only [KA] using
          rawCell_totalBandValuation_le P I hW c mRaw)
  have hdelete :=
    abs_uniformOnFinset_sdiff_expect_sub_uniformOnFinset_expect_le
      S (G n).guards hS
        (by simpa only [S] using hremaining)
        (fun m ↦ valuation p m) hKA
        (by
          intro m hm
          simpa only [S] using hvaluation m hm)
        (by simpa only [S] using hsmallN c)
  let guardError :=
    guardSquarefreeError S (G n).guards 0 n
  have hratio0 : 0 ≤
      ((G n).guards.card : Real) / (S.card : Real) := by
    positivity
  have hrowEnv :
      (p : Real) * KA ≤ (yNat n : Real) ^ 2 := by
    let pBand : BandPrime n W := ⟨p, hpBand⟩
    simpa only [KA] using hrowEnvN c pBand
  have hguardCell :
      (p : Real) *
          (4 * KA *
            (((G n).guards.card : Real) / (S.card : Real))) ≤
        2 * guardError := by
    unfold guardError guardSquarefreeError
    norm_num
    calc
      (p : Real) *
          (4 * KA *
            (((G n).guards.card : Real) / (S.card : Real))) =
        4 * ((p : Real) * KA) *
          (((G n).guards.card : Real) / (S.card : Real)) := by ring
      _ ≤ 4 * (yNat n : Real) ^ 2 *
          (((G n).guards.card : Real) / (S.card : Real)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrowEnv (by norm_num)) hratio0
      _ = 2 *
          (2 * (((G n).guards.card : Real) / (S.card : Real)) *
            (yNat n : Real) ^ 2) := by ring
  have hguardToCanonical :
      guardError ≤ canonicalGuardSquarefreeError P I G 0 n := by
    unfold canonicalGuardSquarefreeError
    exact Finset.single_le_sum
      (fun d _hd ↦ guardSquarefreeError_nonneg
        (rawCell P I n d) (G n).guards 0 n)
      (Finset.mem_univ c)
  have hcanonicalRate :
      canonicalGuardSquarefreeError P I G 0 n ≤ 1 / L n := by
    apply (le_div_iff₀ hL).2
    simpa only [one_mul] using hguardN
  have hdeleteRate :
      4 * KA * (((G n).guards.card : Real) / (S.card : Real)) ≤
        2 / ((p : Real) * L n) := by
    have hdivp :
        4 * KA * (((G n).guards.card : Real) / (S.card : Real)) ≤
          (2 / L n) / (p : Real) := by
      apply (le_div_iff₀ hpR).2
      calc
        (4 * KA *
            (((G n).guards.card : Real) / (S.card : Real))) *
              (p : Real) =
            (p : Real) *
              (4 * KA *
                (((G n).guards.card : Real) / (S.card : Real))) := by ring
        _ ≤ 2 * guardError := hguardCell
        _ ≤ 2 * canonicalGuardSquarefreeError P I G 0 n :=
          mul_le_mul_of_nonneg_left hguardToCanonical (by norm_num)
        _ ≤ 2 * (1 / L n) :=
          mul_le_mul_of_nonneg_left hcanonicalRate (by norm_num)
        _ = 2 / L n := by ring
    calc
      4 * KA * (((G n).guards.card : Real) / (S.card : Real)) ≤
          (2 / L n) / (p : Real) := hdivp
      _ = 2 / ((p : Real) * L n) := by
        field_simp [hpR.ne', hL.ne']
  have hdeleteBound :
      |(uniformOnFinset
            (rawCell P I n c \ (G n).guards) hremaining).expect
            (fun m ↦ valuation p (m : Nat)) -
        (uniformOnFinset (rawCell P I n c) hS).expect
            (fun m ↦ valuation p (m : Nat))| ≤
          2 / ((p : Real) * L n) := by
    have hrawDelete :
        |(uniformOnFinset (S \ (G n).guards)
              (by simpa only [S] using hremaining)).expect
              (fun m ↦ valuation p (m : Nat)) -
          (uniformOnFinset S hS).expect
              (fun m ↦ valuation p (m : Nat))| ≤
            4 * KA *
              (((G n).guards.card : Real) / (S.card : Real)) := by
      simpa only [S] using hdelete
    simpa only [S] using hrawDelete.trans hdeleteRate
  let Kcut := Nat.log p (yNat n ^ 4)
  let mainSum := ∑ k ∈ positiveExponents Kcut,
    paperDivisibilityMain n (p ^ k)
  change
    |(uniformOnFinset
          (rawCell P I n c \ (G n).guards) hremaining).expect
          (fun m ↦ valuation p (m : Nat)) - mainSum| ≤
      Cval / ((p : Real) * L n)
  calc
    |(uniformOnFinset
          (rawCell P I n c \ (G n).guards) hremaining).expect
          (fun m ↦ valuation p (m : Nat)) - mainSum| ≤
      |(uniformOnFinset
            (rawCell P I n c \ (G n).guards) hremaining).expect
            (fun m ↦ valuation p (m : Nat)) -
        (uniformOnFinset (rawCell P I n c) hS).expect
            (fun m ↦ valuation p (m : Nat))| +
      |(uniformOnFinset (rawCell P I n c) hS).expect
            (fun m ↦ valuation p (m : Nat)) - mainSum| := by
        have htri := abs_add_le
          ((uniformOnFinset
              (rawCell P I n c \ (G n).guards) hremaining).expect
              (fun m ↦ valuation p (m : Nat)) -
            (uniformOnFinset (rawCell P I n c) hS).expect
              (fun m ↦ valuation p (m : Nat)))
          ((uniformOnFinset (rawCell P I n c) hS).expect
              (fun m ↦ valuation p (m : Nat)) - mainSum)
        simpa only [sub_add_sub_cancel] using htri
    _ ≤ 2 / ((p : Real) * L n) +
        Craw / ((p : Real) * L n) :=
      add_le_add hdeleteBound (by
        simpa only [H, Alower, Cupper, Kcut, mainSum, rawCell] using
          hrawBound)
    _ = Cval / ((p : Real) * L n) := by
      dsimp only [Cval]
      ring

/-- Bridge-data specialization of the preceding guarded raw-cell theorem.
The only additional input is the repository's literal identification of the
sample data with `canonicalSampleData`; no tilted law is introduced. -/
theorem
    exists_uniform_bridge_guardedCell_valuation_mean_profiles_paperRate
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    (W : Nat) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ q ∈ (P h).primes, q ≤ W) :
    ∃ Cval : Real, 0 < Cval ∧ ∃ N₀ : Nat,
      ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
        (B : BridgeData Head Band),
        N₀ ≤ B.sampleData.n → B.sampleData.W = W →
        (hsep : physicalBound (I.upper .minus) B.sampleData.n <
          physicalBound (I.lower .plus) B.sampleData.n) →
        (hremaining : ∀ c : Cell Head,
          (rawCell P I B.sampleData.n c \
            (G B.sampleData.n).guards).Nonempty) →
        B.sampleData = canonicalSampleData
          (W := B.sampleData.W) P I (G B.sampleData.n)
            hsep hremaining →
        ∀ p : BandPrime B.sampleData.n B.sampleData.W,
          let Kcut := Nat.log p.1 (yNat B.sampleData.n ^ 4)
          ∀ c : Cell Head,
            |(B.guardedCellProbability c).expect
                  (fun m ↦ valuation p.1 (m : Nat)) -
              ∑ k ∈ positiveExponents Kcut,
                paperDivisibilityMain B.sampleData.n (p.1 ^ k)| ≤
              Cval / ((p.1 : Real) * B.L) := by
  obtain ⟨Cval, hCval, N₀, hrate⟩ :=
    exists_uniform_guardedRawCell_valuation_mean_profiles_paperRate
      P I Cprom Cbank G W hW hHeadLe
  refine ⟨Cval, hCval, N₀, ?_⟩
  intro Band _instBand _instBandDec B hN hBW hsep hremaining hcanonical p
  have hrateP :=
    hrate (n := B.sampleData.n) (p := p.1) hN
      (by simpa only [hBW] using p.2)
  dsimp only at hrateP ⊢
  intro c
  have hraw := hrateP c (hremaining c)
  have hcell :
      B.sampleData.cellFinset c =
        rawCell P I B.sampleData.n c \
          (G B.sampleData.n).guards := by
    calc
      B.sampleData.cellFinset c =
          (canonicalSampleData (W := B.sampleData.W)
            P I (G B.sampleData.n) hsep hremaining).cellFinset c :=
        congrArg (fun D : StructuredSampleData Head ↦ D.cellFinset c)
          hcanonical
      _ = rawCell P I B.sampleData.n c \
          (G B.sampleData.n).guards := by
        exact canonicalSampleData_cellFinset
          P I (G B.sampleData.n) hsep hremaining c
  have hreindex :
      (uniformOnFinset
          (rawCell P I B.sampleData.n c \
            (G B.sampleData.n).guards)
          (hremaining c)).expect
            (fun m ↦ valuation p.1 (m : Nat)) =
        (uniformOnFinset
          (B.sampleData.cellFinset c)
          (B.sampleData.cell_nonempty c)).expect
            (fun m ↦ valuation p.1 (m : Nat)) := by
    have htilt :=
      uniformOnFinset_exponentialTilt_expect_eq_of_finset_eq
        (rawCell P I B.sampleData.n c \
          (G B.sampleData.n).guards)
        (B.sampleData.cellFinset c) hcell.symm
        (hremaining c) (B.sampleData.cell_nonempty c)
        (fun _ ↦ (0 : Real)) (fun _ ↦ (0 : Real))
        (by
          intro x y hxy
          rfl)
        (fun m : Nat ↦ valuation p.1 m)
    simpa only [finiteProbability_exponentialTilt_zero_expect] using htilt
  unfold BridgeData.guardedCellProbability
  rw [← hreindex]
  simpa only [BridgeData.L, Erdos390.Full.Scale.L, hBW] using hraw

end BankPaperRealization

end

end Erdos390.WholePaper
