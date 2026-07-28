import Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosureMoving
import Erdos390.Full.PaperValuationCutoff
import Erdos390.WholePaper.BankPaperCanonicalBalancedRawSignedValuationResidualBoundConnector
import Erdos390.WholePaper.TangentPaperCleanListAbsorption

/-!
# Canonical label-one broad-pool specialization

This file specializes the positive moving-prefix theorem to the literal
head-free smooth base pool and then transports the result through the
canonical numerical-guard deletion.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Erdos390.Full.HeadPattern
open Erdos390.Full.StructuredCells
open Erdos390.Full.FiniteProbability
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.PaperMovingPrefixMarkedCell
open Erdos390.Full.PaperValuationCutoff
open Erdos390.Full.ValuationCutoff

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

private theorem sharp_physicalBound_one (n : Nat) :
    physicalBound (1 : Real) n = n := by
  unfold physicalBound
  norm_num

private theorem sharp_physicalBound_two (n : Nat) :
    physicalBound (2 : Real) n = 2 * n := by
  unfold physicalBound
  have hcast :
      (2 : Real) * (n : Real) = ((2 * n : Nat) : Real) := by
    norm_num
  rw [hcast, Nat.floor_natCast]

private theorem half_le_prefixFraction_one_two_of_two_mul_le
    {n t : Nat} (hn : 0 < n) (ht : 2 * t ≤ n) :
    (1 : Real) / 2 ≤
      prefixFraction 1 2 n (2 * n - t) := by
  have htUpper : t ≤ 2 * n := by omega
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have htR : 2 * (t : Real) ≤ (n : Real) := by exact_mod_cast ht
  unfold prefixFraction prefixScale
  rw [Nat.cast_sub htUpper, Nat.cast_mul]
  norm_num
  field_simp [hnR.ne']
  nlinarith

/-- A fixed multiple of the canonical upper-tail length is eventually small
enough that the moving label-one pool occupies at least half of `[n,2n]`. -/
private theorem eventually_two_mul_mul_upperTailLength_le_self
    (K : Nat) {c : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      2 * (K * upperTailLength c n) ≤ n := by
  have hraw :=
    eventually_mul_upperTailLength_le_self (2 * K) hc
  filter_upwards [hraw] with n hn
  simpa only [Nat.mul_assoc] using hn

/-! ## Raw canonical broad pool -/

/-- The raw label-one head-free broad pool inherits the common sharp
full-valuation profile from the moving-prefix theorem. -/
theorem
    exists_uniform_rawSmoothBasePool_valuation_mean_profile_paperRate
    (W K : Nat) (hW : 1 < W) {c : Real} (hc : 0 < c) :
    ∃ Cval : Real, 0 < Cval ∧ ∃ N₀ : Nat,
      ∀ {n p : Nat}, N₀ ≤ n → p ∈ primeBand n W →
        let S := bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K
        let Kcut := Nat.log p (yNat n ^ 4)
        ∃ hS : S.Nonempty,
          |(uniformOnFinset S hS).expect
                (fun m ↦ valuation p (m : Nat)) -
            ∑ j ∈ positiveExponents Kcut,
              paperDivisibilityMain n (p ^ j)| ≤
            Cval / ((p : Real) * L n) := by
  have hHeadLe :
      ∀ q ∈ (roughHeadZeroPattern W).primes, q ≤ W := by
    intro q hq
    change q ∈ primesUpTo W at hq
    exact (mem_primesUpTo.mp hq).2
  obtain ⟨Cval, hCval, Nraw, hraw⟩ :=
    exists_uniform_movingPrefix_valuation_mean_profile_paperRate_of_fraction
      (roughHeadZeroPattern W)
      (A := 1) (C := 2) (rmin := (1 : Real) / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      W hW hHeadLe
  have htail :=
    eventually_two_mul_mul_upperTailLength_le_self K hc
  have hgood : ∀ᶠ n : Nat in atTop,
      2 * (K * upperTailLength c n) ≤ n ∧ 1 < n := by
    filter_upwards [htail, Filter.eventually_gt_atTop 1]
      with n hsmall hn
    exact ⟨hsmall, hn⟩
  obtain ⟨Ntail, hNtail⟩ := Filter.eventually_atTop.mp hgood
  refine ⟨Cval, hCval, max Nraw Ntail, ?_⟩
  intro n p hN hpBand
  dsimp only
  have hNraw : Nraw ≤ n := by omega
  have hNtailBound : Ntail ≤ n := by omega
  obtain ⟨hsmall, hn⟩ := hNtail n hNtailBound
  let h := upperTailLength c n
  let t := K * h
  let k := 2 * n - t
  have hnpos : 0 < n := by omega
  have ht : 2 * t ≤ n := by simpa only [t, h] using hsmall
  have htTwo : t ≤ 2 * n := by omega
  have hlow : physicalBound (1 : Real) n < k := by
    rw [sharp_physicalBound_one]
    dsimp only [k]
    omega
  have hhigh : k ≤ physicalBound (2 : Real) n := by
    rw [sharp_physicalBound_two]
    dsimp only [k]
    omega
  have hfrac :
      (1 : Real) / 2 ≤ prefixFraction 1 2 n k := by
    dsimp only [k]
    exact half_le_prefixFraction_one_two_of_two_mul_le hnpos ht
  obtain ⟨hS, hbound⟩ :=
    hraw (n := n) (k := k) (p := p)
      hNraw hlow hhigh hfrac hpBand
  have hpool :
      bankPaperCanonicalRawSmoothBasePool W n h K =
        structuredCell (roughHeadZeroPattern W) n k (yNat n) := by
    simpa only [h, k, t] using
      bankPaperCanonicalRawSmoothBasePool_eq_zeroHeadStructuredCell
        W n h K
  have hpool' :
      bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K =
        structuredCell (roughHeadZeroPattern W)
          (physicalBound (1 : Real) n) k (yNat n) := by
    simpa only [h, sharp_physicalBound_one] using hpool
  let hPool :
      (bankPaperCanonicalRawSmoothBasePool W n
        (upperTailLength c n) K).Nonempty :=
    hpool'.symm ▸ hS
  refine ⟨hPool, ?_⟩
  have hreindex :
      (uniformOnFinset
          (structuredCell (roughHeadZeroPattern W)
            (physicalBound (1 : Real) n) k (yNat n)) hS).expect
            (fun m ↦ valuation p (m : Nat)) =
        (uniformOnFinset
          (bankPaperCanonicalRawSmoothBasePool W n
            (upperTailLength c n) K) hPool).expect
            (fun m ↦ valuation p (m : Nat)) := by
    have htilt :=
      uniformOnFinset_exponentialTilt_expect_eq_of_finset_eq
        (structuredCell (roughHeadZeroPattern W)
          (physicalBound (1 : Real) n) k (yNat n))
        (bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K)
        hpool'.symm hS hPool
        (fun _ ↦ (0 : Real)) (fun _ ↦ (0 : Real))
        (by
          intro x y hxy
          rfl)
        (fun m : Nat ↦ valuation p m)
    simpa only [finiteProbability_exponentialTilt_zero_expect] using htilt
  rw [← hreindex]
  exact hbound

/-! ## Canonical guard deletion -/

/-- The relevant numerical guard occupies an eventually negligible fraction
of the raw label-one pool, uniformly over the realization and the guard
parameter. -/
private theorem eventually_smoothBase_guardRatio_le_half
    (W K depth : Nat) {c : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth))
        (deltaStar : Real),
        let S := bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K
        let D := R.roughCanonicalGuardSet certificate deltaStar ∩ S
        ((D.card : Real) / (S.card : Real)) ≤ (1 : Real) / 2 := by
  let density : Real := roughCanonicalRawBroadPoolDensity W
  have hdensity : 0 < density :=
    roughCanonicalRawBroadPoolDensity_pos W
  have hsmall :
      ∀ᶠ n : Nat in atTop,
        (1 / density) * ((yNat n : Real) / (n : Real)) ≤
          (1 : Real) / 2 := by
    have htend :
        Tendsto (fun n : Nat ↦
          (1 / density) * ((yNat n : Real) / (n : Real)))
          atTop (nhds 0) := by
      simpa only [mul_zero] using
        tangentPaper_yNat_div_self_tendsto_zero.const_mul
          (1 / density)
    exact htend.eventually (eventually_le_nhds (by norm_num))
  filter_upwards [
      eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower W K hc,
      eventually_ge_atTop (centralAnchorCutoffThreshold depth),
      eventually_yNat_lt_centralAnchorCutoff depth,
      hsmall,
      Filter.eventually_gt_atTop 0] with
      n hpool hthreshold hyCutoff hsmallN hn
  intro R certificate deltaStar
  dsimp only
  let S := bankPaperCanonicalRawSmoothBasePool W n
    (upperTailLength c n) K
  let D := R.roughCanonicalGuardSet certificate deltaStar ∩ S
  have hDcardNat : D.card ≤ yNat n := by
    have hfirst :=
      bankPaperCanonicalSmoothBaseGuardDeletionPool_card_le_anchorIntersection
        R certificate deltaStar W K
    have hsecond :=
      guardedCentralAnchors_inter_rawSmoothBasePool_card_le_yNat
        (h := upperTailLength c n)
        certificate W K hthreshold hyCutoff
    simpa only [D, S, bankPaperCanonicalSmoothBaseGuardDeletionPool] using
      hfirst.trans hsecond
  have hDcard : (D.card : Real) ≤ (yNat n : Real) := by
    exact_mod_cast hDcardNat
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hden : 0 < density * (n : Real) :=
    mul_pos hdensity hnR
  have hScard : 0 < (S.card : Real) :=
    hden.trans_le (by simpa only [density, S] using hpool)
  have hratio :
      (D.card : Real) / (S.card : Real) ≤
        (yNat n : Real) / (density * (n : Real)) := by
    calc
      (D.card : Real) / (S.card : Real) ≤
          (yNat n : Real) / (S.card : Real) :=
        div_le_div_of_nonneg_right hDcard hScard.le
      _ ≤ (yNat n : Real) / (density * (n : Real)) :=
        div_le_div_of_nonneg_left (by positivity) hden
          (by simpa only [density, S] using hpool)
  calc
    (D.card : Real) / (S.card : Real) ≤
        (yNat n : Real) / (density * (n : Real)) := hratio
    _ = (1 / density) * ((yNat n : Real) / (n : Real)) := by
      field_simp [hdensity.ne', hnR.ne']
    _ ≤ (1 : Real) / 2 := hsmallN

/-- Deleting the canonical numerical guard from the label-one smooth broad
pool preserves the common sharp full-valuation profile.  The proof uses only
the literal smooth-anchor census `≤ yNat`, the proved linear raw-pool lower
bound, the elementary valuation cutoff, and
`yNat² L² / n ≤ 1`. -/
theorem
    exists_uniform_guardedSmoothBasePool_valuation_mean_profile_paperRate
    (W K depth : Nat) (hW : 1 < W) {c : Real} (hc : 0 < c) :
    ∃ Cval : Real, 0 < Cval ∧ ∃ N₀ : Nat,
      ∀ {n p : Nat}
        (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth))
        (deltaStar : Real),
        N₀ ≤ n → p ∈ primeBand n W →
        ∀ hguarded :
          (R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar W K 1).Nonempty,
          let Kcut := Nat.log p (yNat n ^ 4)
          |(uniformOnFinset
                (R.roughCanonicalGuardedBroadCorrectionPool certificate
                  deltaStar W K 1) hguarded).expect
                (fun m ↦ valuation p (m : Nat)) -
            ∑ j ∈ positiveExponents Kcut,
              paperDivisibilityMain n (p ^ j)| ≤
            Cval / ((p : Real) * L n) := by
  obtain ⟨Craw, hCraw, Nraw, hraw⟩ :=
    exists_uniform_rawSmoothBasePool_valuation_mean_profile_paperRate
      W K hW hc
  let density : Real := roughCanonicalRawBroadPoolDensity W
  have hdensity : 0 < density :=
    roughCanonicalRawBroadPoolDensity_pos W
  let Cenv : Real := 2 / Real.log (W : Real)
  have hlogW : 0 < Real.log (W : Real) :=
    Real.log_pos (by exact_mod_cast hW)
  have hCenv : 0 < Cenv := by
    dsimp only [Cenv]
    positivity
  let Cguard : Real := 4 * Cenv / density
  have hCguard : 0 < Cguard := by
    dsimp only [Cguard]
    positivity
  have hpoolEvent :=
    eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower W K hc
  have hratioEvent :=
    eventually_smoothBase_guardRatio_le_half W K depth hc
  have hcutEvent :=
    eventually_valuationCutoff_div_L_le
      (2 : Real) W (by norm_num) hW
  have hyRate := eventually_yNat_sq_le_secondOrderScale_div_L
  have hcutoffThreshold :
      ∀ᶠ n : Nat in atTop,
        centralAnchorCutoffThreshold depth ≤ n :=
    eventually_ge_atTop _
  have hyCutoff := eventually_yNat_lt_centralAnchorCutoff depth
  have hgood : ∀ᶠ n : Nat in atTop,
      roughCanonicalRawBroadPoolDensity W * (n : Real) ≤
          ((bankPaperCanonicalRawSmoothBasePool W n
            (upperTailLength c n) K).card : Real) ∧
      (∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth))
        (deltaStar : Real),
        let S := bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K
        let D := R.roughCanonicalGuardSet certificate deltaStar ∩ S
        ((D.card : Real) / (S.card : Real)) ≤ (1 : Real) / 2) ∧
      (∀ p ∈ primeBand n W,
        (valuationCutoff p (physicalBound (2 : Real) n) : Real) / L n ≤
          2 / Real.log (W : Real)) ∧
      (yNat n : Real) ^ 2 ≤ secondOrderScale n / L n ∧
      centralAnchorCutoffThreshold depth ≤ n ∧
      yNat n < centralAnchorCutoff depth n ∧
      1 < n := by
    filter_upwards [hpoolEvent, hratioEvent, hcutEvent, hyRate,
      hcutoffThreshold, hyCutoff, Filter.eventually_gt_atTop 1]
      with n hpool hratio hcut hy hthreshold hycut hn
    exact ⟨hpool, hratio, hcut, hy, hthreshold, hycut, hn⟩
  obtain ⟨Ngood, hNgood⟩ := Filter.eventually_atTop.mp hgood
  let Cval : Real := Craw + Cguard
  have hCval : 0 < Cval := by
    dsimp only [Cval]
    positivity
  refine ⟨Cval, hCval, max Nraw Ngood, ?_⟩
  intro n p R certificate deltaStar hN hpBand hguarded
  dsimp only
  have hNraw : Nraw ≤ n := by omega
  have hNgoodBound : Ngood ≤ n := by omega
  obtain ⟨hpool, hratioAll, hcutAll, hyRateN,
      hthreshold, hyCutoffN, hn⟩ :=
    hNgood n hNgoodBound
  obtain ⟨hS, hrawProfile⟩ :=
    hraw (n := n) (p := p) hNraw hpBand
  let S := bankPaperCanonicalRawSmoothBasePool W n
    (upperTailLength c n) K
  let D := R.roughCanonicalGuardSet certificate deltaStar ∩ S
  have hratio :
      (D.card : Real) / (S.card : Real) ≤ (1 : Real) / 2 := by
    simpa only [S, D] using hratioAll R certificate deltaStar
  have hguardedEq :
      R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K 1 = S \ D := by
    rw [roughCanonicalGuardedSmoothBasePool_eq_zeroHeadStructuredCell_sdiff
      R certificate deltaStar W K]
    rw [← bankPaperCanonicalRawSmoothBasePool_eq_zeroHeadStructuredCell
      W n (upperTailLength c n) K]
    dsimp only [S, D]
    ext a
    simp
  have hremaining : (S \ D).Nonempty := by
    simpa only [← hguardedEq] using hguarded
  have hp := prime_of_mem_primeBand hpBand
  have hpR : (0 : Real) < p := by exact_mod_cast hp.pos
  have hpY : (p : Real) ≤ (yNat n : Real) := by
    exact_mod_cast le_yNat_of_mem_primeBand hpBand
  have hL : 0 < L n := L_pos hn
  have hnR : (0 : Real) < (n : Real) := by
    exact_mod_cast (show 0 < n by omega)
  have hcut :=
    hcutAll p hpBand
  have hcutLe :
      (valuationCutoff p (physicalBound (2 : Real) n) : Real) ≤
        Cenv * L n := by
    have hmul := (div_le_iff₀ hL).mp hcut
    simpa only [Cenv, mul_comm] using hmul
  let KA : Real := Cenv * L n
  have hKA : 0 ≤ KA := by
    dsimp only [KA]
    positivity
  have hvaluation : ∀ m ∈ S, |valuation p m| ≤ KA := by
    intro m hm
    have hmData : m ∈
        structuredCell (roughHeadZeroPattern W) n
          (2 * n - K * upperTailLength c n) (yNat n) := by
      simpa only [S,
        bankPaperCanonicalRawSmoothBasePool_eq_zeroHeadStructuredCell]
        using hm
    have hmPos : 0 < m :=
      pos_of_mem_smoothInterval (mem_structuredCell.mp hmData).1
    have hmUpperRaw :
        m ≤ 2 * n - K * upperTailLength c n :=
      (mem_smoothInterval.mp (mem_structuredCell.mp hmData).1).2.1
    have hmUpper :
        m ≤ physicalBound (2 : Real) n := by
      rw [sharp_physicalBound_two]
      exact hmUpperRaw.trans (Nat.sub_le _ _)
    have hvNat :=
      factorization_le_valuationCutoff hp hmPos hmUpper
    rw [abs_of_nonneg (valuation_nonneg p m)]
    have hvCast :
        (valuation p m : Real) ≤
          (valuationCutoff p (physicalBound (2 : Real) n) : Real) := by
      unfold valuation
      exact_mod_cast hvNat
    exact hvCast.trans (by simpa only [KA] using hcutLe)
  have hdelete :=
    abs_uniformOnFinset_sdiff_expect_sub_uniformOnFinset_expect_le
      S D (by simpa only [S] using hS) hremaining
      (fun m ↦ valuation p m) hKA hvaluation hratio
  have hDcardNat : D.card ≤ yNat n := by
    have hfirst :=
      bankPaperCanonicalSmoothBaseGuardDeletionPool_card_le_anchorIntersection
        R certificate deltaStar W K
    have hsecond :=
      guardedCentralAnchors_inter_rawSmoothBasePool_card_le_yNat
        (h := upperTailLength c n)
        certificate W K hthreshold hyCutoffN
    simpa only [D, S, bankPaperCanonicalSmoothBaseGuardDeletionPool] using
      hfirst.trans hsecond
  have hDcard : (D.card : Real) ≤ (yNat n : Real) := by
    exact_mod_cast hDcardNat
  have hden : 0 < density * (n : Real) :=
    mul_pos hdensity hnR
  have hScard : 0 < (S.card : Real) :=
    hden.trans_le (by simpa only [density, S] using hpool)
  have hratioSharp :
      (D.card : Real) / (S.card : Real) ≤
        (yNat n : Real) / (density * (n : Real)) := by
    calc
      (D.card : Real) / (S.card : Real) ≤
          (yNat n : Real) / (S.card : Real) :=
        div_le_div_of_nonneg_right hDcard hScard.le
      _ ≤ (yNat n : Real) / (density * (n : Real)) :=
        div_le_div_of_nonneg_left (by positivity) hden
          (by simpa only [density, S] using hpool)
  have hyUnit :
      (yNat n : Real) ^ 2 * L n ^ 2 / (n : Real) ≤ 1 := by
    have hmul :=
      mul_le_mul_of_nonneg_right hyRateN (sq_nonneg (L n))
    have hcross :
        (yNat n : Real) ^ 2 * L n ^ 2 ≤ (n : Real) := by
      calc
        (yNat n : Real) ^ 2 * L n ^ 2 ≤
            (secondOrderScale n / L n) * L n ^ 2 := hmul
        _ = (n : Real) := by
          have hlogNe : Real.log (n : Real) ≠ 0 := by
            simpa only [Erdos390.Full.Scale.L] using hL.ne'
          unfold secondOrderScale Erdos390.Full.Scale.L
          field_simp [hlogNe]
    exact (div_le_one hnR).2 hcross
  have hdeleteRate :
      4 * KA * ((D.card : Real) / (S.card : Real)) ≤
        Cguard / ((p : Real) * L n) := by
    have hfirst :
        4 * KA * ((D.card : Real) / (S.card : Real)) ≤
          4 * (Cenv * L n) *
            ((yNat n : Real) / (density * (n : Real))) := by
      dsimp only [KA]
      exact mul_le_mul_of_nonneg_left hratioSharp
        (mul_nonneg (by positivity)
          (mul_nonneg hCenv.le hL.le))
    refine hfirst.trans ?_
    apply (le_div_iff₀ (mul_pos hpR hL)).2
    calc
      (4 * (Cenv * L n) *
          ((yNat n : Real) / (density * (n : Real)))) *
          ((p : Real) * L n) ≤
        (4 * (Cenv * L n) *
          ((yNat n : Real) / (density * (n : Real)))) *
          ((yNat n : Real) * L n) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hpY hL.le)
              (by positivity)
      _ = Cguard *
          ((yNat n : Real) ^ 2 * L n ^ 2 / (n : Real)) := by
        dsimp only [Cguard]
        field_simp [hdensity.ne', hnR.ne']
      _ ≤ Cguard * 1 :=
        mul_le_mul_of_nonneg_left hyUnit hCguard.le
      _ = Cguard := mul_one _
  have hdeleteProfile :
      |(uniformOnFinset
            (R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar W K 1) hguarded).expect
            (fun m ↦ valuation p (m : Nat)) -
        (uniformOnFinset S hS).expect
            (fun m ↦ valuation p (m : Nat))| ≤
          Cguard / ((p : Real) * L n) := by
    have hrawDelete :
        |(uniformOnFinset (S \ D) hremaining).expect
              (fun m ↦ valuation p (m : Nat)) -
          (uniformOnFinset S hS).expect
              (fun m ↦ valuation p (m : Nat))| ≤
            4 * KA * ((D.card : Real) / (S.card : Real)) := by
      exact hdelete
    have hreindex :
        (uniformOnFinset (S \ D) hremaining).expect
              (fun m ↦ valuation p (m : Nat)) =
          (uniformOnFinset
            (R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar W K 1) hguarded).expect
              (fun m ↦ valuation p (m : Nat)) := by
      have htilt :=
        uniformOnFinset_exponentialTilt_expect_eq_of_finset_eq
          (S \ D)
          (R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar W K 1)
          hguardedEq.symm hremaining hguarded
          (fun _ ↦ (0 : Real)) (fun _ ↦ (0 : Real))
          (by
            intro x y hxy
            rfl)
          (fun m : Nat ↦ valuation p m)
      simpa only [finiteProbability_exponentialTilt_zero_expect] using htilt
    rw [← hreindex]
    exact hrawDelete.trans hdeleteRate
  let Kcut := Nat.log p (yNat n ^ 4)
  let mainSum := ∑ j ∈ positiveExponents Kcut,
    paperDivisibilityMain n (p ^ j)
  change
    |(uniformOnFinset
          (R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar W K 1) hguarded).expect
          (fun m ↦ valuation p (m : Nat)) - mainSum| ≤
      Cval / ((p : Real) * L n)
  calc
    |(uniformOnFinset
          (R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar W K 1) hguarded).expect
          (fun m ↦ valuation p (m : Nat)) - mainSum| ≤
      |(uniformOnFinset
            (R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar W K 1) hguarded).expect
            (fun m ↦ valuation p (m : Nat)) -
        (uniformOnFinset S hS).expect
            (fun m ↦ valuation p (m : Nat))| +
      |(uniformOnFinset S hS).expect
            (fun m ↦ valuation p (m : Nat)) - mainSum| := by
        have htri := abs_add_le
          ((uniformOnFinset
              (R.roughCanonicalGuardedBroadCorrectionPool certificate
                deltaStar W K 1) hguarded).expect
              (fun m ↦ valuation p (m : Nat)) -
            (uniformOnFinset S hS).expect
              (fun m ↦ valuation p (m : Nat)))
          ((uniformOnFinset S hS).expect
              (fun m ↦ valuation p (m : Nat)) - mainSum)
        simpa only [sub_add_sub_cancel] using htri
    _ ≤ Cguard / ((p : Real) * L n) +
        Craw / ((p : Real) * L n) :=
      add_le_add hdeleteProfile (by
        simpa only [S, Kcut, mainSum] using hrawProfile)
    _ = Cval / ((p : Real) * L n) := by
      dsimp only [Cval]
      ring

end BankPaperRealization

end

end Erdos390.WholePaper
