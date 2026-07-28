import Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosure

/-!
# Sharp moving-prefix valuation profile for the smooth source

The label-one broad pool has a moving upper endpoint, so it is not one of the
fixed physical cells handled by the preceding file.  This file normalizes the
existing joint divisor/prefix theorem by the prefix mass, proves a uniform
reciprocal fallback on prefixes of fixed positive relative length, and then
sums the literal prime-power decomposition.

No comparison with a guarded pool, and no `O(1 / (p L))` conclusion, is used
as an input.
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
open Erdos390.Full.PrimePowerCovariance
open Erdos390.Full.PrimePowerCutoffCovariance
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.PaperMovingPrefixMarkedCell
open Erdos390.Full.PaperPrimePowerTailRate
open Erdos390.Full.PaperRawTiltedValuationMeanRows
open Erdos390.Full.LocalFugacityBounds
open Erdos390.Full.ValuationScoreDomination

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## Exact conditional-prefix normalization -/

/-- The mass of a physical prefix under the full-cell counting law is exactly
the ratio of the two literal cardinalities. -/
theorem uniformAverage_movingPrefix_indicator_eq_card_ratio
    (P : Pattern) {lo hi y k : Nat} (hk : k ≤ hi) :
    DivisibilityMomentBounds.uniformAverage
        (structuredCell P lo hi y)
        (fun m ↦ if m ≤ k then 1 else 0) =
      ((structuredCell P lo k y).card : Real) /
        ((structuredCell P lo hi y).card : Real) := by
  have hraw :=
    uniformAverage_divInd_mul_prefix_eq_markedCell_ratio
      P (lo := lo) (hi := hi) (y := y) (k := k) (d := 1) hk
  simpa [divInd, markedCell] using hraw

/-- Dividing the joint divisor/prefix probability by the prefix mass gives
the literal uniform divisor average on the moving prefix. -/
theorem uniformAverage_movingPrefix_divInd_eq_joint_div_prefixMass
    (P : Pattern) {lo hi y k d : Nat} (hk : k ≤ hi)
    (hfull : (structuredCell P lo hi y).Nonempty)
    (hprefix : (structuredCell P lo k y).Nonempty) :
    DivisibilityMomentBounds.uniformAverage
        (structuredCell P lo k y) (divInd d) =
      DivisibilityMomentBounds.uniformAverage
          (structuredCell P lo hi y)
          (fun m ↦ divInd d m * if m ≤ k then 1 else 0) /
        DivisibilityMomentBounds.uniformAverage
          (structuredCell P lo hi y)
          (fun m ↦ if m ≤ k then 1 else 0) := by
  rw [uniformAverage_divInd_mul_prefix_eq_markedCell_ratio P hk]
  rw [uniformAverage_movingPrefix_indicator_eq_card_ratio P hk]
  unfold DivisibilityMomentBounds.uniformAverage
  rw [DivisibilityMomentBounds.sum_divInd_eq_card_filter]
  have hfullCard :
      ((structuredCell P lo hi y).card : Real) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hfull
  have hprefixCard :
      ((structuredCell P lo k y).card : Real) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hprefix
  change
    ((markedCell P lo k y d).card : Real) /
          ((structuredCell P lo k y).card : Real) =
      (((markedCell P lo k y d).card : Real) /
          ((structuredCell P lo hi y).card : Real)) /
        (((structuredCell P lo k y).card : Real) /
          ((structuredCell P lo hi y).card : Real))
  field_simp [hfullCard, hprefixCard]

/-! ## Sharp divisor profiles on positive-length prefixes -/

/-- Every moving prefix occupying a fixed positive proportion of its ambient
physical cell has the same normalized Dickman divisor profile, with the
sharp `1 / (d * L)` error. -/
theorem
    exists_uniform_movingPrefix_uniformAverage_divInd_paper_bound_of_fraction
    (P : Pattern) {A C rmin : Real}
    (hA : 0 < A) (hAC : A < C) (hrmin : 0 < rmin) :
    ∃ K : Real, 0 < K ∧ ∃ N₀ : Nat,
      ∀ {n k d : Nat}, N₀ ≤ n →
        physicalBound A n < k → k ≤ physicalBound C n →
        rmin ≤ prefixFraction A C n k →
        0 < d → d ≤ yNat n ^ 4 →
        d ∈ Nat.smoothNumbers (yNat n + 1) →
        Nat.Coprime d P.modulus →
        let S := structuredCell P (physicalBound A n) k (yNat n)
        ∃ _hS : S.Nonempty,
          |DivisibilityMomentBounds.uniformAverage S (divInd d) -
              paperDivisibilityMain n d| ≤
            K / ((d : Real) * L n) := by
  obtain ⟨Kjoint, hKjoint, Njoint, hjoint⟩ :=
    exists_uniform_movingPrefix_uniformAverage_divInd_bound P hA hAC
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlargeL : ∀ᶠ n : Nat in atTop,
      2 * Kjoint / rmin ≤ L n :=
    hLTop.eventually (eventually_ge_atTop (2 * Kjoint / rmin))
  obtain ⟨NL, hNL⟩ := Filter.eventually_atTop.mp hlargeL
  have hrho : 0 < DickmanBasic.rho DickmanBasic.U :=
    DickmanBasic.rho_U_pos
  let Aprofile : Real := Kjoint + Kjoint / DickmanBasic.rho DickmanBasic.U
  let K : Real := 2 * Aprofile / rmin
  have hAprofile : 0 < Aprofile := by
    dsimp only [Aprofile]
    exact add_pos_of_pos_of_nonneg hKjoint
      (div_nonneg hKjoint.le hrho.le)
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, max Njoint NL, ?_⟩
  intro n k d hN hlow hhigh hfrac hd hd4 hdsmooth hcop
  dsimp only
  have hNjoint : Njoint ≤ n := by omega
  have hNLbound : NL ≤ n := by omega
  have hLlarge := hNL n hNLbound
  have hn : 1 < n := by
    by_contra hnle
    have hLle : L n ≤ 0 := by
      unfold L
      rw [Real.log_nonpos_iff (by positivity)]
      exact_mod_cast Nat.le_of_not_gt hnle
    have hlargePos : 0 < 2 * Kjoint / rmin := by positivity
    linarith
  have hL : 0 < L n := L_pos hn
  have hdR : (0 : Real) < d := by exact_mod_cast hd
  let Sfull := structuredCell P
    (physicalBound A n) (physicalBound C n) (yNat n)
  let S := structuredCell P (physicalBound A n) k (yNat n)
  let x : Real := DivisibilityMomentBounds.uniformAverage Sfull
    (fun m ↦ divInd d m * if m ≤ k then 1 else 0)
  let b : Real := DivisibilityMomentBounds.uniformAverage Sfull
    (fun m ↦ if m ≤ k then 1 else 0)
  let r : Real := prefixFraction A C n k
  let t : Real := paperDivisibilityMain n d
  have hjRaw :=
    hjoint hNjoint hlow hhigh hd hd4 hdsmooth hcop
  have hfull : Sfull.Nonempty := by
    simpa only [Sfull] using hjRaw.1
  have hx :
      |x - r * t| ≤ Kjoint / ((d : Real) * L n) := by
    simpa only [x, r, t, Sfull] using hjRaw.2
  have hOneLe : 1 ≤ yNat n ^ 4 :=
    (show 1 ≤ d by omega).trans hd4
  have hbRaw :=
    hjoint (n := n) (k := k) (d := 1) hNjoint hlow hhigh
      (by omega) hOneLe (by simp [Nat.mem_smoothNumbers]) (by simp)
  have hb :
      |b - r| ≤ Kjoint / L n := by
    dsimp only [b, r, Sfull]
    simpa [paperDivisibilityMain_one, divInd] using hbRaw.2
  have hrpos : 0 < r := by
    dsimp only [r]
    exact hrmin.trans_le hfrac
  have hKoverL : Kjoint / L n ≤ rmin / 2 := by
    have htwoK : 2 * Kjoint ≤ L n * rmin :=
      (div_le_iff₀ hrmin).mp hLlarge
    apply (div_le_iff₀ hL).2
    nlinarith
  have hbLower : r / 2 ≤ b := by
    have hdiff : r - b ≤ |b - r| := by
      rw [abs_sub_comm]
      exact le_abs_self (r - b)
    have hminHalf : rmin / 2 ≤ r / 2 := by linarith
    linarith
  have hbpos : 0 < b := (half_pos hrpos).trans_le hbLower
  have hmassExact :
      b = ((S.card : Real) / (Sfull.card : Real)) := by
    dsimp only [b, S, Sfull]
    exact uniformAverage_movingPrefix_indicator_eq_card_ratio P hhigh
  have hSCardPos : 0 < (S.card : Real) := by
    rw [hmassExact] at hbpos
    rcases (div_pos_iff.mp hbpos) with hcase | hcase
    · exact hcase.1
    · have hnot : ¬(Sfull.card : Real) < 0 :=
        not_lt_of_ge (by positivity)
      exact (hnot hcase.2).elim
  have hS : S.Nonempty :=
    Finset.card_pos.mp (by exact_mod_cast hSCardPos)
  refine ⟨hS, ?_⟩
  have htRange := paperDivisibilityMain_nonneg_le hn hd hd4
  have ht0 : 0 ≤ t := by simpa only [t] using htRange.1
  have htUpper :
      t ≤ 1 / (DickmanBasic.rho DickmanBasic.U * (d : Real)) := by
    simpa only [t] using htRange.2
  have hratio :=
    abs_normalized_ratio_sub_le hrpos hbLower hx hb ht0
  have hF0 : 0 ≤ Kjoint / L n :=
    div_nonneg hKjoint.le hL.le
  have htF :
      t * (Kjoint / L n) ≤
        (1 / (DickmanBasic.rho DickmanBasic.U * (d : Real))) *
          (Kjoint / L n) :=
    mul_le_mul_of_nonneg_right htUpper hF0
  have hnumerator :
      Kjoint / ((d : Real) * L n) +
          t * (Kjoint / L n) ≤
        Aprofile / ((d : Real) * L n) := by
    calc
      Kjoint / ((d : Real) * L n) +
          t * (Kjoint / L n) ≤
        Kjoint / ((d : Real) * L n) +
          (1 / (DickmanBasic.rho DickmanBasic.U * (d : Real))) *
            (Kjoint / L n) :=
          add_le_add (le_refl _) htF
      _ = Aprofile / ((d : Real) * L n) := by
        dsimp only [Aprofile]
        field_simp [hrho.ne', hdR.ne', hL.ne']
  have hnum0 :
      0 ≤ Aprofile / ((d : Real) * L n) := by positivity
  have hbound :
      2 *
          (Kjoint / ((d : Real) * L n) +
            t * (Kjoint / L n)) / r ≤
        K / ((d : Real) * L n) := by
    calc
      2 *
          (Kjoint / ((d : Real) * L n) +
            t * (Kjoint / L n)) / r ≤
        2 * (Aprofile / ((d : Real) * L n)) / r := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hnumerator (by norm_num)) hrpos.le
      _ ≤ 2 * (Aprofile / ((d : Real) * L n)) / rmin := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg (by norm_num) hnum0) hrmin hfrac
      _ = K / ((d : Real) * L n) := by
        dsimp only [K]
        field_simp [hrmin.ne', hdR.ne', hL.ne']
  rw [
    uniformAverage_movingPrefix_divInd_eq_joint_div_prefixMass
      P hhigh hfull hS]
  change |x / b - t| ≤ _
  exact hratio.trans hbound

/-! ## Reciprocal fallback on positive-length prefixes -/

/-- Positive relative prefix length supplies a uniform linear density lower
bound, expressed at the physical upper scale used by the elementary multiple
counting fallback. -/
theorem exists_uniform_movingPrefix_density_lower_bound_of_fraction
    (P : Pattern) {A C rmin : Real}
    (hA : 0 < A) (hAC : A < C) (hC : 0 < C) (hrmin : 0 < rmin) :
    ∃ cprefix : Real, 0 < cprefix ∧ ∃ N₀ : Nat,
      ∀ {n k : Nat}, N₀ ≤ n →
        physicalBound A n < k → k ≤ physicalBound C n →
        rmin ≤ prefixFraction A C n k →
        0 < physicalBound C n ∧
          cprefix * (physicalBound C n : Real) ≤
            ((structuredCell P (physicalBound A n) k (yNat n)).card :
              Real) := by
  obtain ⟨Kjoint, hKjoint, Njoint, hjoint⟩ :=
    exists_uniform_movingPrefix_uniformAverage_divInd_bound P hA hAC
  obtain ⟨Ndensity, hdensity⟩ :=
    exists_structuredCell_density_lower_bound P hA hAC
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlargeL : ∀ᶠ n : Nat in atTop,
      2 * Kjoint / rmin ≤ L n :=
    hLTop.eventually (eventually_ge_atTop (2 * Kjoint / rmin))
  obtain ⟨NL, hNL⟩ := Filter.eventually_atTop.mp hlargeL
  have hphysEvent : ∀ᶠ n : Nat in atTop,
      1 ≤ physicalBound C n := by
    have hcastTop : Tendsto (fun n : Nat ↦ (n : Real)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    filter_upwards [hcastTop.eventually
      (eventually_ge_atTop (1 / C))] with n hn
    unfold physicalBound
    apply Nat.le_floor
    have := (div_le_iff₀ hC).mp hn
    exact_mod_cast (show (1 : Real) ≤ C * (n : Real) by
      simpa [mul_comm] using this)
  obtain ⟨Nphys, hNphys⟩ := Filter.eventually_atTop.mp hphysEvent
  let cfull : Real := paperCellDensity P A C
  have hcfull : 0 < cfull := paperCellDensity_pos P hAC
  let cprefix : Real := rmin * cfull / (4 * C)
  have hcprefix : 0 < cprefix := by
    dsimp only [cprefix]
    positivity
  refine ⟨cprefix, hcprefix,
    max 2 (max Njoint (max Ndensity (max NL Nphys))), ?_⟩
  intro n k hN hlow hhigh hfrac
  have hn : 1 < n := by omega
  have hNjoint : Njoint ≤ n := by omega
  have hNdensity : Ndensity ≤ n := by omega
  have hNLbound : NL ≤ n := by omega
  have hNphysBound : Nphys ≤ n := by omega
  have hL : 0 < L n := L_pos hn
  have hLlarge := hNL n hNLbound
  have hMpos : 0 < physicalBound C n := by
    have := hNphys n hNphysBound
    omega
  let Sfull := structuredCell P
    (physicalBound A n) (physicalBound C n) (yNat n)
  let S := structuredCell P (physicalBound A n) k (yNat n)
  let b : Real := DivisibilityMomentBounds.uniformAverage Sfull
    (fun m ↦ if m ≤ k then 1 else 0)
  let r : Real := prefixFraction A C n k
  have hOneLe : 1 ≤ yNat n ^ 4 := by
    have hYone : 1 ≤ yNat n := by
      rw [yNat]
      apply Nat.le_floor
      rw [y]
      have hnOneR : (1 : Real) ≤ (n : Real) := by
        exact_mod_cast (show 1 ≤ n by omega)
      simpa only [Nat.cast_one] using
        Real.one_le_rpow hnOneR
          (by norm_num : (0 : Real) ≤ 2 / 9)
    exact one_le_pow₀ hYone
  have hbRaw :=
    hjoint (n := n) (k := k) (d := 1) hNjoint hlow hhigh
      (by omega) hOneLe (by simp [Nat.mem_smoothNumbers]) (by simp)
  have hfull : Sfull.Nonempty := by
    simpa only [Sfull] using hbRaw.1
  have hb :
      |b - r| ≤ Kjoint / L n := by
    dsimp only [b, r, Sfull]
    simpa [paperDivisibilityMain_one, divInd] using hbRaw.2
  have hKoverL : Kjoint / L n ≤ rmin / 2 := by
    have htwoK : 2 * Kjoint ≤ L n * rmin :=
      (div_le_iff₀ hrmin).mp hLlarge
    apply (div_le_iff₀ hL).2
    nlinarith
  have hbLower : rmin / 2 ≤ b := by
    have hdiff : r - b ≤ |b - r| := by
      rw [abs_sub_comm]
      exact le_abs_self (r - b)
    have hrLower : rmin ≤ r := by simpa only [r] using hfrac
    linarith
  have hmassExact :
      b = ((S.card : Real) / (Sfull.card : Real)) := by
    dsimp only [b, S, Sfull]
    exact uniformAverage_movingPrefix_indicator_eq_card_ratio P hhigh
  have hfullCard :
      (0 : Real) < (Sfull.card : Real) := by
    exact_mod_cast Finset.card_pos.mpr hfull
  have hcardEq :
      (S.card : Real) = b * (Sfull.card : Real) := by
    rw [hmassExact]
    field_simp [hfullCard.ne']
  have hfullDensity :
      cfull * (n : Real) / 2 ≤ (Sfull.card : Real) := by
    simpa only [cfull, Sfull] using hdensity hNdensity
  have hprod :
      (rmin / 2) * (cfull * (n : Real) / 2) ≤
        b * (Sfull.card : Real) := by
    exact mul_le_mul hbLower hfullDensity
      (by positivity) (by linarith)
  have hMcast :
      (physicalBound C n : Real) ≤ C * (n : Real) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hC.le (by positivity))
  refine ⟨hMpos, ?_⟩
  calc
    cprefix * (physicalBound C n : Real) ≤
        cprefix * (C * (n : Real)) :=
      mul_le_mul_of_nonneg_left hMcast hcprefix.le
    _ = (rmin / 2) * (cfull * (n : Real) / 2) := by
      dsimp only [cprefix]
      field_simp [hC.ne']
      ring
    _ ≤ b * (Sfull.card : Real) := hprod
    _ = (S.card : Real) := hcardEq.symm

/-- Arbitrary divisor events on a positive-length moving prefix satisfy a
uniform reciprocal bound.  This supplies the unrestricted prime-power tail
without extending the four-mark chamber. -/
theorem exists_uniform_movingPrefix_divInd_fallback_of_fraction
    (P : Pattern) {A C rmin : Real}
    (hA : 0 < A) (hAC : A < C) (hC : 0 < C) (hrmin : 0 < rmin) :
    ∃ G : Real, 0 < G ∧ ∃ N₀ : Nat,
      ∀ {n k : Nat}, N₀ ≤ n →
        physicalBound A n < k → k ≤ physicalBound C n →
        rmin ≤ prefixFraction A C n k →
        let S := structuredCell P (physicalBound A n) k (yNat n)
        ∀ hS : S.Nonempty, ∀ D : Nat, 0 < D →
          (uniformOnFinset S hS).expect
              (fun m ↦ divInd D (m : Nat)) ≤
            G / (D : Real) := by
  obtain ⟨cprefix, hcprefix, N₀, hdensity⟩ :=
    exists_uniform_movingPrefix_density_lower_bound_of_fraction
      P hA hAC hC hrmin
  let G : Real := 1 / cprefix
  have hG : 0 < G := one_div_pos.mpr hcprefix
  refine ⟨G, hG, N₀, ?_⟩
  intro n k hN hlow hhigh hfrac
  dsimp only
  intro hS D hD
  let S := structuredCell P (physicalBound A n) k (yNat n)
  obtain ⟨hMpos, hcard⟩ :=
    hdensity hN hlow hhigh hfrac
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    exact pos_of_mem_smoothInterval (mem_structuredCell.mp hm).1
  have hSle : ∀ m ∈ S, m ≤ physicalBound C n := by
    intro m hm
    exact
      ((mem_smoothInterval.mp (mem_structuredCell.mp hm).1).2.1).trans
        hhigh
  rw [Erdos390.Full.OmittedScoreCell.uniform_expect_eq_uniformAverage]
  have hraw :=
    OmittedTiltFallback.uniformAverage_divInd_le S hD hMpos hcprefix
      hcard hSpos hSle
  calc
    DivisibilityMomentBounds.uniformAverage S (divInd D) ≤
        1 / (cprefix * (D : Real)) := hraw
    _ = G / (D : Real) := by
      dsimp only [G]
      ring

/-! ## Full valuation on the moving prefix -/

/-- The literal full valuation on every moving prefix of fixed positive
relative length has the same truncated Dickman profile as the fixed cells,
with a uniform `1 / (p * L)` error for every medium prime. -/
theorem
    exists_uniform_movingPrefix_valuation_mean_profile_paperRate_of_fraction
    (P : Pattern) {A C rmin : Real}
    (hA : 0 < A) (hAC : A < C) (hC : 0 < C) (hrmin : 0 < rmin)
    (W : Nat) (_hW : 1 < W)
    (hHeadLe : ∀ q ∈ P.primes, q ≤ W) :
    ∃ Cval : Real, 0 < Cval ∧ ∃ N₀ : Nat,
      ∀ {n k p : Nat}, N₀ ≤ n →
        physicalBound A n < k → k ≤ physicalBound C n →
        rmin ≤ prefixFraction A C n k →
        p ∈ primeBand n W →
        let S := structuredCell P (physicalBound A n) k (yNat n)
        let Kcut := Nat.log p (yNat n ^ 4)
        ∃ hS : S.Nonempty,
          |(uniformOnFinset S hS).expect
                (fun m ↦ valuation p (m : Nat)) -
            ∑ j ∈ positiveExponents Kcut,
              paperDivisibilityMain n (p ^ j)| ≤
            Cval / ((p : Real) * L n) := by
  obtain ⟨K, hK, Nprofile, hprofile⟩ :=
    exists_uniform_movingPrefix_uniformAverage_divInd_paper_bound_of_fraction
      P hA hAC hrmin
  obtain ⟨G, hG, Nfallback, hfallback⟩ :=
    exists_uniform_movingPrefix_divInd_fallback_of_fraction
      P hA hAC hC hrmin
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
  refine ⟨Cval, hCval,
    max Nprofile (max Nfallback Ngood), ?_⟩
  intro n k p hN hlow hhigh hfrac hpBand
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
  let S := structuredCell P (physicalBound A n) k (yNat n)
  let Kcut : Nat := Nat.log p (yNat n ^ 4)
  let main : Nat → Real := fun j ↦
    paperDivisibilityMain n (p ^ j)
  let mainSum : Real := ∑ j ∈ positiveExponents Kcut, main j
  obtain ⟨hS, hprofileP⟩ :=
    hprofile (n := n) (k := k) (d := p)
      hNprofile hlow hhigh hfrac hp.pos hp4 hpSmooth hpHead
  refine ⟨by simpa only [S] using hS, ?_⟩
  have hS' : S.Nonempty := by simpa only [S] using hS
  let mu := uniformOnFinset S hS'
  let trunc : S → Real := fun m ↦
    ∑ j ∈ positiveExponents Kcut, divInd (p ^ j) (m : Nat)
  let tail : S → Real := fun m ↦ valuation p (m : Nat) - trunc m
  have hprofilePower (j : Nat)
      (hj : j ∈ positiveExponents Kcut) :
      |mu.expect (fun m ↦ divInd (p ^ j) (m : Nat)) - main j| ≤
        K / (((p ^ j : Nat) : Real) * L n) := by
    have hjLe : j ≤ Kcut := (mem_positiveExponents.mp hj).2
    have hY4pos : 0 < yNat n ^ 4 :=
      pow_pos (hp.pos.trans_le hpY) 4
    have hpK : p ^ Kcut ≤ yNat n ^ 4 :=
      Nat.pow_log_le_self p hY4pos.ne'
    have hpj4 : p ^ j ≤ yNat n ^ 4 :=
      (Nat.pow_le_pow_right hp.pos hjLe).trans hpK
    have hpjSmooth := StructuredCells.pow_mem_smoothNumbers hpSmooth j
    have hpjHead := hpHead.pow_left j
    obtain ⟨hSj, hraw⟩ :=
      hprofile (n := n) (k := k) (d := p ^ j)
        hNprofile hlow hhigh hfrac
        (pow_pos hp.pos j) hpj4 hpjSmooth hpjHead
    rw [OmittedScoreCell.uniform_expect_eq_uniformAverage]
    simpa only [S, mu, main] using hraw
  have hdiv (D : Nat) (hD : 0 < D) :
      mu.expect (fun m ↦ divInd D (m : Nat)) ≤
        G * (1 / (D : Real)) := by
    have hraw :=
      hfallback (n := n) (k := k) hNfallback
        hlow hhigh hfrac hS' D hD
    simpa only [S, mu, div_eq_mul_inv, one_mul] using hraw
  have hvaluePos : ∀ m : S, 0 < (m : Nat) := by
    intro m
    exact pos_of_mem_smoothInterval (mem_structuredCell.mp m.property).1
  have hvalueLe : ∀ m : S, (m : Nat) ≤ physicalBound C n := by
    intro m
    exact
      ((mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1).trans
        hhigh
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
              ∑ j ∈ positiveExponents Kcut,
                divInd (p ^ j) (m : Nat))| ≤
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
      (∑ j ∈ positiveExponents Kcut,
          1 / (((p ^ j : Nat) : Real))) ≤
        2 / (p : Real) :=
    ValuationScoreDomination.sum_inv_prime_powers_le p Kcut hp.two_le
  have htruncExpand :
      mu.expect trunc =
        ∑ j ∈ positiveExponents Kcut,
          mu.expect (fun m ↦ divInd (p ^ j) (m : Nat)) := by
    exact
      PrimePowerCutoffCovariance.FiniteProbability.expect_sum mu
        (positiveExponents Kcut)
        (fun j m ↦ divInd (p ^ j) (m : Nat))
  have htrunc :
      |mu.expect trunc - mainSum| ≤
        ((2 * K) / L n) * (1 / (p : Real)) := by
    rw [htruncExpand]
    dsimp only [mainSum]
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ j ∈ positiveExponents Kcut,
          (mu.expect (fun m ↦ divInd (p ^ j) (m : Nat)) - main j)| ≤
        ∑ j ∈ positiveExponents Kcut,
          |mu.expect (fun m ↦ divInd (p ^ j) (m : Nat)) - main j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ positiveExponents Kcut,
          K / (((p ^ j : Nat) : Real) * L n) := by
        exact Finset.sum_le_sum fun j hj ↦ hprofilePower j hj
      _ = (K / L n) *
          (∑ j ∈ positiveExponents Kcut,
            1 / (((p ^ j : Nat) : Real))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
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

end BankPaperRealization

end

end Erdos390.WholePaper
