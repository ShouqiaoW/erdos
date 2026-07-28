import Erdos390.Full.PaperRawPrefixThirdCumulantFallback
import Erdos390.Full.PaperPrimePowerTailLedger
import Erdos390.Full.PaperPrimePowerTailRow
import Erdos390.Full.PrimePowerCutoffCovariance
import Erdos390.Full.StructuredCellValuationLaw

/-!
# The raw full-valuation moving-prefix row

This file sums the divisor-prefix estimates over the exact local prime-power
cutoff.  Prime powers in the four-mark chamber use the sharp moving-prefix
estimate.  The remaining powers use the reciprocal fallback and the literal
weighted diagonal tail ledger.  The result is an explicit `p⁻¹` row whose
coefficient tends to zero at the rate required in paper Lemma 8.6.
-/

open Filter
open scoped BigOperators

namespace Erdos390.Full

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance PrimePowerCutoffCovariance
open PaperPrimePowerTailLedger LocalFugacityBounds ValuationCutoff
open PaperPrimePowerTailRow

noncomputable section

namespace PaperRawPrefixValuationRow

/-- A row coefficient dominating both the chamber contribution and the
literal beyond-four tail. -/
def rawValuationPrefixRateMajorant (K G : ℝ) (W n : ℕ) : ℝ :=
  2 * K / L n + tailRowMajorant G W n

/-- The explicit tail in `exists_uniform_rawCell_valuation_prefix_bound`,
after multiplication by its row prime, is absorbed by the already audited
common tail-row majorant. -/
theorem eventually_rawValuationPrefix_rowCoefficient_le
    (K G : ℝ) (W : ℕ) (hG : 0 ≤ G) (hW : 1 < W) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ p ∈ primeBand n W,
      (p : ℝ) *
          ((2 * K / L n) * (1 / (p : ℝ)) +
            (4 * G * (cutoffScale W * L n) ^ 2) /
              ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) ≤
        rawValuationPrefixRateMajorant K G W n := by
  filter_upwards [Filter.eventually_gt_atTop 1] with n hn
  intro p hpBand
  have hp := prime_of_mem_primeBand hpBand
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hpR0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hKscale : 0 ≤ (cutoffScale W * L n) ^ 2 := sq_nonneg _
  have hYsq : 0 ≤ (yNat n : ℝ) ^ 2 := sq_nonneg _
  have htail0 : 0 ≤ tailRowMajorant G W n :=
    tailRowMajorant_nonneg hG hW hn
  have htailPiece :
      (p : ℝ) *
          ((4 * G * (cutoffScale W * L n) ^ 2) /
            ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) ≤
        6 * G *
          ((cutoffScale W * L n) ^ 2 / (yNat n : ℝ) ^ 2) := by
    have hnum : 0 ≤ 4 * G * (cutoffScale W * L n) ^ 2 := by positivity
    have hpInv : (1 : ℝ) / p ≤ 1 := by
      simpa using one_div_le_one_div_of_le
        (show (0 : ℝ) < 1 by norm_num) hpR
    calc
      (p : ℝ) *
          ((4 * G * (cutoffScale W * L n) ^ 2) /
            ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) =
        (4 * G) * (1 / (p : ℝ)) *
          ((cutoffScale W * L n) ^ 2 / (yNat n : ℝ) ^ 2) := by
        field_simp [hpR0.ne']
      _ ≤ (4 * G) * 1 *
          ((cutoffScale W * L n) ^ 2 / (yNat n : ℝ) ^ 2) := by
        gcongr
      _ ≤ 6 * G *
          ((cutoffScale W * L n) ^ 2 / (yNat n : ℝ) ^ 2) := by
        have hratio : 0 ≤
            (cutoffScale W * L n) ^ 2 / (yNat n : ℝ) ^ 2 :=
          div_nonneg hKscale hYsq
        nlinarith
  have hpieceLe :
      6 * G *
          ((cutoffScale W * L n) ^ 2 / (yNat n : ℝ) ^ 2) ≤
        tailRowMajorant G W n := by
    unfold tailRowMajorant
    dsimp only
    have hT : 0 ≤ G + G ^ 2 := by nlinarith [sq_nonneg G]
    have hband : 0 ≤ PrimeSums.bandReciprocalSum n W := by
      unfold PrimeSums.bandReciprocalSum
      positivity
    have hscale : 0 ≤ cutoffScale W * L n :=
      mul_nonneg (cutoffScale_pos hW).le (L_pos hn).le
    have hY : 0 ≤ (yNat n : ℝ) := by positivity
    have hYrpow : 0 ≤ (yNat n : ℝ) ^ (2 / 3 : ℝ) :=
      Real.rpow_nonneg hY _
    exact le_add_of_nonneg_left (add_nonneg
      (mul_nonneg hT (mul_nonneg (div_nonneg hscale hY)
        (by linarith)))
      (mul_nonneg hT (div_nonneg hKscale hYrpow)))
  unfold rawValuationPrefixRateMajorant
  calc
    (p : ℝ) *
        ((2 * K / L n) * (1 / (p : ℝ)) +
          (4 * G * (cutoffScale W * L n) ^ 2) /
            ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) =
      2 * K / L n +
        (p : ℝ) *
          ((4 * G * (cutoffScale W * L n) ^ 2) /
            ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) := by
      field_simp [hpR0.ne']
    _ ≤ 2 * K / L n + tailRowMajorant G W n :=
      add_le_add_right (htailPiece.trans hpieceLe) _

/-- The raw un-tilted moving-prefix row survives the additional moving-low
harmonic loss. -/
theorem tendsto_rawValuationPrefixRateMajorant_mul_logL_zero
    (K G : ℝ) (W : ℕ) (hG : 0 ≤ G) (hW : 1 < W) :
    Filter.Tendsto (fun n : ℕ ↦
      rawValuationPrefixRateMajorant K G W n * Real.log (L n))
      Filter.atTop (nhds 0) := by
  have hLTop : Filter.Tendsto L Filter.atTop Filter.atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hone : Filter.Tendsto
      (fun n : ℕ ↦ Real.log (L n) / L n)
      Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hfirst : Filter.Tendsto
      (fun n : ℕ ↦ (2 * K / L n) * Real.log (L n))
      Filter.atTop (nhds 0) := by
    have hconst : Filter.Tendsto (fun _n : ℕ ↦ 2 * K)
        Filter.atTop (nhds (2 * K)) := tendsto_const_nhds
    have hraw := hconst.mul hone
    have heq :
        (fun n : ℕ ↦ (2 * K / L n) * Real.log (L n)) =
          fun n : ℕ ↦ 2 * K * (Real.log (L n) / L n) := by
      funext n
      ring
    rw [heq]
    simpa only [mul_zero] using hraw
  have htail := tendsto_tailRowMajorant_mul_logL_zero G W hG hW
  unfold rawValuationPrefixRateMajorant
  simpa only [add_mul, zero_add] using hfirst.add htail

/-- On one raw structured cell, the genuine full valuation has a uniformly
small covariance with every moving physical prefix.  The second displayed
term is the exact beyond-four contribution; no infinite prime-power series
or asymptotic `O`-notation is hidden in the statement. -/
theorem exists_uniform_rawCell_valuation_prefix_bound
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) (W : ℕ) (hW : 1 < W)
    (hHeadLe : ∀ q ∈ H.primes, q ≤ W) :
    ∃ K : ℝ, 0 < K ∧ ∃ G : ℝ, 0 < G ∧ ∃ N₀ : ℕ,
      ∀ {n k p : ℕ}, N₀ ≤ n →
      physicalBound A n < k → k ≤ physicalBound C n →
      p ∈ primeBand n W →
      let S := structuredCell H (physicalBound A n) (physicalBound C n)
        (yNat n)
      ∀ hS : S.Nonempty,
        |(uniformOnFinset S hS).covariance
            (fun m : S ↦ valuation p (m : ℕ))
            (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
          (2 * K / L n) * (1 / (p : ℝ)) +
            (4 * G * (cutoffScale W * L n) ^ 2) /
              ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) := by
  obtain ⟨K, hK, Nmove, hmove⟩ :=
    PaperMovingPrefixMarkedCell.exists_uniform_movingPrefix_divInd_covariance_bound
      H hA hAC
  obtain ⟨G, hG, Ndiv, hdiv⟩ :=
    PaperRawPrefixThirdCumulantFallback.exists_uniform_rawCell_divInd_fallback
      H hA hAC hC
  have htailEvent := eventually_actual_diagonal_weighted_reciprocal_tail_le
    C W hC hW
  obtain ⟨Ntail, htail⟩ := Filter.eventually_atTop.mp htailEvent
  refine ⟨K, hK, G, hG, max 2 (max Nmove (max Ndiv Ntail)), ?_⟩
  intro n k p hN hlow hhigh hpBand
  have hn : 1 < n := by omega
  have hNmove : Nmove ≤ n := by omega
  have hNdiv : Ndiv ≤ n := by omega
  have hNtail : Ntail ≤ n := by omega
  have hp := prime_of_mem_primeBand hpBand
  have hpY : p ≤ yNat n := le_yNat_of_mem_primeBand hpBand
  have hY2 : 2 ≤ yNat n := hp.two_le.trans hpY
  have hp4 : p ≤ yNat n ^ 4 := hpY.trans (Nat.le_pow (by omega : 0 < 4))
  have hpSmooth : p ∈ Nat.smoothNumbers (yNat n + 1) :=
    Nat.mem_smoothNumbers_of_lt hp.pos (Nat.lt_succ_of_le hpY)
  have hpHead : Nat.Coprime p H.modulus :=
    PaperPrimePowerAuxiliaryPrime.coprime_modulus_of_mem_primeBand_of_headSupport
      H hHeadLe hpBand
  let M := physicalBound C n
  let R := actualExponentCutoff C n p
  let S := structuredCell H (physicalBound A n) M (yNat n)
  change ∀ hS : S.Nonempty,
    |(uniformOnFinset S hS).covariance
        (fun m : S ↦ valuation p (m : ℕ))
        (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤ _
  intro hS
  let mu := uniformOnFinset S hS
  let pref : S → ℝ := fun m ↦ if (m : ℕ) ≤ k then 1 else 0
  let law : BoundedValuationLaw S M :=
    StructuredCellValuationLaw.ofProbability H (physicalBound A n) M
      (yNat n) mu
  have hdecomp :
      (fun m : S ↦ valuation p (m : ℕ)) =
        fun m : S ↦ divInd p (m : ℕ) +
          ∑ r ∈ highExponents R, divInd (p ^ r) (m : ℕ) := by
    funext m
    change law.V p m = law.I p m +
      ∑ r ∈ highExponents R, law.Ip p r m
    rw [law.V_eq_I_add_J,
      PrimePowerCutoffCovariance.J_eq_valuationCutoff_sum law hp]
    rfl
  have hpref0 : ∀ m : S, 0 ≤ pref m := by
    intro m
    dsimp only [pref]
    split_ifs <;> norm_num
  have hpref1 : ∀ m : S, pref m ≤ 1 := by
    intro m
    dsimp only [pref]
    split_ifs <;> norm_num
  have hsharp (r : ℕ) (hr : 1 ≤ r) (hr4 : p ^ r ≤ yNat n ^ 4) :
      |mu.covariance (fun m : S ↦ divInd (p ^ r) (m : ℕ)) pref| ≤
        K / (((p ^ r : ℕ) : ℝ) * L n) := by
    have hpowSmooth := StructuredCells.pow_mem_smoothNumbers hpSmooth r
    have hpowHead := hpHead.pow_left r
    obtain ⟨hS', hraw⟩ := hmove hNmove hlow hhigh
      (pow_pos hp.pos r) hr4 hpowSmooth hpowHead
    simpa only [S, M, mu, pref] using hraw
  have hfallback (r : ℕ) (hr : 1 ≤ r) :
      |mu.covariance (fun m : S ↦ divInd (p ^ r) (m : ℕ)) pref| ≤
        2 * G / ((p ^ r : ℕ) : ℝ) := by
    have hdivPow :
        mu.expect (fun m : S ↦ divInd (p ^ r) (m : ℕ)) ≤
          G / ((p ^ r : ℕ) : ℝ) := by
      simpa only [S, M, mu] using
        hdiv hNdiv hS (p ^ r) (pow_pos hp.pos r)
    exact mu.abs_covariance_divInd_prefix_le_of_reciprocal_expectation
      (fun m : S ↦ (m : ℕ)) pref (pow_pos hp.pos r)
      hpref0 hpref1 hdivPow
  let inside := (highExponents R).filter (fun r ↦ p ^ r ≤ yNat n ^ 4)
  let outside := (highExponents R).filter (fun r ↦ ¬p ^ r ≤ yNat n ^ 4)
  have hsplit (F : ℕ → ℝ) :
      (∑ r ∈ highExponents R, F r) =
        (∑ r ∈ inside, F r) + ∑ r ∈ outside, F r := by
    dsimp only [inside, outside]
    exact (Finset.sum_filter_add_sum_filter_not
      (highExponents R) (fun r ↦ p ^ r ≤ yNat n ^ 4) F).symm
  have hfirst :
      |mu.covariance (fun m : S ↦ divInd p (m : ℕ)) pref| ≤
        K / ((p : ℝ) * L n) := by
    simpa only [pow_one, Nat.cast_pow] using
      hsharp 1 (by omega) (by simpa using hp4)
  have hins :
      (∑ r ∈ inside,
          |mu.covariance (fun m : S ↦ divInd (p ^ r) (m : ℕ)) pref|) ≤
        ∑ r ∈ inside, K / (((p ^ r : ℕ) : ℝ) * L n) := by
    apply Finset.sum_le_sum
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    exact hsharp r ((show 1 ≤ 2 by omega).trans
      (mem_highExponents.mp hr'.1).1) hr'.2
  have hinsReciprocal :
      (∑ r ∈ inside, 1 / ((p ^ r : ℕ) : ℝ)) ≤
        2 / (p : ℝ) ^ 2 := by
    calc
      (∑ r ∈ inside, 1 / ((p ^ r : ℕ) : ℝ)) ≤
          ∑ r ∈ highExponents R, 1 / ((p ^ r : ℕ) : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
        intro r hr _
        positivity
      _ ≤ 2 / (p : ℝ) ^ 2 := by
        simpa only [highExponents] using
          (sum_inv_pow_tail_le (p := p) (r := 1) (A := R) hp.two_le)
  have hinsBound :
      (∑ r ∈ inside,
          |mu.covariance (fun m : S ↦ divInd (p ^ r) (m : ℕ)) pref|) ≤
        (K / L n) * (2 / (p : ℝ) ^ 2) := by
    calc
      _ ≤ ∑ r ∈ inside,
          K / (((p ^ r : ℕ) : ℝ) * L n) := hins
      _ = (K / L n) *
          (∑ r ∈ inside, 1 / ((p ^ r : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ ≤ (K / L n) * (2 / (p : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hinsReciprocal
          (div_nonneg hK.le (L_pos hn).le)
  have houtEq : outside = diagonalBeyondFour n p R := by
    ext r
    simp only [outside, diagonalBeyondFour, Finset.mem_filter, Nat.not_le]
  have hout :
      (∑ r ∈ outside,
          |mu.covariance (fun m : S ↦ divInd (p ^ r) (m : ℕ)) pref|) ≤
        2 * G *
          (∑ r ∈ diagonalBeyondFour n p R,
            ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) := by
    rw [houtEq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    have hrHigh := (Finset.mem_filter.mp hr).1
    have hr2 := (mem_highExponents.mp hrHigh).1
    have hfb := hfallback r (by omega)
    have hweight : (1 : ℝ) ≤ ((2 * r - 3 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * r - 3 by omega)
    have hpPow : (0 : ℝ) < (p : ℝ) ^ r := by
      exact pow_pos (by exact_mod_cast hp.pos) r
    calc
      _ ≤ 2 * G / ((p ^ r : ℕ) : ℝ) := hfb
      _ = 2 * G * (1 / (p : ℝ) ^ r) := by
        norm_cast
        rw [Nat.cast_pow]
        ring
      _ ≤ 2 * G *
          (((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hG.le)
        exact div_le_div_of_nonneg_right hweight hpPow.le
  have houtBound :
      (∑ r ∈ outside,
          |mu.covariance (fun m : S ↦ divInd (p ^ r) (m : ℕ)) pref|) ≤
        (4 * G * (cutoffScale W * L n) ^ 2) /
          ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) := by
    calc
      _ ≤ 2 * G *
          (∑ r ∈ diagonalBeyondFour n p R,
            ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) := hout
      _ ≤ 2 * G *
          ((2 * (cutoffScale W * L n) ^ 2) /
            ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [R] using htail n hNtail p hpBand)
          (mul_nonneg (by norm_num) hG.le)
      _ = (4 * G * (cutoffScale W * L n) ^ 2) /
          ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) := by ring
  rw [hdecomp, mu.covariance_add_left, mu.covariance_sum_left]
  calc
    |mu.covariance (fun m : S ↦ divInd p (m : ℕ)) pref +
        ∑ r ∈ highExponents R,
          mu.covariance (fun m : S ↦ divInd (p ^ r) (m : ℕ)) pref| ≤
      |mu.covariance (fun m : S ↦ divInd p (m : ℕ)) pref| +
        ∑ r ∈ highExponents R,
          |mu.covariance (fun m : S ↦ divInd (p ^ r) (m : ℕ)) pref| := by
      exact (abs_add_le _ _).trans
        (add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _)
    _ = |mu.covariance (fun m : S ↦ divInd p (m : ℕ)) pref| +
        ((∑ r ∈ inside,
          |mu.covariance (fun m : S ↦ divInd (p ^ r) (m : ℕ)) pref|) +
        ∑ r ∈ outside,
          |mu.covariance (fun m : S ↦ divInd (p ^ r) (m : ℕ)) pref|) := by
      rw [hsplit]
    _ ≤ K / ((p : ℝ) * L n) +
        ((K / L n) * (2 / (p : ℝ) ^ 2) +
          (4 * G * (cutoffScale W * L n) ^ 2) /
            ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) :=
      add_le_add hfirst (add_le_add hinsBound houtBound)
    _ ≤ (2 * K / L n) * (1 / (p : ℝ)) +
        (4 * G * (cutoffScale W * L n) ^ 2) /
          ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) := by
      have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      have hpR0 : (0 : ℝ) < p := by positivity
      have hL : 0 < L n := L_pos hn
      have hmain : K / ((p : ℝ) * L n) +
          (K / L n) * (2 / (p : ℝ) ^ 2) ≤
          (2 * K / L n) * (1 / (p : ℝ)) := by
        field_simp [hpR0.ne', hL.ne']
        nlinarith [hK]
      linarith

end PaperRawPrefixValuationRow

end

end Erdos390.Full
