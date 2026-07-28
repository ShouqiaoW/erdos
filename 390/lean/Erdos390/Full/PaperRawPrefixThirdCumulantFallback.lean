import Erdos390.Full.PaperMediumNuisanceInputReduction
import Erdos390.Full.PaperMovingPrefixMarkedCell
import Erdos390.Full.FullTiltPairChamber

/-!
# Raw-cell fallback for the moving-prefix third cumulant

The sharp four-mark estimate is used only when the relevant lcm lies in the
friable chamber.  Outside that chamber the proof needs a completely uniform
reciprocal fallback.  This file supplies that fallback directly for the
un-tilted counting law on an actual structured cell.

There are two logically separate ingredients.

* A finite-probability lemma shows that reciprocal divisor expectations imply
  a reciprocal divisor/prefix covariance and then an lcm-scale third-cumulant
  bound.  No asymptotic statement or independence assertion is used.
* The positive density theorem for a structured cell supplies the reciprocal
  divisor expectations with a constant depending only on the fixed cell.

The displayed constants are deliberately retained: for coprime `D,E` the
third cumulant is bounded by `(2G+4G^2)/(DE)`, which is exactly the coefficient
used by the beyond-four prime-power ledger after setting its fallback
parameter to `2G`.
-/

open Filter
open scoped BigOperators

namespace Erdos390.Full

open ArithmeticModel Scale HeadPattern StructuredCells
open DivisibilityMomentBounds
open FiniteProbability
open PaperScaleMarkedCell
open FullTiltPairChamber

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

/-- If every divisor event has expectation at most `G/D`, its covariance
with an arbitrary `[0,1]`-valued prefix statistic is at most `2G/D`.

The harmless factor two comes from bounding the joint and product terms
separately.  Keeping this elementary form avoids any hidden use of positive
association or independence. -/
theorem abs_covariance_divInd_prefix_le_of_reciprocal_expectation
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (pref : Omega → ℝ) {D : ℕ} {G : ℝ}
    (hD : 0 < D)
    (hpref0 : ∀ omega, 0 ≤ pref omega)
    (hpref1 : ∀ omega, pref omega ≤ 1)
    (hdiv : mu.expect (fun omega ↦ divInd D (value omega)) ≤
      G / (D : ℝ)) :
    |mu.covariance (fun omega ↦ divInd D (value omega)) pref| ≤
      2 * G / (D : ℝ) := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hFabs :
      (fun omega ↦ |divInd D (value omega)|) =
        fun omega ↦ divInd D (value omega) := by
    funext omega
    rw [abs_of_nonneg (divInd_nonneg D (value omega))]
  have hPabs : (fun omega ↦ |pref omega|) = pref := by
    funext omega
    rw [abs_of_nonneg (hpref0 omega)]
  have hmarked :
      mu.expect (fun omega ↦
          |divInd D (value omega)| * |pref omega|) ≤
        mu.expect (fun omega ↦ divInd D (value omega)) := by
    apply mu.expect_mono
    intro omega
    rw [abs_of_nonneg (divInd_nonneg D (value omega)),
      abs_of_nonneg (hpref0 omega)]
    exact mul_le_of_le_one_right (divInd_nonneg D (value omega))
      (hpref1 omega)
  have hprefMean : mu.expect (fun omega ↦ |pref omega|) ≤ 1 := by
    rw [hPabs]
    calc
      mu.expect pref ≤ mu.expect (fun _ ↦ (1 : ℝ)) :=
        mu.expect_mono pref _ hpref1
      _ = 1 := by
        unfold expect
        rw [← Finset.sum_mul, mu.mass_sum, one_mul]
  have hFmean0 : 0 ≤
      mu.expect (fun omega ↦ divInd D (value omega)) :=
    mu.expect_nonneg _ (fun omega ↦ divInd_nonneg D (value omega))
  have hraw := mu.abs_covariance_le_expect_abs_mul_add
    (fun omega ↦ divInd D (value omega)) pref
  rw [hFabs] at hraw
  calc
    |mu.covariance (fun omega ↦ divInd D (value omega)) pref| ≤
        mu.expect (fun omega ↦
            |divInd D (value omega)| * |pref omega|) +
          mu.expect (fun omega ↦ divInd D (value omega)) *
            mu.expect (fun omega ↦ |pref omega|) := hraw
    _ ≤ mu.expect (fun omega ↦ divInd D (value omega)) +
          mu.expect (fun omega ↦ divInd D (value omega)) * 1 := by
      exact add_le_add hmarked
        (mul_le_mul_of_nonneg_left hprefMean hFmean0)
    _ ≤ G / (D : ℝ) + G / (D : ℝ) := by
      exact add_le_add hdiv (by simpa using hdiv)
    _ = 2 * G / (D : ℝ) := by ring

/-- Reciprocal divisor expectations give an unconditional lcm-scale bound
for the first Taylor coefficient of a prefix covariance.  This is the exact
fallback used outside the four-mark chamber. -/
theorem abs_covarianceThirdCentered_divInd_prefix_divInd_fallback_le
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (pref : Omega → ℝ) {D E : ℕ} {G : ℝ}
    (hD : 0 < D) (hE : 0 < E) (hG : 0 ≤ G)
    (hpref0 : ∀ omega, 0 ≤ pref omega)
    (hpref1 : ∀ omega, pref omega ≤ 1)
    (hdiv : ∀ d : ℕ, 0 < d →
      mu.expect (fun omega ↦ divInd d (value omega)) ≤
        G / (d : ℝ)) :
    |mu.covarianceThirdCentered
        (fun omega ↦ divInd D (value omega)) pref
        (fun omega ↦ divInd E (value omega))| ≤
      2 * G / (Nat.lcm D E : ℝ) +
        (G / (E : ℝ)) * (2 * G / (D : ℝ)) +
        (G / (D : ℝ)) * (2 * G / (E : ℝ)) := by
  have hLcm : 0 < Nat.lcm D E := Nat.lcm_pos hD hE
  have hcovD := mu.abs_covariance_divInd_prefix_le_of_reciprocal_expectation
    value pref hD hpref0 hpref1 (hdiv D hD)
  have hcovE := mu.abs_covariance_divInd_prefix_le_of_reciprocal_expectation
    value pref hE hpref0 hpref1 (hdiv E hE)
  have hcovLcm :=
    mu.abs_covariance_divInd_prefix_le_of_reciprocal_expectation
      value pref hLcm hpref0 hpref1 (hdiv (Nat.lcm D E) hLcm)
  have hraw :=
    mu.abs_covarianceThirdCentered_divInd_prefix_divInd_lcm_le
      (K := 2 * G) (A := G) (L := 1)
      value pref hD hE hG
      (by simpa using hcovD) (by simpa using hcovE)
      (by simpa using hcovLcm) (hdiv D hD) (hdiv E hE)
  simpa only [one_mul, mul_one] using hraw

/-- For coprime divisors the fallback keeps the full product-reciprocal
scale. -/
theorem abs_covarianceThirdCentered_divInd_prefix_divInd_coprime_fallback_le
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (pref : Omega → ℝ) {D E : ℕ} {G : ℝ}
    (hD : 0 < D) (hE : 0 < E) (hcop : Nat.Coprime D E)
    (hG : 0 ≤ G)
    (hpref0 : ∀ omega, 0 ≤ pref omega)
    (hpref1 : ∀ omega, pref omega ≤ 1)
    (hdiv : ∀ d : ℕ, 0 < d →
      mu.expect (fun omega ↦ divInd d (value omega)) ≤
        G / (d : ℝ)) :
    |mu.covarianceThirdCentered
        (fun omega ↦ divInd D (value omega)) pref
        (fun omega ↦ divInd E (value omega))| ≤
      (2 * G + 4 * G ^ 2) / ((D : ℝ) * (E : ℝ)) := by
  have hraw :=
    mu.abs_covarianceThirdCentered_divInd_prefix_divInd_fallback_le
      value pref hD hE hG hpref0 hpref1 hdiv
  rw [hcop.lcm_eq_mul] at hraw
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hEreal : (0 : ℝ) < E := by exact_mod_cast hE
  calc
    _ ≤ 2 * G / ((D * E : ℕ) : ℝ) +
        (G / (E : ℝ)) * (2 * G / (D : ℝ)) +
        (G / (D : ℝ)) * (2 * G / (E : ℝ)) := hraw
    _ = (2 * G + 4 * G ^ 2) / ((D : ℝ) * (E : ℝ)) := by
      norm_cast
      rw [Nat.cast_mul]
      field_simp [hDreal.ne', hEreal.ne']
      ring

end FiniteProbability

namespace PaperRawPrefixThirdCumulantFallback

/-- The un-tilted law on a fixed structured cell has a reciprocal divisor
bound uniform in the divisor and in all sufficiently large `n`. -/
theorem exists_uniform_rawCell_divInd_fallback
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) :
    ∃ G : ℝ, 0 < G ∧ ∃ N₀ : ℕ, ∀ {n : ℕ}, N₀ ≤ n →
      let S := structuredCell H (physicalBound A n) (physicalBound C n)
        (yNat n)
      ∀ hS : S.Nonempty, ∀ D : ℕ, 0 < D →
        (uniformOnFinset S hS).expect
            (fun m : S ↦ divInd D (m : ℕ)) ≤ G / (D : ℝ) := by
  let c : ℝ := pairFallbackDensity H A C
  have hc : 0 < c := pairFallbackDensity_pos_of_pos H hAC hC
  let G : ℝ := 1 / c
  have hG : 0 < G := one_div_pos.mpr hc
  obtain ⟨Ndensity, hdensity⟩ :=
    exists_structuredCell_density_lower_bound H hA hAC
  have hphysEvent : ∀ᶠ n : ℕ in atTop, 1 ≤ physicalBound C n := by
    have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    filter_upwards [hcastTop.eventually
      (eventually_ge_atTop (1 / C))] with n hn
    unfold physicalBound
    apply Nat.le_floor
    have := (div_le_iff₀ hC).mp hn
    exact_mod_cast (show (1 : ℝ) ≤ C * (n : ℝ) by
      simpa [mul_comm] using this)
  obtain ⟨Nphys, hphys⟩ := Filter.eventually_atTop.mp hphysEvent
  refine ⟨G, hG, max 2 (max Ndensity Nphys), ?_⟩
  intro n hN
  have hn : 1 < n := by omega
  have hNdensity : Ndensity ≤ n := by omega
  have hNphys : Nphys ≤ n := by omega
  let S := structuredCell H (physicalBound A n) (physicalBound C n)
    (yNat n)
  change ∀ hS : S.Nonempty, ∀ D : ℕ, 0 < D →
    (uniformOnFinset S hS).expect
        (fun m : S ↦ divInd D (m : ℕ)) ≤ G / (D : ℝ)
  intro hS D hD
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hMpos : 0 < physicalBound C n :=
    Nat.zero_lt_of_lt (hphys n hNphys)
  have hMcast : (physicalBound C n : ℝ) ≤ C * (n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hC.le hnR.le)
  have hcard : c * (physicalBound C n : ℝ) ≤ (S.card : ℝ) := by
    calc
      c * (physicalBound C n : ℝ) ≤ c * (C * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hMcast hc.le
      _ = paperCellDensity H A C * (n : ℝ) / 2 := by
        dsimp only [c, pairFallbackDensity]
        field_simp [hC.ne']
      _ ≤ (S.card : ℝ) := by
        simpa only [S] using hdensity hNdensity
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    exact pos_of_mem_smoothInterval (mem_structuredCell.mp hm).1
  have hSle : ∀ m ∈ S, m ≤ physicalBound C n := by
    intro m hm
    exact (mem_smoothInterval.mp (mem_structuredCell.mp hm).1).2.1
  rw [Erdos390.Full.OmittedScoreCell.uniform_expect_eq_uniformAverage]
  have hraw := OmittedTiltFallback.uniformAverage_divInd_le S hD hMpos hc
    hcard hSpos hSle
  calc
    DivisibilityMomentBounds.uniformAverage S (divInd D) ≤
        1 / (c * (D : ℝ)) := hraw
    _ = G / (D : ℝ) := by
      dsimp only [G]
      ring

/-- The corresponding sharp lcm-scale chamber estimate, without assuming
that the two divisors are coprime.  This is the same-prime input: for
`D=p^r`, `E=p^s`, the joint row is charged at `p^(max r s)`. -/
theorem exists_uniform_rawCell_thirdCumulant_lcm_chamber
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∃ G : ℝ, 0 < G ∧ ∃ N₀ : ℕ,
      ∀ {n k D E : ℕ}, N₀ ≤ n →
      physicalBound A n < k → k ≤ physicalBound C n →
      0 < D → 0 < E →
      D ≤ yNat n ^ 4 → E ≤ yNat n ^ 4 →
      Nat.lcm D E ≤ yNat n ^ 4 →
      D ∈ Nat.smoothNumbers (yNat n + 1) →
      E ∈ Nat.smoothNumbers (yNat n + 1) →
      Nat.lcm D E ∈ Nat.smoothNumbers (yNat n + 1) →
      Nat.Coprime D H.modulus → Nat.Coprime E H.modulus →
      Nat.Coprime (Nat.lcm D E) H.modulus →
      let S := structuredCell H (physicalBound A n) (physicalBound C n)
        (yNat n)
      ∀ hS : S.Nonempty,
        |(uniformOnFinset S hS).covarianceThirdCentered
            (fun m : S ↦ divInd D (m : ℕ))
            (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)
            (fun m : S ↦ divInd E (m : ℕ))| ≤
          K / ((Nat.lcm D E : ℝ) * L n) +
            (G / (E : ℝ)) * (K / ((D : ℝ) * L n)) +
            (G / (D : ℝ)) * (K / ((E : ℝ) * L n)) := by
  obtain ⟨K, hK, Nmove, hmove⟩ :=
    PaperMovingPrefixMarkedCell.exists_uniform_movingPrefix_divInd_covariance_bound
      H hA hAC
  obtain ⟨G, hG, Ndiv, hdiv⟩ :=
    exists_uniform_rawCell_divInd_fallback H hA hAC hC
  refine ⟨K, hK, G, hG, max 2 (max Nmove Ndiv), ?_⟩
  intro n k D E hN hlow hhigh hD hE hD4 hE4 hLcm4
    hDsmooth hEsmooth hLcmsmooth hDmod hEmod hLcmmod
  have hn : 1 < n := by omega
  have hNmove : Nmove ≤ n := by omega
  have hNdiv : Ndiv ≤ n := by omega
  have hLcm : 0 < Nat.lcm D E := Nat.lcm_pos hD hE
  let S := structuredCell H (physicalBound A n) (physicalBound C n)
    (yNat n)
  change ∀ hS : S.Nonempty,
    |(uniformOnFinset S hS).covarianceThirdCentered
        (fun m : S ↦ divInd D (m : ℕ))
        (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)
        (fun m : S ↦ divInd E (m : ℕ))| ≤
      K / ((Nat.lcm D E : ℝ) * L n) +
        (G / (E : ℝ)) * (K / ((D : ℝ) * L n)) +
        (G / (D : ℝ)) * (K / ((E : ℝ) * L n))
  intro hS
  let mu := uniformOnFinset S hS
  let pref : S → ℝ := fun m ↦ if (m : ℕ) ≤ k then 1 else 0
  have hcov (d : ℕ) (hd : 0 < d) (hd4 : d ≤ yNat n ^ 4)
      (hdsmooth : d ∈ Nat.smoothNumbers (yNat n + 1))
      (hdmod : Nat.Coprime d H.modulus) :
      |mu.covariance (fun m : S ↦ divInd d (m : ℕ)) pref| ≤
        K / ((d : ℝ) * L n) := by
    obtain ⟨hS', hraw⟩ := hmove hNmove hlow hhigh hd hd4 hdsmooth hdmod
    simpa only [S, mu, pref] using hraw
  have hdivAll (d : ℕ) (hd : 0 < d) :
      mu.expect (fun m : S ↦ divInd d (m : ℕ)) ≤ G / (d : ℝ) := by
    simpa only [S, mu] using hdiv hNdiv hS d hd
  have hraw := mu.abs_covarianceThirdCentered_divInd_prefix_divInd_lcm_le
    (fun m : S ↦ (m : ℕ)) pref hD hE hG.le
    (hcov D hD hD4 hDsmooth hDmod)
    (hcov E hE hE4 hEsmooth hEmod)
    (hcov (Nat.lcm D E) hLcm hLcm4 hLcmsmooth hLcmmod)
    (hdivAll D hD) (hdivAll E hE)
  simpa only [mu, pref] using hraw

/-- Paper-facing same-prime specialization of the lcm chamber theorem.  All
smoothness and head-coprimality hypotheses are discharged from literal
membership in the moving prime band. -/
theorem exists_uniform_rawCell_samePrime_thirdCumulant_chamber
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) (W : ℕ) (hHW : H.modulus ≤ W) :
    ∃ K : ℝ, 0 < K ∧ ∃ G : ℝ, 0 < G ∧ ∃ N₀ : ℕ,
      ∀ {n k p r s : ℕ}, N₀ ≤ n →
      physicalBound A n < k → k ≤ physicalBound C n →
      p ∈ primeBand n W → 1 ≤ r → 1 ≤ s →
      p ^ max r s ≤ yNat n ^ 4 →
      let S := structuredCell H (physicalBound A n) (physicalBound C n)
        (yNat n)
      ∀ hS : S.Nonempty,
        |(uniformOnFinset S hS).covarianceThirdCentered
            (fun m : S ↦ divInd (p ^ r) (m : ℕ))
            (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)
            (fun m : S ↦ divInd (p ^ s) (m : ℕ))| ≤
          K / (((p ^ max r s : ℕ) : ℝ) * L n) +
            (G / ((p ^ s : ℕ) : ℝ)) *
              (K / (((p ^ r : ℕ) : ℝ) * L n)) +
            (G / ((p ^ r : ℕ) : ℝ)) *
              (K / (((p ^ s : ℕ) : ℝ) * L n)) := by
  obtain ⟨K, hK, G, hG, N₀, hchamber⟩ :=
    exists_uniform_rawCell_thirdCumulant_lcm_chamber H hA hAC hC
  refine ⟨K, hK, G, hG, N₀, ?_⟩
  intro n k p r s hN hlow hhigh hpBand hr hs hmax4
  have hp := prime_of_mem_primeBand hpBand
  have hpY : p ≤ yNat n := le_yNat_of_mem_primeBand hpBand
  have hpSmooth : p ∈ Nat.smoothNumbers (yNat n + 1) :=
    Nat.mem_smoothNumbers_of_lt hp.pos (Nat.lt_succ_of_le hpY)
  have hpowR : p ^ r ≤ p ^ max r s :=
    Nat.pow_le_pow_right hp.pos (Nat.le_max_left r s)
  have hpowS : p ^ s ≤ p ^ max r s :=
    Nat.pow_le_pow_right hp.pos (Nat.le_max_right r s)
  have hpHead : Nat.Coprime p H.modulus :=
    PaperPrimePowerAuxiliaryPrime.coprime_modulus_of_mem_primeBand
      H hHW hpBand
  have hraw := hchamber hN hlow hhigh
    (pow_pos hp.pos r) (pow_pos hp.pos s)
    (hpowR.trans hmax4) (hpowS.trans hmax4)
    (by simpa only [PrimePowerLcmGeometry.lcm_pow_pow_eq_pow_max] using hmax4)
    (StructuredCells.pow_mem_smoothNumbers hpSmooth r)
    (StructuredCells.pow_mem_smoothNumbers hpSmooth s)
    (by
      simpa only [PrimePowerLcmGeometry.lcm_pow_pow_eq_pow_max] using
        StructuredCells.pow_mem_smoothNumbers hpSmooth (max r s))
    (hpHead.pow_left r) (hpHead.pow_left s)
    (by
      simpa only [PrimePowerLcmGeometry.lcm_pow_pow_eq_pow_max] using
        hpHead.pow_left (max r s))
  simpa only [PrimePowerLcmGeometry.lcm_pow_pow_eq_pow_max] using hraw

/-- Inside the four-mark chamber, the three literal moving-prefix divisor
rows at `D`, `E`, and `DE` give the extra factor `L⁻¹` in the third
cumulant.  All witnesses are simultaneous in the moving prefix and in the
two divisors. -/
theorem exists_uniform_rawCell_coprime_thirdCumulant_chamber
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∃ G : ℝ, 0 < G ∧ ∃ N₀ : ℕ,
      ∀ {n k D E : ℕ}, N₀ ≤ n →
      physicalBound A n < k → k ≤ physicalBound C n →
      0 < D → 0 < E → D * E ≤ yNat n ^ 4 →
      D ∈ Nat.smoothNumbers (yNat n + 1) →
      E ∈ Nat.smoothNumbers (yNat n + 1) →
      D * E ∈ Nat.smoothNumbers (yNat n + 1) →
      Nat.Coprime D E → Nat.Coprime D H.modulus →
      Nat.Coprime E H.modulus → Nat.Coprime (D * E) H.modulus →
      let S := structuredCell H (physicalBound A n) (physicalBound C n)
        (yNat n)
      ∀ hS : S.Nonempty,
        |(uniformOnFinset S hS).covarianceThirdCentered
            (fun m : S ↦ divInd D (m : ℕ))
            (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)
            (fun m : S ↦ divInd E (m : ℕ))| ≤
          (K * (1 + 2 * G)) /
            (((D : ℝ) * (E : ℝ)) * L n) := by
  obtain ⟨K, hK, Nmove, hmove⟩ :=
    PaperMovingPrefixMarkedCell.exists_uniform_movingPrefix_divInd_covariance_bound
      H hA hAC
  obtain ⟨G, hG, Ndiv, hdiv⟩ :=
    exists_uniform_rawCell_divInd_fallback H hA hAC hC
  refine ⟨K, hK, G, hG, max 2 (max Nmove Ndiv), ?_⟩
  intro n k D E hN hlow hhigh hD hE hDE4 hDsmooth hEsmooth hDEsmooth
    hcop hDmod hEmod hDEmod
  have hn : 1 < n := by omega
  have hNmove : Nmove ≤ n := by omega
  have hNdiv : Ndiv ≤ n := by omega
  have hD4 : D ≤ yNat n ^ 4 := by
    have hDE : D ≤ D * E := by
      calc
        D = D * 1 := by omega
        _ ≤ D * E := Nat.mul_le_mul_left D (by omega)
    exact hDE.trans hDE4
  have hE4 : E ≤ yNat n ^ 4 := by
    have hED : E ≤ E * D := by
      calc
        E = E * 1 := by omega
        _ ≤ E * D := Nat.mul_le_mul_left E (by omega)
    exact hED.trans (by simpa [Nat.mul_comm] using hDE4)
  let S := structuredCell H (physicalBound A n) (physicalBound C n)
    (yNat n)
  change ∀ hS : S.Nonempty,
    |(uniformOnFinset S hS).covarianceThirdCentered
        (fun m : S ↦ divInd D (m : ℕ))
        (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)
        (fun m : S ↦ divInd E (m : ℕ))| ≤
      (K * (1 + 2 * G)) / (((D : ℝ) * (E : ℝ)) * L n)
  intro hS
  let mu := uniformOnFinset S hS
  let pref : S → ℝ := fun m ↦ if (m : ℕ) ≤ k then 1 else 0
  have hcov (d : ℕ) (hd : 0 < d) (hd4 : d ≤ yNat n ^ 4)
      (hdsmooth : d ∈ Nat.smoothNumbers (yNat n + 1))
      (hdmod : Nat.Coprime d H.modulus) :
      |mu.covariance (fun m : S ↦ divInd d (m : ℕ)) pref| ≤
        K / ((d : ℝ) * L n) := by
    obtain ⟨hS', hraw⟩ := hmove hNmove hlow hhigh hd hd4 hdsmooth hdmod
    simpa only [S, mu, pref] using hraw
  have hdivAll (d : ℕ) (hd : 0 < d) :
      mu.expect (fun m : S ↦ divInd d (m : ℕ)) ≤ G / (d : ℝ) := by
    simpa only [S, mu] using hdiv hNdiv hS d hd
  have hraw := mu.abs_covarianceThirdCentered_divInd_prefix_divInd_le
    (fun m : S ↦ (m : ℕ)) pref hD hE hcop hK.le hG.le (L_pos hn)
    (hcov D hD hD4 hDsmooth hDmod)
    (hcov E hE hE4 hEsmooth hEmod)
    (by
      simpa only [Nat.cast_mul] using
        hcov (D * E) (Nat.mul_pos hD hE) hDE4 hDEsmooth hDEmod)
    (hdivAll D hD) (hdivAll E hE)
  simpa only [mu, pref] using hraw

end PaperRawPrefixThirdCumulantFallback

end

end Erdos390.Full
