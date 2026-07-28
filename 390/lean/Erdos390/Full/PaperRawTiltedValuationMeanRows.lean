import Erdos390.Full.FixedFiniteMixtureSignedSquarefree
import Erdos390.Full.PaperPrimePowerTailRate
import Erdos390.Full.PaperMediumNuisanceInputReduction

/-!
# Raw tilted full-valuation component-mean agreement

The common four-mark profile is summed only through
`Nat.log p (yNat n ^ 4)`.  The arbitrary-divisor fallback controls the
literal remaining valuation tail.  This produces the sharp
`epsilon(n)/p`, `epsilon(n) log L(n) -> 0` component-mean row needed for the
head nuisance coordinate.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.PaperRawTiltedValuationMeanRows

open Erdos390.Full
open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open StructuredCellValuationLaw ValuationScoreDomination
open OmittedTiltPairChamber FullTiltPairChamber
open FullTiltPrimePowerFallback
open PaperPrimePowerChamberError PaperScaleMarkedCell
open FixedFiniteMixtureFullUniform FixedFiniteMixtureSignedSquarefree
open PaperPrimePowerAuxiliaryPrime PaperPrimePowerTailRate
open LocalFugacityBounds

noncomputable section

set_option maxHeartbeats 2400000

/-- The finite full-valuation tail estimate remains true without assuming
that the chosen exponent cutoff is below the ambient endpoint.  If the
cutoff is larger, the valuation expansion already terminates and the tail
is identically zero. -/
theorem PrimePowerTail.abs_expect_valuation_sub_cutoff_le_of_divisor_fallback_unrestricted
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    {M p Kcut : ℕ} {G : ℝ}
    (hp : p.Prime) (hvaluePos : ∀ omega, 0 < value omega)
    (hvalueLe : ∀ omega, value omega ≤ M)
    (hG : 0 ≤ G)
    (hdiv : ∀ D : ℕ, 0 < D →
      mu.expect (fun omega ↦ divInd D (value omega)) ≤
        G * (1 / (D : ℝ))) :
    |mu.expect (fun omega ↦
        valuation p (value omega) -
          ∑ k ∈ positiveExponents Kcut,
            divInd (p ^ k) (value omega))| ≤
      G * (2 / (p : ℝ) ^ (Kcut + 1)) := by
  by_cases hcut : Kcut ≤ M
  · exact PrimePowerTail.abs_expect_valuation_sub_cutoff_le_of_divisor_fallback
      mu value hp hvaluePos hvalueLe hcut hG hdiv
  · have hMK : M ≤ Kcut := (Nat.lt_of_not_ge hcut).le
    have hpoint : (fun omega ↦
        valuation p (value omega) -
          ∑ k ∈ positiveExponents Kcut,
            divInd (p ^ k) (value omega)) = fun _ ↦ 0 := by
      funext omega
      rw [valuation_eq_sum_divInd_of_le hp (hvaluePos omega)
        ((hvalueLe omega).trans hMK)]
      ring
    rw [hpoint]
    have hzero : mu.expect (fun _ ↦ (0 : ℝ)) = 0 := by
      exact mu.expect_zero
    rw [hzero, abs_zero]
    positivity

/-- The chamber single-prime weight has a uniform geometric sum beginning
at exponent one. -/
theorem sum_singleWeight_positiveExponents_le
    {p R : ℕ} (hp : 2 ≤ p) :
    (∑ r ∈ positiveExponents R, singleWeight p r) ≤
      6 / (p : ℝ) := by
  by_cases hR : 1 ≤ R
  · have hset : positiveExponents R =
        insert 1 (Finset.Icc 2 R) := by
      ext r
      simp only [positiveExponents, Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    have htail := sum_raddone_inv_pow_le (p := p) (R := R) hp
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hp0 : (0 : ℝ) < p := zero_lt_two.trans_le hpR
    have hsq : 8 / (p : ℝ) ^ 2 ≤ 4 / (p : ℝ) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hp0) hp0).2
      nlinarith [mul_nonneg hp0.le (sub_nonneg.mpr hpR)]
    calc
      singleWeight p 1 + ∑ x ∈ Finset.Icc 2 R, singleWeight p x =
          2 / (p : ℝ) +
            ∑ x ∈ Finset.Icc 2 R,
              (((x : ℝ) + 1) / (p : ℝ) ^ x) := by
        unfold singleWeight
        norm_num
      _ ≤ 2 / (p : ℝ) + 8 / (p : ℝ) ^ 2 :=
        add_le_add le_rfl htail
      _ ≤ 2 / (p : ℝ) + 4 / (p : ℝ) :=
        add_le_add le_rfl hsq
      _ = 6 / (p : ℝ) := by ring
  · have hR0 : R = 0 := by omega
    subst R
    simp [positiveExponents]
    positivity

variable {Cell : Type*} [Fintype Cell]

/-- Fixed-finite raw component means agree at the sharp reciprocal rate.
The coefficient box is arbitrary after `W`; all box dependence is confined
to the rate and eventual threshold. -/
theorem exists_uniform_fixedFinite_rawCell_tilted_valuation_mean_agreement_rate
    (H : Cell → Pattern) (A C : Cell → ℝ) (Cmax : ℝ)
    (hA : ∀ c, 0 < A c) (hAC : ∀ c, A c < C c)
    (hC : ∀ c, 0 < C c) (hC_le : ∀ c, C c ≤ Cmax)
    (W : ℕ) (hW : 1 < W)
    (hHeadLe : ∀ c, ∀ p ∈ (H c).primes, p ≤ W)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ, ∀ {n p : ℕ} (eta : ℕ → ℝ),
        N₀ ≤ n → p ∈ primeBand n W →
        (∀ z ∈ primeBand n W, |eta z| ≤ B) →
        let S := fun c ↦ structuredCell (H c)
          (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
        ∀ hS : ∀ c, (S c).Nonempty, ∀ c c' : Cell,
          |((uniformOnFinset (S c) (hS c)).exponentialTilt
                (fun m : S c ↦
                  valuationScore (primeBand n W) eta (L n) (m : ℕ))).expect
              (fun m ↦ valuation p (m : ℕ)) -
            ((uniformOnFinset (S c') (hS c')).exponentialTilt
                (fun m : S c' ↦
                  valuationScore (primeBand n W) eta (L n) (m : ℕ))).expect
              (fun m ↦ valuation p (m : ℕ))| ≤
            epsilon n / (p : ℝ) := by
  obtain ⟨signedError, hsigned0, _hsignedT, hsignedRate,
    Nprofile, hprofileAll⟩ :=
      exists_boxIndependent_fixedFiniteMixture_signed_profiles_of_pos
        H A C Cmax hA hAC hC hC_le W hW
          hHeadLe
          B hB
  have hfallbackExists : ∀ c, ∃ Gc : ℝ, 0 < Gc ∧ ∃ Nc : ℕ,
      ∀ {n : ℕ} (eta : ℕ → ℝ), Nc ≤ n →
      (∀ z ∈ primeBand n W, |eta z| ≤ B) →
      let S := structuredCell (H c) (physicalBound (A c) n)
        (physicalBound (C c) n) (yNat n)
      ∀ hS : S.Nonempty, ∀ D : ℕ, 0 < D →
        (valuationTilt (H c) (physicalBound (A c) n)
          (physicalBound (C c) n) (yNat n) hS
          (primeBand n W) eta (L n)).probability.expect
            (fun m ↦ divInd D (m : ℕ)) ≤ Gc / (D : ℝ) := by
    intro c
    exact exists_uniform_fullTilt_primePower_fallback
      (H c) (hA c) (hAC c) (hC c) B W hB hW
  choose Gcell hGcellData using hfallbackExists
  have hGcell (c : Cell) : 0 < Gcell c := (hGcellData c).1
  choose NfallbackCell hfallbackCell using fun c ↦ (hGcellData c).2
  let Gf : ℝ := ∑ c, Gcell c
  let Nfallback : ℕ := ∑ c, NfallbackCell c
  have hGf0 : 0 ≤ Gf := by
    dsimp only [Gf]
    exact Finset.sum_nonneg fun c hc ↦ (hGcell c).le
  have hGcellLe (c : Cell) : Gcell c ≤ Gf := by
    dsimp only [Gf]
    exact Finset.single_le_sum
      (fun d hd ↦ (hGcell d).le) (Finset.mem_univ c)
  let tailCoefficient : ℕ → ℝ := fun n ↦ 4 * Gf / L n
  let epsilon : ℕ → ℝ := fun n ↦ 12 * signedError n + tailCoefficient n
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLdivL : Tendsto (fun n : ℕ ↦ Real.log (L n) / L n)
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have htailRate : Tendsto (fun n : ℕ ↦
      tailCoefficient n * Real.log (L n)) atTop (nhds 0) := by
    have hconst : Tendsto (fun _n : ℕ ↦ 4 * Gf)
        atTop (nhds (4 * Gf)) := tendsto_const_nhds
    have hmul := hconst.mul hlogLdivL
    have hmul0 : Tendsto (fun n : ℕ ↦
        (4 * Gf) * (Real.log (L n) / L n)) atTop (nhds 0) := by
      simpa only [mul_zero] using hmul
    apply hmul0.congr'
    filter_upwards with n
    dsimp only [tailCoefficient]
    ring
  have hepsilonRate : Tendsto (fun n : ℕ ↦
      epsilon n * Real.log (L n)) atTop (nhds 0) := by
    have hsignedConst : Tendsto (fun n : ℕ ↦
        12 * (signedError n * Real.log (L n))) atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hsignedRate
    have hsum := hsignedConst.add htailRate
    have hsum0 : Tendsto (fun n : ℕ ↦
        12 * (signedError n * Real.log (L n)) +
          tailCoefficient n * Real.log (L n)) atTop (nhds 0) := by
      simpa only [zero_add] using hsum
    apply hsum0.congr'
    filter_upwards with n
    dsimp only [epsilon]
    ring
  have hepsilon0 : ∀ n, 0 ≤ epsilon n := by
    intro n
    cases n with
    | zero => simp [epsilon, tailCoefficient, L, hsigned0]
    | succ n =>
      dsimp only [epsilon, tailCoefficient]
      have hL0 : 0 ≤ L (n + 1) := by
        exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      exact add_nonneg
        (mul_nonneg (by norm_num) (hsigned0 (n + 1)))
        (div_nonneg (mul_nonneg (by norm_num) hGf0) hL0)
  obtain ⟨q₀, q₁, aux, _hq₀, _hq₁, _hWq₀, _hq₀q₁,
    _hauxDef, hauxEvent⟩ := exists_eventually_auxiliaryPrime W
  have htailSharp := eventually_mul_two_div_yNat_pow_four_le_sharp
  have hgood : ∀ᶠ n : ℕ in atTop,
      (q₀ ∈ primeBand n W ∧ q₁ ∈ primeBand n W ∧
        ∀ p ∈ primeBand n W, aux p ∈ (primeBand n W).erase p) ∧
      (∀ p : ℕ, 0 < p → p ≤ yNat n → ∀ G : ℝ, 0 ≤ G →
        G * (2 / ((yNat n ^ 4 : ℕ) : ℝ)) ≤
          ((2 * G) / L n) * (1 / (p : ℝ))) ∧
      1 < n := by
    filter_upwards [hauxEvent, htailSharp, Filter.eventually_gt_atTop 1]
      with n haux htail hn
    exact ⟨haux, htail, hn⟩
  obtain ⟨Ngood, hNgood⟩ := Filter.eventually_atTop.mp hgood
  refine ⟨epsilon, hepsilon0, hepsilonRate,
    max Nprofile (max Nfallback Ngood), ?_⟩
  intro n p eta hN hpBand heta
  have hNprofile : Nprofile ≤ n := by omega
  have hNfallback : Nfallback ≤ n := by omega
  have hNgoodBound : Ngood ≤ n := by omega
  obtain ⟨⟨hq₀Band, hq₁Band, haux⟩, htailSharpN, hn⟩ :=
    hNgood n hNgoodBound
  let S := fun c ↦ structuredCell (H c)
    (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
  change ∀ hS : ∀ c, (S c).Nonempty, ∀ c c' : Cell, _
  intro hS c c'
  have hp := prime_of_mem_primeBand hpBand
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpY : p ≤ yNat n := le_yNat_of_mem_primeBand hpBand
  have hTpos : 0 < yNat n ^ 4 := pow_pos (hp.pos.trans_le hpY) 4
  let Kcut : ℕ := Nat.log p (yNat n ^ 4)
  let main : ℕ → ℝ := fun k ↦ paperDivisibilityMain n (p ^ k)
  let mainSum : ℝ := ∑ k ∈ positiveExponents Kcut, main k
  have hprofiles := (hprofileAll eta hNprofile heta).2 hS
  have hpairProfile := hprofiles.1
  have hqErase : aux p ∈ (primeBand n W).erase p := haux p hpBand
  have hprofileOne (d : Cell) (k : ℕ)
      (hk : k ∈ positiveExponents Kcut) :
      |((uniformOnFinset (S d) (hS d)).exponentialTilt
            (fun m : S d ↦
              valuationScore (primeBand n W) eta (L n) (m : ℕ))).expect
          (fun m ↦ divInd (p ^ k) (m : ℕ)) - main k| ≤
        signedError n * singleWeight p k := by
    have hkLe : k ≤ Kcut := (mem_positiveExponents.mp hk).2
    have hpK : p ^ Kcut ≤ yNat n ^ 4 :=
      Nat.pow_log_le_self p hTpos.ne'
    have hpk : p ^ k ≤ yNat n ^ 4 :=
      (Nat.pow_le_pow_right hp.pos hkLe).trans hpK
    have hraw := hpairProfile d p hpBand (aux p) hqErase k 0
      (by simpa only [pairPower, pow_zero, mul_one] using hpk)
    simpa only [S, main, pairPower, pow_zero, mul_one,
      pairWeight_eq_single_mul, singleWeight, Nat.cast_zero, zero_add,
      div_one, mul_one,
      PrimePowerCovariance.BoundedValuationLaw.widen_probability,
      PrimePowerCovariance.BoundedValuationLaw.widen_value,
      StructuredCellValuationLaw.valuationTilt_probability,
      StructuredCellValuationLaw.valuationTilt_value] using hraw
  have htailOne (d : Cell) :
      |((uniformOnFinset (S d) (hS d)).exponentialTilt
            (fun m : S d ↦
              valuationScore (primeBand n W) eta (L n) (m : ℕ))).expect
          (fun m ↦ valuation p (m : ℕ) -
            ∑ k ∈ positiveExponents Kcut,
              divInd (p ^ k) (m : ℕ))| ≤
        ((2 * Gf) / L n) * (1 / (p : ℝ)) := by
    have hNcell : NfallbackCell d ≤ n := by
      have hd : NfallbackCell d ≤ Nfallback := by
        dsimp only [Nfallback]
        exact Finset.single_le_sum
          (fun e he ↦ Nat.zero_le (NfallbackCell e)) (Finset.mem_univ d)
      exact hd.trans hNfallback
    have hdivCell := hfallbackCell d eta hNcell heta (hS d)
    have hdiv (D : ℕ) (hD : 0 < D) :
        ((uniformOnFinset (S d) (hS d)).exponentialTilt
            (fun m : S d ↦
              valuationScore (primeBand n W) eta (L n) (m : ℕ))).expect
          (fun m ↦ divInd D (m : ℕ)) ≤ Gf * (1 / (D : ℝ)) := by
      have hraw := hdivCell D hD
      have hmono := div_le_div_of_nonneg_right (hGcellLe d)
        (by positivity : (0 : ℝ) ≤ (D : ℝ))
      simpa only [S, valuationTilt_probability, valuationTilt_value,
        one_mul, div_eq_mul_inv] using hraw.trans hmono
    have hvaluePos : ∀ m : S d, 0 < (m : ℕ) := by
      intro m
      exact pos_of_mem_smoothInterval (mem_structuredCell.mp m.property).1
    have hvalueLe : ∀ m : S d, (m : ℕ) ≤ physicalBound (C d) n := by
      intro m
      exact (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1
    have hraw :=
      PrimePowerTail.abs_expect_valuation_sub_cutoff_le_of_divisor_fallback_unrestricted
        ((uniformOnFinset (S d) (hS d)).exponentialTilt
          (fun m : S d ↦
            valuationScore (primeBand n W) eta (L n) (m : ℕ)))
        (fun m : S d ↦ (m : ℕ)) hp hvaluePos hvalueLe hGf0 hdiv
        (Kcut := Kcut)
    have hpowNat : yNat n ^ 4 < p ^ (Kcut + 1) := by
      simpa only [Kcut, Nat.succ_eq_add_one] using
        Nat.lt_pow_succ_log_self hp.one_lt (yNat n ^ 4)
    have hpow : ((yNat n ^ 4 : ℕ) : ℝ) ≤
        (p : ℝ) ^ (Kcut + 1) := by exact_mod_cast hpowNat.le
    have hTreal : (0 : ℝ) < (yNat n ^ 4 : ℕ) := by exact_mod_cast hTpos
    have hrecip : 2 / (p : ℝ) ^ (Kcut + 1) ≤
        2 / ((yNat n ^ 4 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hTreal hpow
    calc
      _ ≤ Gf * (2 / (p : ℝ) ^ (Kcut + 1)) := hraw
      _ ≤ Gf * (2 / ((yNat n ^ 4 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hrecip hGf0
      _ ≤ ((2 * Gf) / L n) * (1 / (p : ℝ)) :=
        htailSharpN p hp.pos hpY Gf hGf0
  have hsumWeight : (∑ k ∈ positiveExponents Kcut,
      singleWeight p k) ≤ 6 / (p : ℝ) :=
    sum_singleWeight_positiveExponents_le hp.two_le
  have hcomponent (d : Cell) :
      |((uniformOnFinset (S d) (hS d)).exponentialTilt
            (fun m : S d ↦
              valuationScore (primeBand n W) eta (L n) (m : ℕ))).expect
          (fun m ↦ valuation p (m : ℕ)) - mainSum| ≤
        (6 * signedError n + 2 * Gf / L n) * (1 / (p : ℝ)) := by
    let mu := (uniformOnFinset (S d) (hS d)).exponentialTilt
      (fun m : S d ↦ valuationScore (primeBand n W) eta (L n) (m : ℕ))
    let trunc : S d → ℝ := fun m ↦
      ∑ k ∈ positiveExponents Kcut, divInd (p ^ k) (m : ℕ)
    let tail : S d → ℝ := fun m ↦ valuation p (m : ℕ) - trunc m
    have hexpect : mu.expect (fun m ↦ valuation p (m : ℕ)) =
        mu.expect trunc + mu.expect tail := by
      have hpoint : (fun m : S d ↦ (valuation p (m : ℕ) : ℝ)) =
          fun m ↦ trunc m + tail m := by
        funext m
        dsimp only [tail]
        ring
      rw [hpoint, mu.expect_add]
    have htruncExpand : mu.expect trunc =
        ∑ k ∈ positiveExponents Kcut,
          mu.expect (fun m ↦ divInd (p ^ k) (m : ℕ)) := by
      exact PrimePowerCutoffCovariance.FiniteProbability.expect_sum mu
        (positiveExponents Kcut) (fun k m ↦ divInd (p ^ k) (m : ℕ))
    have htrunc : |mu.expect trunc - mainSum| ≤
        signedError n * (6 / (p : ℝ)) := by
      rw [htruncExpand]
      dsimp only [mainSum]
      rw [← Finset.sum_sub_distrib]
      calc
        |∑ k ∈ positiveExponents Kcut,
            (mu.expect (fun m ↦ divInd (p ^ k) (m : ℕ)) - main k)| ≤
          ∑ k ∈ positiveExponents Kcut,
            |mu.expect (fun m ↦ divInd (p ^ k) (m : ℕ)) - main k| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ positiveExponents Kcut,
            signedError n * singleWeight p k := by
          exact Finset.sum_le_sum fun k hk ↦ by
            simpa only [mu] using hprofileOne d k hk
        _ = signedError n *
            (∑ k ∈ positiveExponents Kcut, singleWeight p k) := by
          rw [Finset.mul_sum]
        _ ≤ signedError n * (6 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hsumWeight (hsigned0 n)
    have htail : |mu.expect tail| ≤
        ((2 * Gf) / L n) * (1 / (p : ℝ)) := by
      simpa only [mu, tail, trunc] using htailOne d
    rw [hexpect]
    calc
      |mu.expect trunc + mu.expect tail - mainSum| =
          |(mu.expect trunc - mainSum) + mu.expect tail| := by ring_nf
      _ ≤ |mu.expect trunc - mainSum| + |mu.expect tail| := abs_add_le _ _
      _ ≤ signedError n * (6 / (p : ℝ)) +
          ((2 * Gf) / L n) * (1 / (p : ℝ)) :=
        add_le_add htrunc htail
      _ = (6 * signedError n + 2 * Gf / L n) *
          (1 / (p : ℝ)) := by ring
  calc
    _ ≤ |((uniformOnFinset (S c) (hS c)).exponentialTilt
            (fun m : S c ↦
              valuationScore (primeBand n W) eta (L n) (m : ℕ))).expect
          (fun m ↦ valuation p (m : ℕ)) - mainSum| +
        |((uniformOnFinset (S c') (hS c')).exponentialTilt
            (fun m : S c' ↦
              valuationScore (primeBand n W) eta (L n) (m : ℕ))).expect
          (fun m ↦ valuation p (m : ℕ)) - mainSum| := by
      have htri := abs_sub
        (((uniformOnFinset (S c) (hS c)).exponentialTilt
            (fun m : S c ↦ valuationScore (primeBand n W) eta (L n)
              (m : ℕ))).expect (fun m ↦ valuation p (m : ℕ)) - mainSum)
        (((uniformOnFinset (S c') (hS c')).exponentialTilt
            (fun m : S c' ↦ valuationScore (primeBand n W) eta (L n)
              (m : ℕ))).expect (fun m ↦ valuation p (m : ℕ)) - mainSum)
      simpa only [sub_sub_sub_cancel_right] using htri
    _ ≤ (6 * signedError n + 2 * Gf / L n) * (1 / (p : ℝ)) +
        (6 * signedError n + 2 * Gf / L n) * (1 / (p : ℝ)) :=
      add_le_add (hcomponent c) (hcomponent c')
    _ = 2 * ((6 * signedError n + 2 * Gf / L n) *
        (1 / (p : ℝ))) := by ring
    _ = epsilon n / (p : ℝ) := by
      dsimp only [epsilon, tailCoefficient]
      ring

end

end Erdos390.Full.PaperRawTiltedValuationMeanRows
