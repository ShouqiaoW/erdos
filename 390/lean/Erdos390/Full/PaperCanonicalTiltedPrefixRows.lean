import Erdos390.Full.PaperFixedFiniteRawTiltedPrefixRows
import Erdos390.Full.PaperCanonicalMediumNuisanceRows
import Erdos390.Full.GuardSquarefreeErrorRate
import Erdos390.Full.PaperPrimePowerTailRate

/-!
# Canonical guard-deleted tilted moving-prefix rows

The raw Taylor row is transported through the literal guard deletion and
the exact canonical sample-space reindexing.  After row normalization, the
guard error contains the factor `p * valuationEnvelope`.  Uniformly in the
moving band this is eventually at most `yNat^2`, so it is absorbed by the
already audited squarefree guard error.  The final coefficient therefore
still satisfies the sharp `epsilon(n) * log L(n) -> 0` rate.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.PaperCanonicalTiltedPrefixRows

open ArithmeticModel Scale HeadPattern StructuredCells
open ArithmeticBandGeometry PaperBridgeFit
open FiniteProbability ValuationScoreDomination ValuationTiltCell
open PaperGuardCensus GuardDeletionSquarefreeProfiles
open GuardSquarefreeErrorRate PaperPrimePowerTailRate
open PaperFixedFiniteRawTiltedPrefixRows

noncomputable section

set_option maxHeartbeats 1600000

/-- Every fixed multiple of `L` is eventually below `yNat`.  The proof uses
the explicit intermediate scale `n^(1/5)`, safely below `y=n^(2/9)`. -/
theorem eventually_two_div_log_mul_L_le_yNat
    (W : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (2 / Real.log (W : ℝ)) * L n ≤ (yNat n : ℝ) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (1 : ℝ) / x ^ (1 / 5 : ℝ))
      atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 5)).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  have hbase : Tendsto
      (fun n : ℕ ↦ L n / (n : ℝ) ^ (1 / 5 : ℝ))
      atTop (nhds 0) := by
    change Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) /
        (n : ℝ) ^ (1 / 5 : ℝ)) atTop (nhds 0)
    simpa only [Function.comp_apply, Real.rpow_one] using hnat
  let K : ℝ := 2 / Real.log (W : ℝ)
  have hscaled : Tendsto
      (fun n : ℕ ↦ (K * L n) / (n : ℝ) ^ (1 / 5 : ℝ))
      atTop (nhds 0) := by
    have hK : Tendsto (fun _n : ℕ ↦ K) atTop (nhds K) :=
      tendsto_const_nhds
    have hraw := hK.mul hbase
    have hraw' : Tendsto
        (fun n : ℕ ↦ K * (L n / (n : ℝ) ^ (1 / 5 : ℝ)))
        atTop (nhds 0) := by simpa only [mul_zero] using hraw
    apply hraw'.congr'
    filter_upwards with n
    ring
  have hle : ∀ᶠ n : ℕ in atTop,
      (K * L n) / (n : ℝ) ^ (1 / 5 : ℝ) ≤ 1 :=
    hscaled.eventually (eventually_le_nhds (by norm_num))
  filter_upwards [hle, eventually_rpow_one_fifth_le_yNat,
    Filter.eventually_gt_atTop 0] with n hratio hpow hn
  have hden : 0 < (n : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hKL : K * L n ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
    have := (div_le_iff₀ hden).mp hratio
    simpa only [one_mul] using this
  simpa only [K] using hKL.trans hpow

/-- Uniform logarithmic envelope bounds for the fixed finite family of
physical cells.  Both nonnegativity and the precise fixed-cutoff multiple of
`L` are retained for downstream multiplication. -/
theorem eventually_valuationEnvelope_bounds
    {Head : Type*} [Fintype Head]
    (I : PhysicalIntervals) (W : ℕ) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ c : PaperBridgeFit.Cell Head,
      0 ≤ valuationEnvelope I n W c ∧
      valuationEnvelope I n W c ≤
        (2 / Real.log (W : ℝ)) * L n := by
  rw [Filter.eventually_all]
  intro c
  let C : ℝ := I.upper c.2
  have hC : 0 < C := (I.lower_pos c.2).trans (I.lower_lt_upper c.2)
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hCevent : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop C)
  have hInvCevent : ∀ᶠ n : ℕ in atTop, 1 / C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop (1 / C))
  filter_upwards [hCevent, hInvCevent, Filter.eventually_gt_atTop 1]
      with n hCn hInvCn hn
  have hnR : (0 : ℝ) < n := by positivity
  have hL : 0 < L n := L_pos hn
  have hlogW : 0 < Real.log (W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  let M := physicalBound C n
  have hMcast : (M : ℝ) ≤ C * (n : ℝ) := by
    dsimp only [M]
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hC.le hnR.le)
  have hMone : 1 ≤ M := by
    dsimp only [M]
    unfold physicalBound
    apply Nat.le_floor
    have hraw := (div_le_iff₀ hC).mp hInvCn
    exact_mod_cast (show (1 : ℝ) ≤ C * (n : ℝ) by
      simpa only [one_mul, mul_comm] using hraw)
  have hMpos : 0 < M := Nat.zero_lt_of_lt hMone
  have hCnSq : C * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hlogM : Real.log (M : ℝ) ≤ 2 * L n := by
    have hle : (M : ℝ) ≤ (n : ℝ) ^ 2 := hMcast.trans hCnSq
    have hraw := Real.log_le_log (by exact_mod_cast hMpos) hle
    rw [Real.log_pow] at hraw
    simpa [L] using hraw
  have henv0 : 0 ≤ valuationEnvelope I n W c := by
    unfold valuationEnvelope
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hMone)) hlogW.le
  refine ⟨henv0, ?_⟩
  unfold valuationEnvelope
  change Real.log (M : ℝ) / Real.log (W : ℝ) ≤ _
  calc
    Real.log (M : ℝ) / Real.log (W : ℝ) ≤
        (2 * L n) / Real.log (W : ℝ) :=
      div_le_div_of_nonneg_right hlogM hlogW.le
    _ = (2 / Real.log (W : ℝ)) * L n := by ring

/-- Row-normalized guard envelope: `p * valuationEnvelope <= yNat^2`
uniformly in the cell and moving band prime. -/
theorem eventually_bandPrime_mul_valuationEnvelope_le_yNat_sq
    {Head : Type*} [Fintype Head]
    (I : PhysicalIntervals) (W : ℕ) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (c : PaperBridgeFit.Cell Head) (p : BandPrime n W),
        (p.1 : ℝ) * valuationEnvelope I n W c ≤ (yNat n : ℝ) ^ 2 := by
  filter_upwards [eventually_valuationEnvelope_bounds (Head := Head) I W hW,
    eventually_two_div_log_mul_L_le_yNat W] with n henv hscale
  intro c p
  have hpY : (p.1 : ℝ) ≤ (yNat n : ℝ) := by
    exact_mod_cast le_yNat_of_mem_primeBand p.2
  have henvY : valuationEnvelope I n W c ≤ (yNat n : ℝ) :=
    (henv c).2.trans hscale
  have hy0 : (0 : ℝ) ≤ yNat n := by positivity
  have hmul := mul_le_mul hpY henvY (henv c).1 hy0
  simpa only [pow_two] using hmul

/-- A fixed finite physical-interval constant dominating every relative
cell span. -/
def physicalSpanMajorant (I : PhysicalIntervals) : ℝ :=
  ∑ sigma : PhysicalSign, 2 * I.upper sigma / I.lower sigma

theorem physicalSpanMajorant_nonneg (I : PhysicalIntervals) :
    0 ≤ physicalSpanMajorant I := by
  unfold physicalSpanMajorant
  exact Finset.sum_nonneg fun sigma hsigma ↦
    div_nonneg (mul_nonneg (by norm_num)
      ((I.lower_pos sigma).trans (I.lower_lt_upper sigma)).le)
      (I.lower_pos sigma).le

/-- The literal floored physical endpoints have a uniformly bounded
relative span. -/
theorem eventually_physicalBound_relativeSpan_le
    (I : PhysicalIntervals) :
    ∀ᶠ n : ℕ in atTop, ∀ sigma : PhysicalSign,
      0 < physicalBound (I.lower sigma) n ∧
      (((physicalBound (I.upper sigma) n : ℝ) -
          (physicalBound (I.lower sigma) n : ℝ)) /
          (physicalBound (I.lower sigma) n : ℝ)) ≤
        physicalSpanMajorant I := by
  rw [Filter.eventually_all]
  intro sigma
  let A := I.lower sigma
  let C := I.upper sigma
  have hA : 0 < A := I.lower_pos sigma
  have hC : 0 < C := hA.trans (I.lower_lt_upper sigma)
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 / A ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop (2 / A))
  filter_upwards [hlarge, Filter.eventually_gt_atTop 0] with n hnlarge hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hAnTwo : (2 : ℝ) ≤ A * (n : ℝ) := by
    have := (div_le_iff₀ hA).mp hnlarge
    simpa only [mul_comm] using this
  let lo := physicalBound A n
  let hi := physicalBound C n
  have hloFloor : A * (n : ℝ) < (lo : ℝ) + 1 := by
    dsimp only [lo, physicalBound]
    exact Nat.lt_floor_add_one _
  have hloHalf : A * (n : ℝ) / 2 ≤ (lo : ℝ) := by
    nlinarith
  have hloPosR : (0 : ℝ) < lo :=
    (div_pos (mul_pos hA hnR) (by norm_num)).trans_le hloHalf
  have hloPos : 0 < lo := by exact_mod_cast hloPosR
  have hhi : (hi : ℝ) ≤ C * (n : ℝ) := by
    dsimp only [hi, physicalBound]
    exact Nat.floor_le (mul_nonneg hC.le hnR.le)
  have hspan0 : (0 : ℝ) ≤ (lo : ℝ) := hloPosR.le
  have hnum : (hi : ℝ) - (lo : ℝ) ≤ C * (n : ℝ) := by
    linarith
  have hlocal :
      (((hi : ℝ) - (lo : ℝ)) / (lo : ℝ)) ≤ 2 * C / A := by
    have hfirst := div_le_div_of_nonneg_right hnum hloPosR.le
    have hsecond : C * (n : ℝ) / (lo : ℝ) ≤ 2 * C / A := by
      apply (div_le_iff₀ hloPosR).2
      have hCA0 : 0 ≤ 2 * C / A := by positivity
      have hmul := mul_le_mul_of_nonneg_left hloHalf hCA0
      calc
        C * (n : ℝ) ≤ (2 * C / A) * (A * (n : ℝ) / 2) := by
          field_simp [hA.ne']
          norm_num
        _ ≤ (2 * C / A) * (lo : ℝ) := hmul
    exact hfirst.trans hsecond
  refine ⟨hloPos, hlocal.trans ?_⟩
  unfold physicalSpanMajorant
  exact Finset.single_le_sum
    (fun tau htau ↦ div_nonneg
      (mul_nonneg (by norm_num)
        ((I.lower_pos tau).trans (I.lower_lt_upper tau)).le)
      (I.lower_pos tau).le)
    (Finset.mem_univ sigma)

namespace PaperBridgeFit.BridgeData

open PaperBridgeFit

variable {Head : Type*} [Fintype Head] [DecidableEq Head]

/-- Canonical, guard-deleted terminal moving-prefix row.  No raw prefix,
third-cumulant, density, score-smallness, or guard estimate remains as a
hypothesis.  The threshold is uniform in the bridge data, the effective
coefficient vector, all cells, all prefixes, and all moving primes. -/
theorem exists_uniform_canonical_cellMediumLaw_tilted_valuation_prefix_rate_unrestricted
    [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank)
    (W : ℕ) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ q ∈ (P h).primes, q ≤ W)
    (Acoef : ℝ) (hAcoef : 0 ≤ Acoef) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ,
        ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
          (B : BridgeData Head Band) (xi : B.ParamSpace),
          N₀ ≤ B.sampleData.n → B.sampleData.W = W →
          (∀ p : BandPrime B.sampleData.n B.sampleData.W,
            |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n) →
          (hremaining : ∀ c : Cell Head,
            (rawCell P I B.sampleData.n c \ (G B.sampleData.n).guards).Nonempty) →
          B.sampleData = canonicalSampleData
            (W := B.sampleData.W) P I (G B.sampleData.n) hsep hremaining →
          ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
            (c : Cell Head) (k : ℕ),
            |(B.cellMediumLaw xi c).covariance
                (fun m ↦ (valuation p.1 (m : ℕ) : ℝ))
                (fun m ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
              epsilon B.sampleData.n / (p.1 : ℝ) := by
  let H : Cell Head → Pattern := fun c ↦ P c.1
  let Alower : Cell Head → ℝ := fun c ↦ I.lower c.2
  let Cupper : Cell Head → ℝ := fun c ↦ I.upper c.2
  obtain ⟨epsilonRaw, hepsilonRaw0, hepsilonRawRate, Nraw, hraw⟩ :=
    exists_uniform_fixedFinite_rawCell_tilted_valuation_all_prefix_rate_unrestricted
      H Alower Cupper
      (fun c ↦ I.lower_pos c.2)
      (fun c ↦ I.lower_lt_upper c.2)
      (fun c ↦ (I.lower_pos c.2).trans (I.lower_lt_upper c.2))
      Acoef W hAcoef hW (fun c ↦ hHeadLe c.1)
  let Kscore : ℝ := (2 * Acoef) / Real.log (W : ℝ)
  let epsilonGuard : ℕ → ℝ := fun n ↦
    6 * canonicalGuardSquarefreeError P I G Kscore n
  let epsilon : ℕ → ℝ := fun n ↦
    epsilonRaw n + epsilonGuard n
  have hepsilonGuard0 : ∀ n, 0 ≤ epsilonGuard n := by
    intro n
    dsimp only [epsilonGuard]
    exact mul_nonneg (by norm_num)
      (canonicalGuardSquarefreeError_nonneg P I G Kscore n)
  have hepsilon0 : ∀ n, 0 ≤ epsilon n := by
    intro n
    dsimp only [epsilon]
    exact add_nonneg (hepsilonRaw0 n) (hepsilonGuard0 n)
  have hepsilonGuardRate : Tendsto (fun n : ℕ ↦
      epsilonGuard n * Real.log (L n)) atTop (nhds 0) := by
    have hrawRate :=
      tendsto_canonicalGuardSquarefreeError_mul_logL_zero P I G Kscore
    have hsix : Tendsto (fun _n : ℕ ↦ (6 : ℝ)) atTop (nhds 6) :=
      tendsto_const_nhds
    have hmul := hsix.mul hrawRate
    simpa only [epsilonGuard, mul_zero, mul_assoc] using hmul
  have hepsilonRate : Tendsto (fun n : ℕ ↦
      epsilon n * Real.log (L n)) atTop (nhds 0) := by
    have hsum := hepsilonRawRate.add hepsilonGuardRate
    simpa only [epsilon, add_mul, zero_add] using hsum
  have hsmallEvent :=
    eventually_exp_two_mul_guardRatio_rawCell_le_half
      P I Cprom Cbank G Kscore
  have henvEvent :=
    eventually_valuationEnvelope_bounds (Head := Head) I W hW
  have hrowEnvEvent :=
    eventually_bandPrime_mul_valuationEnvelope_le_yNat_sq
      (Head := Head) I W hW
  have hAll : ∀ᶠ n : ℕ in atTop,
      (∀ c : Cell Head,
        Real.exp (2 * Kscore) * ((G n).guards.card : ℝ) /
          ((rawCell P I n c).card : ℝ) ≤ (1 : ℝ) / 2) ∧
      (∀ c : Cell Head, 0 ≤ valuationEnvelope I n W c ∧
        valuationEnvelope I n W c ≤
          (2 / Real.log (W : ℝ)) * L n) ∧
      (∀ (c : Cell Head) (p : BandPrime n W),
        (p.1 : ℝ) * valuationEnvelope I n W c ≤
          (yNat n : ℝ) ^ 2) ∧ 1 < n := by
    filter_upwards [hsmallEvent, henvEvent, hrowEnvEvent,
      Filter.eventually_gt_atTop 1] with n hsmallN henvN hrowEnvN hn
    exact ⟨hsmallN, henvN, hrowEnvN, hn⟩
  obtain ⟨Nevent, hNevent⟩ := Filter.eventually_atTop.mp hAll
  refine ⟨epsilon, hepsilon0, hepsilonRate, max Nraw Nevent, ?_⟩
  intro Band _instBand _instBandDec B xi hN hBW heta hsep hremaining hcanonical
  subst W
  have hNraw : Nraw ≤ B.sampleData.n := by omega
  have hNeventBound : Nevent ≤ B.sampleData.n := by omega
  obtain ⟨hsmallN, henvN, hrowEnvN, hn⟩ :=
    hNevent B.sampleData.n hNeventBound
  have hetaNat : ∀ q ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.effectiveNatCoefficient xi q| ≤ Acoef := by
    intro q hq
    rw [B.effectiveNatCoefficient_of_mem xi hq]
    exact heta ⟨q, hq⟩
  intro p c k
  have hpW : 1 < B.sampleData.W := hW
  have hrawPrefix : ∀ j : ℕ,
      |((uniformOnFinset (rawCell P I B.sampleData.n c)
          ((hremaining c).mono Finset.sdiff_subset)).exponentialTilt
        (fun m ↦ valuationScore
          (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ))).covariance
          (fun m ↦ (valuation p.1 (m : ℕ) : ℝ))
          (fun m ↦ if (m : ℕ) ≤ j then 1 else 0)| ≤
        epsilonRaw B.sampleData.n / (p.1 : ℝ) := by
    intro j
    have hrawJ := hraw c (n := B.sampleData.n) (k := j) (p := p.1)
      (B.effectiveNatCoefficient xi)
      hNraw p.2 hetaNat ((hremaining c).mono Finset.sdiff_subset)
    simpa only [H, Alower, Cupper, rawCell, BridgeData.L, Scale.L] using hrawJ
  have hL : 0 < B.L := B.L_pos
  have hlogW : 0 < Real.log (B.sampleData.W : ℝ) :=
    Real.log_pos (by exact_mod_cast hpW)
  have hscore : ∀ m : rawCell P I B.sampleData.n c,
      |valuationScore (primeBand B.sampleData.n B.sampleData.W)
        (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤ Kscore := by
    intro m
    have hmpos : 0 < (m : ℕ) :=
      pos_of_mem_smoothInterval (mem_structuredCell.mp m.property).1
    have hmM : (m : ℕ) ≤
        physicalBound (I.upper c.2) B.sampleData.n :=
      (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1
    have hprimeW : ∀ q ∈ primeBand B.sampleData.n B.sampleData.W,
        B.sampleData.W ≤ q := by
      intro q hq
      exact (cutoff_lt_of_mem_primeBand hq).le
    have hscoreRaw := abs_valuationScore_le_log_ratio
      (primeBand B.sampleData.n B.sampleData.W)
      (B.effectiveNatCoefficient xi) hmpos hmM hpW hprimeW
      hAcoef hL hetaNat
    have henvUpper : valuationEnvelope I B.sampleData.n
        B.sampleData.W c ≤
          (2 / Real.log (B.sampleData.W : ℝ)) * B.L := by
      simpa only [BridgeData.L, Scale.L] using (henvN c).2
    have hcoef : 0 ≤ Acoef / B.L := div_nonneg hAcoef hL.le
    calc
      |valuationScore (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤
        (Acoef / B.L) * valuationEnvelope I B.sampleData.n
          B.sampleData.W c := by
        simpa only [valuationEnvelope] using hscoreRaw
      _ ≤ (Acoef / B.L) *
          ((2 / Real.log (B.sampleData.W : ℝ)) * B.L) :=
        mul_le_mul_of_nonneg_left henvUpper hcoef
      _ = Kscore := by
        dsimp only [Kscore]
        field_simp [hL.ne', hlogW.ne']
  let KA := valuationEnvelope I B.sampleData.n B.sampleData.W c
  have hKA : 0 ≤ KA := by
    dsimp only [KA]
    exact (henvN c).1
  have hvaluation : ∀ m : rawCell P I B.sampleData.n c,
      |(valuation p.1 (m : ℕ) : ℝ)| ≤ KA := by
    intro m
    rw [abs_of_nonneg (valuation_nonneg p.1 (m : ℕ))]
    exact (rawCell_valuation_le_total P I p c m).trans
      (by simpa only [KA] using rawCell_totalBandValuation_le P I hpW c m)
  have hcanonicalPrefix := B.cellMediumLaw_prefix_bound_of_raw_tilt
    P I (G B.sampleData.n) hsep hremaining hcanonical xi c p.1 hKA
    hscore hvaluation (hsmallN c) hrawPrefix k
  let delta : ℝ := Real.exp (2 * Kscore) *
    ((G B.sampleData.n).guards.card : ℝ) /
      ((rawCell P I B.sampleData.n c).card : ℝ)
  have hdelta0 : 0 ≤ delta := by
    dsimp only [delta]
    have hguardCard : (0 : ℝ) ≤ ((G B.sampleData.n).guards.card : ℝ) := by
      exact_mod_cast Nat.zero_le (G B.sampleData.n).guards.card
    have hrawCard : (0 : ℝ) ≤
        ((rawCell P I B.sampleData.n c).card : ℝ) := by
      exact_mod_cast Nat.zero_le (rawCell P I B.sampleData.n c).card
    exact div_nonneg
      (mul_nonneg (Real.exp_pos _).le hguardCard) hrawCard
  have hpR : (0 : ℝ) < p.1 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  have hrowEnv : (p.1 : ℝ) * KA ≤
      (yNat B.sampleData.n : ℝ) ^ 2 := by
    simpa only [KA] using hrowEnvN c p
  have hguardCell :
      (p.1 : ℝ) * (12 * KA * delta) ≤
        6 * guardSquarefreeError
          (rawCell P I B.sampleData.n c) (G B.sampleData.n).guards
            Kscore B.sampleData.n := by
    unfold guardSquarefreeError
    dsimp only [delta]
    calc
      (p.1 : ℝ) *
          (12 * KA *
            (Real.exp (2 * Kscore) *
              ((G B.sampleData.n).guards.card : ℝ) /
                ((rawCell P I B.sampleData.n c).card : ℝ))) =
        12 * ((p.1 : ℝ) * KA) *
          (Real.exp (2 * Kscore) *
            ((G B.sampleData.n).guards.card : ℝ) /
              ((rawCell P I B.sampleData.n c).card : ℝ)) := by ring
      _ ≤ 12 * (yNat B.sampleData.n : ℝ) ^ 2 *
          (Real.exp (2 * Kscore) *
            ((G B.sampleData.n).guards.card : ℝ) /
              ((rawCell P I B.sampleData.n c).card : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrowEnv (by norm_num)) hdelta0
      _ = 6 *
          (2 * (Real.exp (2 * Kscore) *
            ((G B.sampleData.n).guards.card : ℝ) /
              ((rawCell P I B.sampleData.n c).card : ℝ)) *
                (yNat B.sampleData.n : ℝ) ^ 2) := by ring
  have hcellToSum : guardSquarefreeError
      (rawCell P I B.sampleData.n c) (G B.sampleData.n).guards
        Kscore B.sampleData.n ≤
      canonicalGuardSquarefreeError P I G Kscore B.sampleData.n := by
    unfold canonicalGuardSquarefreeError
    exact Finset.single_le_sum
      (fun d hd ↦ guardSquarefreeError_nonneg
        (rawCell P I B.sampleData.n d) (G B.sampleData.n).guards
          Kscore B.sampleData.n)
      (Finset.mem_univ c)
  have hguardRow : 12 * KA * delta ≤
      epsilonGuard B.sampleData.n / (p.1 : ℝ) := by
    apply (le_div_iff₀ hpR).2
    calc
      12 * KA * delta * (p.1 : ℝ) =
          (p.1 : ℝ) * (12 * KA * delta) := by ring
      _ ≤ 6 * guardSquarefreeError
          (rawCell P I B.sampleData.n c) (G B.sampleData.n).guards
            Kscore B.sampleData.n := hguardCell
      _ ≤ 6 * canonicalGuardSquarefreeError P I G Kscore
          B.sampleData.n := mul_le_mul_of_nonneg_left hcellToSum (by norm_num)
      _ = epsilonGuard B.sampleData.n := rfl
  calc
    |(B.cellMediumLaw xi c).covariance
        (fun m ↦ (valuation p.1 (m : ℕ) : ℝ))
        (fun m ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
      epsilonRaw B.sampleData.n / (p.1 : ℝ) +
        12 * KA * delta := by
      simpa only [KA, delta] using hcanonicalPrefix
    _ ≤ epsilonRaw B.sampleData.n / (p.1 : ℝ) +
        epsilonGuard B.sampleData.n / (p.1 : ℝ) :=
      add_le_add le_rfl hguardRow
    _ = epsilon B.sampleData.n / (p.1 : ℝ) := by
      dsimp only [epsilon]
      ring

/-- The canonical physical marked row obtained by exact finite Stieltjes
summation from the preceding all-prefix theorem.  No prefix estimate remains
in the hypotheses. -/
theorem exists_uniform_canonical_cellMediumLaw_physical_valuation_rate_unrestricted
    [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank)
    (W : ℕ) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ q ∈ (P h).primes, q ≤ W)
    (Acoef : ℝ) (hAcoef : 0 ≤ Acoef) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ,
        ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
          (B : BridgeData Head Band) (xi : B.ParamSpace),
          N₀ ≤ B.sampleData.n → B.sampleData.W = W →
          (∀ p : BandPrime B.sampleData.n B.sampleData.W,
            |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n) →
          (hremaining : ∀ c : Cell Head,
            (rawCell P I B.sampleData.n c \ (G B.sampleData.n).guards).Nonempty) →
          B.sampleData = canonicalSampleData
            (W := B.sampleData.W) P I (G B.sampleData.n) hsep hremaining →
          ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
            (c : Cell Head),
            |(B.cellMediumLaw xi c).covariance
                (fun m ↦ valuation p.1 (m : ℕ))
                (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
              epsilon B.sampleData.n / (p.1 : ℝ) := by
  obtain ⟨epsilonPrefix, hepsilonPrefix0, hepsilonPrefixRate,
    Nprefix, hprefix⟩ :=
      exists_uniform_canonical_cellMediumLaw_tilted_valuation_prefix_rate_unrestricted
        P I Cprom Cbank G W hW hHeadLe Acoef hAcoef
  let Kspan := physicalSpanMajorant I
  let epsilon : ℕ → ℝ := fun n ↦ Kspan * epsilonPrefix n
  have hKspan : 0 ≤ Kspan := physicalSpanMajorant_nonneg I
  have hepsilon0 : ∀ n, 0 ≤ epsilon n := by
    intro n
    dsimp only [epsilon]
    exact mul_nonneg hKspan (hepsilonPrefix0 n)
  have hepsilonRate : Tendsto (fun n : ℕ ↦
      epsilon n * Real.log (L n)) atTop (nhds 0) := by
    have hK : Tendsto (fun _n : ℕ ↦ Kspan) atTop (nhds Kspan) :=
      tendsto_const_nhds
    have hraw := hK.mul hepsilonPrefixRate
    simpa only [epsilon, mul_zero, mul_assoc] using hraw
  obtain ⟨Nspan, hspan⟩ := Filter.eventually_atTop.mp
    (eventually_physicalBound_relativeSpan_le I)
  refine ⟨epsilon, hepsilon0, hepsilonRate, max Nprefix Nspan, ?_⟩
  intro Band _instBand _instBandDec B xi hN hBW heta hsep hremaining hcanonical
  have hNprefix : Nprefix ≤ B.sampleData.n := by omega
  have hNspan : Nspan ≤ B.sampleData.n := by omega
  have hprefixN := hprefix B xi hNprefix hBW heta hsep hremaining hcanonical
  intro p c
  have hspanN := hspan B.sampleData.n hNspan c.2
  have hlo : 0 < B.sampleData.lo c.2 := by
    rw [hcanonical]
    simpa only [canonicalSampleData_lo] using hspanN.1
  have hrelative :
      ((B.sampleData.hi c.2 : ℝ) - (B.sampleData.lo c.2 : ℝ)) /
          (B.sampleData.lo c.2 : ℝ) ≤ Kspan := by
    rw [hcanonical]
    simpa only [canonicalSampleData_lo, canonicalSampleData_hi, Kspan]
      using hspanN.2
  have hcentered : ∀ t ∈ Set.Ioc
      (B.sampleData.lo c.2 : ℝ) (B.sampleData.hi c.2 : ℝ),
      |∑ k ∈ Finset.Icc 0 ⌊t⌋₊,
        FiniteLogStieltjes.centeredFiberMass
          (B.cellMediumLaw xi c) (fun m ↦ (m : ℕ))
            (fun m ↦ valuation p.1 (m : ℕ)) k| ≤
        (epsilonPrefix B.sampleData.n / (1 : ℝ)) *
          (1 / (p.1 : ℝ)) := by
    intro t ht
    rw [FiniteLogStieltjes.sum_centeredFiberMass_Icc_eq_covariance_prefixIndicator]
    calc
      _ ≤ epsilonPrefix B.sampleData.n / (p.1 : ℝ) :=
        hprefixN p c ⌊t⌋₊
      _ = (epsilonPrefix B.sampleData.n / (1 : ℝ)) *
          (1 / (p.1 : ℝ)) := by ring
  have hraw := B.abs_cellMediumLaw_covariance_valuation_physical_le_of_prefix_rate
    xi c (prime_of_mem_primeBand p.2).pos
    (hepsilonPrefix0 B.sampleData.n) (by norm_num : (0 : ℝ) < 1)
    hlo hrelative hcentered
  calc
    |(B.cellMediumLaw xi c).covariance
        (fun m ↦ valuation p.1 (m : ℕ))
        (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
      (Kspan * epsilonPrefix B.sampleData.n) *
        (1 / (p.1 : ℝ)) := by simpa only [div_one, mul_assoc] using hraw
    _ = epsilon B.sampleData.n / (p.1 : ℝ) := by
      dsimp only [epsilon]
      ring

end PaperBridgeFit.BridgeData

end

end Erdos390.Full.PaperCanonicalTiltedPrefixRows
