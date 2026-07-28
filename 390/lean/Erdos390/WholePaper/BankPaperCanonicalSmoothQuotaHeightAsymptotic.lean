import Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightLedger
import Erdos390.WholePaper.BankPaperCanonicalRawBroadSurplusAsymptotic
import Erdos390.WholePaper.BankPaperCanonicalHeadActiveMassEventually

/-!
# The analytic Section 8 smooth-row quota and height bridge

The raw active smooth component from the exact companion file has a positive
`n / log n` lower bound by the repository's uniform de Bruijn--Saias and
fixed-head estimates.  This file proves that bound directly for complete-
rough label one, then propagates it through the exact nearest-integer and
height-center constructions.

Only one repository-level analytic ledger remains absent.  It is named
`BankPaperCanonicalSectionEightAnalyticLedger` below and contains exactly:

* the actual post-guard smooth mass differs from the explicit raw base mass
  by `o(n / log n)`;
* the literal frozen height defect `A0` is `O(n / log n)`.

These are precisely the two estimates asserted together in the paper's
Section 8 frozen ledger.  No selector, active-measure, or positivity premise
is hidden in that predicate.  Every consequence after it, including
`d = O(n / log^2 n)` and the positive lower bound for `q0 - d`, is proved
here.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## The label-one raw base pool is macroscopically large -/

private theorem bankPaperCanonicalSmoothBase_yNat_tendsto_atTop :
    Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : Nat => y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : Real) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_nat_floor_atTop.comp hy

private theorem bankPaperCanonicalSmoothBase_log_yNat_tendsto_atTop :
    Tendsto (fun n : Nat => Real.log (yNat n : Real)) atTop atTop := by
  have hyReal : Tendsto (fun n : Nat => (yNat n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      bankPaperCanonicalSmoothBase_yNat_tendsto_atTop
  exact Real.tendsto_log_atTop.comp hyReal

/-- The explicit label-one head-free broad pool retains a fixed positive
linear fraction of `n`.  Unlike the existing active-row theorem, this result
does not exclude label one. -/
theorem eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower
    (W K : Nat) {c : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      roughCanonicalRawBroadPoolDensity W * (n : Real) <=
        ((bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K).card : Real) := by
  obtain ⟨C, hC, YdeBruijn, hdeBruijn⟩ :=
    FriableAsymptotic.exists_uniform_friableCount_dickman_bound_all_faces
  obtain ⟨Kshift, hKshift, Yshift, hshift⟩ :=
    exists_uniform_roughFixedHead_friableCount_shift_bound W
  let P : Real := roughHeadModulus W
  let r : Real := roughCanonicalPoolDickmanFloor
  have hr : 0 < r := by
    dsimp only [r]
    exact roughCanonicalPoolDickmanFloor_pos
  let A0 : Nat :=
    max (roughHeadModulus W)
      (max 2 ⌈192 * P / (roughHeadDensity W * r)⌉₊)
  let logThreshold : Real :=
    max (2 / r)
      (max (32 * C / r)
        (128 * P * Kshift / (roughHeadDensity W * r)))
  have hlogEvent : ∀ᶠ n : Nat in atTop,
      logThreshold <= Real.log (yNat n : Real) :=
    bankPaperCanonicalSmoothBase_log_yNat_tendsto_atTop.eventually
      (eventually_ge_atTop logThreshold)
  have hyEvent : ∀ᶠ n : Nat in atTop,
      max W (max YdeBruijn (max Yshift 2)) <= yNat n :=
    bankPaperCanonicalSmoothBase_yNat_tendsto_atTop.eventually
      (eventually_ge_atTop (max W (max YdeBruijn (max Yshift 2))))
  have hAEvent : ∀ᶠ n : Nat in atTop, A0 <= n :=
    eventually_ge_atTop A0
  have htailEvent : ∀ᶠ n : Nat in atTop,
      ((2 * K * upperTailLength c n : Nat) : Real) / (n : Real) <=
        1 / 2 := by
    have hT : Tendsto
        (fun n : Nat => (2 * (K : Real)) *
          ((upperTailLength c n : Real) / (n : Real)))
        atTop (nhds 0) := by
      simpa only [mul_zero] using
        (upperTailLength_ratio_tendsto_zero hc).const_mul
          (2 * (K : Real))
    have hsmall := hT.eventually
      (eventually_lt_nhds (by norm_num : (0 : Real) < 1 / 2))
    filter_upwards [hsmall] with n hn
    have hn' :
        (2 * (K : Real)) *
            ((upperTailLength c n : Real) / (n : Real)) < 1 / 2 := hn
    calc
      ((2 * K * upperTailLength c n : Nat) : Real) / (n : Real) =
          (2 * (K : Real)) *
            ((upperTailLength c n : Real) / (n : Real)) := by
        push_cast
        ring
      _ <= 1 / 2 := hn'.le
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLEvent : ∀ᶠ n : Nat in atTop,
      54 * Real.log 2 <= L n :=
    hLTop.eventually (eventually_ge_atTop (54 * Real.log 2))
  filter_upwards [eventually_gt_atTop 0, hlogEvent, hyEvent, hAEvent,
    htailEvent, hLEvent] with n hn hlog hy hA0 htail hLlarge
  let A : Nat := n
  let B : Nat := 2 * n - K * upperTailLength c n
  have htailNat : 4 * K * upperTailLength c n <= n := by
    have hnReal : (0 : Real) < n := by exact_mod_cast hn
    have hcross := (div_le_iff₀ hnReal).mp htail
    have hcast :
        ((2 * K * upperTailLength c n : Nat) : Real) <=
          (n : Real) / 2 := by
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using hcross
    have hcast' :
        ((4 * K * upperTailLength c n : Nat) : Real) <= (n : Real) := by
      push_cast at hcast ⊢
      linarith
    exact_mod_cast hcast'
  have htailNat' :
      4 * (K * upperTailLength c n) <= n := by
    simpa only [mul_assoc] using htailNat
  have hKh : K * upperTailLength c n <= n := by omega
  have hAB : A <= B := by
    dsimp only [A, B]
    omega
  have hBthree : B <= 3 * A := by
    dsimp only [A, B]
    omega
  have hlength : A <= 2 * (B - A) := by
    dsimp only [A, B]
    omega
  have hmodA : roughHeadModulus W <= A := by
    dsimp only [A]
    exact (le_max_left _ _).trans hA0
  have hyTwo : 2 <= yNat n :=
    (le_max_right Yshift 2).trans
      ((le_max_right YdeBruijn _).trans ((le_max_right W _).trans hy))
  have hlogB : Real.log (B : Real) <=
      5 * Real.log (yNat n : Real) := by
    have hAPos : 0 < A := by simpa only [A] using hn
    have hBPos : 0 < B := hAPos.trans_le hAB
    have hBLe : B <= 2 * n := by
      dsimp only [B]
      exact Nat.sub_le _ _
    have hlogLe : Real.log (B : Real) <=
        Real.log ((2 * n : Nat) : Real) :=
      Real.log_le_log (by exact_mod_cast hBPos) (by exact_mod_cast hBLe)
    have hypos : 0 < y n := y_pos hn
    have hyFloor : (yNat n : Real) <= y n := Nat.floor_le hypos.le
    have hyRealTwo : (2 : Real) <= y n := by
      exact (by exact_mod_cast hyTwo : (2 : Real) <= (yNat n : Real)).trans
        hyFloor
    have hyNatLower : y n / 2 <= (yNat n : Real) := by
      have hfloor : y n < (yNat n : Real) + 1 := Nat.lt_floor_add_one _
      linarith
    have hlogLower : Real.log (y n / 2) <=
        Real.log (yNat n : Real) :=
      Real.log_le_log (div_pos hypos (by norm_num)) hyNatLower
    have hlogDiv : Real.log (y n / 2) =
        Real.log (y n) - Real.log 2 := by
      rw [Real.log_div hypos.ne' (by norm_num : (2 : Real) ≠ 0)]
    calc
      Real.log (B : Real) <= Real.log ((2 * n : Nat) : Real) := hlogLe
      _ = Real.log 2 + L n := by
        rw [show ((2 * n : Nat) : Real) = 2 * (n : Real) by norm_num,
          Real.log_mul (by norm_num : (2 : Real) ≠ 0)
            (by exact_mod_cast hn.ne')]
        rfl
      _ <= 5 * Real.log (y n / 2) := by
        rw [hlogDiv, log_y hn]
        nlinarith
      _ <= 5 * Real.log (yNat n : Real) := by
        gcongr
  have hlogY : 0 < Real.log (yNat n : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < yNat n by omega))
  have hlogMain :
      2 / Real.log (yNat n : Real) <= r := by
    have hthreshold : 2 / r <= Real.log (yNat n : Real) :=
      (le_max_left _ _).trans hlog
    exact (div_le_iff₀ hlogY).2 <| by
      simpa only [mul_comm] using (div_le_iff₀ hr).1 hthreshold
  have hlogSmooth :
      8 * C / Real.log (yNat n : Real) <= r / 4 := by
    have hthreshold : 32 * C / r <= Real.log (yNat n : Real) :=
      (le_max_left (32 * C / r)
        (128 * P * Kshift / (roughHeadDensity W * r))).trans
          ((le_max_right (2 / r) _).trans hlog)
    have hcross : 32 * C <=
        r * Real.log (yNat n : Real) := by
      simpa only [mul_comm] using (div_le_iff₀ hr).1 hthreshold
    have hleft : 32 * C / Real.log (yNat n : Real) <= r :=
      (div_le_iff₀ hlogY).2 hcross
    calc
      8 * C / Real.log (yNat n : Real) =
          (32 * C / Real.log (yNat n : Real)) / 4 := by ring
      _ <= r / 4 :=
        div_le_div_of_nonneg_right hleft (by norm_num)
  have hlogHead :
      4 * P * Kshift / Real.log (yNat n : Real) <=
        roughHeadDensity W * r / 32 := by
    have hthreshold :
        128 * P * Kshift / (roughHeadDensity W * r) <=
          Real.log (yNat n : Real) :=
      (le_max_right (32 * C / r) _).trans
        ((le_max_right (2 / r) _).trans hlog)
    have hdenom : 0 < roughHeadDensity W * r :=
      mul_pos (roughHeadDensity_pos W) hr
    have hnumerator : 128 * P * Kshift <=
        (roughHeadDensity W * r) * Real.log (yNat n : Real) := by
      simpa only [mul_comm] using (div_le_iff₀ hdenom).1 hthreshold
    have hcross :
        128 * P * Kshift / Real.log (yNat n : Real) <=
          roughHeadDensity W * r :=
      (div_le_iff₀ hlogY).2 hnumerator
    calc
      4 * P * Kshift / Real.log (yNat n : Real) =
          (128 * P * Kshift / Real.log (yNat n : Real)) / 32 := by ring
      _ <= (roughHeadDensity W * r) / 32 :=
        div_le_div_of_nonneg_right hcross (by norm_num)
  have hendpoint :
      6 * P <= roughHeadDensity W * r / 32 * (A : Real) := by
    have hceil :
        192 * P / (roughHeadDensity W * r) <=
          (⌈192 * P / (roughHeadDensity W * r)⌉₊ : Real) :=
      Nat.le_ceil _
    have hceilA :
        (⌈192 * P / (roughHeadDensity W * r)⌉₊ : Nat) <= A :=
      by
        have hceilA0 :
            (⌈192 * P / (roughHeadDensity W * r)⌉₊ : Nat) <= A0 :=
          (le_max_right 2 _).trans
            (le_max_right (roughHeadModulus W) _)
        simpa only [A] using hceilA0.trans hA0
    have hcastA :
        192 * P / (roughHeadDensity W * r) <= (A : Real) :=
      hceil.trans (by exact_mod_cast hceilA)
    have hdenom : 0 < roughHeadDensity W * r :=
      mul_pos (roughHeadDensity_pos W) hr
    have hcross :
        192 * P <= (A : Real) * (roughHeadDensity W * r) :=
      (div_le_iff₀ hdenom).1 hcastA
    calc
      6 * P = (192 * P) / 32 := by ring
      _ <= ((A : Real) * (roughHeadDensity W * r)) / 32 :=
        div_le_div_of_nonneg_right hcross (by norm_num)
      _ = roughHeadDensity W * r / 32 * (A : Real) := by ring
  have hlower := roughCanonical_headFreeSmoothInterval_card_lower
    hC hKshift hdeBruijn hshift
    ((le_max_left YdeBruijn (max Yshift 2)).trans
      ((le_max_right W _).trans hy))
    ((le_max_left Yshift 2).trans
      ((le_max_right YdeBruijn _).trans ((le_max_right W _).trans hy)))
    ((le_max_left W _).trans hy)
    hyTwo hmodA hAB hBthree hlength hlogB
    (by simpa only [r] using hlogMain)
    (by simpa only [r] using hlogSmooth)
    (by simpa only [P, r] using hlogHead)
    (by simpa only [P, r] using hendpoint)
  rw [bankPaperCanonicalRawSmoothBasePool_card_eq_headFreeSmoothInterval]
  simpa only [roughCanonicalRawBroadPoolDensity, A, B] using hlower

/-- Therefore the literal `betaAct / L` base component has the minimal
positive paper-scale lower bound whenever `betaAct > 0`. -/
theorem bankPaperCanonicalRawSmoothBaseMass_paperScaleLower
    (W K : Nat) {c betaAct : Real} (hc : 0 < c) (hbeta : 0 < betaAct) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct) := by
  use betaAct * roughCanonicalRawBroadPoolDensity W,
    mul_pos hbeta (roughCanonicalRawBroadPoolDensity_pos W)
  have hpool :=
    eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower W K hc
  filter_upwards [hpool, eventually_gt_atTop 1] with n hpoolN hn
  have hL : 0 < L n := L_pos hn
  calc
    (betaAct * roughCanonicalRawBroadPoolDensity W) * secondOrderScale n =
        (betaAct / L n) *
          (roughCanonicalRawBroadPoolDensity W * (n : Real)) := by
      unfold secondOrderScale L
      ring
    _ <= (betaAct / L n) *
          ((bankPaperCanonicalRawSmoothBasePool W n
            (upperTailLength c n) K).card : Real) :=
      mul_le_mul_of_nonneg_left hpoolN (div_nonneg hbeta.le hL.le)
    _ = bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) K betaAct := by
      rfl

/-- The raw base mass is also `O(n / log n)`, by the elementary containment
of its support in the broad interval. -/
theorem bankPaperCanonicalRawSmoothBaseMass_isBigO
    (W K : Nat) (c betaAct : Real) :
    (fun n => bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct) =O[atTop] secondOrderScale := by
  apply (isBigO_iff).2
  use |betaAct|
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  have hscale : 0 < secondOrderScale n := secondOrderScale_pos (by omega)
  have hsubset : bankPaperCanonicalRawSmoothBasePool W n
      (upperTailLength c n) K ⊆
        roughBroadLowerBlock n (upperTailLength c n) K := by
    intro a ha
    change a ∈ roughCanonicalBroadCorrectionPool W n
      (upperTailLength c n) K (yNat n) 1 at ha
    have haRow := mem_completeRoughRowFiber.mp ha
    exact (mem_roughHeadFree.mp haRow.1).1
  have hcardNat :
      (bankPaperCanonicalRawSmoothBasePool W n
        (upperTailLength c n) K).card <= n := by
    calc
      (bankPaperCanonicalRawSmoothBasePool W n
        (upperTailLength c n) K).card <=
          (roughBroadLowerBlock n (upperTailLength c n) K).card :=
        Finset.card_le_card hsubset
      _ <= n := by
        simp only [roughBroadLowerBlock, Nat.card_Ioc]
        omega
  have hcard :
      ((bankPaperCanonicalRawSmoothBasePool W n
        (upperTailLength c n) K).card : Real) <= (n : Real) := by
    exact_mod_cast hcardNat
  have hcardNonneg :
      (0 : Real) <=
        ((bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K).card : Real) :=
    Nat.cast_nonneg _
  rw [bankPaperCanonicalRawSmoothBaseMass, Real.norm_eq_abs,
    abs_mul, abs_div, abs_of_pos hL, abs_of_nonneg hcardNonneg,
    Real.norm_eq_abs, abs_of_pos hscale]
  rw [secondOrderScale]
  have hcoef : 0 <= |betaAct| / L n :=
    div_nonneg (abs_nonneg _) hL.le
  calc
    |betaAct| / L n *
        ((bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K).card : Real) <=
        |betaAct| / L n * (n : Real) :=
      mul_le_mul_of_nonneg_left hcard hcoef
    _ = |betaAct| * ((n : Real) / L n) := by ring

/-! ## The exact missing analytic ledger -/

/-- The smallest Section 8 analytic input not represented by the current
repository constructions.  The first field connects the actual post-guard
smooth mass to the explicit raw base mass; the second is the paper's frozen
height-ledger bound. -/
def BankPaperCanonicalSectionEightAnalyticLedger
    (rawBase qTilde A0 : Nat -> Real) : Prop :=
  (fun n => rawBase n - qTilde n) =o[atTop] secondOrderScale ∧
    A0 =O[atTop] secondOrderScale

/-! ## Nearest-integer initialization preserves the paper scale -/

/-- The uniformly bounded initialization error is little-o of
`secondOrderScale`. -/
theorem bankPaperCanonicalSmoothQ0Family_sub_qTilde_isLittleO
    (mFrozen qTilde : Nat -> Real) :
    (fun n => bankPaperCanonicalSmoothQ0Family mFrozen qTilde n -
      qTilde n) =o[atTop] secondOrderScale := by
  have hbounded :
      (fun n => bankPaperCanonicalSmoothQ0Family mFrozen qTilde n -
        qTilde n) =O[atTop] (fun _n : Nat => (1 : Real)) := by
    apply (isBigO_iff).2
    use 1 / 2
    filter_upwards [] with n
    simpa only [Real.norm_eq_abs, abs_one, mul_one] using
      bankPaperCanonicalSmoothQ0Family_abs_sub_qTilde_le
        mFrozen qTilde n
  have hnorm : Tendsto (norm ∘ secondOrderScale) atTop atTop := by
    simpa only [Function.comp_apply, Real.norm_eq_abs] using
      tendsto_abs_atTop_atTop.comp secondOrderScale_tendsto_atTop
  have hone : (fun _n : Nat => (1 : Real)) =o[atTop]
      secondOrderScale :=
    isLittleO_const_left.mpr (Or.inr hnorm)
  exact hbounded.trans_isLittleO hone

/-- A negligible raw-to-post-guard loss transfers the positive lower bound
from the explicit raw base mass to the actual mass `qTilde`. -/
theorem bankPaperCanonicalPostGuardSmoothMass_paperScaleLower
    (rawBase qTilde : Nat -> Real)
    (Hraw : BankPaperCanonicalActiveMassPaperScaleLower rawBase)
    (Hguard : (fun n => rawBase n - qTilde n) =o[atTop]
      secondOrderScale) :
    BankPaperCanonicalActiveMassPaperScaleLower qTilde := by
  rcases bankPaperCanonicalActiveMassPaperScaleLower_sub_of_isLittleO
      rawBase (fun n => rawBase n - qTilde n) Hraw Hguard with
    ⟨C, hC, hlower⟩
  use C, hC
  filter_upwards [hlower] with n hn
  convert hn using 1 ; ring

/-- The half-unit nearest-integer initialization transfers that lower bound
from `qTilde` to the literal `q0` family. -/
theorem bankPaperCanonicalSmoothQ0Family_paperScaleLower
    (mFrozen qTilde : Nat -> Real)
    (HqTilde : BankPaperCanonicalActiveMassPaperScaleLower qTilde) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (bankPaperCanonicalSmoothQ0Family mFrozen qTilde) := by
  have hround :=
    bankPaperCanonicalSmoothQ0Family_sub_qTilde_isLittleO
      mFrozen qTilde
  have hd : (fun n => qTilde n -
      bankPaperCanonicalSmoothQ0Family mFrozen qTilde n) =o[atTop]
        secondOrderScale :=
    hround.neg_left.congr_left (fun n => by ring)
  rcases bankPaperCanonicalActiveMassPaperScaleLower_sub_of_isLittleO
      qTilde
      (fun n => qTilde n -
        bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)
      HqTilde hd with ⟨C, hC, hlower⟩
  use C, hC
  filter_upwards [hlower] with n hn
  convert hn using 1 ; ring

/-- A little-o raw-to-post-guard error also transfers the upper `O(N)`
bound. -/
theorem bankPaperCanonicalPostGuardSmoothMass_isBigO
    (rawBase qTilde : Nat -> Real)
    (Hraw : rawBase =O[atTop] secondOrderScale)
    (Hguard : (fun n => rawBase n - qTilde n) =o[atTop]
      secondOrderScale) :
    qTilde =O[atTop] secondOrderScale := by
  exact (Hraw.sub Hguard.isBigO).congr_left (fun n => by ring)

/-- The nearest-integer `q0` family inherits the upper `O(N)` bound. -/
theorem bankPaperCanonicalSmoothQ0Family_isBigO
    (mFrozen qTilde : Nat -> Real)
    (HqTilde : qTilde =O[atTop] secondOrderScale) :
    bankPaperCanonicalSmoothQ0Family mFrozen qTilde =O[atTop]
      secondOrderScale := by
  have hround :=
    bankPaperCanonicalSmoothQ0Family_sub_qTilde_isLittleO
      mFrozen qTilde
  exact (HqTilde.add hround.isBigO).congr_left (fun n => by ring)

/-! ## The logarithmically smaller height adjustment -/

/-- The paper's scale `n / log^2 n` tends to infinity. -/
theorem secondOrderScale_div_L_tendsto_atTop :
    Tendsto (fun n : Nat => secondOrderScale n / L n) atTop atTop := by
  have hzero : Tendsto
      (fun n : Nat => L n ^ 2 / (n : Real)) atTop (nhds 0) := by
    simpa only [L, Function.comp_apply, id_eq] using
      ((Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := Real))).tendsto_div_nhds_zero
  have hpos : ∀ᶠ n : Nat in atTop,
      0 < L n ^ 2 / (n : Real) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact div_pos (pow_pos (L_pos hn) 2) (by positivity)
  have hright : Tendsto
      (fun n : Nat => L n ^ 2 / (n : Real)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  apply hright.inv_tendsto_nhdsGT_zero.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  have hnReal : (n : Real) ≠ 0 := by positivity
  apply (eq_div_iff hL.ne').2
  change (L n ^ 2 / (n : Real))⁻¹ * L n = (n : Real) / L n
  rw [inv_div]
  field_simp [hL.ne', hnReal]

/-- The reciprocal of `L + mu` is `O(1/L)` for fixed positive `mu`. -/
theorem bankPaperCanonical_inv_L_add_mu_isBigO_inv_L
    {mu : Real} (hmu : 0 < mu) :
    (fun n : Nat => (L n + mu)⁻¹) =O[atTop]
      (fun n : Nat => (L n)⁻¹) := by
  apply (isBigO_iff).2
  use 1
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  have hdenom : 0 < L n + mu := add_pos hL hmu
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdenom),
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL), one_mul]
  exact (inv_le_inv₀ hdenom hL).2 (le_add_of_nonneg_right hmu.le)

/-- From `q0 = O(N)` and `A0 = O(N)`, the exact rounded height adjustment
constructed in the companion file satisfies `d = O(N/L)`. -/
theorem bankPaperCanonicalSmoothHeightAdjustment_isBigO
    {mu : Real} (hmu : 0 < mu) (q0 A0 : Nat -> Real)
    (Hq0 : q0 =O[atTop] secondOrderScale)
    (HA0 : A0 =O[atTop] secondOrderScale) :
    (fun n => (bankPaperCanonicalSmoothHeightAdjustment
      n mu (q0 n) (A0 n) : Real)) =O[atTop]
        (fun n => secondOrderScale n / L n) := by
  have hnum : (fun n => mu * q0 n - A0 n) =O[atTop]
      secondOrderScale :=
    (Hq0.const_mul_left mu).sub HA0
  have hinv := bankPaperCanonical_inv_L_add_mu_isBigO_inv_L hmu
  have hcenter : (fun n => bankPaperCanonicalSmoothHeightCenter
      n mu (q0 n) (A0 n)) =O[atTop]
        (fun n => secondOrderScale n / L n) := by
    apply (hnum.mul hinv).congr
    · intro n
      rw [bankPaperCanonicalSmoothHeightCenter, div_eq_mul_inv]
    · intro n
      rw [div_eq_mul_inv]
  have hroundOne :
      (fun n => (bankPaperCanonicalSmoothHeightAdjustment
          n mu (q0 n) (A0 n) : Real) -
        bankPaperCanonicalSmoothHeightCenter n mu (q0 n) (A0 n))
        =O[atTop] (fun _n : Nat => (1 : Real)) := by
    apply (isBigO_iff).2
    use 1 / 2
    filter_upwards [] with n
    simpa only [Real.norm_eq_abs, abs_one, mul_one] using
      bankPaperCanonicalSmoothHeightAdjustment_abs_sub_center_le
        n mu (q0 n) (A0 n)
  have hone : (fun _n : Nat => (1 : Real)) =O[atTop]
      (fun n => secondOrderScale n / L n) := by
    apply (isBigO_iff).2
    use 1
    have hlarge := secondOrderScale_div_L_tendsto_atTop.eventually
      (eventually_ge_atTop (1 : Real))
    filter_upwards [hlarge] with n hn
    have hnonneg : 0 <= secondOrderScale n / L n := zero_le_one.trans hn
    simpa only [norm_one, one_mul, Real.norm_eq_abs,
      abs_of_nonneg hnonneg] using hn
  have hround := hroundOne.trans hone
  exact (hcenter.add hround).congr_left (fun n => by ring)

/-! ## Full propagation from the minimal missing ledger -/

/-- Under the single missing Section 8 analytic ledger, the literal `q0`
family has a positive paper-scale lower bound. -/
theorem bankPaperCanonicalSectionEight_q0_paperScaleLower
    (W K : Nat) {c betaAct : Real} (hc : 0 < c)
    (hbeta : 0 < betaAct)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (bankPaperCanonicalSmoothQ0Family mFrozen qTilde) := by
  have hraw := bankPaperCanonicalRawSmoothBaseMass_paperScaleLower
    W K hc hbeta
  have hpost := bankPaperCanonicalPostGuardSmoothMass_paperScaleLower
    (fun n => bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct)
    qTilde hraw Hledger.1
  exact bankPaperCanonicalSmoothQ0Family_paperScaleLower
    mFrozen qTilde hpost

/-- The same ledger gives the paper's displayed `d = O(n/log^2 n)`. -/
theorem bankPaperCanonicalSectionEight_d_isBigO
    (W K : Nat) (c betaAct : Real) {mu : Real} (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    bankPaperCanonicalSmoothDRealFamily
        mu logY Lambda0 mFrozen qTilde =O[atTop]
      (fun n => secondOrderScale n / L n) := by
  have hrawBigO := bankPaperCanonicalRawSmoothBaseMass_isBigO
    W K c betaAct
  have hpostBigO := bankPaperCanonicalPostGuardSmoothMass_isBigO
    (fun n => bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct)
    qTilde hrawBigO Hledger.1
  have hq0BigO := bankPaperCanonicalSmoothQ0Family_isBigO
    mFrozen qTilde hpostBigO
  simpa only [bankPaperCanonicalSmoothDRealFamily,
      bankPaperCanonicalSmoothDIntFamily] using
    bankPaperCanonicalSmoothHeightAdjustment_isBigO hmu
      (bankPaperCanonicalSmoothQ0Family mFrozen qTilde)
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)
      hq0BigO Hledger.2

/-- Consequently the constructed final active mass `qAct(d) = q0 - d`
retains a positive `n / log n` lower bound. -/
theorem bankPaperCanonicalSectionEight_finalActiveMass_paperScaleLower
    (W K : Nat) {c betaAct mu : Real} (hc : 0 < c)
    (hbeta : 0 < betaAct) (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (bankPaperCanonicalSmoothFinalActiveMassFamily
        mu logY Lambda0 mFrozen qTilde) := by
  have hq0 := bankPaperCanonicalSectionEight_q0_paperScaleLower
    W K hc hbeta logY Lambda0 mFrozen qTilde Hledger
  have hd := bankPaperCanonicalSectionEight_d_isBigO
    W K c betaAct hmu logY Lambda0 mFrozen qTilde Hledger
  exact bankPaperCanonicalActiveMassPaperScaleLower_sub_of_logScale_isBigO
    (bankPaperCanonicalSmoothQ0Family mFrozen qTilde)
    (bankPaperCanonicalSmoothDRealFamily
      mu logY Lambda0 mFrozen qTilde) hq0 hd

/-- The paper's physical-interiority error:
`A(d) / qAct(d) - mu = O(L / N)`, where
`N = secondOrderScale = n / L`. -/
theorem bankPaperCanonicalSectionEight_physicalMeanError_isBigO
    (W K : Nat) {c betaAct mu : Real} (hc : 0 < c)
    (hbeta : 0 < betaAct) (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    bankPaperCanonicalSmoothPhysicalMeanErrorFamily
        mu logY Lambda0 mFrozen qTilde =O[atTop]
      (fun n => L n / secondOrderScale n) := by
  rcases bankPaperCanonicalSectionEight_finalActiveMass_paperScaleLower
      W K hc hbeta hmu logY Lambda0 mFrozen qTilde Hledger with
    ⟨C, hC, hlower⟩
  apply (isBigO_iff).2
  use 1 / C
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmuEvent : ∀ᶠ n : Nat in atTop, mu <= L n :=
    hLTop.eventually (eventually_ge_atTop mu)
  filter_upwards [hlower, eventually_secondOrderScale_pos,
    eventually_gt_atTop 1, hmuEvent] with n hmassLower hscale hn hmuL
  have hL : 0 < L n := L_pos hn
  have hmassPos : 0 <
      bankPaperCanonicalSmoothFinalActiveMassFamily
        mu logY Lambda0 mFrozen qTilde n :=
    (mul_pos hC hscale).trans_le hmassLower
  have hdenom : L n + mu ≠ 0 := (add_pos hL hmu).ne'
  have hpoint := bankPaperCanonicalSmoothPhysicalMeanErrorFamily_bound
    logY Lambda0 mFrozen qTilde n hdenom hmassPos
  have hnum : (1 / 2 : Real) * |L n + mu| <= L n := by
    rw [abs_of_pos (add_pos hL hmu)]
    linarith
  have hfirst :
      ((1 / 2 : Real) * |L n + mu|) /
          bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde n <=
        L n /
          bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde n :=
    div_le_div_of_nonneg_right hnum hmassPos.le
  have hscaleLowerPos : 0 < C * secondOrderScale n :=
    mul_pos hC hscale
  have hsecond :
      L n /
          bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde n <=
        L n / (C * secondOrderScale n) :=
    div_le_div_of_nonneg_left hL.le hscaleLowerPos hmassLower
  calc
    ‖bankPaperCanonicalSmoothPhysicalMeanErrorFamily
        mu logY Lambda0 mFrozen qTilde n‖ =
        |bankPaperCanonicalSmoothPhysicalMeanErrorFamily
          mu logY Lambda0 mFrozen qTilde n| := Real.norm_eq_abs _
    _ <= ((1 / 2 : Real) * |L n + mu|) /
          bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde n := hpoint
    _ <= L n /
          bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde n := hfirst
    _ <= L n / (C * secondOrderScale n) := hsecond
    _ = (1 / C) * (L n / secondOrderScale n) := by
      field_simp [hC.ne', hscale.ne']
    _ = (1 / C) * ‖L n / secondOrderScale n‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (div_pos hL hscale)]

/-- The exact active-measure constructor threshold follows eventually. -/
theorem eventually_one_le_bankPaperCanonicalSectionEight_finalActiveMass
    (W K : Nat) {c betaAct mu : Real} (hc : 0 < c)
    (hbeta : 0 < betaAct) (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    ∀ᶠ n : Nat in atTop,
      1 <= bankPaperCanonicalSmoothFinalActiveMassFamily
        mu logY Lambda0 mFrozen qTilde n :=
  eventually_one_le_bankPaperCanonicalActiveMass_of_paperScaleLower
    (bankPaperCanonicalSmoothFinalActiveMassFamily
      mu logY Lambda0 mFrozen qTilde)
    (bankPaperCanonicalSectionEight_finalActiveMass_paperScaleLower
      W K hc hbeta hmu logY Lambda0 mFrozen qTilde Hledger)

/-- Connector to the mass field currently stored in `HeadSimplexReserve`. -/
theorem bankPaperCanonicalSectionEight_headActiveMass_paperScaleLower
    {Phead : Finset Nat} (Rhead : Nat -> HeadSimplexReserve Phead)
    (W K : Nat) {c betaAct mu : Real} (hc : 0 < c)
    (hbeta : 0 < betaAct) (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (hactive : ∀ n,
      (Rhead n).activeMass =
        bankPaperCanonicalSmoothFinalActiveMassFamily
          mu logY Lambda0 mFrozen qTilde n)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    BankPaperCanonicalHeadActiveMassPaperScaleLower Rhead := by
  rcases bankPaperCanonicalSectionEight_finalActiveMass_paperScaleLower
      W K hc hbeta hmu logY Lambda0 mFrozen qTilde Hledger with
    ⟨C, hC, hlower⟩
  exact ⟨C, hC, hlower.mono fun n hn => hn.trans_eq (hactive n).symm⟩

/-- Head-reserve form of the eventual constructor threshold. -/
theorem eventually_one_le_bankPaperCanonicalSectionEight_headActiveMass
    {Phead : Finset Nat} (Rhead : Nat -> HeadSimplexReserve Phead)
    (W K : Nat) {c betaAct mu : Real} (hc : 0 < c)
    (hbeta : 0 < betaAct) (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (hactive : ∀ n,
      (Rhead n).activeMass =
        bankPaperCanonicalSmoothFinalActiveMassFamily
          mu logY Lambda0 mFrozen qTilde n)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    ∀ᶠ n : Nat in atTop, 1 <= (Rhead n).activeMass :=
  eventually_one_le_bankPaperCanonicalHeadActiveMass Rhead
    (bankPaperCanonicalSectionEight_headActiveMass_paperScaleLower
      Rhead W K hc hbeta hmu logY Lambda0 mFrozen qTilde
      hactive Hledger)

end

end Erdos390.WholePaper
