import Erdos390.Full.Scale
import Erdos390.WholePaper.BankBottomConcreteDemand
import Erdos390.WholePaper.BankOrdinaryCorePaths
import Erdos390.WholePaper.BankOrdinaryDonorSupply

/-!
# Concrete ordinary-component requests and their demand

For every signed rounding slot, this file materializes one request for every
nonterminal source of its actual core path.  A request is routed by its exact
geometric-grid index and by the sign of the slot.  The request fibers are
finite sigma types, not cardinality placeholders.

The path congestion bounds give `17 * sum beta` at each small scale and the
sharp `2 * sum beta` at every large scale.  Finally the already audited
`O(yNat)` beta reserve is compared with the worst ordinary marker scale
`(n/log n)/yNat`; this is the uniform little-o estimate required by all moving
grid scales `Q <= yNat`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-- One ordinary pool is a geometric-grid index and a path orientation. -/
abbrev BankOrdinaryOrientationPool := ℕ × BankBottomOrientation

/-- One literal request: a signed beta copy and one actual nonterminal source
on the deterministic path belonging to its prime. -/
abbrev BankOrdinaryPaperRequest (n : ℕ) :=
  Σ slot : SignedBankSlot (bankRoundingBetaOnSupport n),
    ↑(bankOrdinaryCoreSources slot.1.1)

/-- The complete finite ordinary request family. -/
def bankOrdinaryPaperRequests (n : ℕ) :
    Finset (BankOrdinaryPaperRequest n) :=
  Finset.univ

def bankOrdinaryPaperRequestSource
    {n : ℕ} (request : BankOrdinaryPaperRequest n) : ℕ :=
  request.2.1

def bankOrdinaryPaperRequestTarget
    {n : ℕ} (request : BankOrdinaryPaperRequest n) : ℕ :=
  bankOrdinaryCoreStep (bankOrdinaryPaperRequestSource request)

/-- Literal routing by the component's grid scale and the signed-copy
orientation. -/
def bankOrdinaryPaperRequestPool
    (n : ℕ) (request : BankOrdinaryPaperRequest n) :
    BankOrdinaryOrientationPool :=
  (bankOrdinaryComponentScaleIndex
      (bankOrdinaryPaperRequestSource request),
    bankSignedSlotOrientation request.1)

def bankOrdinaryRequestsInPool
    (n : ℕ) (pool : BankOrdinaryOrientationPool) :
    Finset (BankOrdinaryPaperRequest n) :=
  (bankOrdinaryPaperRequests n).filter fun request ↦
    bankOrdinaryPaperRequestPool n request = pool

def bankOrdinaryPoolDemand
    (n : ℕ) (pool : BankOrdinaryOrientationPool) : ℕ :=
  (bankOrdinaryRequestsInPool n pool).card

/-- Every materialized request is an actual certified component of its
prime's terminating path. -/
theorem bankOrdinaryPaperRequest_component_spec
    {n : ℕ} (request : BankOrdinaryPaperRequest n) :
    IsBankOrdinaryCoreComponent
      (bankOrdinaryPaperRequestSource request)
      (bankOrdinaryPaperRequestTarget request) := by
  let p : ↑(bankRoundingPrimeSupport n) := request.1.1
  have hp := bankRoundingPrimeSupport_prime p.property
  have hp6 : 6 ≤ p.1 := by
    by_contra h
    have hp5 : p.1 ≤ 5 := by omega
    let source : ℕ := request.2.1
    have hsource : source ∈ bankOrdinaryCoreSources p.1 :=
      request.2.property
    rw [bankOrdinaryCoreSources_of_le_five hp5] at hsource
    simp at hsource
  have hpPower : ¬ IsPowerOfTwo p.1 :=
    prime_not_isPowerOfTwo_of_five_le hp (by omega)
  exact bankOrdinaryCoreSource_spec (show 5 ≤ p.1 by omega) hpPower
    request.2.property

theorem bankOrdinaryPaperRequest_scale_le_yNat
    {n : ℕ} (request : BankOrdinaryPaperRequest n) :
    bankOrdinaryScale (bankOrdinaryPaperRequestPool n request).1 ≤
      (yNat n : ℚ) := by
  have hspec := bankOrdinaryPaperRequest_component_spec request
  have hsourcePrime : request.1.1.1 ≤ yNat n :=
    bankRoundingPrimeSupport_le_yNat request.1.1.property
  have hsourceLe := bankOrdinaryCoreSource_le_start request.2.property
  have hscaleLt :
      bankOrdinaryScale (bankOrdinaryPaperRequestPool n request).1 <
        (bankOrdinaryPaperRequestSource request : ℚ) :=
    hspec.2.2.2.2.2.2.1.1
  have hsourceY : bankOrdinaryPaperRequestSource request ≤ yNat n :=
    hsourceLe.trans hsourcePrime
  exact hscaleLt.le.trans (by exact_mod_cast hsourceY)

/-! ## Exact request-fiber cardinality -/

private def bankOrdinaryPaperRequestFiberEquiv
    (n : ℕ) (pool : BankOrdinaryOrientationPool) :
    ↑(bankOrdinaryRequestsInPool n pool) ≃
      Σ p : ↑(bankRoundingPrimeSupport n),
        Fin (bankRoundingBetaOnSupport n p) ×
          ↑(bankOrdinaryCoreSourcesAtScale p.1 pool.1) where
  toFun request :=
    ⟨request.1.1.1,
      (match request.1.1.2 with
        | .inl copy => copy
        | .inr copy => copy),
      ⟨request.1.2.1, by
        apply Finset.mem_filter.mpr
        refine ⟨request.1.2.property, ?_⟩
        have hpool := (Finset.mem_filter.mp request.property).2
        exact congrArg Prod.fst hpool⟩⟩
  invFun indexed :=
    ⟨⟨⟨indexed.1,
        match pool.2 with
        | .downward => Sum.inl indexed.2.1
        | .upward => Sum.inr indexed.2.1⟩,
      ⟨indexed.2.2.1, (Finset.mem_filter.mp indexed.2.2.property).1⟩⟩,
      by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rcases pool with ⟨j, orientation⟩
        cases orientation <;>
          simpa [bankOrdinaryPaperRequestPool,
            bankOrdinaryPaperRequestSource, bankSignedSlotOrientation] using
              (Finset.mem_filter.mp indexed.2.2.property).2⟩
  left_inv request := by
    rcases pool with ⟨j, orientation⟩
    rcases request with ⟨⟨⟨prime, signedCopy⟩, source⟩, hrequest⟩
    have hpool := (Finset.mem_filter.mp hrequest).2
    cases signedCopy with
    | inl copy =>
        have horientation : orientation = .downward := by
          exact (congrArg Prod.snd hpool).symm
        subst orientation
        rfl
    | inr copy =>
        have horientation : orientation = .upward := by
          exact (congrArg Prod.snd hpool).symm
        subst orientation
        rfl
  right_inv indexed := by
    rcases pool with ⟨j, orientation⟩
    rcases indexed with ⟨prime, copy, source⟩
    cases orientation <;> rfl

/-- Exact demand in one scale/orientation fiber.  Fixing the orientation
leaves exactly `beta_p` signed copies for every prime. -/
theorem bankOrdinaryPoolDemand_eq
    (n : ℕ) (pool : BankOrdinaryOrientationPool) :
    bankOrdinaryPoolDemand n pool =
      ∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p *
          (bankOrdinaryCoreSourcesAtScale p pool.1).card := by
  rw [bankOrdinaryPoolDemand, ← Fintype.card_coe]
  rw [Fintype.card_congr (bankOrdinaryPaperRequestFiberEquiv n pool),
    Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin,
    Fintype.card_coe, bankRoundingBetaOnSupport]
  simpa only using
    (Finset.sum_attach (bankRoundingPrimeSupport n) (fun p ↦
      bankRoundingBeta n p *
        (bankOrdinaryCoreSourcesAtScale p pool.1).card))

private theorem bankOrdinaryCoreSourcesAtScale_card_le_seventeen_of_prime
    {p j : ℕ} (hp : p.Prime) (hj : j ≤ 5) :
    (bankOrdinaryCoreSourcesAtScale p j).card ≤ 17 := by
  by_cases hp5 : p ≤ 5
  · simp [bankOrdinaryCoreSourcesAtScale,
      bankOrdinaryCoreSources_of_le_five hp5]
  · exact bankOrdinaryCoreSourcesAtSmallScale_card_le
      (by omega) (prime_not_isPowerOfTwo_of_five_le hp (by omega)) hj

private theorem bankOrdinaryCoreSourcesAtScale_card_le_two_of_prime
    {p j : ℕ} (hp : p.Prime) (hj : 6 ≤ j) :
    (bankOrdinaryCoreSourcesAtScale p j).card ≤ 2 := by
  by_cases hp5 : p ≤ 5
  · simp [bankOrdinaryCoreSourcesAtScale,
      bankOrdinaryCoreSources_of_le_five hp5]
  · exact bankOrdinaryCoreSourcesAtLargeScale_card_le_two
      (by omega) (prime_not_isPowerOfTwo_of_five_le hp (by omega)) hj

/-- Literal small-table demand bound for either orientation. -/
theorem bankOrdinaryPoolDemand_le_seventeen_beta
    (n : ℕ) (pool : BankOrdinaryOrientationPool) (hpool : pool.1 ≤ 5) :
    bankOrdinaryPoolDemand n pool ≤ 17 * bankBottomPaperDemand n := by
  rw [bankOrdinaryPoolDemand_eq, bankBottomPaperDemand]
  calc
    (∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p *
          (bankOrdinaryCoreSourcesAtScale p pool.1).card) ≤
      ∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p * 17 := by
          apply Finset.sum_le_sum
          intro p hp
          exact Nat.mul_le_mul_left _
            (bankOrdinaryCoreSourcesAtScale_card_le_seventeen_of_prime
              (bankRoundingPrimeSupport_prime hp) hpool)
    _ = (∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p) * 17 := by
          rw [Finset.sum_mul]
    _ = 17 * ∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p := by omega

/-- Sharp large-grid demand bound for either orientation. -/
theorem bankOrdinaryPoolDemand_le_two_beta
    (n : ℕ) (pool : BankOrdinaryOrientationPool) (hpool : 6 ≤ pool.1) :
    bankOrdinaryPoolDemand n pool ≤ 2 * bankBottomPaperDemand n := by
  rw [bankOrdinaryPoolDemand_eq, bankBottomPaperDemand]
  calc
    (∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p *
          (bankOrdinaryCoreSourcesAtScale p pool.1).card) ≤
      ∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p * 2 := by
          apply Finset.sum_le_sum
          intro p hp
          exact Nat.mul_le_mul_left _
            (bankOrdinaryCoreSourcesAtScale_card_le_two_of_prime
              (bankRoundingPrimeSupport_prime hp) hpool)
    _ = (∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p) * 2 := by
          rw [Finset.sum_mul]
    _ = 2 * ∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p := by omega

theorem bankOrdinaryPoolDemand_scale_zero (n : ℕ)
    (orientation : BankBottomOrientation) :
    bankOrdinaryPoolDemand n (0, orientation) = 0 := by
  rw [bankOrdinaryPoolDemand_eq]
  apply Finset.sum_eq_zero
  intro p hp
  apply Nat.mul_eq_zero.mpr
  right
  apply Finset.card_eq_zero.mpr
  rw [bankOrdinaryCoreSourcesAtScale]
  apply Finset.filter_eq_empty_iff.mpr
  intro source hsource hsourceScale
  have hpPrime := bankRoundingPrimeSupport_prime hp
  have hp5 : 5 ≤ p := by
    by_contra hpSmall
    have hpLe : p ≤ 5 := by omega
    rw [bankOrdinaryCoreSources_of_le_five hpLe] at hsource
    simp at hsource
  have hpPower := prime_not_isPowerOfTwo_of_five_le hpPrime hp5
  have hspec := bankOrdinaryCoreSource_spec hp5 hpPower hsource
  have hpositive := one_le_bankOrdinaryComponentScaleIndex hspec.1
  omega

theorem bankOrdinaryPoolDemand_zero_of_scale_gt_yNat
    {n : ℕ} {pool : BankOrdinaryOrientationPool}
    (hscale : (yNat n : ℚ) < bankOrdinaryScale pool.1) :
    bankOrdinaryPoolDemand n pool = 0 := by
  rw [bankOrdinaryPoolDemand_eq]
  apply Finset.sum_eq_zero
  intro p hp
  apply Nat.mul_eq_zero.mpr
  right
  apply Finset.card_eq_zero.mpr
  rw [bankOrdinaryCoreSourcesAtScale]
  apply Finset.filter_eq_empty_iff.mpr
  intro source hsource hsourceScale
  have hsourcePrime := bankRoundingPrimeSupport_prime hp
  have hp5 : 5 ≤ p := by
    by_contra hpSmall
    have hpLe : p ≤ 5 := by omega
    exact (by
      rw [bankOrdinaryCoreSources_of_le_five hpLe] at hsource
      simp at hsource)
  have hpPower := prime_not_isPowerOfTwo_of_five_le hsourcePrime hp5
  have hspec := bankOrdinaryCoreSource_spec hp5 hpPower hsource
  have hsourceLe := bankOrdinaryCoreSource_le_start hsource
  have hpY := bankRoundingPrimeSupport_le_yNat hp
  have hscaleLt : bankOrdinaryScale pool.1 < (source : ℚ) := by
    rw [← hsourceScale]
    exact hspec.2.2.2.2.2.2.1.1
  have hsourceY : source ≤ yNat n := hsourceLe.trans hpY
  exact (not_lt_of_ge (by exact_mod_cast hsourceY))
    (hscale.trans hscaleLt)

/-! ## The beta reserve against the worst moving ordinary scale -/

/-- The smallest marker scale among `Q <= yNat`, with a harmless positive
denominator at small `n`. -/
def bankOrdinaryWorstMarkerScale (n : ℕ) : ℝ :=
  secondOrderScale n / max 1 (yNat n : ℝ)

theorem yNat_div_bankOrdinaryWorstMarkerScale_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ (yNat n : ℝ) / bankOrdinaryWorstMarkerScale n)
      atTop (nhds 0) := by
  have hsqueeze : Tendsto
      (fun n : ℕ ↦ (yNat n : ℝ) /
        bankOrdinaryWorstMarkerScale n) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds Erdos390.Full.Scale.tendsto_endpointRatio_zero
    · filter_upwards [eventually_gt_atTop 2] with n hn
      have hscale : 0 < bankOrdinaryWorstMarkerScale n := by
        rw [bankOrdinaryWorstMarkerScale]
        exact div_pos (secondOrderScale_pos (by omega)) (by positivity)
      exact div_nonneg (Nat.cast_nonneg _) hscale.le
    · filter_upwards [eventually_ge_atTop 3,
          Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat]
          with n hn hlogY
      have hnPos : (0 : ℝ) < n := by positivity
      have hL : 1 ≤ L n := by
        rw [L]
        exact (show (1 : ℝ) ≤ Real.log (n : ℝ) by
          have hthree : (3 : ℝ) ≤ n := by exact_mod_cast hn
          have : Real.exp 1 ≤ (n : ℝ) :=
            Real.exp_one_lt_three.le.trans hthree
          exact (Real.le_log_iff_exp_le hnPos).2 this)
      have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (by positivity) _
      have hyFloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
      have hyNatOne : (1 : ℝ) ≤ yNat n := by
        have hlogPos : 0 < Real.log (yNat n : ℝ) := by
          have hLPos : 0 < L n := lt_of_lt_of_le (by norm_num) hL
          nlinarith
        exact ((Real.log_pos_iff (Nat.cast_nonneg _)).mp hlogPos).le
      have hmax : max 1 (yNat n : ℝ) = yNat n := max_eq_right hyNatOne
      rw [bankOrdinaryWorstMarkerScale, secondOrderScale, hmax]
      have hyNatPos : (0 : ℝ) < yNat n := lt_of_lt_of_le (by norm_num) hyNatOne
      have hLPos : 0 < L n := lt_of_lt_of_le (by norm_num) hL
      rw [show Real.log (n : ℝ) = L n by rfl]
      have hidentity :
          (yNat n : ℝ) / (((n : ℝ) / L n) / (yNat n : ℝ)) =
            (yNat n : ℝ) ^ 2 * L n / (n : ℝ) := by
        field_simp
      rw [hidentity, endpointRatio]
      apply div_le_div_of_nonneg_right _ hnPos.le
      calc
        (yNat n : ℝ) ^ 2 * L n ≤ y n ^ 2 * L n := by
          gcongr
        _ ≤ y n ^ 2 * L n ^ 2 := by
          have hySq : 0 ≤ y n ^ 2 := sq_nonneg _
          have hLsq : L n ≤ L n ^ 2 := by
            nlinarith [sq_nonneg (L n)]
          exact mul_le_mul_of_nonneg_left hLsq hySq
  exact hsqueeze

private theorem yNat_isLittleO_bankOrdinaryWorstMarkerScale :
    (fun n : ℕ ↦ (yNat n : ℝ)) =o[atTop]
      bankOrdinaryWorstMarkerScale := by
  apply (isLittleO_iff_tendsto' ?_).mpr
    yNat_div_bankOrdinaryWorstMarkerScale_tendsto_zero
  filter_upwards [eventually_gt_atTop 2] with n hn hzero
  have hscale : 0 < bankOrdinaryWorstMarkerScale n := by
    rw [bankOrdinaryWorstMarkerScale]
    exact div_pos (secondOrderScale_pos (by omega)) (by positivity)
  exact (hscale.ne' hzero).elim

/-- The beta reserve itself, in the little-o form used for ordinary pools. -/
theorem bankBottomPaperDemand_isLittleO_bankOrdinaryWorstMarkerScale :
    (fun n : ℕ ↦ (bankBottomPaperDemand n : ℝ)) =o[atTop]
      bankOrdinaryWorstMarkerScale :=
  bankBottomPaperDemand_isBigO_yNat.trans_isLittleO
    yNat_isLittleO_bankOrdinaryWorstMarkerScale

/-- Uniform analytic terminal for ordinary demand: the common beta reserve is
little-o of the worst marker lower bound among all moving grid scales. -/
theorem bankBottomPaperDemand_div_bankOrdinaryWorstMarkerScale_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (bankBottomPaperDemand n : ℝ) /
          bankOrdinaryWorstMarkerScale n)
      atTop (nhds 0) :=
  bankBottomPaperDemand_isLittleO_bankOrdinaryWorstMarkerScale.tendsto_div_nhds_zero

/-- Each moving large-scale orientation demand is little-o of the worst
ordinary marker scale. -/
theorem bankOrdinary_largeOrientationDemand_isLittleO
    (pool : ℕ → BankOrdinaryOrientationPool)
    (hlarge : ∀ᶠ n : ℕ in atTop, 6 ≤ (pool n).1) :
    (fun n : ℕ ↦ (bankOrdinaryPoolDemand n (pool n) : ℝ))
      =o[atTop] bankOrdinaryWorstMarkerScale := by
  have hdemandO :
      (fun n : ℕ ↦ (bankOrdinaryPoolDemand n (pool n) : ℝ))
        =O[atTop] (fun n : ℕ ↦ (bankBottomPaperDemand n : ℝ)) := by
    apply IsBigO.of_bound 2
    filter_upwards [hlarge] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ bankOrdinaryPoolDemand n (pool n)),
      Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ bankBottomPaperDemand n)]
    exact_mod_cast bankOrdinaryPoolDemand_le_two_beta n (pool n) hn
  exact hdemandO.trans_isLittleO
    bankBottomPaperDemand_isLittleO_bankOrdinaryWorstMarkerScale

private theorem bankBottomPaperDemand_isLittleO_bankBottomPrimeScale :
    (fun n : ℕ ↦ (bankBottomPaperDemand n : ℝ)) =o[atTop]
      bankBottomPrimeScale := by
  apply (isLittleO_iff_tendsto' ?_).mpr
    bankBottomPaperDemand_div_bankBottomPrimeScale_tendsto_zero
  filter_upwards [eventually_gt_atTop 2,
      eventually_secondOrderScale_pos] with n hn hsecond hzero
  have hscale : 0 < bankBottomPrimeScale n := by
    rw [bankBottomPrimeScale, SafePrimeCounting.shortIntervalPrimeScale]
    exact div_pos hsecond
      (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  exact (hscale.ne' hzero).elim

/-- Each fixed small-scale orientation demand is little-o of its
`n/(log n)^2` marker lower-bound scale. -/
theorem bankOrdinary_smallOrientationDemand_isLittleO
    (scale : SmallDescentScale) (orientation : BankBottomOrientation) :
    (fun n : ℕ ↦
      (bankOrdinaryPoolDemand n
        (smallDescentScaleIndex scale, orientation) : ℝ))
      =o[atTop] bankBottomPrimeScale := by
  have hdemandO :
      (fun n : ℕ ↦
        (bankOrdinaryPoolDemand n
          (smallDescentScaleIndex scale, orientation) : ℝ))
        =O[atTop] (fun n : ℕ ↦ (bankBottomPaperDemand n : ℝ)) := by
    apply IsBigO.of_bound 17
    filter_upwards [] with n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ bankOrdinaryPoolDemand n
          (smallDescentScaleIndex scale, orientation)),
      Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ bankBottomPaperDemand n)]
    exact_mod_cast bankOrdinaryPoolDemand_le_seventeen_beta n
      (smallDescentScaleIndex scale, orientation)
      (smallDescentScaleIndex_le_five scale)
  exact hdemandO.trans_isLittleO
    bankBottomPaperDemand_isLittleO_bankBottomPrimeScale

/-- Uniform comparison of the denominator in the analytic marker lower bound
with `yNat`.  The factor five comes directly from the audited lower bound on
`log(yNat)`. -/
theorem eventually_bankOrdinary_max_scale_log_le_five_yNat :
    ∀ᶠ n : ℕ in atTop, ∀ Q : ℚ,
      Q ≤ (yNat n : ℚ) →
        max (Q : ℝ) (Real.log (n : ℝ)) ≤
          5 * max 1 (yNat n : ℝ) := by
  filter_upwards [eventually_gt_atTop 2,
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat]
      with n hn hlogY
  intro Q hQ
  have hyPos : 0 < (yNat n : ℝ) := by
    have hLPos : 0 < L n := L_pos (by omega)
    have : 0 < Real.log (yNat n : ℝ) := by nlinarith
    exact (show (0 : ℝ) < 1 by norm_num).trans
      ((Real.log_pos_iff (Nat.cast_nonneg _)).mp this)
  have hlogLe : Real.log (yNat n : ℝ) ≤ yNat n := by
    have h := Real.log_le_sub_one_of_pos hyPos
    linarith
  have hLLe : Real.log (n : ℝ) ≤ 5 * (yNat n : ℝ) := by
    rw [← show L n = Real.log (n : ℝ) by rfl]
    nlinarith
  have hQR : (Q : ℝ) ≤ yNat n := by exact_mod_cast hQ
  apply max_le
  · exact hQR.trans (by
      have : (0 : ℝ) ≤ yNat n := hyPos.le
      exact le_trans (le_mul_of_one_le_left this (by norm_num))
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)))
  · exact hLLe.trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))

end

end Erdos390.WholePaper
