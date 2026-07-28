import Erdos390.WholePaper.BankOrdinaryConcreteDemand
import Mathlib.Data.Fintype.EquivFin

/-!
# Actual matching of ordinary requests to marker--donor pairs

At every grid scale the selected marker--donor pairs are split by
`BankMarkerDonorCombinatorics` into the two path orientations.  The marker
intervals of distinct geometric scales are disjoint, so these are genuinely
disjoint pools of numerical pairs, not merely scale-tagged copies.

The beta-demand estimates are compared with the large moving marker lower
bound and the five fixed small-scale marker lower bounds.  Pointwise finite
embeddings then give one globally injective assignment from every actual
ordinary component request to an actual eligible marker--donor pair.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Actual oriented occurrence pools -/

/-- One half of the actual chosen marker--donor pairs at the prescribed grid
scale. -/
def bankOrdinaryAvailablePairs
    (n M : ℕ) (pool : BankOrdinaryOrientationPool) : Finset (ℕ × ℕ) :=
  match pool.2 with
  | .downward =>
      bankOrientationPoolFirst
        (bankOrdinaryEligibleRelation n M (bankOrdinaryScale pool.1))
  | .upward =>
      bankOrientationPoolSecond
        (bankOrdinaryEligibleRelation n M (bankOrdinaryScale pool.1))

def bankOrdinaryPoolCapacity
    (n M : ℕ) (pool : BankOrdinaryOrientationPool) : ℕ :=
  (bankOrdinaryAvailablePairs n M pool).card

theorem bankOrdinaryAvailablePairs_subset_eligible
    (n M : ℕ) (pool : BankOrdinaryOrientationPool) :
    bankOrdinaryAvailablePairs n M pool ⊆
      bankOrdinaryEligibleRelation n M (bankOrdinaryScale pool.1) := by
  cases pool with
  | mk j orientation =>
      cases orientation
      · exact bankOrientationPoolFirst_subset_eligible _
      · exact bankOrientationPoolSecond_subset_eligible _

theorem bankOrdinaryPoolCapacity_ge_half_markerCount
    (n M : ℕ) (pool : BankOrdinaryOrientationPool) :
    bankEligibleMarkerCount
        (bankOrdinaryEligibleRelation n M (bankOrdinaryScale pool.1)) / 2 ≤
      bankOrdinaryPoolCapacity n M pool := by
  cases pool with
  | mk j orientation =>
      cases orientation
      · rw [bankOrdinaryPoolCapacity, bankOrdinaryAvailablePairs,
          card_bankOrientationPoolFirst, card_bankMarkerDonorPairs]
      · have hbalanced := (bankOrientationPools_card_balanced
            (bankOrdinaryEligibleRelation n M (bankOrdinaryScale j))).1
        rw [card_bankOrientationPoolFirst, card_bankMarkerDonorPairs]
          at hbalanced
        simpa only [bankOrdinaryPoolCapacity,
          bankOrdinaryAvailablePairs] using hbalanced

private theorem bankOrdinary_markerIntervals_disjoint_ordered
    {n P j k : ℕ} (hjk : j < k)
    (hj : InOrdinaryBankMarkerInterval n (bankOrdinaryScale j) P)
    (hk : InOrdinaryBankMarkerInterval n (bankOrdinaryScale k) P) :
    False := by
  have hsucc : j + 1 ≤ k := by omega
  have hscale := bankOrdinaryScale_mono hsucc
  rw [bankOrdinaryScale_succ] at hscale
  have hP : (0 : ℚ) ≤ P := by positivity
  have hscaleP := mul_le_mul_of_nonneg_right hscale hP
  unfold InOrdinaryBankMarkerInterval at hj hk
  nlinarith

theorem bankOrdinary_markerIntervals_disjoint
    {n P j k : ℕ} (hjk : j ≠ k)
    (hj : InOrdinaryBankMarkerInterval n (bankOrdinaryScale j) P)
    (hk : InOrdinaryBankMarkerInterval n (bankOrdinaryScale k) P) :
    False := by
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · exact bankOrdinary_markerIntervals_disjoint_ordered hjk hj hk
  · exact bankOrdinary_markerIntervals_disjoint_ordered hkj hk hj

/-- Distinct scale/orientation labels give disjoint actual numerical pools. -/
theorem bankOrdinaryAvailablePairs_disjoint
    {n M : ℕ} {pool pool' : BankOrdinaryOrientationPool}
    (hpools : pool ≠ pool') :
    Disjoint (bankOrdinaryAvailablePairs n M pool)
      (bankOrdinaryAvailablePairs n M pool') := by
  rw [Finset.disjoint_left]
  intro pair hpair hpair'
  by_cases hscale : pool.1 = pool'.1
  · have horientation : pool.2 ≠ pool'.2 := by
      intro h
      exact hpools (Prod.ext hscale h)
    rcases pool with ⟨j, orientation⟩
    rcases pool' with ⟨j', orientation'⟩
    simp only at hscale
    subst j'
    cases orientation <;> cases orientation'
    · exact (horientation rfl).elim
    · exact (Finset.disjoint_left.mp
        (bankOrientationPools_disjoint
          (bankOrdinaryEligibleRelation n M (bankOrdinaryScale j))))
            hpair hpair'
    · exact (Finset.disjoint_left.mp
        (bankOrientationPools_disjoint
          (bankOrdinaryEligibleRelation n M (bankOrdinaryScale j))).symm)
            hpair hpair'
    · exact (horientation rfl).elim
  · have heligible := bankOrdinaryAvailablePairs_subset_eligible n M pool hpair
    have heligible' := bankOrdinaryAvailablePairs_subset_eligible n M pool' hpair'
    have hmarker := (mem_bankOrdinaryEligibleRelation.mp heligible).2.2.2.1
    have hmarker' := (mem_bankOrdinaryEligibleRelation.mp heligible').2.2.2.1
    exact bankOrdinary_markerIntervals_disjoint hscale hmarker hmarker'

/-! ## Capacity from the beta reserve -/

private theorem demand_le_half_of_two_mul_le
    {d K : ℕ} (h : 2 * d ≤ K) : d ≤ K / 2 := by
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
  simpa only [Nat.mul_comm] using h

private theorem eventually_bankOrdinary_smallPoolDemand_le_capacity
    {c : ℝ} (hc : 0 < c) (scale : SmallDescentScale)
    (orientation : BankBottomOrientation) :
    ∀ᶠ n : ℕ in atTop,
      bankOrdinaryPoolDemand n
          (smallDescentScaleIndex scale, orientation) ≤
        bankOrdinaryPoolCapacity n
          (upperEndpoint n (upperTailLength c n))
          (smallDescentScaleIndex scale, orientation) := by
  obtain ⟨rho, hrho, hmarkers⟩ :=
    bankOrdinary_smallScale_markerCount_lower hc scale
  have hratio :=
    bankBottomPaperDemand_div_bankBottomPrimeScale_tendsto_zero
  have hsmall := hratio.eventually
    (eventually_lt_nhds (div_pos hrho (by norm_num : (0 : ℝ) < 34)))
  filter_upwards [hmarkers, hsmall, eventually_gt_atTop 2,
      eventually_secondOrderScale_pos] with n hmarker hbeta hn hsecond
  let pool : BankOrdinaryOrientationPool :=
    (smallDescentScaleIndex scale, orientation)
  let eligible := bankOrdinaryEligibleRelation n
    (upperEndpoint n (upperTailLength c n))
    (bankOrdinaryScale (smallDescentScaleIndex scale))
  let K := bankEligibleMarkerCount eligible
  have hdemand := bankOrdinaryPoolDemand_le_seventeen_beta n pool
    (smallDescentScaleIndex_le_five scale)
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hprimeScale : 0 < bankBottomPrimeScale n := by
    rw [bankBottomPrimeScale, SafePrimeCounting.shortIntervalPrimeScale]
    exact div_pos hsecond hlog
  have hbetaMul :
      (34 : ℝ) * bankBottomPaperDemand n <
        rho * bankBottomPrimeScale n := by
    have := (div_lt_iff₀ hprimeScale).mp hbeta
    nlinarith
  have hmarker' : rho * bankBottomPrimeScale n ≤ (K : ℝ) := by
    dsimp only [K, eligible]
    rw [← smallDescentScaleValue_eq_bankOrdinaryScale]
    simpa only [bankBottomPrimeScale,
      SafePrimeCounting.shortIntervalPrimeScale, mul_div_assoc] using hmarker
  have htwoDemand : 2 * bankOrdinaryPoolDemand n pool ≤ K := by
    have hdemandR :
        ((2 * bankOrdinaryPoolDemand n pool : ℕ) : ℝ) < (K : ℝ) := by
      have hdemandCast : (bankOrdinaryPoolDemand n pool : ℝ) ≤
          17 * bankBottomPaperDemand n := by exact_mod_cast hdemand
      push_cast
      nlinarith [hbetaMul, hmarker']
    exact_mod_cast hdemandR.le
  exact (demand_le_half_of_two_mul_le htwoDemand).trans
    (bankOrdinaryPoolCapacity_ge_half_markerCount n
      (upperEndpoint n (upperTailLength c n)) pool)

private theorem eventually_bankOrdinary_allSmallPoolDemands_le_capacity
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ∀ scale : SmallDescentScale, ∀ orientation : BankBottomOrientation,
        bankOrdinaryPoolDemand n
            (smallDescentScaleIndex scale, orientation) ≤
          bankOrdinaryPoolCapacity n
            (upperEndpoint n (upperTailLength c n))
            (smallDescentScaleIndex scale, orientation) := by
  rw [Filter.eventually_all]
  intro scale
  rw [Filter.eventually_all]
  exact eventually_bankOrdinary_smallPoolDemand_le_capacity hc scale

private theorem eventually_bankOrdinary_largePoolDemands_le_capacity
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ, 6 ≤ j → ∀ orientation : BankBottomOrientation,
        bankOrdinaryPoolDemand n (j, orientation) ≤
          bankOrdinaryPoolCapacity n
            (upperEndpoint n (upperTailLength c n)) (j, orientation) := by
  obtain ⟨rho, hrho, hmarkers⟩ :=
    exists_eventually_bankOrdinary_markerCount_lower hc
  have hratio :=
    bankBottomPaperDemand_div_bankOrdinaryWorstMarkerScale_tendsto_zero
  have hsmall := hratio.eventually
    (eventually_lt_nhds (div_pos hrho (by norm_num : (0 : ℝ) < 20)))
  filter_upwards [hmarkers, hsmall,
      eventually_bankOrdinary_max_scale_log_le_five_yNat,
      eventually_gt_atTop 3, eventually_secondOrderScale_pos]
      with n hmarker hbeta hmax hn hsecond
  intro j hj orientation
  let pool : BankOrdinaryOrientationPool := (j, orientation)
  let Q : ℚ := bankOrdinaryScale j
  by_cases hQY : Q ≤ (yNat n : ℚ)
  · have hQ20 : (20 : ℚ) < Q :=
      twenty_lt_bankOrdinaryScale_of_six_le hj
    have hdemand := bankOrdinaryPoolDemand_le_two_beta n pool hj
    have hmarkerN := hmarker Q hQ20 hQY
    let eligible := bankOrdinaryEligibleRelation n
      (upperEndpoint n (upperTailLength c n)) Q
    let K := bankEligibleMarkerCount eligible
    have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hyMax : 0 < max 1 (yNat n : ℝ) := by positivity
    have hworst : 0 < bankOrdinaryWorstMarkerScale n := by
      rw [bankOrdinaryWorstMarkerScale]
      exact div_pos hsecond hyMax
    have hbetaMul :
        (20 : ℝ) * bankBottomPaperDemand n <
          rho * bankOrdinaryWorstMarkerScale n := by
      have := (div_lt_iff₀ hworst).mp hbeta
      nlinarith
    have hmaxN := hmax Q hQY
    have hdenomPos :
        0 < max (Q : ℝ) (Real.log (n : ℝ)) := by
      have hQposQ : (0 : ℚ) < Q := by linarith
      have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQposQ
      exact hQpos.trans_le (le_max_left _ _)
    have hworstCompare :
        rho / 5 * bankOrdinaryWorstMarkerScale n ≤
          rho * secondOrderScale n /
            max (Q : ℝ) (Real.log (n : ℝ)) := by
      rw [bankOrdinaryWorstMarkerScale]
      field_simp [hyMax.ne', hdenomPos.ne']
      nlinarith [hmaxN, mul_pos hrho hsecond]
    have htwoDemand : 2 * bankOrdinaryPoolDemand n pool ≤ K := by
      have htwoDemandR :
          ((2 * bankOrdinaryPoolDemand n pool : ℕ) : ℝ) < (K : ℝ) := by
        have hdemandR :
            (bankOrdinaryPoolDemand n pool : ℝ) ≤
              2 * bankBottomPaperDemand n := by exact_mod_cast hdemand
        have hbetaR :
            4 * (bankBottomPaperDemand n : ℝ) <
              rho / 5 * bankOrdinaryWorstMarkerScale n := by
          nlinarith
        have hmarkerR :
            rho * secondOrderScale n /
                max (Q : ℝ) (Real.log (n : ℝ)) ≤ (K : ℝ) := by
          simpa only [K, eligible, Q] using hmarkerN
        push_cast
        calc
          2 * (bankOrdinaryPoolDemand n pool : ℝ) ≤
              4 * (bankBottomPaperDemand n : ℝ) := by
            nlinarith
          _ < rho / 5 * bankOrdinaryWorstMarkerScale n := hbetaR
          _ ≤ rho * secondOrderScale n /
              max (Q : ℝ) (Real.log (n : ℝ)) := hworstCompare
          _ ≤ (K : ℝ) := hmarkerR
      exact_mod_cast htwoDemandR.le
    exact (demand_le_half_of_two_mul_le htwoDemand).trans
      (bankOrdinaryPoolCapacity_ge_half_markerCount n
        (upperEndpoint n (upperTailLength c n)) pool)
  · have hdemandZero : bankOrdinaryPoolDemand n pool = 0 :=
      bankOrdinaryPoolDemand_zero_of_scale_gt_yNat
        (lt_of_not_ge hQY)
    rw [hdemandZero]
    exact Nat.zero_le _

/-- All ordinary grid-scale capacity inequalities hold simultaneously. -/
theorem eventually_bankOrdinary_allPoolDemands_le_capacity
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ pool : BankOrdinaryOrientationPool,
      bankOrdinaryPoolDemand n pool ≤
        bankOrdinaryPoolCapacity n
          (upperEndpoint n (upperTailLength c n)) pool := by
  filter_upwards [eventually_bankOrdinary_allSmallPoolDemands_le_capacity hc,
      eventually_bankOrdinary_largePoolDemands_le_capacity hc]
      with n hsmall hlarge
  rintro ⟨j, orientation⟩
  by_cases hj0 : j = 0
  · subst j
    rw [bankOrdinaryPoolDemand_scale_zero]
    exact Nat.zero_le _
  · by_cases hj5 : j ≤ 5
    · interval_cases j
      · exact (hj0 rfl).elim
      · simpa [smallDescentScaleIndex] using hsmall .one orientation
      · simpa [smallDescentScaleIndex] using hsmall .two orientation
      · simpa [smallDescentScaleIndex] using hsmall .three orientation
      · simpa [smallDescentScaleIndex] using hsmall .four orientation
      · simpa [smallDescentScaleIndex] using hsmall .five orientation
    · exact hlarge j (by omega) orientation

/-! ## Finite poolwise matching -/

/-- A matching is an actual embedding of every request fiber into its actual
oriented marker--donor pool. -/
structure BankOrdinaryPoolMatching
    (n M : ℕ) where
  toEmbedding : (pool : BankOrdinaryOrientationPool) →
    ↑(bankOrdinaryRequestsInPool n pool) ↪
      ↑(bankOrdinaryAvailablePairs n M pool)

private theorem bankOrdinaryPoolMatching_nonempty
    (n M : ℕ)
    (hcapacity : ∀ pool : BankOrdinaryOrientationPool,
      bankOrdinaryPoolDemand n pool ≤ bankOrdinaryPoolCapacity n M pool) :
    Nonempty (BankOrdinaryPoolMatching n M) := by
  let embedding : (pool : BankOrdinaryOrientationPool) →
      ↑(bankOrdinaryRequestsInPool n pool) ↪
        ↑(bankOrdinaryAvailablePairs n M pool) := fun pool ↦
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_coe, bankOrdinaryPoolDemand,
        bankOrdinaryPoolCapacity] using hcapacity pool))
  exact ⟨⟨embedding⟩⟩

def bankOrdinaryRequestInItsPool
    {n : ℕ} (request : ↑(bankOrdinaryPaperRequests n)) :
    ↑(bankOrdinaryRequestsInPool n
      (bankOrdinaryPaperRequestPool n request.1)) :=
  ⟨request.1, Finset.mem_filter.mpr ⟨request.property, rfl⟩⟩

abbrev BankOrdinaryLabeledRequest (n : ℕ) :=
  Σ pool : BankOrdinaryOrientationPool,
    ↑(bankOrdinaryRequestsInPool n pool)

def bankOrdinaryLabelRequest
    {n : ℕ} (request : ↑(bankOrdinaryPaperRequests n)) :
    BankOrdinaryLabeledRequest n :=
  ⟨bankOrdinaryPaperRequestPool n request.1,
    bankOrdinaryRequestInItsPool request⟩

theorem bankOrdinaryLabelRequest_injective (n : ℕ) :
    Function.Injective (@bankOrdinaryLabelRequest n) := by
  intro request request' heq
  apply Subtype.ext
  exact congrArg (fun labeled ↦ labeled.2.1) heq

def BankOrdinaryPoolMatching.slotOfLabeledRequest
    {n M : ℕ} (matching : BankOrdinaryPoolMatching n M)
    (request : BankOrdinaryLabeledRequest n) : ℕ × ℕ :=
  (matching.toEmbedding request.1 request.2).1

theorem BankOrdinaryPoolMatching.slotOfLabeledRequest_mem
    {n M : ℕ} (matching : BankOrdinaryPoolMatching n M)
    (request : BankOrdinaryLabeledRequest n) :
    matching.slotOfLabeledRequest request ∈
      bankOrdinaryAvailablePairs n M request.1 :=
  (matching.toEmbedding request.1 request.2).property

theorem BankOrdinaryPoolMatching.slotOfLabeledRequest_injective
    {n M : ℕ} (matching : BankOrdinaryPoolMatching n M) :
    Function.Injective matching.slotOfLabeledRequest := by
  rintro ⟨pool, request⟩ ⟨pool', request'⟩ heq
  by_cases hp : pool = pool'
  · subst pool'
    have hembedding : matching.toEmbedding pool request =
        matching.toEmbedding pool request' := by
      apply Subtype.ext
      exact heq
    have hrequest := (matching.toEmbedding pool).injective hembedding
    subst request'
    rfl
  · have hleft : matching.slotOfLabeledRequest ⟨pool, request⟩ ∈
        bankOrdinaryAvailablePairs n M pool :=
      matching.slotOfLabeledRequest_mem ⟨pool, request⟩
    have hright : matching.slotOfLabeledRequest ⟨pool, request⟩ ∈
        bankOrdinaryAvailablePairs n M pool' := by
      rw [heq]
      exact matching.slotOfLabeledRequest_mem ⟨pool', request'⟩
    exact False.elim ((Finset.disjoint_left.mp
      (bankOrdinaryAvailablePairs_disjoint hp)) hleft hright)

def BankOrdinaryPoolMatching.matchedPair
    {n M : ℕ} (matching : BankOrdinaryPoolMatching n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ × ℕ :=
  matching.slotOfLabeledRequest (bankOrdinaryLabelRequest request)

theorem BankOrdinaryPoolMatching.matchedPair_mem_available
    {n M : ℕ} (matching : BankOrdinaryPoolMatching n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    matching.matchedPair request ∈
      bankOrdinaryAvailablePairs n M
        (bankOrdinaryPaperRequestPool n request.1) :=
  matching.slotOfLabeledRequest_mem (bankOrdinaryLabelRequest request)

theorem BankOrdinaryPoolMatching.matchedPair_injective
    {n M : ℕ} (matching : BankOrdinaryPoolMatching n M) :
    Function.Injective matching.matchedPair :=
  matching.slotOfLabeledRequest_injective.comp
    (bankOrdinaryLabelRequest_injective n)

theorem BankOrdinaryPoolMatching.matchedPair_eligible
    {n M : ℕ} (matching : BankOrdinaryPoolMatching n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    matching.matchedPair request ∈
      bankOrdinaryEligibleRelation n M
        (bankOrdinaryScale
          (bankOrdinaryPaperRequestPool n request.1).1) := by
  exact bankOrdinaryAvailablePairs_subset_eligible n M _
    (matching.matchedPair_mem_available request)

/-- Terminal ordinary allocation: every actual signed-copy/component request
receives a globally distinct actual eligible marker--donor pair in its exact
scale and orientation pool. -/
theorem eventually_exists_bankOrdinaryPaper_injective_assignment
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ∃ matching : BankOrdinaryPoolMatching n
          (upperEndpoint n (upperTailLength c n)),
        Function.Injective matching.matchedPair ∧
          ∀ request : ↑(bankOrdinaryPaperRequests n),
            matching.matchedPair request ∈
              bankOrdinaryEligibleRelation n
                (upperEndpoint n (upperTailLength c n))
                (bankOrdinaryScale
                  (bankOrdinaryPaperRequestPool n request.1).1) := by
  filter_upwards [eventually_bankOrdinary_allPoolDemands_le_capacity hc]
      with n hcapacity
  let matching := Classical.choice
    (bankOrdinaryPoolMatching_nonempty n
      (upperEndpoint n (upperTailLength c n)) hcapacity)
  exact ⟨matching, matching.matchedPair_injective,
    matching.matchedPair_eligible⟩

end

end Erdos390.WholePaper
