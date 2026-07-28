import Erdos390.WholePaper.BankOrdinaryPoolMatching
import Erdos390.WholePaper.BankRoughSignatures

/-!
# Realized ordinary bank components

An ordinary matching supplies an actual pair `(P,u)` to every concrete path
request `q→b`.  This file materializes the three factor occurrences

* source state `P*q`,
* target state `P*b`, and
* backing donor `P*u`.

All three lie in `(n,M]` and have the same complete rough signature.  The
large prime marker is recovered uniquely from any realized occurrence, which
gives marker injectivity, donor-product injectivity, and collision-freedom
across requests, scales, and orientations.  Finally, cancellation of the
common marker turns the realized component changes back into the actual
finite path telescope.

The public names intentionally mirror `BankBottomPaperComponents`: a
realization object, factor-valued methods, an occurrence-kind enumeration,
and `occurrenceValue`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Coarse global size bounds -/

/-- A prime path has at most `p` nonterminal component sources.  This coarse
bound is deliberately independent of the geometric-cell congestion bounds:
it is the convenient global estimate used when every ordinary marker is
guarded at once. -/
theorem bankOrdinaryPrimeCoreSources_card_le
    {p : ℕ} (hp : p.Prime) :
    (bankOrdinaryCoreSources p).card ≤ p := by
  by_cases hp5 : p ≤ 5
  · simp [bankOrdinaryCoreSources_of_le_five hp5]
  · have hp6 : 6 ≤ p := by omega
    have hpPower : ¬ IsPowerOfTwo p :=
      prime_not_isPowerOfTwo_of_five_le hp (by omega)
    have hsubset : bankOrdinaryCoreSources p ⊆ Finset.Icc 1 p := by
      intro source hsource
      have hspec := bankOrdinaryCoreSource_spec
        (show 5 ≤ p by omega) hpPower hsource
      exact Finset.mem_Icc.mpr
        ⟨(show 1 ≤ 6 by norm_num).trans hspec.1,
          bankOrdinaryCoreSource_le_start hsource⟩
    exact (Finset.card_le_card hsubset).trans (by simp)

/-- The number of signed beta slots is exactly twice the common one-sided
bottom demand. -/
theorem bankOrdinarySignedSlots_card_eq_two_mul_demand (n : ℕ) :
    Fintype.card (SignedBankSlot (bankRoundingBetaOnSupport n)) =
      2 * bankBottomPaperDemand n := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_sum, Fintype.card_fin,
    bankRoundingBetaOnSupport]
  calc
    (∑ p : ↑(bankRoundingPrimeSupport n),
        (bankRoundingBeta n p.1 + bankRoundingBeta n p.1)) =
        2 * ∑ p : ↑(bankRoundingPrimeSupport n),
          bankRoundingBeta n p.1 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p _hp
            omega
    _ = 2 * bankBottomPaperDemand n := by
      congr 1
      simpa only [bankBottomPaperDemand] using
        (Finset.sum_attach (bankRoundingPrimeSupport n)
          (fun p ↦ bankRoundingBeta n p))

/-- The complete ordinary request family has the pointwise coarse bound
`2*yNat*sum beta`.  In particular, the source multiplicity contributes only
one additional factor of `yNat`. -/
theorem bankOrdinaryPaperRequests_card_le_two_mul_yNat_mul_demand
    (n : ℕ) :
    (bankOrdinaryPaperRequests n).card ≤
      2 * yNat n * bankBottomPaperDemand n := by
  rw [bankOrdinaryPaperRequests, Finset.card_univ, Fintype.card_sigma]
  calc
    (∑ slot : SignedBankSlot (bankRoundingBetaOnSupport n),
        Fintype.card ↑(bankOrdinaryCoreSources slot.1.1)) ≤
        ∑ _slot : SignedBankSlot (bankRoundingBetaOnSupport n),
          yNat n := by
            apply Finset.sum_le_sum
            intro slot _hslot
            simpa only [Fintype.card_coe] using
              (bankOrdinaryPrimeCoreSources_card_le
                  (bankRoundingPrimeSupport_prime slot.1.property)).trans
                (bankRoundingPrimeSupport_le_yNat slot.1.property)
    _ = Fintype.card
          (SignedBankSlot (bankRoundingBetaOnSupport n)) * yNat n := by
            simp
    _ = 2 * yNat n * bankBottomPaperDemand n := by
      rw [bankOrdinarySignedSlots_card_eq_two_mul_demand]
      ring

/-- Globally there are only `O(yNat²)` ordinary components.  This is the
coarse estimate needed to replace the cofactor of every ordinary marker,
without singling out a collision prefix. -/
theorem bankOrdinaryPaperRequests_card_isBigO_yNat_sq :
    (fun n : ℕ ↦ ((bankOrdinaryPaperRequests n).card : ℝ))
      =O[atTop] (fun n : ℕ ↦ (yNat n : ℝ) ^ 2) := by
  have hpoint :
      (fun n : ℕ ↦ ((bankOrdinaryPaperRequests n).card : ℝ))
        =O[atTop]
          (fun n : ℕ ↦
            2 * (yNat n : ℝ) * bankBottomPaperDemand n) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ (bankOrdinaryPaperRequests n).card),
      Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ 2 * (yNat n : ℝ) * bankBottomPaperDemand n),
      one_mul]
    exact_mod_cast
      bankOrdinaryPaperRequests_card_le_two_mul_yNat_mul_demand n
  have hproduct :=
    (isBigO_refl (fun n : ℕ ↦ (yNat n : ℝ)) atTop).mul
      bankBottomPaperDemand_isBigO_yNat
  have hscaled := hproduct.const_mul_left (2 : ℝ)
  exact hpoint.trans (hscaled.congr'
    (Eventually.of_forall fun n ↦ by ring)
    (Eventually.of_forall fun n ↦ (pow_two (yNat n : ℝ)).symm))

/-- The public reserve interface for guarding every ordinary marker at once:
an `O(yNat²)` family consumes `o(secondOrderScale)` positions. -/
theorem yNat_sq_div_secondOrderScale_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ (yNat n : ℝ) ^ 2 / secondOrderScale n)
      atTop (nhds 0) := by
  apply yNat_div_bankOrdinaryWorstMarkerScale_tendsto_zero.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hyNatOne : 1 ≤ yNat n := by
    rw [yNat]
    apply Nat.le_floor
    rw [y]
    have hnOneR : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show 1 ≤ n by omega)
    simpa only [Nat.cast_one] using
      Real.one_le_rpow hnOneR
        (by norm_num : (0 : ℝ) ≤ 2 / 9)
  have hyNatPos : 0 < yNat n :=
    lt_of_lt_of_le Nat.zero_lt_one hyNatOne
  have hyPos : (0 : ℝ) < yNat n := by exact_mod_cast hyNatPos
  have hsecond : 0 < secondOrderScale n := secondOrderScale_pos hn
  rw [bankOrdinaryWorstMarkerScale,
    max_eq_right (by exact_mod_cast hyNatOne : (1 : ℝ) ≤ yNat n)]
  field_simp [hyPos.ne', hsecond.ne']

/-- The actual ordinary component has exactly three interval occurrences.
The bare prime marker is deliberately not an occurrence: it is smaller than
the interval endpoint and is retained separately as bookkeeping data. -/
inductive BankOrdinaryPaperOccurrenceKind where
  | sourceState
  | targetState
  | donor
  deriving DecidableEq, Fintype

/-! ## Arithmetic helpers for rough signatures -/

private theorem bank_yNat_sq_le
    {n : ℕ} (hn : 1 ≤ n) : yNat n * yNat n ≤ n := by
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (by positivity) _
  have hyFloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
  have hyFloorNonneg : (0 : ℝ) ≤ yNat n := by positivity
  have hsq : (yNat n : ℝ) ^ 2 ≤ y n ^ 2 :=
    (sq_le_sq₀ hyFloorNonneg hyNonneg).2 hyFloor
  have hpow : (n : ℝ) ^ (4 / 9 : ℝ) ≤ (n : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hnOne
        (by norm_num : (4 / 9 : ℝ) ≤ 1)
  rw [Erdos390.Full.Scale.y_pow_two] at hsq
  have hcast : ((yNat n * yNat n : ℕ) : ℝ) ≤ (n : ℝ) := by
    push_cast
    simpa only [pow_two] using hsq.trans hpow
  exact_mod_cast hcast

/-- Multiplying two smooth cofactors by the same nonzero marker preserves
their complete rough signature. -/
theorem completeRoughSignature_marker_mul_smooth_eq
    {y P a b : ℕ} (hP : P ≠ 0)
    (ha : a ∈ Nat.smoothNumbers (y + 1))
    (hb : b ∈ Nat.smoothNumbers (y + 1)) :
    completeRoughSignature y (P * a) =
      completeRoughSignature y (P * b) := by
  ext r
  rw [completeRoughSignature_apply, completeRoughSignature_apply]
  by_cases hry : y < r
  · simp only [hry, if_true]
    have haZero : a.factorization r = 0 := by
      by_cases hr : r.Prime
      · apply Nat.factorization_eq_zero_of_not_dvd
        intro hrDiv
        have hrSmall := (Nat.mem_smoothNumbers').mp ha r hr hrDiv
        omega
      · exact Nat.factorization_eq_zero_of_not_prime _ hr
    have hbZero : b.factorization r = 0 := by
      by_cases hr : r.Prime
      · apply Nat.factorization_eq_zero_of_not_dvd
        intro hrDiv
        have hrSmall := (Nat.mem_smoothNumbers').mp hb r hr hrDiv
        omega
      · exact Nat.factorization_eq_zero_of_not_prime _ hr
    rw [Nat.factorization_mul hP (Nat.ne_zero_of_mem_smoothNumbers ha),
      Nat.factorization_mul hP (Nat.ne_zero_of_mem_smoothNumbers hb),
      Finsupp.add_apply, Finsupp.add_apply, haZero, hbZero]
  · simp [hry]

/-- A product of a prime marker above the smooth cutoff remembers that marker
uniquely. -/
theorem primeMarker_mul_smooth_marker_eq
    {y P P' a a' : ℕ}
    (hP : P.Prime) (hP' : P'.Prime)
    (hPy : y < P) (_hP'y : y < P')
    (_ha : a ∈ Nat.smoothNumbers (y + 1))
    (ha' : a' ∈ Nat.smoothNumbers (y + 1))
    (heq : P * a = P' * a') :
    P = P' := by
  have hdiv : P ∣ P' * a' := by
    rw [← heq]
    exact dvd_mul_right P a
  rcases hP.dvd_mul.mp hdiv with hPP' | hPa'
  · exact (Nat.prime_dvd_prime_iff_eq hP hP').mp hPP'
  · have hsmall := (Nat.mem_smoothNumbers').mp ha' P hP hPa'
    omega

theorem primeMarker_mul_smooth_pair_eq
    {y P P' a a' : ℕ}
    (hP : P.Prime) (hP' : P'.Prime)
    (hPy : y < P) (hP'y : y < P')
    (ha : a ∈ Nat.smoothNumbers (y + 1))
    (ha' : a' ∈ Nat.smoothNumbers (y + 1))
    (heq : P * a = P' * a') :
    (P, a) = (P', a') := by
  have hmarker := primeMarker_mul_smooth_marker_eq
    hP hP' hPy hP'y ha ha' heq
  subst P'
  have hcofactor : a = a' := Nat.mul_left_cancel hP.pos heq
  exact Prod.ext rfl hcofactor

/-! ## Marker injectivity inherited from the orientation pools -/

theorem bankOrdinaryAvailablePairs_subset_markerDonorPairs
    (n M : ℕ) (pool : BankOrdinaryOrientationPool) :
    bankOrdinaryAvailablePairs n M pool ⊆
      bankMarkerDonorPairs
        (bankOrdinaryEligibleRelation n M (bankOrdinaryScale pool.1)) := by
  rcases pool with ⟨j, orientation⟩
  cases orientation
  · exact bankOrientationPoolFirst_subset_pairs _
  · intro pair hpair
    exact (Finset.mem_sdiff.mp hpair).1

def BankOrdinaryPoolMatching.matchedMarker
    {n M : ℕ} (matching : BankOrdinaryPoolMatching n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ :=
  (matching.matchedPair request).1

def BankOrdinaryPoolMatching.matchedDonorCore
    {n M : ℕ} (matching : BankOrdinaryPoolMatching n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ :=
  (matching.matchedPair request).2

theorem BankOrdinaryPoolMatching.matchedMarker_injective
    {n M : ℕ} (matching : BankOrdinaryPoolMatching n M) :
    Function.Injective matching.matchedMarker := by
  intro request request' hmarker
  let pool := bankOrdinaryPaperRequestPool n request.1
  let pool' := bankOrdinaryPaperRequestPool n request'.1
  by_cases hscale : pool.1 = pool'.1
  · let eligible := bankOrdinaryEligibleRelation n M
      (bankOrdinaryScale pool.1)
    have hpair : matching.matchedPair request ∈
        bankMarkerDonorPairs eligible := by
      exact bankOrdinaryAvailablePairs_subset_markerDonorPairs n M pool
        (matching.matchedPair_mem_available request)
    have hpair' : matching.matchedPair request' ∈
        bankMarkerDonorPairs eligible := by
      have hmem := bankOrdinaryAvailablePairs_subset_markerDonorPairs
        n M pool' (matching.matchedPair_mem_available request')
      simpa only [eligible, hscale] using hmem
    have hpairs := bankMarkerDonorPairs_injective_by_marker eligible
      hpair hpair' hmarker
    exact matching.matchedPair_injective hpairs
  · have heligible := matching.matchedPair_eligible request
    have heligible' := matching.matchedPair_eligible request'
    have hcell := (mem_bankOrdinaryEligibleRelation.mp heligible).2.2.2.1
    have hcell' := (mem_bankOrdinaryEligibleRelation.mp heligible').2.2.2.1
    have hcellAt : InOrdinaryBankMarkerInterval n
        (bankOrdinaryScale pool'.1) (matching.matchedMarker request) :=
      Eq.mp
        (congrArg
          (fun P ↦ InOrdinaryBankMarkerInterval n
            (bankOrdinaryScale pool'.1) P) hmarker).symm
        hcell'
    exact False.elim
      (bankOrdinary_markerIntervals_disjoint hscale hcell hcellAt)

/-! ## The public realization object and its actual factors -/

/-- An ordinary realization packages the actual matching together with the
two elementary endpoint-range hypotheses used by every component. -/
structure BankOrdinaryPaperRealization (n M : ℕ) where
  matching : BankOrdinaryPoolMatching n M
  one_le_n : 1 ≤ n
  two_mul_n_le_M : 2 * n ≤ M

namespace BankOrdinaryPaperRealization

def marker {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ :=
  R.matching.matchedMarker request

def donorCore {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ :=
  R.matching.matchedDonorCore request

def markerDonorPair {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ × ℕ :=
  (R.marker request, R.donorCore request)

theorem markerDonorPair_eq_matchedPair
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.markerDonorPair request = R.matching.matchedPair request := rfl

theorem markerDonorPair_mem
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.markerDonorPair request ∈
      bankOrdinaryEligibleRelation n M
        (bankOrdinaryScale
          (bankOrdinaryPaperRequestPool n request.1).1) :=
  R.matching.matchedPair_eligible request

theorem marker_prime
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    (R.marker request).Prime :=
  (mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)).2.1

theorem donorCore_pos
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    0 < R.donorCore request :=
  (mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)).2.2.1

theorem donorCore_smooth
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.donorCore request ∈ Nat.smoothNumbers (yNat n + 1) :=
  (mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)).2.2.2.2.2.1

theorem sourceCore_le_yNat
    {n M : ℕ} (_R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    bankOrdinaryPaperRequestSource request.1 ≤ yNat n := by
  exact (bankOrdinaryCoreSource_le_start request.1.2.property).trans
    (bankRoundingPrimeSupport_le_yNat request.1.1.1.property)

theorem targetCore_le_yNat
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    bankOrdinaryPaperRequestTarget request.1 ≤ yNat n := by
  have hspec := bankOrdinaryPaperRequest_component_spec request.1
  exact hspec.2.2.2.2.1.le.trans (R.sourceCore_le_yNat request)

theorem sourceCore_smooth
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    bankOrdinaryPaperRequestSource request.1 ∈
      Nat.smoothNumbers (yNat n + 1) := by
  have hspec := bankOrdinaryPaperRequest_component_spec request.1
  have hsourcePos : 0 < bankOrdinaryPaperRequestSource request.1 := by
    have hsourceSix := hspec.1
    omega
  exact Nat.mem_smoothNumbers_of_lt hsourcePos
    (Nat.lt_succ_of_le (R.sourceCore_le_yNat request))

theorem targetCore_smooth
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    bankOrdinaryPaperRequestTarget request.1 ∈
      Nat.smoothNumbers (yNat n + 1) := by
  have hspec := bankOrdinaryPaperRequest_component_spec request.1
  have htargetPos : 0 < bankOrdinaryPaperRequestTarget request.1 := by
    have htargetFive := hspec.2.2.2.1
    omega
  exact Nat.mem_smoothNumbers_of_lt htargetPos
    (Nat.lt_succ_of_le (R.targetCore_le_yNat request))

/-- Every matched marker lies above the complete-signature cutoff. -/
theorem yNat_lt_marker
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    yNat n < R.marker request := by
  have heligible := mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)
  have hQY := bankOrdinaryPaperRequest_scale_le_yNat request.1
  have hySq := bank_yNat_sq_le R.one_le_n
  by_contra hmarker
  have hmarkerLe : R.marker request ≤ yNat n := by omega
  have hmarkerQ : (0 : ℚ) ≤ R.marker request := by positivity
  have hproduct :
      bankOrdinaryScale (bankOrdinaryPaperRequestPool n request.1).1 *
          (R.marker request : ℚ) ≤
        (yNat n : ℚ) * yNat n := by
    exact mul_le_mul hQY (by exact_mod_cast hmarkerLe) hmarkerQ
      (by positivity : (0 : ℚ) ≤ yNat n)
  have hySqQ : (yNat n : ℚ) * yNat n ≤ n := by
    exact_mod_cast hySq
  have hmarkerLower := heligible.2.2.2.1.1
  nlinarith

/-- Ordinary markers lie strictly below every bottom-row marker scale.  The
first ordinary grid value is `16/3`, and the upper marker inequality at that
scale already forces `3P<n`. -/
theorem three_mul_marker_lt_n
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    3 * R.marker request < n := by
  have heligible := mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)
  have hspec := bankOrdinaryPaperRequest_component_spec request.1
  have hindex :
      1 ≤ (bankOrdinaryPaperRequestPool n request.1).1 := by
    simpa only [bankOrdinaryPaperRequestPool] using
      one_le_bankOrdinaryComponentScaleIndex hspec.1
  have hscale := bankOrdinaryScale_mono hindex
  have hscaleLower : (16 / 3 : ℚ) ≤
      bankOrdinaryScale (bankOrdinaryPaperRequestPool n request.1).1 := by
    norm_num [bankOrdinaryScale] at hscale ⊢
    exact hscale
  have hmarkerUpper := heligible.2.2.2.1.2
  have hmarkerPos : (0 : ℚ) < R.marker request := by
    exact_mod_cast (R.marker_prime request).pos
  have hbound : (3 : ℚ) * R.marker request < n := by
    nlinarith
  exact_mod_cast hbound

def sourceStateValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ :=
  R.marker request * bankOrdinaryPaperRequestSource request.1

def targetStateValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ :=
  R.marker request * bankOrdinaryPaperRequestTarget request.1

def donorValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ :=
  R.marker request * R.donorCore request

private theorem stateValues_mem_factorInterval
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.sourceStateValue request ∈ factorInterval n M ∧
      R.targetStateValue request ∈ factorInterval n M := by
  have heligible := mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)
  have hspec := bankOrdinaryPaperRequest_component_spec request.1
  let P := R.marker request
  let q := bankOrdinaryPaperRequestSource request.1
  let b := bankOrdinaryPaperRequestTarget request.1
  let Q := bankOrdinaryScale
    (bankOrdinaryPaperRequestPool n request.1).1
  have hPpos : (0 : ℚ) < P := by
    exact_mod_cast (R.marker_prime request).pos
  have hPnonneg : (0 : ℚ) ≤ P := hPpos.le
  have hmarker := heligible.2.2.2.1
  have hcell := hspec.2.2.2.2.2.2
  change 4 * (n : ℚ) < 3 * Q * P ∧
    2 * Q * P ≤ 3 * (n : ℚ) at hmarker
  change (Q < (q : ℚ) ∧ (q : ℚ) ≤ 4 * Q / 3) ∧
    3 * Q / 4 < (b : ℚ) at hcell
  have hQq := mul_lt_mul_of_pos_left hcell.1.1
    hPpos
  have hqUpper := mul_le_mul_of_nonneg_left hcell.1.2 hPnonneg
  have hbLower := mul_lt_mul_of_pos_left hcell.2
    hPpos
  have hmarkerLower := hmarker.1
  have hmarkerUpper := hmarker.2
  have hsourceLowerQ : (n : ℚ) < P * q := by
    nlinarith [hmarkerLower, hQq]
  have htargetLowerQ : (n : ℚ) < P * b := by
    nlinarith [hmarkerLower, hbLower]
  have hcellSourceUpper : P * (4 * Q / 3) ≤ 2 * (n : ℚ) := by
    have hscaled := mul_le_mul_of_nonneg_left hmarkerUpper
      (by norm_num : (0 : ℚ) ≤ 2 / 3)
    convert hscaled using 1 <;> ring
  have hsourceUpperQ : P * q ≤ 2 * (n : ℚ) := by
    exact hqUpper.trans hcellSourceUpper
  have hsourceLower : n < P * q := by exact_mod_cast hsourceLowerQ
  have htargetLower : n < P * b := by exact_mod_cast htargetLowerQ
  have hsourceUpper : P * q ≤ M := by
    have : P * q ≤ 2 * n := by exact_mod_cast hsourceUpperQ
    exact this.trans R.two_mul_n_le_M
  have htargetUpper : P * b ≤ M := by
    have hbq : b ≤ q := hspec.2.2.2.2.1.le
    exact (Nat.mul_le_mul_left P hbq).trans hsourceUpper
  simp only [sourceStateValue, targetStateValue, factorInterval,
    Finset.mem_Ioc]
  exact ⟨⟨hsourceLower, hsourceUpper⟩,
    ⟨htargetLower, htargetUpper⟩⟩

theorem donorValue_mem_factorInterval
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.donorValue request ∈ factorInterval n M := by
  have heligible := mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)
  simp only [donorValue, factorInterval, Finset.mem_Ioc]
  have hlower := heligible.2.2.2.2.2.2.1
  change 2 * n < R.marker request * R.donorCore request at hlower
  exact ⟨by omega, heligible.2.2.2.2.2.2.2⟩

/-- Factor-valued methods, matching the bottom-component API. -/
def sourceStateFactor
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    ↑(factorInterval n M) :=
  ⟨R.sourceStateValue request, (R.stateValues_mem_factorInterval request).1⟩

def targetStateFactor
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    ↑(factorInterval n M) :=
  ⟨R.targetStateValue request, (R.stateValues_mem_factorInterval request).2⟩

def donorFactor
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    ↑(factorInterval n M) :=
  ⟨R.donorValue request, R.donorValue_mem_factorInterval request⟩

theorem state_donor_completeRoughSignature_eq
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    completeRoughSignature (yNat n) (R.sourceStateValue request) =
        completeRoughSignature (yNat n) (R.targetStateValue request) ∧
      completeRoughSignature (yNat n) (R.targetStateValue request) =
        completeRoughSignature (yNat n) (R.donorValue request) := by
  constructor
  · exact completeRoughSignature_marker_mul_smooth_eq
      (R.marker_prime request).ne_zero
      (R.sourceCore_smooth request) (R.targetCore_smooth request)
  · exact completeRoughSignature_marker_mul_smooth_eq
      (R.marker_prime request).ne_zero
      (R.targetCore_smooth request) (R.donorCore_smooth request)

theorem marker_injective
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M) :
    Function.Injective R.marker :=
  R.matching.matchedMarker_injective

theorem markerDonorPair_injective
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M) :
    Function.Injective R.markerDonorPair := by
  intro request request' hpairs
  exact R.marker_injective (congrArg Prod.fst hpairs)

/-- The finite set of all ordinary markers used by this realization. -/
def markers
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M) : Finset ℕ :=
  Finset.univ.image R.marker

@[simp] theorem marker_mem_markers
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.marker request ∈ R.markers := by
  simp [markers]

/-- Marker injectivity makes the marker set equinumerous with the complete
ordinary component-request family. -/
theorem markers_card_eq_paperRequests_card
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M) :
    R.markers.card = (bankOrdinaryPaperRequests n).card := by
  rw [markers, Finset.card_image_of_injective _ R.marker_injective]
  simp

theorem markers_card_le_two_mul_yNat_mul_demand
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M) :
    R.markers.card ≤ 2 * yNat n * bankBottomPaperDemand n := by
  rw [R.markers_card_eq_paperRequests_card]
  exact bankOrdinaryPaperRequests_card_le_two_mul_yNat_mul_demand n

private theorem exists_request_for_marker
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (P : ↑R.markers) :
    ∃ request : ↑(bankOrdinaryPaperRequests n),
      R.marker request = P.1 := by
  simpa only [markers, Finset.mem_image, Finset.mem_univ, true_and] using
    P.property

/-- The unique request carrying a marker from `R.markers`. -/
def requestForMarker
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (P : ↑R.markers) : ↑(bankOrdinaryPaperRequests n) :=
  Classical.choose (R.exists_request_for_marker P)

@[simp] theorem marker_requestForMarker
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (P : ↑R.markers) :
    R.marker (R.requestForMarker P) = P.1 :=
  Classical.choose_spec (R.exists_request_for_marker P)

theorem requestForMarker_unique
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (P : ↑R.markers)
    (request : ↑(bankOrdinaryPaperRequests n))
    (hmarker : R.marker request = P.1) :
    request = R.requestForMarker P := by
  apply R.marker_injective
  exact hmarker.trans (R.marker_requestForMarker P).symm

/-- The path-source cofactor canonically attached to a realized marker. -/
def markerSourceCore
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (P : ↑R.markers) : ℕ :=
  bankOrdinaryPaperRequestSource (R.requestForMarker P).1

@[simp] theorem markerSourceCore_of_request
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.markerSourceCore
        ⟨R.marker request, R.marker_mem_markers request⟩ =
      bankOrdinaryPaperRequestSource request.1 := by
  unfold markerSourceCore
  have hrequest :
      R.requestForMarker
          ⟨R.marker request, R.marker_mem_markers request⟩ = request := by
    symm
    exact R.requestForMarker_unique _ request rfl
  rw [hrequest]

/-- Consequently a marker can never carry two different source cores. -/
theorem sourceCore_eq_of_marker_eq
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    {request request' : ↑(bankOrdinaryPaperRequests n)}
    (hmarker : R.marker request = R.marker request') :
    bankOrdinaryPaperRequestSource request.1 =
      bankOrdinaryPaperRequestSource request'.1 := by
  rw [R.marker_injective hmarker]

theorem markerSourceCore_le_yNat
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (P : ↑R.markers) :
    R.markerSourceCore P ≤ yNat n :=
  R.sourceCore_le_yNat (R.requestForMarker P)

/-! ## The three actual occurrences and global collision-freedom -/

theorem targetStateValue_lt_sourceStateValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.targetStateValue request < R.sourceStateValue request := by
  have htarget :=
    (bankOrdinaryPaperRequest_component_spec request.1).2.2.2.2.1
  exact Nat.mul_lt_mul_of_pos_left htarget (R.marker_prime request).pos

theorem sourceStateValue_le_two_mul_n
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.sourceStateValue request ≤ 2 * n := by
  have heligible := mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)
  have hspec := bankOrdinaryPaperRequest_component_spec request.1
  let P := R.marker request
  let q := bankOrdinaryPaperRequestSource request.1
  let Q := bankOrdinaryScale
    (bankOrdinaryPaperRequestPool n request.1).1
  have hPnonneg : (0 : ℚ) ≤ P := by positivity
  have hqUpper := mul_le_mul_of_nonneg_left
    hspec.2.2.2.2.2.2.1.2 hPnonneg
  have hmarkerUpper := heligible.2.2.2.1.2
  change (P : ℚ) * q ≤ (P : ℚ) * (4 * Q / 3) at hqUpper
  change 2 * Q * (P : ℚ) ≤ 3 * (n : ℚ) at hmarkerUpper
  have hcellSourceUpper : (P : ℚ) * (4 * Q / 3) ≤
      2 * (n : ℚ) := by
    have hscaled := mul_le_mul_of_nonneg_left hmarkerUpper
      (by norm_num : (0 : ℚ) ≤ 2 / 3)
    convert hscaled using 1 <;> ring
  have hsourceUpperQ : (P : ℚ) * q ≤ 2 * n := by
    exact hqUpper.trans hcellSourceUpper
  exact_mod_cast hsourceUpperQ

theorem two_mul_n_lt_donorValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    2 * n < R.donorValue request :=
  (mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)).2.2.2.2.2.2.1

theorem sourceStateValue_lt_donorValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.sourceStateValue request < R.donorValue request :=
  (R.sourceStateValue_le_two_mul_n request).trans_lt
    (R.two_mul_n_lt_donorValue request)

def occurrenceCofactor
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    BankOrdinaryPaperOccurrenceKind → ℕ
  | .sourceState => bankOrdinaryPaperRequestSource request.1
  | .targetState => bankOrdinaryPaperRequestTarget request.1
  | .donor => R.donorCore request

def occurrenceValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n))
    (kind : BankOrdinaryPaperOccurrenceKind) : ℕ :=
  R.marker request * R.occurrenceCofactor request kind

@[simp] theorem occurrenceValue_sourceState
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.occurrenceValue request .sourceState = R.sourceStateValue request := rfl

@[simp] theorem occurrenceValue_targetState
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.occurrenceValue request .targetState = R.targetStateValue request := rfl

@[simp] theorem occurrenceValue_donor
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.occurrenceValue request .donor = R.donorValue request := rfl

theorem occurrenceValue_injective
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    Function.Injective (R.occurrenceValue request) := by
  intro kind kind' heq
  have htargetSource := R.targetStateValue_lt_sourceStateValue request
  have hsourceDonor := R.sourceStateValue_lt_donorValue request
  cases kind <;> cases kind'
  all_goals simp only [occurrenceValue_sourceState,
    occurrenceValue_targetState, occurrenceValue_donor] at heq
  all_goals try rfl
  all_goals omega

theorem occurrenceCofactor_smooth
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n))
    (kind : BankOrdinaryPaperOccurrenceKind) :
    R.occurrenceCofactor request kind ∈
      Nat.smoothNumbers (yNat n + 1) := by
  cases kind
  · exact R.sourceCore_smooth request
  · exact R.targetCore_smooth request
  · exact R.donorCore_smooth request

theorem occurrenceValue_eq_marker_implies_request_eq
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    {request request' : ↑(bankOrdinaryPaperRequests n)}
    {kind kind' : BankOrdinaryPaperOccurrenceKind}
    (heq : R.occurrenceValue request kind =
      R.occurrenceValue request' kind') :
    request = request' := by
  have hmarker : R.marker request = R.marker request' :=
    primeMarker_mul_smooth_marker_eq
      (R.marker_prime request) (R.marker_prime request')
      (R.yNat_lt_marker request) (R.yNat_lt_marker request')
      (R.occurrenceCofactor_smooth request kind)
      (R.occurrenceCofactor_smooth request' kind') heq
  exact R.marker_injective hmarker

theorem occurrenceValue_ne_of_request_ne
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    {request request' : ↑(bankOrdinaryPaperRequests n)}
    (hrequest : request ≠ request')
    (kind kind' : BankOrdinaryPaperOccurrenceKind) :
    R.occurrenceValue request kind ≠
      R.occurrenceValue request' kind' := by
  intro heq
  exact hrequest (R.occurrenceValue_eq_marker_implies_request_eq heq)

def componentOccurrences
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : Finset ℕ :=
  Finset.univ.image (R.occurrenceValue request)

theorem occurrenceValue_mem_componentOccurrences
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n))
    (kind : BankOrdinaryPaperOccurrenceKind) :
    R.occurrenceValue request kind ∈ R.componentOccurrences request := by
  exact Finset.mem_image.mpr ⟨kind, Finset.mem_univ _, rfl⟩

/-- Each ordinary component contributes exactly its source state, target
state, and donor occurrence. -/
theorem componentOccurrences_card
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    (R.componentOccurrences request).card = 3 := by
  rw [componentOccurrences,
    Finset.card_image_of_injective _ (R.occurrenceValue_injective request)]
  decide

theorem componentOccurrence_mem_factorInterval
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n))
    {occurrence : ℕ}
    (hoccurrence : occurrence ∈ R.componentOccurrences request) :
    occurrence ∈ factorInterval n M := by
  rw [componentOccurrences, Finset.mem_image] at hoccurrence
  obtain ⟨kind, _hkind, hvalue⟩ := hoccurrence
  cases kind
  · simpa only [← hvalue, occurrenceValue_sourceState] using
      (R.stateValues_mem_factorInterval request).1
  · simpa only [← hvalue, occurrenceValue_targetState] using
      (R.stateValues_mem_factorInterval request).2
  · simpa only [← hvalue, occurrenceValue_donor] using
      R.donorValue_mem_factorInterval request

theorem componentOccurrences_disjoint
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    {request request' : ↑(bankOrdinaryPaperRequests n)}
    (hrequest : request ≠ request') :
    Disjoint (R.componentOccurrences request)
      (R.componentOccurrences request') := by
  rw [Finset.disjoint_left]
  intro value hvalue hvalue'
  rw [componentOccurrences, Finset.mem_image] at hvalue hvalue'
  obtain ⟨kind, _hkind, rfl⟩ := hvalue
  obtain ⟨kind', _hkind', heq⟩ := hvalue'
  exact R.occurrenceValue_ne_of_request_ne hrequest kind kind' heq.symm

theorem occurrenceValue_ne_of_pool_ne
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    {request request' : ↑(bankOrdinaryPaperRequests n)}
    (hpools : bankOrdinaryPaperRequestPool n request.1 ≠
      bankOrdinaryPaperRequestPool n request'.1)
    (kind kind' : BankOrdinaryPaperOccurrenceKind) :
    R.occurrenceValue request kind ≠
      R.occurrenceValue request' kind' := by
  apply R.occurrenceValue_ne_of_request_ne
  intro hrequest
  subst request'
  exact hpools rfl

/-! ## Realized component and signed-slot changes -/

theorem factorMoveChange_mul_left
    {P source target : ℕ}
    (hP : P ≠ 0) (hsource : source ≠ 0) (htarget : target ≠ 0) :
    factorMoveChange (P * source) (P * target) =
      factorMoveChange source target := by
  funext r
  simp only [factorMoveChange, integerValuationVector, Pi.sub_apply]
  rw [Nat.factorization_mul hP hsource,
    Nat.factorization_mul hP htarget,
    Finsupp.add_apply, Finsupp.add_apply]
  push_cast
  ring

def fromStateValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ :=
  match (bankOrdinaryPaperRequestPool n request.1).2 with
  | .downward => R.sourceStateValue request
  | .upward => R.targetStateValue request

def toStateValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ :=
  match (bankOrdinaryPaperRequestPool n request.1).2 with
  | .downward => R.targetStateValue request
  | .upward => R.sourceStateValue request

def realizedComponentChange
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : BankVector ℕ :=
  factorMoveChange (R.fromStateValue request) (R.toStateValue request)

theorem realizedComponentChange_eq
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.realizedComponentChange request =
      match (bankOrdinaryPaperRequestPool n request.1).2 with
      | .downward =>
          factorMoveChange
            (bankOrdinaryPaperRequestSource request.1)
            (bankOrdinaryPaperRequestTarget request.1)
      | .upward =>
          -factorMoveChange
            (bankOrdinaryPaperRequestSource request.1)
            (bankOrdinaryPaperRequestTarget request.1) := by
  have hspec := bankOrdinaryPaperRequest_component_spec request.1
  have hP := (R.marker_prime request).ne_zero
  have hsource : bankOrdinaryPaperRequestSource request.1 ≠ 0 := by
    have hsourceSix := hspec.1
    omega
  have htarget : bankOrdinaryPaperRequestTarget request.1 ≠ 0 := by
    have htargetFive := hspec.2.2.2.1
    omega
  cases horientation : (bankOrdinaryPaperRequestPool n request.1).2
  · rw [realizedComponentChange, fromStateValue, toStateValue,
      horientation, sourceStateValue, targetStateValue,
      factorMoveChange_mul_left hP hsource htarget]
  · rw [realizedComponentChange, fromStateValue, toStateValue,
      horientation, sourceStateValue, targetStateValue,
      factorMoveChange_mul_left hP htarget hsource]
    unfold factorMoveChange
    abel

def requestOfSource
    {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (source : ↑(bankOrdinaryCoreSources slot.1.1)) :
    ↑(bankOrdinaryPaperRequests n) :=
  ⟨⟨slot, source⟩, Finset.mem_univ _⟩

def realizedSlotChange
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) : BankVector ℕ :=
  ∑ source : ↑(bankOrdinaryCoreSources slot.1.1),
    R.realizedComponentChange (requestOfSource slot source)

def signedFinitePathChange
    {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    BankVector ℕ :=
  match slot.2 with
  | .inl _copy => bankOrdinaryFinitePathChange slot.1.1
  | .inr _copy => -bankOrdinaryFinitePathChange slot.1.1

/-- The complete realized ordinary change of each signed slot is exactly the
deterministic finite-path change (or its reverse). -/
theorem realizedSlotChange_eq_signedFinitePathChange
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.realizedSlotChange slot = signedFinitePathChange slot := by
  rcases slot with ⟨prime, signedCopy⟩
  cases signedCopy with
  | inl copy =>
      rw [realizedSlotChange, signedFinitePathChange]
      calc
        (∑ source : ↑(bankOrdinaryCoreSources prime.1),
            R.realizedComponentChange
              (requestOfSource ⟨prime, Sum.inl copy⟩ source)) =
          ∑ source : ↑(bankOrdinaryCoreSources prime.1),
            factorMoveChange source.1
              (bankOrdinaryCoreStep source.1) := by
                apply Finset.sum_congr rfl
                intro source _hsource
                simpa [bankOrdinaryPaperRequestTarget,
                  bankOrdinaryPaperRequestPool, bankSignedSlotOrientation]
                  using R.realizedComponentChange_eq
                    (requestOfSource ⟨prime, Sum.inl copy⟩ source)
        _ = bankOrdinaryFinitePathChange prime.1 := by
          exact Finset.sum_attach (bankOrdinaryCoreSources prime.1)
            (fun source ↦ factorMoveChange source
              (bankOrdinaryCoreStep source))
  | inr copy =>
      rw [realizedSlotChange, signedFinitePathChange]
      calc
        (∑ source : ↑(bankOrdinaryCoreSources prime.1),
            R.realizedComponentChange
              (requestOfSource ⟨prime, Sum.inr copy⟩ source)) =
          ∑ source : ↑(bankOrdinaryCoreSources prime.1),
            -factorMoveChange source.1
              (bankOrdinaryCoreStep source.1) := by
                apply Finset.sum_congr rfl
                intro source _hsource
                simpa [bankOrdinaryPaperRequestTarget,
                  bankOrdinaryPaperRequestPool, bankSignedSlotOrientation]
                  using R.realizedComponentChange_eq
                    (requestOfSource ⟨prime, Sum.inr copy⟩ source)
        _ = -bankOrdinaryFinitePathChange prime.1 := by
          rw [Finset.sum_neg_distrib]
          exact congrArg Neg.neg
            (Finset.sum_attach (bankOrdinaryCoreSources prime.1)
              (fun source ↦ factorMoveChange source
                (bankOrdinaryCoreStep source)))

def signedPrimeToFiveChange
    {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    BankVector ℕ :=
  match slot.2 with
  | .inl _copy => coordinateUnit 5 - coordinateUnit slot.1.1
  | .inr _copy => coordinateUnit slot.1.1 - coordinateUnit 5

theorem realizedSlotChange_eq_signedPrimeToFiveChange
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (hp5 : 5 ≤ slot.1.1) :
    R.realizedSlotChange slot = signedPrimeToFiveChange slot := by
  rw [R.realizedSlotChange_eq_signedFinitePathChange]
  have hp := bankRoundingPrimeSupport_prime slot.1.property
  rcases slot with ⟨prime, signedCopy⟩
  cases signedCopy
  · simpa [signedFinitePathChange, signedPrimeToFiveChange] using
      bankOrdinaryFinitePathChange_prime_to_five hp hp5
  · rw [signedFinitePathChange, signedPrimeToFiveChange,
      bankOrdinaryFinitePathChange_prime_to_five hp hp5]
    abel

end BankOrdinaryPaperRealization

/-! ## Eventual realized allocation -/

/-- Terminal realization compatible with the bottom realization object: at
the paper endpoint, every ordinary request has actual factor occurrences and
all request occurrence sets are pairwise disjoint. -/
theorem eventually_exists_bankOrdinaryPaperRealization
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      Nonempty (BankOrdinaryPaperRealization n
        (upperEndpoint n (upperTailLength c n))) := by
  filter_upwards [eventually_exists_bankOrdinaryPaper_injective_assignment hc,
      eventually_ge_atTop 1] with n hmatching hn
  obtain ⟨matching, _hinjective, _heligible⟩ := hmatching
  exact ⟨⟨matching, hn,
    two_mul_le_upperEndpoint n (upperTailLength c n)⟩⟩

end

end Erdos390.WholePaper
