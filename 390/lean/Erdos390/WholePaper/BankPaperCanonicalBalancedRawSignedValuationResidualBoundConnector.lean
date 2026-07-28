import Erdos390.WholePaper.BankPaperCanonicalSelectorDeficitPaperRateClosureConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionEightTopFrozenInitialMassConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionEightTwoZeroOneShotConnector
import Erdos390.WholePaper.FixedModulusReducedResidueCount
import Erdos390.WholePaper.ValuationError
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The balanced raw signed valuation residual

The raw signed residual is the one generic term left as a premise in the
four-term paper-rate closure.  This file proves it directly from the
elementary fixed-modulus interval count.

For a fixed prime `p`, every valuation is expanded into the indicators of
`p ^ k` divisibility.  At one exponent, the upper interval has endpoint
error less than one, while each of the two head-free lower intervals has
error at most `roughHeadModulus W + 1`.  The three real-length main terms
cancel exactly by `roughHeadBalancedAlpha_length_normalization`.

The resulting finite bound is logarithmic in the physical endpoint.  The
last section absorbs that logarithm uniformly for `p <= yNat n` into the
paper scale `secondOrderScale n / (p * L n)`.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Valuations as finite prime-power column sums -/

private theorem raw_factorization_le_log_of_le
    {a M p : Nat} (ha : 0 < a) (haM : a <= M) (hp : p.Prime) :
    a.factorization p <= Nat.log p M := by
  have hpowDvd : p ^ (a.factorization p) ∣ a :=
    (hp.pow_dvd_iff_le_factorization ha.ne').mpr le_rfl
  have hpowLe : p ^ (a.factorization p) <= a :=
    Nat.le_of_dvd ha hpowDvd
  exact (Nat.le_log_of_pow_le hp.one_lt hpowLe).trans
    (Nat.log_mono_right haM)

/-- Public finite expansion of a valuation into its prime-power divisibility
indicators.  The endpoint `M` only has to dominate the positive integer
being expanded. -/
theorem factorization_cast_eq_sum_primeExponentIndicators
    {a M p : Nat} (ha : 0 < a) (haM : a <= M) (hp : p.Prime) :
    (a.factorization p : Real) =
      ∑ k ∈ primeExponentRange p M,
        if p ^ k ∣ a then (1 : Real) else 0 := by
  classical
  have hfac : a.factorization p <= Nat.log p M :=
    raw_factorization_le_log_of_le ha haM hp
  have hfilter :
      (primeExponentRange p M).filter (fun k => p ^ k ∣ a) =
        Finset.Icc 1 (a.factorization p) := by
    ext k
    simp only [primeExponentRange, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hk, _⟩, hdvd⟩
      exact ⟨hk, (hp.pow_dvd_iff_le_factorization ha.ne').mp hdvd⟩
    · rintro ⟨hk, hkfac⟩
      exact ⟨⟨hk, hkfac.trans hfac⟩,
        (hp.pow_dvd_iff_le_factorization ha.ne').mpr hkfac⟩
  calc
    (a.factorization p : Real) =
        ((Finset.Icc 1 (a.factorization p)).card : Real) := by simp
    _ = (((primeExponentRange p M).filter
        (fun k => p ^ k ∣ a)).card : Real) := by rw [hfilter]
    _ = ∑ k ∈ primeExponentRange p M,
        if p ^ k ∣ a then (1 : Real) else 0 := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- Summing the preceding pointwise expansion turns an unweighted valuation
sum into the cardinalities of its prime-power divisor fibers. -/
theorem sum_factorization_cast_eq_sum_primePowerDivisorCounts
    {A : Finset Nat} {M p : Nat}
    (hpos : ∀ a ∈ A, 0 < a) (hle : ∀ a ∈ A, a <= M)
    (hp : p.Prime) :
    (∑ a ∈ A, (a.factorization p : Real)) =
      ∑ k ∈ primeExponentRange p M,
        (((A.filter (fun a => p ^ k ∣ a)).card : Nat) : Real) := by
  classical
  calc
    (∑ a ∈ A, (a.factorization p : Real)) =
        ∑ a ∈ A, ∑ k ∈ primeExponentRange p M,
          if p ^ k ∣ a then (1 : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact factorization_cast_eq_sum_primeExponentIndicators
        (hpos a ha) (hle a ha) hp
    _ = ∑ k ∈ primeExponentRange p M, ∑ a ∈ A,
          if p ^ k ∣ a then (1 : Real) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ primeExponentRange p M,
        (((A.filter (fun a => p ^ k ∣ a)).card : Nat) : Real) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_filter]
      simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]

/-- Weighted companion of
`sum_factorization_cast_eq_sum_primePowerDivisorCounts`. -/
theorem sum_weight_mul_factorization_cast_eq_sum_primePowerIndicators
    {A : Finset Nat} {M p : Nat} (weight : Nat -> Real)
    (hpos : ∀ a ∈ A, 0 < a) (hle : ∀ a ∈ A, a <= M)
    (hp : p.Prime) :
    (∑ a ∈ A, weight a * (a.factorization p : Real)) =
      ∑ k ∈ primeExponentRange p M, ∑ a ∈ A,
        weight a * (if p ^ k ∣ a then (1 : Real) else 0) := by
  classical
  calc
    (∑ a ∈ A, weight a * (a.factorization p : Real)) =
        ∑ a ∈ A, weight a *
          (∑ k ∈ primeExponentRange p M,
            if p ^ k ∣ a then (1 : Real) else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [factorization_cast_eq_sum_primeExponentIndicators
        (hpos a ha) (hle a ha) hp]
    _ = ∑ a ∈ A, ∑ k ∈ primeExponentRange p M,
          weight a * (if p ^ k ∣ a then (1 : Real) else 0) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
    _ = ∑ k ∈ primeExponentRange p M, ∑ a ∈ A,
        weight a * (if p ^ k ∣ a then (1 : Real) else 0) := by
      rw [Finset.sum_comm]

/-! ## The literal one-column residual -/

/-- The number of multiples of `D` in `(lo,hi]` differs from the real
interval length divided by `D` by less than one. -/
theorem Ioc_filter_dvd_card_sub_realLengthDiv_abs_lt_one
    {D lo hi : Nat} (hD : 0 < D) (hlohi : lo <= hi) :
    abs ((((Finset.Ioc lo hi).filter (fun a => D ∣ a)).card : Real) -
        (((hi - lo : Nat) : Real) / (D : Real))) < 1 := by
  have hcard :
      ((Finset.Ioc lo hi).filter (fun a => D ∣ a)).card =
        hi / D - lo / D := by
    simpa [coprimeMultipleIoc, reducedResidueIoc] using
      (coprimeMultipleIoc_card_eq_reducedResidueIoc
        (M := 1) (D := D) (lo := lo) (hi := hi) hD
        (by simp : Nat.Coprime D 1))
  rw [hcard]
  exact quotientIocLength_sub_realLengthDiv_abs_lt_one hD hlohi

/-- The upper-minus-high-minus-broad discrepancy at one prime-power
divisibility column. -/
def roughCanonicalRawPrimePowerColumnResidual
    (W n h K : Nat) (alpha beta ell : Real) (p k : Nat) : Real :=
  (((roughUpperBlock n h).filter (fun a => p ^ k ∣ a)).card : Real) -
    alpha *
      ((coprimeMultipleIoc (roughHeadModulus W) (p ^ k)
        (2 * n - K * h) (2 * n)).card : Real) -
    (beta / ell) *
      ((coprimeMultipleIoc (roughHeadModulus W) (p ^ k)
        n (2 * n - K * h)).card : Real)

/-- On a fixed prime-power column, summing the literal raw weight is exactly
the weighted sum of the two head-free interval counts. -/
theorem sum_roughHeadCompatibleRawWeight_mul_primePowerIndicator
    (W n h K : Nat) (alpha beta ell : Real) (p k : Nat) :
    (∑ a ∈ roughRawCandidateSet n h K,
      roughHeadCompatibleRawWeight W n h K alpha beta ell a *
        (if p ^ k ∣ a then (1 : Real) else 0)) =
      alpha *
        ((coprimeMultipleIoc (roughHeadModulus W) (p ^ k)
          (2 * n - K * h) (2 * n)).card : Real) +
      (beta / ell) *
        ((coprimeMultipleIoc (roughHeadModulus W) (p ^ k)
          n (2 * n - K * h)).card : Real) := by
  classical
  have hdisjoint :=
    roughHighLowerBlock_disjoint_roughBroadLowerBlock n h K
  have hhigh :
      (∑ a ∈ roughHighLowerBlock n h K,
        roughHeadCompatibleRawWeight W n h K alpha beta ell a *
          (if p ^ k ∣ a then (1 : Real) else 0)) =
        alpha *
          ((coprimeMultipleIoc (roughHeadModulus W) (p ^ k)
            (2 * n - K * h) (2 * n)).card : Real) := by
    calc
      (∑ a ∈ roughHighLowerBlock n h K,
        roughHeadCompatibleRawWeight W n h K alpha beta ell a *
          (if p ^ k ∣ a then (1 : Real) else 0)) =
          ∑ a ∈ roughHighLowerBlock n h K,
            if p ^ k ∣ a ∧ Nat.Coprime a (roughHeadModulus W)
              then alpha else 0 := by
        apply Finset.sum_congr rfl
        intro a haHigh
        have haBroad : a ∉ roughBroadLowerBlock n h K := by
          intro haBroad
          exact Finset.disjoint_left.mp hdisjoint haHigh haBroad
        by_cases hdiv : p ^ k ∣ a <;>
          by_cases hcop : Nat.Coprime a (roughHeadModulus W) <;>
          simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
            haHigh, haBroad, hdiv, hcop]
      _ = alpha *
          ((coprimeMultipleIoc (roughHeadModulus W) (p ^ k)
            (2 * n - K * h) (2 * n)).card : Real) := by
        rw [← Finset.sum_filter]
        simp [coprimeMultipleIoc, roughHighLowerBlock]
        ring
  have hbroad :
      (∑ a ∈ roughBroadLowerBlock n h K,
        roughHeadCompatibleRawWeight W n h K alpha beta ell a *
          (if p ^ k ∣ a then (1 : Real) else 0)) =
        (beta / ell) *
          ((coprimeMultipleIoc (roughHeadModulus W) (p ^ k)
            n (2 * n - K * h)).card : Real) := by
    calc
      (∑ a ∈ roughBroadLowerBlock n h K,
        roughHeadCompatibleRawWeight W n h K alpha beta ell a *
          (if p ^ k ∣ a then (1 : Real) else 0)) =
          ∑ a ∈ roughBroadLowerBlock n h K,
            if p ^ k ∣ a ∧ Nat.Coprime a (roughHeadModulus W)
              then beta / ell else 0 := by
        apply Finset.sum_congr rfl
        intro a haBroad
        have haHigh : a ∉ roughHighLowerBlock n h K := by
          intro haHigh
          exact Finset.disjoint_left.mp hdisjoint haHigh haBroad
        by_cases hdiv : p ^ k ∣ a <;>
          by_cases hcop : Nat.Coprime a (roughHeadModulus W) <;>
          simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
            haHigh, haBroad, hdiv, hcop]
      _ = (beta / ell) *
          ((coprimeMultipleIoc (roughHeadModulus W) (p ^ k)
            n (2 * n - K * h)).card : Real) := by
        rw [← Finset.sum_filter]
        simp [coprimeMultipleIoc, roughBroadLowerBlock]
        ring
  rw [roughRawCandidateSet, Finset.sum_union hdisjoint, hhigh, hbroad]

/-- Exact prime-power-column expansion of the raw signed valuation
residual. -/
theorem roughCanonicalRawSignedValuationResidual_eq_sum_primePowerColumns
    (W n h K : Nat) (alpha beta ell : Real) (p : Nat)
    (hp : p.Prime) :
    roughCanonicalRawSignedValuationResidual n h K
        (roughHeadCompatibleRawWeight W n h K alpha beta ell) p =
      ∑ k ∈ primeExponentRange p (2 * n + h),
        roughCanonicalRawPrimePowerColumnResidual
          W n h K alpha beta ell p k := by
  classical
  have hupperPos :
      ∀ a ∈ roughUpperBlock n h, 0 < a := by
    intro a ha
    simp only [roughUpperBlock, Finset.mem_Ioc] at ha
    omega
  have hupperLe :
      ∀ a ∈ roughUpperBlock n h, a <= 2 * n + h := by
    intro a ha
    exact (Finset.mem_Ioc.mp ha).2
  have hrawPos :
      ∀ a ∈ roughRawCandidateSet n h K, 0 < a := by
    intro a ha
    simp only [roughRawCandidateSet, roughHighLowerBlock,
      roughBroadLowerBlock, Finset.mem_union, Finset.mem_Ioc] at ha
    omega
  have hrawLe :
      ∀ a ∈ roughRawCandidateSet n h K, a <= 2 * n + h := by
    intro a ha
    simp only [roughRawCandidateSet, roughHighLowerBlock,
      roughBroadLowerBlock, Finset.mem_union, Finset.mem_Ioc] at ha
    omega
  have hupper :=
    sum_factorization_cast_eq_sum_primePowerDivisorCounts
      hupperPos hupperLe hp
  have hlower :=
    sum_weight_mul_factorization_cast_eq_sum_primePowerIndicators
      (roughHeadCompatibleRawWeight W n h K alpha beta ell)
      hrawPos hrawLe hp
  unfold roughCanonicalRawSignedValuationResidual
  rw [hupper, hlower, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [sum_roughHeadCompatibleRawWeight_mul_primePowerIndicator]
  unfold roughCanonicalRawPrimePowerColumnResidual
  ring

/-- One prime-power column has only the three literal endpoint errors left
after exact balanced main-term cancellation. -/
theorem abs_roughCanonicalRawPrimePowerColumnResidual_le
    {W n h K p k : Nat} {alpha beta ell : Real}
    (hKh : K * h <= n)
    (hnormalization :
      roughHeadDensity W *
          (alpha * ((K * h : Nat) : Real) +
            (beta / ell) * ((n - K * h : Nat) : Real)) =
        (h : Real))
    (hp : p.Prime) (hWp : W < p) :
    abs (roughCanonicalRawPrimePowerColumnResidual
      W n h K alpha beta ell p k) <=
      1 +
        abs alpha * ((roughHeadModulus W : Real) + 1) +
        abs (beta / ell) * ((roughHeadModulus W : Real) + 1) := by
  let D : Nat := p ^ k
  let U : Real :=
    (((roughUpperBlock n h).filter (fun a => p ^ k ∣ a)).card : Real)
  let H : Real :=
    ((coprimeMultipleIoc (roughHeadModulus W) (p ^ k)
      (2 * n - K * h) (2 * n)).card : Real)
  let J : Real :=
    ((coprimeMultipleIoc (roughHeadModulus W) (p ^ k)
      n (2 * n - K * h)).card : Real)
  let delta : Real := roughHeadDensity W
  let q : Real := beta / ell
  have hD : 0 < D := by
    exact pow_pos hp.pos k
  have hDReal : (0 : Real) < (D : Real) := by
    exact_mod_cast hD
  have hupperLength : 2 * n + h - 2 * n = h := by omega
  have hhighLength :
      2 * n - (2 * n - K * h) = K * h := by omega
  have hbroadLength :
      2 * n - K * h - n = n - K * h := by omega
  have hupper :
      abs (U - (h : Real) / (D : Real)) <= 1 := by
    dsimp only [U, D]
    simpa only [roughUpperBlock, hupperLength] using
      (Ioc_filter_dvd_card_sub_realLengthDiv_abs_lt_one
        (D := p ^ k) (lo := 2 * n) (hi := 2 * n + h)
        hD (by omega)).le
  have hhigh :
      abs (H - delta * ((K * h : Nat) : Real) / (D : Real)) <=
        (roughHeadModulus W : Real) + 1 := by
    dsimp only [H, delta, D]
    simpa only [hhighLength, mul_div_assoc] using
      (roughHeadPrimePowerMultipleIoc_card_error_le
        (W := W) (p := p) (k := k)
        (lo := 2 * n - K * h) (hi := 2 * n)
        hp hWp (by omega))
  have hbroad :
      abs (J - delta * ((n - K * h : Nat) : Real) / (D : Real)) <=
        (roughHeadModulus W : Real) + 1 := by
    dsimp only [J, delta, D]
    simpa only [hbroadLength, mul_div_assoc] using
      (roughHeadPrimePowerMultipleIoc_card_error_le
        (W := W) (p := p) (k := k)
        (lo := n) (hi := 2 * n - K * h)
        hp hWp (by omega))
  have hnormalization' :
      delta *
          (alpha * ((K * h : Nat) : Real) +
            q * ((n - K * h : Nat) : Real)) =
        (h : Real) := by
    simpa only [delta, q] using hnormalization
  have hsplit :
      U - alpha * H - q * J =
        (U - (h : Real) / (D : Real)) -
          alpha *
            (H - delta * ((K * h : Nat) : Real) / (D : Real)) -
          q *
            (J - delta * ((n - K * h : Nat) : Real) / (D : Real)) := by
    rw [← hnormalization']
    field_simp [hDReal.ne']
    ring
  unfold roughCanonicalRawPrimePowerColumnResidual
  change abs (U - alpha * H - q * J) <= _
  rw [hsplit]
  calc
    abs ((U - (h : Real) / (D : Real)) -
        alpha *
          (H - delta * ((K * h : Nat) : Real) / (D : Real)) -
        q *
          (J - delta * ((n - K * h : Nat) : Real) / (D : Real))) <=
      abs ((U - (h : Real) / (D : Real)) -
        alpha *
          (H - delta * ((K * h : Nat) : Real) / (D : Real))) +
      abs (q *
        (J - delta * ((n - K * h : Nat) : Real) / (D : Real))) :=
        abs_sub _ _
    _ <=
      (abs (U - (h : Real) / (D : Real)) +
        abs (alpha *
          (H - delta * ((K * h : Nat) : Real) / (D : Real)))) +
      abs (q *
        (J - delta * ((n - K * h : Nat) : Real) / (D : Real))) := by
      exact add_le_add
        (abs_sub
          (U - (h : Real) / (D : Real))
          (alpha *
            (H - delta * ((K * h : Nat) : Real) / (D : Real))))
        (le_refl (abs (q *
          (J - delta * ((n - K * h : Nat) : Real) / (D : Real)))))
    _ =
      abs (U - (h : Real) / (D : Real)) +
        abs alpha *
          abs (H - delta * ((K * h : Nat) : Real) / (D : Real)) +
        abs q *
          abs (J - delta * ((n - K * h : Nat) : Real) / (D : Real)) := by
      rw [abs_mul, abs_mul]
    _ <=
      1 +
        abs alpha * ((roughHeadModulus W : Real) + 1) +
        abs q * ((roughHeadModulus W : Real) + 1) := by
      gcongr
    _ =
      1 +
        abs alpha * ((roughHeadModulus W : Real) + 1) +
        abs (beta / ell) * ((roughHeadModulus W : Real) + 1) := by
      rfl

/-- Finite logarithmic bound for the complete raw signed valuation residual.
No asymptotic estimate occurs in this theorem. -/
theorem abs_roughCanonicalRawSignedValuationResidual_le_log_mul_columnBound
    {W n h K p : Nat} {alpha beta ell : Real}
    (hKh : K * h <= n)
    (hnormalization :
      roughHeadDensity W *
          (alpha * ((K * h : Nat) : Real) +
            (beta / ell) * ((n - K * h : Nat) : Real)) =
        (h : Real))
    (hp : p.Prime) (hWp : W < p) :
    abs (roughCanonicalRawSignedValuationResidual n h K
      (roughHeadCompatibleRawWeight W n h K alpha beta ell) p) <=
      (Nat.log p (2 * n + h) : Real) *
        (1 +
          abs alpha * ((roughHeadModulus W : Real) + 1) +
          abs (beta / ell) * ((roughHeadModulus W : Real) + 1)) := by
  rw [roughCanonicalRawSignedValuationResidual_eq_sum_primePowerColumns
    W n h K alpha beta ell p hp]
  calc
    abs (∑ k ∈ primeExponentRange p (2 * n + h),
        roughCanonicalRawPrimePowerColumnResidual
          W n h K alpha beta ell p k) <=
      ∑ k ∈ primeExponentRange p (2 * n + h),
        abs (roughCanonicalRawPrimePowerColumnResidual
          W n h K alpha beta ell p k) := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ <=
      ∑ _k ∈ primeExponentRange p (2 * n + h),
        (1 +
          abs alpha * ((roughHeadModulus W : Real) + 1) +
          abs (beta / ell) * ((roughHeadModulus W : Real) + 1)) := by
        apply Finset.sum_le_sum
        intro k _
        exact abs_roughCanonicalRawPrimePowerColumnResidual_le
          hKh hnormalization hp hWp
    _ =
      (Nat.log p (2 * n + h) : Real) *
        (1 +
          abs alpha * ((roughHeadModulus W : Real) + 1) +
          abs (beta / ell) * ((roughHeadModulus W : Real) + 1)) := by
        simp [primeExponentRange]
        ring

/-! ## Fixed constants for the balanced point -/

/-- Fixed upper bound for one prime-power column after inserting the
balanced coefficient and requiring `L n >= 1`. -/
noncomputable def roughCanonicalBalancedRawPrimePowerColumnConstant
    (W K0 : Nat) (c beta : Real) : Real :=
  1 +
    (roughBalancedAlphaConstant W K0 c beta + abs beta) *
      ((roughHeadModulus W : Real) + 1)

theorem roughCanonicalBalancedRawPrimePowerColumnConstant_nonneg
    (W K0 : Nat) {c beta : Real} (hc : 0 < c) :
    0 <= roughCanonicalBalancedRawPrimePowerColumnConstant
      W K0 c beta := by
  unfold roughCanonicalBalancedRawPrimePowerColumnConstant
  have hAlpha :
      0 <= roughBalancedAlphaConstant W K0 c beta :=
    roughBalancedAlphaConstant_nonneg W K0 (beta := beta) hc
  positivity

/-- The explicit constant in the eventual paper-rate bound.  The factor
`5 / log 2` converts the exponent count to the existing
`5 * log (yNat n)` endpoint chamber. -/
noncomputable def roughCanonicalBalancedRawSignedValuationConstant
    (W K0 : Nat) (c beta : Real) : Real :=
  (5 / Real.log 2) *
    roughCanonicalBalancedRawPrimePowerColumnConstant W K0 c beta

theorem roughCanonicalBalancedRawSignedValuationConstant_nonneg
    (W K0 : Nat) {c beta : Real} (hc : 0 < c) :
    0 <= roughCanonicalBalancedRawSignedValuationConstant
      W K0 c beta := by
  unfold roughCanonicalBalancedRawSignedValuationConstant
  exact mul_nonneg
    (div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le)
    (roughCanonicalBalancedRawPrimePowerColumnConstant_nonneg
      W K0 hc)

/-- The squared smooth cutoff is eventually bounded by the exact
`secondOrderScale / L` scale.  This is the stronger intermediate estimate
behind the previously exported linear cutoff bound. -/
theorem eventually_yNat_sq_le_secondOrderScale_div_L :
    ∀ᶠ n : Nat in atTop,
      (yNat n : Real) ^ 2 <= secondOrderScale n / L n := by
  have hratio := tendsto_endpointRatio_zero.eventually
    (eventually_lt_nhds (by norm_num : (0 : Real) < 1))
  filter_upwards [hratio, eventually_ge_atTop 2]
      with n hratioN hn
  have hnPos : 0 < n := by omega
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hnPos
  have hL : 0 < L n := L_pos hn
  have hyNonneg : 0 <= y n := (y_pos hnPos).le
  have hyFloor : (yNat n : Real) <= y n :=
    Nat.floor_le hyNonneg
  have hySq : (yNat n : Real) ^ 2 <= y n ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg _) hyNonneg).2 hyFloor
  have hratioNat :
      (yNat n : Real) ^ 2 * L n ^ 2 / (n : Real) <= 1 := by
    calc
      (yNat n : Real) ^ 2 * L n ^ 2 / (n : Real) <=
          y n ^ 2 * L n ^ 2 / (n : Real) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hySq (sq_nonneg _)) hnReal.le
      _ = endpointRatio n := by rfl
      _ <= 1 := hratioN.le
  have hySqScale :
      (yNat n : Real) ^ 2 <= (n : Real) / L n ^ 2 := by
    apply (le_div_iff₀ (pow_pos hL 2)).2
    have hcross := (div_le_iff₀ hnReal).1 hratioNat
    simpa only [one_mul] using hcross
  have htarget :
      (n : Real) / L n ^ 2 = secondOrderScale n / L n := by
    unfold secondOrderScale L
    ring
  exact hySqScale.trans_eq htarget

/-- The balanced one-column error is eventually bounded by the fixed
constant chosen before `n` and `p`. -/
theorem eventually_balancedRaw_primePowerColumnBound_le_constant
    (W K0 : Nat) {c beta : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      1 +
          abs (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n)) *
            ((roughHeadModulus W : Real) + 1) +
          abs (beta / L n) * ((roughHeadModulus W : Real) + 1) <=
        roughCanonicalBalancedRawPrimePowerColumnConstant
          W K0 c beta := by
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,
      hLTop.eventually (eventually_ge_atTop (1 : Real))]
      with n hn hL
  have halpha :
      abs (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n)) <=
        roughBalancedAlphaConstant W K0 c beta := by
    simpa only [roughBalancedAlphaConstant] using
      roughHeadBalancedAlpha_succ_abs_le W K0 (beta := beta) hc hn
  have hLPos : 0 < L n := zero_lt_one.trans_le hL
  have hbetaDiv : abs (beta / L n) <= abs beta := by
    rw [abs_div, abs_of_pos hLPos]
    apply (div_le_iff₀ hLPos).2
    nlinarith [abs_nonneg beta]
  have hperiod :
      0 <= (roughHeadModulus W : Real) + 1 := by positivity
  unfold roughCanonicalBalancedRawPrimePowerColumnConstant
  calc
    1 +
        abs (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n)) *
          ((roughHeadModulus W : Real) + 1) +
        abs (beta / L n) * ((roughHeadModulus W : Real) + 1) <=
      1 +
        roughBalancedAlphaConstant W K0 c beta *
          ((roughHeadModulus W : Real) + 1) +
        abs beta * ((roughHeadModulus W : Real) + 1) := by
      exact add_le_add
        (add_le_add le_rfl
          (mul_le_mul_of_nonneg_right halpha hperiod))
        (mul_le_mul_of_nonneg_right hbetaDiv hperiod)
    _ =
      1 +
        (roughBalancedAlphaConstant W K0 c beta + abs beta) *
          ((roughHeadModulus W : Real) + 1) := by ring

/-! ## Eventual paper-rate absorption -/

/-- Explicit eventual paper-rate estimate for the balanced raw signed
valuation residual, uniform over every medium prime above the fixed head. -/
theorem eventually_roughCanonicalBalancedRawSignedValuationResidualBound
    (W K0 : Nat) {c beta : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop, ∀ p : Nat,
      p.Prime -> W < p -> p <= yNat n ->
      RoughCanonicalBalancedRawSignedValuationResidualBound
        W n K0 c beta p
        (roughCanonicalBalancedRawSignedValuationConstant W K0 c beta *
          secondOrderScale n / ((p : Real) * L n)) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [
      eventually_ge_atTop 2,
      eventually_mul_upperTailLength_le_self (K0 + 1) hc,
      eventually_upperTailLength_pos hc,
      eventually_upperTailLength_le hc,
      hLTop.eventually (eventually_ge_atTop (1 : Real)),
      eventually_log_three_mul_natCast_le_five_log_yNat,
      eventually_yNat_sq_le_secondOrderScale_div_L,
      eventually_bankBottom_six_le_yNat,
      eventually_balancedRaw_primePowerColumnBound_le_constant
        W K0 hc]
      with n hn hKh htailPos htailLe hLOne hlogThree
        hySq hySix hcolumn
  intro p hp hWp hpY
  have hKhPos :
      0 < (K0 + 1) * upperTailLength c n :=
    Nat.mul_pos (by omega) htailPos
  have hfinite :=
    abs_roughCanonicalRawSignedValuationResidual_le_log_mul_columnBound
      (W := W) (n := n) (h := upperTailLength c n)
      (K := K0 + 1) (p := p)
      (alpha := roughHeadBalancedAlpha W n (upperTailLength c n)
        (K0 + 1) beta (L n))
      (beta := beta) (ell := L n)
      hKh
      (roughHeadBalancedAlpha_length_normalization
        (W := W) (n := n) (h := upperTailLength c n)
        (K := K0 + 1) (beta := beta) (L := L n) hKhPos)
      hp hWp
  have hcolumnNonneg :
      0 <= roughCanonicalBalancedRawPrimePowerColumnConstant
        W K0 c beta :=
    roughCanonicalBalancedRawPrimePowerColumnConstant_nonneg
      W K0 hc
  have hrawLog :
      abs (roughCanonicalRawSignedValuationResidual n
        (upperTailLength c n) (K0 + 1)
        (roughHeadCompatibleRawWeight W n (upperTailLength c n)
          (K0 + 1)
          (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n))
          beta (L n)) p) <=
        (Nat.log p (2 * n + upperTailLength c n) : Real) *
          roughCanonicalBalancedRawPrimePowerColumnConstant
            W K0 c beta := by
    exact hfinite.trans
      (mul_le_mul_of_nonneg_left hcolumn (Nat.cast_nonneg _))
  have hendpoint :
      2 * n + upperTailLength c n <= 3 * n := by omega
  have hendpointPos :
      0 < 2 * n + upperTailLength c n := by omega
  have hendpointReal :
      (2 * n + upperTailLength c n : Real) <=
        3 * (n : Real) := by
    exact_mod_cast hendpoint
  have hlogEndpoint :
      Real.log (2 * n + upperTailLength c n : Real) <=
        Real.log (3 * (n : Real)) :=
    Real.log_le_log (by exact_mod_cast hendpointPos) hendpointReal
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogCount :
      (Nat.log p (2 * n + upperTailLength c n) : Real) <=
        (5 / Real.log 2) * Real.log (yNat n : Real) := by
    calc
      (Nat.log p (2 * n + upperTailLength c n) : Real) <=
          (Nat.log 2 (2 * n + upperTailLength c n) : Real) := by
        exact_mod_cast
          (Nat.log_mono Nat.one_lt_two hp.two_le
            (le_refl (2 * n + upperTailLength c n)))
      _ <= Real.logb 2 (2 * n + upperTailLength c n : Nat) :=
        Real.natLog_le_logb (2 * n + upperTailLength c n) 2
      _ = Real.log (2 * n + upperTailLength c n : Real) /
          Real.log 2 := by
        simp only [Real.logb, Nat.cast_add, Nat.cast_mul,
          Nat.cast_ofNat]
      _ <= Real.log (3 * (n : Real)) / Real.log 2 :=
        (div_le_div_iff_of_pos_right hlogTwo).2 hlogEndpoint
      _ <= (5 * Real.log (yNat n : Real)) / Real.log 2 := by
        exact (div_le_div_iff_of_pos_right hlogTwo).2 hlogThree
      _ = (5 / Real.log 2) * Real.log (yNat n : Real) := by ring
  have hconstantNonneg :
      0 <= roughCanonicalBalancedRawSignedValuationConstant
        W K0 c beta :=
    roughCanonicalBalancedRawSignedValuationConstant_nonneg
      W K0 hc
  have hyPosNat : 0 < yNat n := by omega
  have hyPos : (0 : Real) < (yNat n : Real) := by
    exact_mod_cast hyPosNat
  have hlogYLeY :
      Real.log (yNat n : Real) <= (yNat n : Real) := by
    have hlogSub := Real.log_le_sub_one_of_pos hyPos
    linarith
  have hpReal : (0 : Real) < (p : Real) := by
    exact_mod_cast hp.pos
  have hpYReal : (p : Real) <= (yNat n : Real) := by
    exact_mod_cast hpY
  have hpMulY :
      (p : Real) * (yNat n : Real) <= (yNat n : Real) ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul_of_nonneg_right hpYReal (Nat.cast_nonneg _)
  have hLPos : 0 < L n := zero_lt_one.trans_le hLOne
  have hyTarget :
      (yNat n : Real) <=
        secondOrderScale n / ((p : Real) * L n) := by
    apply (le_div_iff₀ (mul_pos hpReal hLPos)).2
    calc
      (yNat n : Real) * ((p : Real) * L n) =
          ((p : Real) * (yNat n : Real)) * L n := by ring
      _ <= (yNat n : Real) ^ 2 * L n :=
        mul_le_mul_of_nonneg_right hpMulY hLPos.le
      _ <= (secondOrderScale n / L n) * L n :=
        mul_le_mul_of_nonneg_right hySq hLPos.le
      _ = secondOrderScale n := div_mul_cancel₀ _ hLPos.ne'
  unfold RoughCanonicalBalancedRawSignedValuationResidualBound
  calc
    abs (roughCanonicalRawSignedValuationResidual n
        (upperTailLength c n) (K0 + 1)
        (roughHeadCompatibleRawWeight W n (upperTailLength c n)
          (K0 + 1)
          (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n))
          beta (L n)) p) <=
      (Nat.log p (2 * n + upperTailLength c n) : Real) *
        roughCanonicalBalancedRawPrimePowerColumnConstant
          W K0 c beta := hrawLog
    _ <=
      ((5 / Real.log 2) * Real.log (yNat n : Real)) *
        roughCanonicalBalancedRawPrimePowerColumnConstant
          W K0 c beta :=
      mul_le_mul_of_nonneg_right hlogCount hcolumnNonneg
    _ =
      roughCanonicalBalancedRawSignedValuationConstant W K0 c beta *
        Real.log (yNat n : Real) := by
      unfold roughCanonicalBalancedRawSignedValuationConstant
      ring
    _ <=
      roughCanonicalBalancedRawSignedValuationConstant W K0 c beta *
        (yNat n : Real) :=
      mul_le_mul_of_nonneg_left hlogYLeY hconstantNonneg
    _ <=
      roughCanonicalBalancedRawSignedValuationConstant W K0 c beta *
        (secondOrderScale n / ((p : Real) * L n)) :=
      mul_le_mul_of_nonneg_left hyTarget hconstantNonneg
    _ =
      roughCanonicalBalancedRawSignedValuationConstant W K0 c beta *
          secondOrderScale n / ((p : Real) * L n) := by ring

/-- Existential packaging matching the remaining raw-input interface of the
generic four-term residual closure. -/
theorem
    exists_eventually_roughCanonicalBalancedRawSignedValuationResidualBound
    (W K0 : Nat) {c beta : Real} (hc : 0 < c) :
    ∃ Craw : Real, 0 <= Craw ∧
      ∀ᶠ n : Nat in atTop, ∀ p : Nat,
        p.Prime -> W < p -> p <= yNat n ->
        RoughCanonicalBalancedRawSignedValuationResidualBound
          W n K0 c beta p
          (Craw * secondOrderScale n / ((p : Real) * L n)) := by
  exact ⟨roughCanonicalBalancedRawSignedValuationConstant W K0 c beta,
    roughCanonicalBalancedRawSignedValuationConstant_nonneg W K0 hc,
    eventually_roughCanonicalBalancedRawSignedValuationResidualBound
      W K0 hc⟩

end BankPaperRealization

end

end Erdos390.WholePaper
