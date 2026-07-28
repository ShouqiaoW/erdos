import Erdos390.WholePaper.BankOrdinaryDonorRelation
import Erdos390.WholePaper.SafePrimeCounting
import Erdos390.WholePaper.SafeShortIntervalPrimeCounting

/-!
# Analytic supply for the ordinary bank

This file supplies the analytic half of the ordinary marker--donor argument.
The only prime-number input is the already audited cumulative estimate
`FriableAsymptotic.exists_primeLogSumUpTo_error_bound 3`.  We first turn its
two endpoint errors into a lower bound for an actual finite prime interval.
We then count the literal smooth donor window, sum the resulting occurrences,
and pass the exact marker-fiber bound through
`bankOccurrenceCeilDiv_le_markerCount`.

No asymptotic assertion is stored in a structure or accepted as a field.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Erdos390.Full.FriableAsymptotic

noncomputable section

/-! ## A cumulative-theta short-interval lemma -/

/-- The actual finite prime interval `(A,B]`. -/
def bankPrimeInterval (A B : ℕ) : Finset ℕ :=
  (Finset.Ioc A B).filter Nat.Prime

private theorem bankPrimeInterval_eq_logSumSupport (A B : ℕ) :
    bankPrimeInterval A B =
      (B + 1).primesBelow \ (A + 1).primesBelow := by
  ext p
  by_cases hp : p.Prime
  · simp only [bankPrimeInterval, Finset.mem_filter, Finset.mem_Ioc,
      Finset.mem_sdiff, Nat.mem_primesBelow, hp, and_true]
    omega
  · simp [bankPrimeInterval, Nat.mem_primesBelow, hp]

private theorem primeLogSumInterval_le_card_mul_log
    {A B : ℕ} :
    primeLogSumInterval A B ≤
      (bankPrimeInterval A B).card * Real.log (B : ℝ) := by
  rw [primeLogSumInterval, ← bankPrimeInterval_eq_logSumSupport]
  calc
    ∑ p ∈ bankPrimeInterval A B, Real.log (p : ℝ) ≤
        ∑ _p ∈ bankPrimeInterval A B, Real.log (B : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpmem := (Finset.mem_filter.mp hp)
      have hpIoc := Finset.mem_Ioc.mp hpmem.1
      exact Real.log_le_log (by exact_mod_cast hpmem.2.pos)
        (by exact_mod_cast hpIoc.2)
    _ = (bankPrimeInterval A B).card * Real.log (B : ℝ) := by
      simp

/-- A direct consequence of a two-endpoint cumulative theta error.  This is
the precise mechanism used below: no theorem about arbitrary short intervals
is imported or assumed. -/
theorem primeInterval_card_lower_of_logSum_error
    {C : ℝ} {X₀ A B : ℕ}
    (hC : 0 ≤ C)
    (hX₀ : 2 ≤ X₀)
    (herror : ∀ X, X₀ ≤ X →
      |primeLogSumUpTo X - (X : ℝ)| ≤
        C * ((X : ℝ) / Real.log (X : ℝ) ^ (3 : ℕ)))
    (hA : X₀ ≤ A) (hAB : A ≤ B)
    (hdominates :
      2 * C * ((B : ℝ) / Real.log (B : ℝ) ^ 3 +
        (A : ℝ) / Real.log (A : ℝ) ^ 3) ≤
          (B : ℝ) - (A : ℝ)) :
    ((B : ℝ) - (A : ℝ)) / (2 * Real.log (B : ℝ)) ≤
      (bankPrimeInterval A B).card := by
  have hA2 : 2 ≤ A := hX₀.trans hA
  have hB2 : 2 ≤ B := hA2.trans hAB
  have herrorR : ∀ X, X₀ ≤ X →
      |primeLogSumUpTo X - (X : ℝ)| ≤
        C * ((X : ℝ) / Real.log (X : ℝ) ^ (3 : ℝ)) := by
    intro X hX
    simpa [Real.rpow_natCast] using herror X hX
  have hinterval := primeLogSumInterval_error_bound herrorR hA
    (hA.trans hAB) hAB
  have hintervalNat :
      |primeLogSumInterval A B - ((B : ℝ) - (A : ℝ))| ≤
        C * ((B : ℝ) / Real.log (B : ℝ) ^ (3 : ℕ) +
          (A : ℝ) / Real.log (A : ℝ) ^ (3 : ℕ)) := by
    simpa [Real.rpow_natCast] using hinterval
  have hnonneg :
      0 ≤ C * ((B : ℝ) / Real.log (B : ℝ) ^ 3 +
        (A : ℝ) / Real.log (A : ℝ) ^ 3) := by
    positivity
  have hlower :
      ((B : ℝ) - (A : ℝ)) / 2 ≤
        primeLogSumInterval A B := by
    have habsLower := neg_le_of_abs_le hintervalNat
    nlinarith
  have hsumUpper := primeLogSumInterval_le_card_mul_log (A := A) (B := B)
  have hlogB : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  apply (div_le_iff₀ (mul_pos (by norm_num) hlogB)).2
  have hhalf := hlower.trans hsumUpper
  nlinarith

/-- The preceding finite lemma with constants obtained directly from the
audited power-three theta estimate. -/
theorem exists_primeInterval_card_lower_from_cumulativePNT :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, 2 ≤ X₀ ∧
      ∀ A B : ℕ, X₀ ≤ A → A ≤ B →
        2 * C * ((B : ℝ) / Real.log (B : ℝ) ^ 3 +
          (A : ℝ) / Real.log (A : ℝ) ^ 3) ≤
            (B : ℝ) - (A : ℝ) →
        ((B : ℝ) - (A : ℝ)) /
            (2 * Real.log (B : ℝ)) ≤
          (bankPrimeInterval A B).card := by
  obtain ⟨C, hC, X₀, hX₀⟩ :=
    exists_primeLogSumUpTo_error_bound (3 : ℝ)
  let X₁ : ℕ := max X₀ 2
  have hX₁2 : 2 ≤ X₁ := le_max_right _ _
  have hbound : ∀ X, X₁ ≤ X →
      |primeLogSumUpTo X - (X : ℝ)| ≤
        C * ((X : ℝ) / Real.log (X : ℝ) ^ (3 : ℕ)) := by
    intro X hX
    have hraw := hX₀ X ((le_max_left X₀ 2).trans hX)
    simpa [Real.rpow_natCast] using hraw
  exact ⟨C, hC, X₁, hX₁2, fun A B hA hAB hdom ↦
    primeInterval_card_lower_of_logSum_error hC.le hX₁2 hbound hA hAB hdom⟩

/-! ## The literal smooth donor window -/

/-- All integers in the shrunken rational donor window. -/
def bankOrdinaryBulkDonorIntegers (Q : ℚ) : Finset ℕ :=
  Finset.Icc ⌈7 * Q / 5⌉₊ ⌊29 * Q / 20⌋₊

/-- The actual `yNat n`-smooth integers in the shrunken donor window. -/
def bankOrdinarySmoothBulkDonors (n : ℕ) (Q : ℚ) : Finset ℕ :=
  (bankOrdinaryBulkDonorIntegers Q).filter
    fun u ↦ u ∈ Nat.smoothNumbers (yNat n + 1)

@[simp] theorem mem_bankOrdinaryBulkDonorIntegers
    {Q : ℚ} {u : ℕ} (hQ : 0 ≤ Q) :
    u ∈ bankOrdinaryBulkDonorIntegers Q ↔
      InOrdinaryBankBulkDonorWindow Q u := by
  simp only [bankOrdinaryBulkDonorIntegers, Finset.mem_Icc,
    InOrdinaryBankBulkDonorWindow]
  constructor
  · rintro ⟨hlower, hupper⟩
    have ha : 7 * Q / 5 ≤ (u : ℚ) :=
      (Nat.le_ceil (7 * Q / 5)).trans (by exact_mod_cast hlower)
    have hupperQ : (u : ℚ) ≤ (⌊29 * Q / 20⌋₊ : ℚ) := by
      exact_mod_cast hupper
    have hb : (u : ℚ) ≤ 29 * Q / 20 :=
      hupperQ.trans
        (Nat.floor_le (by positivity : 0 ≤ 29 * Q / 20))
    constructor <;> linarith
  · rintro ⟨hlower, hupper⟩
    constructor
    · apply Nat.ceil_le.mpr
      linarith
    · apply Nat.le_floor
      linarith

@[simp] theorem mem_bankOrdinarySmoothBulkDonors
    {n : ℕ} {Q : ℚ} {u : ℕ} (hQ : 0 ≤ Q) :
    u ∈ bankOrdinarySmoothBulkDonors n Q ↔
      InOrdinaryBankBulkDonorWindow Q u ∧
        u ∈ Nat.smoothNumbers (yNat n + 1) := by
  simp [bankOrdinarySmoothBulkDonors,
    mem_bankOrdinaryBulkDonorIntegers hQ]

private theorem bankOrdinaryBulkDonorIntegers_nonempty
    {Q : ℚ} (hQ : 20 < Q) :
    (bankOrdinaryBulkDonorIntegers Q).Nonempty := by
  have hQ0 : 0 ≤ Q := le_of_lt (by linarith : 0 < Q)
  have hgap : 7 * Q / 5 < 29 * Q / 20 - 1 := by linarith
  have hfloor : 29 * Q / 20 - 1 < (⌊29 * Q / 20⌋₊ : ℚ) :=
    Nat.sub_one_lt_floor _
  have hceil : ⌈7 * Q / 5⌉₊ ≤ ⌊29 * Q / 20⌋₊ := by
    apply Nat.ceil_le.mpr
    exact (hgap.trans hfloor).le
  exact ⟨⌈7 * Q / 5⌉₊, by
    simp [bankOrdinaryBulkDonorIntegers, hceil]⟩

private theorem bankOrdinaryBulkDonorIntegers_card_lower
    {Q : ℚ} (hQ : 100 ≤ Q) :
    (Q : ℝ) / 25 ≤ (bankOrdinaryBulkDonorIntegers Q).card := by
  have hQ20 : 20 < Q := lt_of_lt_of_le (by norm_num) hQ
  have hQ0 : 0 ≤ Q := by linarith
  have hfloor :
      (29 * Q / 20 : ℚ) - 1 < (⌊29 * Q / 20⌋₊ : ℚ) :=
    Nat.sub_one_lt_floor _
  have hceil :
      (⌈7 * Q / 5⌉₊ : ℚ) < 7 * Q / 5 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  rw [bankOrdinaryBulkDonorIntegers, Nat.card_Icc]
  have hle : ⌈7 * Q / 5⌉₊ ≤ ⌊29 * Q / 20⌋₊ + 1 := by
    have hbase : ⌈7 * Q / 5⌉₊ ≤ ⌊29 * Q / 20⌋₊ := by
      apply Nat.ceil_le.mpr
      exact (by linarith : 7 * Q / 5 ≤ (⌊29 * Q / 20⌋₊ : ℚ))
    omega
  rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one]
  have hcast :
      ((Q : ℝ) / 25) ≤
        ((⌊29 * Q / 20⌋₊ : ℕ) : ℝ) + 1 -
          ((⌈7 * Q / 5⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast (show
      (Q / 25 : ℚ) ≤
        (⌊29 * Q / 20⌋₊ : ℚ) + 1 -
          (⌈7 * Q / 5⌉₊ : ℚ) by
      linarith)
  simpa only [Nat.cast_ofNat] using hcast

/-- Below twice the smoothness cutoff, failure of smoothness forces the
integer itself to be a prime above the cutoff. -/
private theorem prime_of_bulkDonor_not_smooth
    {n u : ℕ} {Q : ℚ} (hQ : 20 < Q)
    (hQY : Q ≤ (yNat n : ℚ))
    (hu : u ∈ bankOrdinaryBulkDonorIntegers Q)
    (hnot : u ∉ Nat.smoothNumbers (yNat n + 1)) :
    u.Prime := by
  have hQ0 : 0 ≤ Q := by linarith
  have huWindow := (mem_bankOrdinaryBulkDonorIntegers hQ0).mp hu
  have hYpos : 0 < yNat n := by
    have : (20 : ℚ) < yNat n := hQ.trans_le hQY
    exact_mod_cast (show (0 : ℚ) < yNat n by linarith)
  have huPos : 0 < u := by
    have hposQ : (0 : ℚ) < 7 * Q := by positivity
    have huQ : (0 : ℚ) < u := by linarith [huWindow.1]
    exact_mod_cast huQ
  have huTwoY : u < 2 * yNat n := by
    have huQ : (u : ℚ) ≤ 29 * Q / 20 := by linarith [huWindow.2]
    have : (u : ℚ) < 2 * (yNat n : ℚ) := by
      have hYQ : (Q : ℚ) ≤ yNat n := hQY
      nlinarith
    exact_mod_cast this
  rw [Nat.mem_smoothNumbers'] at hnot
  push_neg at hnot
  obtain ⟨p, hp, hpdiv, hpLarge⟩ := hnot
  have hYp : yNat n < p := by omega
  have hpTwo : u < 2 * p := huTwoY.trans_le (Nat.mul_le_mul_left 2 hYp.le)
  rcases hpdiv with ⟨k, rfl⟩
  have hkPos : 0 < k := by
    by_contra hk
    simp only [Nat.not_lt, Nat.le_zero] at hk
    subst k
    simp at huPos
  have hkTwo : k < 2 := by
    apply (Nat.mul_lt_mul_left hp.pos).mp
    simpa only [Nat.mul_comm] using hpTwo
  have hk : k = 1 := by omega
  simpa only [hk, Nat.mul_one] using hp

/-- Exact loss estimate for smooth donors: every excluded donor injects into
the primes up to the upper endpoint of the donor window. -/
theorem bankOrdinaryBulkDonor_card_le_smooth_add_primeCounting
    {n : ℕ} {Q : ℚ} (hQ : 20 < Q)
    (hQY : Q ≤ (yNat n : ℚ)) :
    (bankOrdinaryBulkDonorIntegers Q).card ≤
      (bankOrdinarySmoothBulkDonors n Q).card +
        Nat.primeCounting ⌊29 * Q / 20⌋₊ := by
  let rough := (bankOrdinaryBulkDonorIntegers Q).filter
    fun u ↦ u ∉ Nat.smoothNumbers (yNat n + 1)
  have hrough : rough.card ≤ Nat.primeCounting ⌊29 * Q / 20⌋₊ := by
    have hmap : Set.MapsTo id (↑rough : Set ℕ)
        (↑((⌊29 * Q / 20⌋₊ + 1).primesBelow) : Set ℕ) := by
      intro u hu
      change u ∈ rough at hu
      have huData := Finset.mem_filter.mp hu
      have huPrime := prime_of_bulkDonor_not_smooth hQ hQY
        huData.1 huData.2
      have huUpper := (Finset.mem_Icc.mp huData.1).2
      change u ∈ (⌊29 * Q / 20⌋₊ + 1).primesBelow
      rw [Nat.mem_primesBelow]
      exact ⟨by omega, huPrime⟩
    have hinj : Set.InjOn id (↑rough : Set ℕ) :=
      Set.injOn_id (↑rough : Set ℕ)
    have hcard := Finset.card_le_card_of_injOn id hmap hinj
    simpa only [Nat.primeCounting, Nat.primeCounting',
      Nat.count_eq_card_filter_range, Nat.primesBelow] using hcard
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := bankOrdinaryBulkDonorIntegers Q)
    (fun u ↦ u ∈ Nat.smoothNumbers (yNat n + 1))
  change
    (bankOrdinarySmoothBulkDonors n Q).card + rough.card =
      (bankOrdinaryBulkDonorIntegers Q).card at hpartition
  omega

private theorem yNat_tendsto_atTop :
    Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : ℕ ↦ y n) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
      tendsto_natCast_atTop_atTop
  exact tendsto_nat_floor_atTop.comp hy

/-- Uniform positive density of smooth donor cofactors throughout the moving
range `20 < Q ≤ floor(n^(2/9))`.  The proof is literal: for large `Q` it
subtracts the Chebyshev upper bound for the nonsmooth primes, and for the
bounded remaining range eventual smoothness is exact. -/
theorem exists_eventually_bankOrdinarySmoothBulkDonors_lower :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ᶠ n : ℕ in atTop, ∀ Q : ℚ,
        20 < Q → Q ≤ (yNat n : ℚ) →
          delta * (Q : ℝ) ≤
            (bankOrdinarySmoothBulkDonors n Q).card := by
  let A : ℝ := Real.log 4 + 1
  have hA : 0 < A := by
    dsimp only [A]
    have := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    linarith
  have hprimeReal := Chebyshev.eventually_primeCounting_le
    (by norm_num : (0 : ℝ) < 1)
  have hlogReal : ∀ᶠ x : ℝ in atTop, 145 * A ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (145 * A))
  have hprimeNat : ∀ᶠ m : ℕ in atTop,
      (Nat.primeCounting m : ℝ) ≤
        A * (m : ℝ) / Real.log (m : ℝ) := by
    have h := tendsto_natCast_atTop_atTop.eventually hprimeReal
    filter_upwards [h] with m hm
    simpa only [Nat.floor_natCast, A] using hm
  have hlogNat : ∀ᶠ m : ℕ in atTop,
      145 * A ≤ Real.log (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogReal
  rw [eventually_atTop] at hprimeNat hlogNat
  obtain ⟨R₁, hR₁⟩ := hprimeNat
  obtain ⟨R₂, hR₂⟩ := hlogNat
  let R : ℕ := max 100 (max R₁ R₂)
  have hR100 : 100 ≤ R := le_max_left _ _
  have hRpos : 0 < R := by omega
  let delta : ℝ := 1 / (100 * (R : ℝ))
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  refine ⟨delta, hdelta, ?_⟩
  have hYevent :
      ∀ᶠ n : ℕ in atTop, ⌈29 * (R : ℚ) / 20⌉₊ ≤ yNat n :=
    yNat_tendsto_atTop.eventually
      (eventually_ge_atTop ⌈29 * (R : ℚ) / 20⌉₊)
  filter_upwards [hYevent] with n hYn
  intro Q hQ hQY
  have hQ0 : 0 ≤ Q := by linarith
  by_cases hlarge : (R : ℚ) ≤ Q
  · have hQ100 : (100 : ℚ) ≤ Q := by
      have h100R : (100 : ℚ) ≤ (R : ℚ) := by exact_mod_cast hR100
      exact h100R.trans hlarge
    have hraw := bankOrdinaryBulkDonorIntegers_card_lower hQ100
    let B : ℕ := ⌊29 * Q / 20⌋₊
    have hRB : R ≤ B := by
      apply Nat.le_floor
      have : (R : ℚ) ≤ 29 * Q / 20 := by nlinarith
      exact this
    have hR₁B : R₁ ≤ B :=
      (le_max_left R₁ R₂).trans
        ((le_max_right 100 (max R₁ R₂)).trans hRB)
    have hR₂B : R₂ ≤ B :=
      (le_max_right R₁ R₂).trans
        ((le_max_right 100 (max R₁ R₂)).trans hRB)
    have hpi := hR₁ B hR₁B
    have hlog := hR₂ B hR₂B
    have hBupperQ : (B : ℚ) ≤ 29 * Q / 20 := by
      exact Nat.floor_le (by positivity : 0 ≤ 29 * Q / 20)
    have hBupper : (B : ℝ) ≤ 29 * (Q : ℝ) / 20 := by
      exact_mod_cast hBupperQ
    have hlogPos : 0 < Real.log (B : ℝ) := lt_of_lt_of_le
      (mul_pos (by norm_num) hA) hlog
    have hpiSmall : (Nat.primeCounting B : ℝ) ≤ (Q : ℝ) / 100 := by
      calc
        (Nat.primeCounting B : ℝ) ≤
            A * (B : ℝ) / Real.log (B : ℝ) := hpi
        _ ≤ A * (29 * (Q : ℝ) / 20) / (145 * A) := by
          gcongr
        _ = (Q : ℝ) / 100 := by field_simp [hA.ne']; ring
    have hloss := bankOrdinaryBulkDonor_card_le_smooth_add_primeCounting
      hQ hQY
    have hsmooth :
        3 * (Q : ℝ) / 100 ≤
          (bankOrdinarySmoothBulkDonors n Q).card := by
      have hlossR :
          ((bankOrdinaryBulkDonorIntegers Q).card : ℝ) ≤
            (bankOrdinarySmoothBulkDonors n Q).card +
              Nat.primeCounting B := by exact_mod_cast hloss
      dsimp only [B] at hpiSmall hlossR
      nlinarith
    have hdeltaLe : delta ≤ 3 / 100 := by
      dsimp only [delta]
      have hRone : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 100 * R)).2
      nlinarith
    have hQ0R : (0 : ℝ) ≤ Q := by exact_mod_cast hQ0
    calc
      delta * (Q : ℝ) ≤ (3 / 100 : ℝ) * (Q : ℝ) :=
        mul_le_mul_of_nonneg_right hdeltaLe hQ0R
      _ = 3 * (Q : ℝ) / 100 := by ring
      _ ≤ (bankOrdinarySmoothBulkDonors n Q).card := hsmooth
  · have hQR : Q < (R : ℚ) := lt_of_not_ge hlarge
    have hsmoothEq : bankOrdinarySmoothBulkDonors n Q =
        bankOrdinaryBulkDonorIntegers Q := by
      apply Finset.filter_eq_self.mpr
      intro u hu
      apply Nat.mem_smoothNumbers_of_lt
      · have huWindow := (mem_bankOrdinaryBulkDonorIntegers hQ0).mp hu
        have huQ : (0 : ℚ) < u := by nlinarith [huWindow.1]
        exact_mod_cast huQ
      · have huUpper := (Finset.mem_Icc.mp hu).2
        have hfloorMono : ⌊29 * Q / 20⌋₊ ≤
            ⌈29 * (R : ℚ) / 20⌉₊ := by
          have hRat : (29 * Q / 20 : ℚ) ≤
              ⌈29 * (R : ℚ) / 20⌉₊ := by
            exact (le_of_lt (by nlinarith : 29 * Q / 20 < 29 * R / 20)).trans
              (Nat.le_ceil _)
          have hfloorQ : (⌊29 * Q / 20⌋₊ : ℚ) ≤ 29 * Q / 20 :=
            Nat.floor_le (by positivity)
          exact_mod_cast hfloorQ.trans hRat
        omega
    have hcardOne : 1 ≤ (bankOrdinarySmoothBulkDonors n Q).card := by
      rw [hsmoothEq]
      exact (bankOrdinaryBulkDonorIntegers_nonempty hQ).card_pos
    have hdeltaQ : delta * (Q : ℝ) ≤ 1 := by
      dsimp only [delta]
      have hQRreal : (Q : ℝ) ≤ (R : ℝ) := by
        exact_mod_cast hQR.le
      have hRreal : (0 : ℝ) < R := by exact_mod_cast hRpos
      calc
        1 / (100 * (R : ℝ)) * (Q : ℝ) ≤
            1 / (100 * (R : ℝ)) * (R : ℝ) := by gcongr
        _ = 1 / 100 := by field_simp [hRreal.ne']
        _ ≤ 1 := by norm_num
    exact hdeltaQ.trans (by exact_mod_cast hcardOne)

/-! ## Summing one-donor prime intervals -/

/-- Prime markers whose product with a fixed donor lies in `(2n,M]`. -/
def bankOrdinaryPrimeChoices (n M u : ℕ) : Finset ℕ :=
  bankPrimeInterval ((2 * n) / u) (M / u)

@[simp] theorem mem_bankOrdinaryPrimeChoices
    {n M u P : ℕ} (hu : 0 < u) :
    P ∈ bankOrdinaryPrimeChoices n M u ↔
      P.Prime ∧ 2 * n < P * u ∧ P * u ≤ M := by
  simp only [bankOrdinaryPrimeChoices, bankPrimeInterval,
    Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlower, hupper⟩, hprime⟩
    exact ⟨hprime,
      (by simpa only [Nat.mul_comm] using
        (Nat.div_lt_iff_lt_mul hu).1 hlower),
      (by simpa only [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le hu).1 hupper)⟩
  · rintro ⟨hprime, hlower, hupper⟩
    exact ⟨⟨(Nat.div_lt_iff_lt_mul hu).2 (by
      simpa only [Nat.mul_comm] using hlower),
      (Nat.le_div_iff_mul_le hu).2 (by
        simpa only [Nat.mul_comm] using hupper)⟩, hprime⟩

/-- The bulk occurrence relation contains the disjoint union of the prime
intervals supplied by every smooth donor in its literal window. -/
theorem sum_bankOrdinaryPrimeChoices_le_bulkRelation
    {n M : ℕ} {Q : ℚ} (hQ : 20 < Q) :
    ∑ u ∈ bankOrdinarySmoothBulkDonors n Q,
        (bankOrdinaryPrimeChoices n M u).card ≤
      (bankOrdinaryBulkRelation n M Q).card := by
  have hQpos : 0 < Q := by linarith
  have hQnonneg : 0 ≤ Q := hQpos.le
  have hmaps : Set.MapsTo Prod.snd
      (↑(bankOrdinaryBulkRelation n M Q) : Set (ℕ × ℕ))
      (↑(bankOrdinarySmoothBulkDonors n Q) : Set ℕ) := by
    intro pair hpair
    have hp := mem_bankOrdinaryBulkRelation.mp hpair
    exact (mem_bankOrdinarySmoothBulkDonors hQnonneg).mpr
      ⟨hp.2.2.2.1, hp.2.2.2.2.1⟩
  have hfiber : ∀ u ∈ bankOrdinarySmoothBulkDonors n Q,
      (bankOrdinaryPrimeChoices n M u).card ≤
        ((bankOrdinaryBulkRelation n M Q).filter
          fun pair ↦ pair.2 = u).card := by
    intro u hu
    have huData := (mem_bankOrdinarySmoothBulkDonors hQnonneg).mp hu
    have huPos : 0 < u := by
      have huQ : (0 : ℚ) < u := by nlinarith [huData.1.1]
      exact_mod_cast huQ
    apply Finset.card_le_card_of_injOn (fun P : ℕ ↦ (P, u))
    · intro P hP
      have hPData := (mem_bankOrdinaryPrimeChoices huPos).mp hP
      apply Finset.mem_filter.mpr
      constructor
      · rw [mem_bankOrdinaryBulkRelation]
        exact ⟨hQpos, hPData.1, huPos, huData.1, huData.2,
          hPData.2.1, hPData.2.2⟩
      · rfl
    · intro P _ P' _ hpair
      exact congrArg Prod.fst hpair
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  rw [hpartition]
  exact Finset.sum_le_sum fun u hu ↦ hfiber u hu

/-- The actual relation has at least the summed bulk occurrences whenever the
paper's endpoint is at most `2.1n`. -/
theorem sum_bankOrdinaryPrimeChoices_le_occurrenceTotal
    {n M : ℕ} {Q : ℚ} (hQ : 20 < Q)
    (hM : 10 * M ≤ 21 * n) :
    ∑ u ∈ bankOrdinarySmoothBulkDonors n Q,
        (bankOrdinaryPrimeChoices n M u).card ≤
      bankMarkerOccurrenceTotal (bankOrdinaryEligibleRelation n M Q) := by
  exact (sum_bankOrdinaryPrimeChoices_le_bulkRelation hQ).trans
    (Finset.card_le_card
      (bankOrdinaryBulkRelation_subset_eligible hM))

/-! ## Uniform one-donor geometry -/

private theorem cast_natDiv_le_realDiv (x q : ℕ) :
    ((x / q : ℕ) : ℝ) ≤ (x : ℝ) / (q : ℝ) :=
  Nat.cast_div_le

private theorem realDiv_sub_one_lt_cast_natDiv
    (x q : ℕ) (_hq : 0 < q) :
    (x : ℝ) / (q : ℝ) - 1 < ((x / q : ℕ) : ℝ) := by
  have hfloor :
      (x : ℝ) / (q : ℝ) < ((x / q : ℕ) : ℝ) + 1 := by
    simpa only [Nat.floor_div_eq_div] using
      (Nat.lt_floor_add_one ((x : ℝ) / (q : ℝ)))
  linarith

private theorem sevenNinthPower_div_log_tendsto_atTop :
    Tendsto
      (fun n : ℕ ↦
        (n : ℝ) ^ (7 / 9 : ℝ) / Real.log (n : ℝ))
      atTop atTop := by
  have hzeroReal : Tendsto
      (fun x : ℝ ↦ Real.log x / x ^ (7 / 9 : ℝ))
      atTop (nhds 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
        (by norm_num : (0 : ℝ) < 7 / 9)).tendsto_div_nhds_zero
  have hzero : Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) /
        (n : ℝ) ^ (7 / 9 : ℝ))
      atTop (nhds 0) := by
    simpa only [Function.comp_apply, Real.rpow_one] using
      hzeroReal.comp tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ n : ℕ in atTop,
      0 < Real.log (n : ℝ) / (n : ℝ) ^ (7 / 9 : ℝ) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact div_pos (Real.log_pos (by exact_mod_cast hn)) (by positivity)
  have hright : Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) /
        (n : ℝ) ^ (7 / 9 : ℝ))
      atTop (𝓝[>] (0 : ℝ)) := tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  apply hright.inv_tendsto_nhdsGT_zero.congr'
  exact Eventually.of_forall fun n ↦ by
    simp only [Pi.inv_apply, inv_div]

private theorem eventually_log_sq_ge (D : ℝ) :
    ∀ᶠ n : ℕ in atTop, D ≤ Real.log (n : ℝ) ^ 2 := by
  let r : ℝ := Real.sqrt (max D 0)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hlog : ∀ᶠ n : ℕ in atTop, r ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop r)
  filter_upwards [hlog] with n hn
  have hsqrt : r ^ 2 = max D 0 := by
    exact Real.sq_sqrt (le_max_right D 0)
  have hD : D ≤ r ^ 2 := by rw [hsqrt]; exact le_max_left _ _
  nlinarith

set_option maxHeartbeats 800000 in
private theorem eventually_bankOrdinary_oneDonor_geometry
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C) (X₀ : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      10 * upperTailLength c n ≤ n ∧
      (upperTailLength c n : ℝ) ≤
        2 * c * secondOrderScale n ∧
      ∀ Q : ℚ, 20 < Q → Q ≤ (yNat n : ℚ) →
        ∀ u : ℕ, InOrdinaryBankBulkDonorWindow Q u →
          let A := (2 * n) / u
          let B := upperEndpoint n (upperTailLength c n) / u
          X₀ ≤ A ∧ A ≤ B ∧
          c / 10 * (n : ℝ) /
              ((Q : ℝ) * Real.log (n : ℝ)) ≤
            (B : ℝ) - (A : ℝ) ∧
          (7 / 9 : ℝ) * Real.log (n : ℝ) ≤
            Real.log (A : ℝ) ∧
          Real.log (B : ℝ) ≤ 2 * Real.log (n : ℝ) ∧
          (B : ℝ) ≤
            3 / 2 * (n : ℝ) / (Q : ℝ) ∧
          2 * C * ((B : ℝ) / Real.log (B : ℝ) ^ 3 +
            (A : ℝ) / Real.log (A : ℝ) ^ 3) ≤
              (B : ℝ) - (A : ℝ) := by
  have htailLower : ∀ᶠ n : ℕ in atTop,
      c / 2 ≤ (upperTailLength c n : ℝ) / secondOrderScale n :=
    (upperTailLength_normalized_tendsto hc).eventually
      (eventually_ge_nhds (half_lt_self hc))
  have htailUpper : ∀ᶠ n : ℕ in atTop,
      (upperTailLength c n : ℝ) / secondOrderScale n ≤ 2 * c :=
    (upperTailLength_normalized_tendsto hc).eventually
      (eventually_le_nhds (by linarith : c < 2 * c))
  have htailSmall : ∀ᶠ n : ℕ in atTop,
      (upperTailLength c n : ℝ) / (n : ℝ) < 1 / 10 :=
    (upperTailLength_ratio_tendsto_zero hc).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 10))
  have hzTop : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ (7 / 9 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 9)).comp
      tendsto_natCast_atTop_atTop
  have hzLarge : ∀ᶠ n : ℕ in atTop,
      (max X₀ 3 : ℝ) ≤ (n : ℝ) ^ (7 / 9 : ℝ) :=
    hzTop.eventually (eventually_ge_atTop (max X₀ 3 : ℝ))
  have hratioLarge : ∀ᶠ n : ℕ in atTop,
      1 ≤ (71 * c / 290) *
        ((n : ℝ) ^ (7 / 9 : ℝ) / Real.log (n : ℝ)) := by
    have ht := (sevenNinthPower_div_log_tendsto_atTop.const_mul_atTop
      (by positivity : 0 < 71 * c / 290)).eventually
        (eventually_ge_atTop (1 : ℝ))
    simpa only [mul_div_assoc] using ht
  have herrorLarge : ∀ᶠ n : ℕ in atTop,
      60 * C ≤ c * (7 / 9 : ℝ) ^ 3 * Real.log (n : ℝ) ^ 2 := by
    have hsq := eventually_log_sq_ge
      (60 * C / (c * (7 / 9 : ℝ) ^ 3))
    filter_upwards [hsq] with n hn
    have hcoef : 0 < c * (7 / 9 : ℝ) ^ 3 := by positivity
    have hh := (div_le_iff₀ hcoef).mp (by simpa only using hn)
    calc
      60 * C ≤ Real.log (n : ℝ) ^ 2 *
          (c * (7 / 9 : ℝ) ^ 3) := hh
      _ = c * (7 / 9 : ℝ) ^ 3 * Real.log (n : ℝ) ^ 2 :=
        mul_comm _ _
  filter_upwards [eventually_gt_atTop 3, eventually_secondOrderScale_pos,
      htailLower, htailUpper, htailSmall, hzLarge, hratioLarge,
      herrorLarge] with n hn hscale htailLo htailHi htailRatio hz
        hratio herror
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogN : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have htailNat : 10 * upperTailLength c n ≤ n := by
    have hmul : (upperTailLength c n : ℝ) <
        (1 / 10 : ℝ) * (n : ℝ) :=
      (div_lt_iff₀ hnR).mp htailRatio
    have hmulLe : (10 : ℝ) * upperTailLength c n ≤ (n : ℝ) := by
      nlinarith
    exact_mod_cast hmulLe
  have htailCastUpper : (upperTailLength c n : ℝ) ≤
      2 * c * secondOrderScale n := by
    exact (div_le_iff₀ hscale).mp htailHi
  refine ⟨htailNat, htailCastUpper, ?_⟩
  intro Q hQ hQY u hu
  dsimp only
  have hQposRat : (0 : ℚ) < Q := by linarith
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQposRat
  have huRatPos : (0 : ℚ) < u := by nlinarith [hu.1]
  have huPos : 0 < u := by exact_mod_cast huRatPos
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast huPos
  have huLower : 7 * (Q : ℝ) ≤ 5 * (u : ℝ) := by
    exact_mod_cast hu.1
  have huUpper : 20 * (u : ℝ) ≤ 29 * (Q : ℝ) := by
    exact_mod_cast hu.2
  have hQYreal : (Q : ℝ) ≤ (yNat n : ℝ) := by
    exact_mod_cast hQY
  have hyNat : (yNat n : ℝ) ≤
      (n : ℝ) ^ (2 / 9 : ℝ) := by
    exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)
  have hQpow : (Q : ℝ) ≤ (n : ℝ) ^ (2 / 9 : ℝ) :=
    hQYreal.trans hyNat
  let z : ℝ := (n : ℝ) ^ (7 / 9 : ℝ)
  have hzPos : 0 < z := by dsimp only [z]; positivity
  have hpowProduct : (n : ℝ) ^ (2 / 9 : ℝ) * z = (n : ℝ) := by
    dsimp only [z]
    rw [← Real.rpow_add hnR]
    norm_num [Real.rpow_one]
  have hzQ : z ≤ (n : ℝ) / (Q : ℝ) := by
    apply (le_div_iff₀ hQpos).2
    calc
      z * (Q : ℝ) ≤ z * (n : ℝ) ^ (2 / 9 : ℝ) := by gcongr
      _ = (n : ℝ) := by rw [mul_comm, hpowProduct]
  have hzThree : 3 ≤ z := by
    exact le_trans (by exact_mod_cast (le_max_right X₀ 3)) hz
  let A : ℕ := (2 * n) / u
  let B : ℕ := upperEndpoint n (upperTailLength c n) / u
  have hAleReal : z ≤ (A : ℝ) := by
    have hdivLower := realDiv_sub_one_lt_cast_natDiv (2 * n) u huPos
    have hmain : 40 / 29 * z ≤
        (2 * (n : ℝ)) / (u : ℝ) := by
      apply (le_div_iff₀ huR).2
      have hnQ : z * (Q : ℝ) ≤ (n : ℝ) :=
        (le_div_iff₀ hQpos).mp hzQ
      nlinarith [huUpper]
    dsimp only [A]
    push_cast at hdivLower
    nlinarith
  have hX₀A : X₀ ≤ A := by
    have hXmax : (X₀ : ℝ) ≤ (max X₀ 3 : ℝ) := by
      exact_mod_cast (le_max_left X₀ 3)
    have hXz : (X₀ : ℝ) ≤ z := hXmax.trans hz
    have hXreal : (X₀ : ℝ) ≤ (A : ℝ) := hXz.trans hAleReal
    exact_mod_cast hXreal
  have hAB : A ≤ B := by
    dsimp only [A, B]
    exact Nat.div_le_div_right (two_mul_le_upperEndpoint n
      (upperTailLength c n))
  have hBLower := realDiv_sub_one_lt_cast_natDiv
    (upperEndpoint n (upperTailLength c n)) u huPos
  have hAUpper := cast_natDiv_le_realDiv (2 * n) u
  have htailLowerCast : c / 2 * secondOrderScale n ≤
      (upperTailLength c n : ℝ) := by
    exact (le_div_iff₀ hscale).mp htailLo
  have hwidth : c / 10 * (n : ℝ) /
        ((Q : ℝ) * Real.log (n : ℝ)) ≤
      (B : ℝ) - (A : ℝ) := by
    have hscaleEq : secondOrderScale n =
        (n : ℝ) / Real.log (n : ℝ) := rfl
    have htailDiv :
        10 * c / 29 * ((n : ℝ) /
          ((Q : ℝ) * Real.log (n : ℝ))) ≤
          (upperTailLength c n : ℝ) / (u : ℝ) := by
      apply (le_div_iff₀ huR).2
      calc
        (10 * c / 29 * ((n : ℝ) /
              ((Q : ℝ) * Real.log (n : ℝ)))) * (u : ℝ) =
            (c / 2 * ((n : ℝ) / Real.log (n : ℝ))) *
              (20 * (u : ℝ) / (29 * (Q : ℝ))) := by
                field_simp [hQpos.ne', hlogN.ne']
                ring
        _ ≤ (c / 2 * ((n : ℝ) / Real.log (n : ℝ))) * 1 := by
          gcongr
          apply (div_le_iff₀ (by positivity : (0 : ℝ) < 29 * Q)).2
          nlinarith [huUpper]
        _ = c / 2 * secondOrderScale n := by
          rw [secondOrderScale]
          ring
        _ ≤ (upperTailLength c n : ℝ) := htailLowerCast
    have hratioUse :
        1 ≤ 71 * c / 290 *
          ((n : ℝ) / ((Q : ℝ) * Real.log (n : ℝ))) := by
      calc
        1 ≤ 71 * c / 290 * (z / Real.log (n : ℝ)) := hratio
        _ ≤ 71 * c / 290 *
            ((n : ℝ) / ((Q : ℝ) * Real.log (n : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc
            z / Real.log (n : ℝ) ≤
                ((n : ℝ) / (Q : ℝ)) / Real.log (n : ℝ) :=
              div_le_div_of_nonneg_right hzQ hlogN.le
            _ = (n : ℝ) / ((Q : ℝ) * Real.log (n : ℝ)) := by
              field_simp [hQpos.ne', hlogN.ne']
    dsimp only [A, B] at hBLower hAUpper ⊢
    rw [upperEndpoint, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hBLower
    push_cast at hBLower hAUpper
    have hfloorGap : (upperTailLength c n : ℝ) / (u : ℝ) - 1 ≤
        ((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) -
          (((2 * n) / u : ℕ) : ℝ) := by
      calc
        (upperTailLength c n : ℝ) / (u : ℝ) - 1 =
            ((2 * (n : ℝ) + upperTailLength c n) / (u : ℝ) - 1) -
              (2 * (n : ℝ)) / (u : ℝ) := by ring
        _ ≤ ((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) -
              (((2 * n) / u : ℕ) : ℝ) := by
          apply sub_le_sub hBLower.le
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using hAUpper
    calc
      c / 10 * (n : ℝ) / ((Q : ℝ) * Real.log (n : ℝ)) =
          10 * c / 29 * ((n : ℝ) /
              ((Q : ℝ) * Real.log (n : ℝ))) -
            71 * c / 290 * ((n : ℝ) /
              ((Q : ℝ) * Real.log (n : ℝ))) := by ring
      _ ≤ (upperTailLength c n : ℝ) / (u : ℝ) - 1 :=
        sub_le_sub htailDiv hratioUse
      _ ≤ ((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) -
          (((2 * n) / u : ℕ) : ℝ) := hfloorGap
  have hlogA : (7 / 9 : ℝ) * Real.log (n : ℝ) ≤
      Real.log (A : ℝ) := by
    have hzLog : Real.log z =
        (7 / 9 : ℝ) * Real.log (n : ℝ) := by
      dsimp only [z]
      exact Real.log_rpow hnR (7 / 9 : ℝ)
    rw [← hzLog]
    exact Real.log_le_log hzPos hAleReal
  have hMcast : (upperEndpoint n (upperTailLength c n) : ℝ) ≤
      21 / 10 * (n : ℝ) := by
    rw [upperEndpoint, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have htailR : (upperTailLength c n : ℝ) ≤ (n : ℝ) / 10 := by
      have htailMul : (10 : ℝ) * upperTailLength c n ≤ (n : ℝ) := by
        exact_mod_cast htailNat
      nlinarith
    linarith
  have hBupper : (B : ℝ) ≤
      3 / 2 * (n : ℝ) / (Q : ℝ) := by
    have hdiv := cast_natDiv_le_realDiv
      (upperEndpoint n (upperTailLength c n)) u
    dsimp only [B]
    calc
      ((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) ≤
          (upperEndpoint n (upperTailLength c n) : ℝ) / (u : ℝ) := hdiv
      _ ≤ (21 / 10 * (n : ℝ)) / (7 / 5 * (Q : ℝ)) := by
        exact div_le_div₀ (by positivity) hMcast
          (by positivity : (0 : ℝ) < 7 / 5 * Q) (by nlinarith [huLower])
      _ = 3 / 2 * (n : ℝ) / (Q : ℝ) := by
        field_simp [hQpos.ne']
        ring
  have hlogB : Real.log (B : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hAcast : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
    have hBpos : 0 < (B : ℝ) := hzPos.trans_le (hAleReal.trans hAcast)
    have hBthree : (B : ℝ) ≤ 3 * (n : ℝ) := by
      have hQtwenty : (20 : ℝ) < Q := by exact_mod_cast hQ
      calc
        (B : ℝ) ≤ 3 / 2 * (n : ℝ) / (Q : ℝ) := hBupper
        _ ≤ 3 * (n : ℝ) := by
          apply (div_le_iff₀ hQpos).2
          nlinarith
    calc
      Real.log (B : ℝ) ≤ Real.log (3 * (n : ℝ)) :=
        Real.log_le_log hBpos hBthree
      _ = Real.log 3 + Real.log (n : ℝ) := by
        rw [Real.log_mul (by norm_num) hnR.ne']
      _ ≤ 2 * Real.log (n : ℝ) := by
        have : Real.log 3 ≤ Real.log (n : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hn.le)
        linarith
  have herrorDom :
      2 * C * ((B : ℝ) / Real.log (B : ℝ) ^ 3 +
        (A : ℝ) / Real.log (A : ℝ) ^ 3) ≤
          (B : ℝ) - (A : ℝ) := by
    have hlogApos : 0 < Real.log (A : ℝ) :=
      (mul_pos (by norm_num : (0 : ℝ) < 7 / 9) hlogN).trans_le hlogA
    have hlogAle : Real.log (A : ℝ) ≤ Real.log (B : ℝ) := by
      exact Real.log_le_log (hzPos.trans_le hAleReal) (by exact_mod_cast hAB)
    have hAcast : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
    have hbaseLogPos : 0 < (7 / 9 : ℝ) * Real.log (n : ℝ) :=
      mul_pos (by norm_num) hlogN
    have hbaseLogA : (7 / 9 : ℝ) * Real.log (n : ℝ) ≤
        Real.log (A : ℝ) := hlogA
    have hbaseLogB : (7 / 9 : ℝ) * Real.log (n : ℝ) ≤
        Real.log (B : ℝ) := hbaseLogA.trans hlogAle
    have hsum :
        (B : ℝ) / Real.log (B : ℝ) ^ 3 +
          (A : ℝ) / Real.log (A : ℝ) ^ 3 ≤
        3 * (n : ℝ) /
          ((Q : ℝ) * ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3) := by
      have htermB : (B : ℝ) / Real.log (B : ℝ) ^ 3 ≤
          (B : ℝ) / ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3 := by
        exact div_le_div_of_nonneg_left (by positivity)
          (pow_pos hbaseLogPos 3)
          (pow_le_pow_left₀ hbaseLogPos.le hbaseLogB 3)
      have htermA : (A : ℝ) / Real.log (A : ℝ) ^ 3 ≤
          (B : ℝ) / ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3 := by
        calc
          (A : ℝ) / Real.log (A : ℝ) ^ 3 ≤
              (B : ℝ) / Real.log (A : ℝ) ^ 3 :=
            div_le_div_of_nonneg_right hAcast (by positivity)
          _ ≤ (B : ℝ) / ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3 :=
            div_le_div_of_nonneg_left (by positivity)
              (pow_pos hbaseLogPos 3)
              (pow_le_pow_left₀ hbaseLogPos.le hbaseLogA 3)
      calc
        _ ≤ (B : ℝ) / ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3 +
            (B : ℝ) / ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3 :=
          add_le_add htermB htermA
        _ = 2 * (B : ℝ) /
            ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3 := by ring
        _ ≤ 3 * (n : ℝ) /
            ((Q : ℝ) * ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3) := by
          have hnum : 2 * (B : ℝ) ≤ 3 * (n : ℝ) / (Q : ℝ) := by
            calc
              2 * (B : ℝ) ≤ 2 * (3 / 2 * (n : ℝ) / (Q : ℝ)) :=
                mul_le_mul_of_nonneg_left hBupper (by norm_num)
              _ = 3 * (n : ℝ) / (Q : ℝ) := by ring
          calc
            2 * (B : ℝ) / ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3 ≤
                (3 * (n : ℝ) / (Q : ℝ)) /
                  ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3 :=
              div_le_div_of_nonneg_right hnum (by positivity)
            _ = 3 * (n : ℝ) /
                ((Q : ℝ) * ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3) := by
              field_simp [hQpos.ne']
    calc
      2 * C * ((B : ℝ) / Real.log (B : ℝ) ^ 3 +
          (A : ℝ) / Real.log (A : ℝ) ^ 3) ≤
          2 * C * (3 * (n : ℝ) /
            ((Q : ℝ) * ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3)) := by
        gcongr
      _ ≤ c / 10 * (n : ℝ) /
          ((Q : ℝ) * Real.log (n : ℝ)) := by
        calc
          2 * C * (3 * (n : ℝ) /
              ((Q : ℝ) * ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3)) =
            (60 * C) * ((n : ℝ) /
              (10 * (Q : ℝ) *
                ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3)) := by ring
          _ ≤ (c * (7 / 9 : ℝ) ^ 3 * Real.log (n : ℝ) ^ 2) *
              ((n : ℝ) /
                (10 * (Q : ℝ) *
                  ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3)) :=
            mul_le_mul_of_nonneg_right herror (by positivity)
          _ = c / 10 * (n : ℝ) /
              ((Q : ℝ) * Real.log (n : ℝ)) := by
            field_simp [hQpos.ne', hlogN.ne']
      _ ≤ (B : ℝ) - (A : ℝ) := hwidth
  exact ⟨hX₀A, hAB, hwidth, hlogA, hlogB, hBupper, herrorDom⟩

/-- Uniform prime supply for each actual smooth donor, including moving
rational scales all the way up to `floor(n^(2/9))`. -/
theorem exists_eventually_bankOrdinaryPrimeChoices_lower
    {c : ℝ} (hc : 0 < c) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ᶠ n : ℕ in atTop, ∀ Q : ℚ,
        20 < Q → Q ≤ (yNat n : ℚ) →
          ∀ u ∈ bankOrdinarySmoothBulkDonors n Q,
            kappa * secondOrderScale n /
                ((Q : ℝ) * Real.log (n : ℝ)) ≤
              (bankOrdinaryPrimeChoices n
                (upperEndpoint n (upperTailLength c n)) u).card := by
  obtain ⟨C, hC, X₀, hX₀, hshort⟩ :=
    exists_primeInterval_card_lower_from_cumulativePNT
  let kappa : ℝ := c / 40
  refine ⟨kappa, by dsimp only [kappa]; positivity, ?_⟩
  have hgeometry := eventually_bankOrdinary_oneDonor_geometry hc hC X₀
  filter_upwards [hgeometry, eventually_gt_atTop 3] with n hgeom hn
  intro Q hQ hQY u hu
  have hQ0 : 0 ≤ Q := by linarith
  have hQpos : (0 : ℝ) < (Q : ℝ) := by
    exact_mod_cast (show (0 : ℚ) < Q by linarith)
  have huData := (mem_bankOrdinarySmoothBulkDonors hQ0).mp hu
  have hg := hgeom.2.2 Q hQ hQY u huData.1
  let A : ℕ := (2 * n) / u
  let B : ℕ := upperEndpoint n (upperTailLength c n) / u
  change kappa * secondOrderScale n /
      ((Q : ℝ) * Real.log (n : ℝ)) ≤
    (bankPrimeInterval A B).card
  have hprime := hshort A B hg.1 hg.2.1 hg.2.2.2.2.2.2
  have hlogN : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogA : 0 < Real.log (A : ℝ) :=
    (mul_pos (by norm_num : (0 : ℝ) < 7 / 9) hlogN).trans_le
      hg.2.2.2.1
  have hApos : 0 < (A : ℝ) := by
    exact_mod_cast (show 0 < A by omega)
  have hlogB : 0 < Real.log (B : ℝ) :=
    hlogA.trans_le (Real.log_le_log hApos
      (by exact_mod_cast hg.2.1))
  calc
    kappa * secondOrderScale n /
        ((Q : ℝ) * Real.log (n : ℝ)) =
      c / 40 * (n : ℝ) /
        ((Q : ℝ) * Real.log (n : ℝ) ^ 2) := by
          dsimp only [kappa, secondOrderScale]
          field_simp
    _ ≤ ((B : ℝ) - (A : ℝ)) /
        (2 * Real.log (B : ℝ)) := by
      have hwidth := hg.2.2.1
      have hlogUpper := hg.2.2.2.2.1
      apply (le_div_iff₀ (mul_pos (by norm_num) hlogB)).2
      calc
        (c / 40 * (n : ℝ) /
            ((Q : ℝ) * Real.log (n : ℝ) ^ 2)) *
              (2 * Real.log (B : ℝ)) ≤
            (c / 40 * (n : ℝ) /
              ((Q : ℝ) * Real.log (n : ℝ) ^ 2)) *
                (4 * Real.log (n : ℝ)) := by
          have hbase : 0 ≤ c / 40 * (n : ℝ) /
              ((Q : ℝ) * Real.log (n : ℝ) ^ 2) := by positivity
          apply mul_le_mul_of_nonneg_left _ hbase
          linarith
        _ = c / 10 * (n : ℝ) /
              ((Q : ℝ) * Real.log (n : ℝ)) := by
          field_simp [hQpos.ne', hlogN.ne']; ring
        _ ≤ (B : ℝ) - (A : ℝ) := hwidth
    _ ≤ (bankPrimeInterval A B).card := hprime

/-- Uniform lower bound for the total number of actual ordinary-bank
marker--donor occurrences at every moving large scale. -/
theorem exists_eventually_bankOrdinary_occurrenceTotal_lower
    {c : ℝ} (hc : 0 < c) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ᶠ n : ℕ in atTop, ∀ Q : ℚ,
        20 < Q → Q ≤ (yNat n : ℚ) →
          eta * secondOrderScale n / Real.log (n : ℝ) ≤
            (bankMarkerOccurrenceTotal
              (bankOrdinaryEligibleRelation n
                (upperEndpoint n (upperTailLength c n)) Q) : ℝ) := by
  obtain ⟨delta, hdelta, hdonors⟩ :=
    exists_eventually_bankOrdinarySmoothBulkDonors_lower
  obtain ⟨kappa, hkappa, hprime⟩ :=
    exists_eventually_bankOrdinaryPrimeChoices_lower hc
  let eta : ℝ := delta * kappa
  refine ⟨eta, mul_pos hdelta hkappa, ?_⟩
  have htailSmall : ∀ᶠ n : ℕ in atTop,
      10 * upperTailLength c n ≤ n := by
    have hratio := (upperTailLength_ratio_tendsto_zero hc).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 10))
    filter_upwards [hratio, eventually_gt_atTop 0] with n hn hnpos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hmul : (upperTailLength c n : ℝ) <
        (1 / 10 : ℝ) * (n : ℝ) := (div_lt_iff₀ hnR).mp hn
    have hmulLe : (10 : ℝ) * upperTailLength c n ≤ (n : ℝ) := by
      nlinarith
    exact_mod_cast hmulLe
  filter_upwards [hdonors, hprime, htailSmall,
      eventually_gt_atTop 3, eventually_secondOrderScale_pos] with
      n hdonorN hprimeN htailN hn hscale
  intro Q hQ hQY
  have hQreal : 0 < (Q : ℝ) := by
    exact_mod_cast (show (0 : ℚ) < Q by linarith)
  have hlogN : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  let donors := bankOrdinarySmoothBulkDonors n Q
  let M := upperEndpoint n (upperTailLength c n)
  have hM : 10 * M ≤ 21 * n := by
    dsimp only [M, upperEndpoint]
    omega
  have hfinite := sum_bankOrdinaryPrimeChoices_le_occurrenceTotal hQ hM
  have hdonor := hdonorN Q hQ hQY
  have hone : ∀ u ∈ donors,
      kappa * secondOrderScale n /
          ((Q : ℝ) * Real.log (n : ℝ)) ≤
        ((bankOrdinaryPrimeChoices n M u).card : ℝ) := by
    intro u hu
    exact hprimeN Q hQ hQY u hu
  have hsum :
      (donors.card : ℝ) *
          (kappa * secondOrderScale n /
            ((Q : ℝ) * Real.log (n : ℝ))) ≤
        ∑ u ∈ donors, ((bankOrdinaryPrimeChoices n M u).card : ℝ) := by
    calc
      (donors.card : ℝ) *
          (kappa * secondOrderScale n /
            ((Q : ℝ) * Real.log (n : ℝ))) =
        ∑ _u ∈ donors,
          kappa * secondOrderScale n /
            ((Q : ℝ) * Real.log (n : ℝ)) := by simp
      _ ≤ _ := Finset.sum_le_sum fun u hu ↦ hone u hu
  have hsumFinite :
      ∑ u ∈ donors, ((bankOrdinaryPrimeChoices n M u).card : ℝ) ≤
        (bankMarkerOccurrenceTotal
          (bankOrdinaryEligibleRelation n M Q) : ℝ) := by
    exact_mod_cast hfinite
  calc
    eta * secondOrderScale n / Real.log (n : ℝ) =
        (delta * (Q : ℝ)) *
          (kappa * secondOrderScale n /
            ((Q : ℝ) * Real.log (n : ℝ))) := by
      dsimp only [eta]
      field_simp [hQreal.ne', hlogN.ne']
    _ ≤ (donors.card : ℝ) *
          (kappa * secondOrderScale n /
            ((Q : ℝ) * Real.log (n : ℝ))) := by
      exact mul_le_mul_of_nonneg_right hdonor (by positivity)
    _ ≤ ∑ u ∈ donors,
        ((bankOrdinaryPrimeChoices n M u).card : ℝ) := hsum
    _ ≤ (bankMarkerOccurrenceTotal
        (bankOrdinaryEligibleRelation n M Q) : ℝ) := hsumFinite

/-- Fixed large scales are a direct specialization of the same uniform
moving-scale theorem. -/
theorem bankOrdinary_fixedScale_occurrenceTotal_lower
    {c : ℝ} (hc : 0 < c) {Q : ℚ} (hQ : 20 < Q) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ᶠ n : ℕ in atTop,
        eta * secondOrderScale n / Real.log (n : ℝ) ≤
          (bankMarkerOccurrenceTotal
            (bankOrdinaryEligibleRelation n
              (upperEndpoint n (upperTailLength c n)) Q) : ℝ) := by
  obtain ⟨eta, heta, hsupply⟩ :=
    exists_eventually_bankOrdinary_occurrenceTotal_lower hc
  have hQevent : ∀ᶠ n : ℕ in atTop, Q ≤ (yNat n : ℚ) := by
    have hY := yNat_tendsto_atTop.eventually
      (eventually_ge_atTop ⌈Q⌉₊)
    filter_upwards [hY] with n hn
    exact (Nat.le_ceil Q).trans (by exact_mod_cast hn)
  refine ⟨eta, heta, ?_⟩
  filter_upwards [hsupply, hQevent] with n hn hQn
  exact hn Q hQ hQn

/-- Sequence form for a genuinely moving rational scale. -/
theorem bankOrdinary_movingScale_occurrenceTotal_lower
    {c : ℝ} (hc : 0 < c) (Q : ℕ → ℚ)
    (hQ : ∀ᶠ n : ℕ in atTop,
      20 < Q n ∧ Q n ≤ (yNat n : ℚ)) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ᶠ n : ℕ in atTop,
        eta * secondOrderScale n / Real.log (n : ℝ) ≤
          (bankMarkerOccurrenceTotal
            (bankOrdinaryEligibleRelation n
              (upperEndpoint n (upperTailLength c n)) (Q n)) : ℝ) := by
  obtain ⟨eta, heta, hsupply⟩ :=
    exists_eventually_bankOrdinary_occurrenceTotal_lower hc
  refine ⟨eta, heta, ?_⟩
  filter_upwards [hsupply, hQ] with n hn hQn
  exact hn (Q n) hQn.1 hQn.2

/-! ## Marker supply from the exact fiber bound -/

/-- A convenient integral cap for the donor multiplicity of one marker. -/
def bankOrdinaryMultiplicityCap (c : ℝ) (n : ℕ) (Q : ℚ) : ℕ :=
  ⌈2 * c * (Q : ℝ) / Real.log (n : ℝ) + 2⌉₊

private theorem cast_div_sub_div_le_tail_div_add_one
    {n h P : ℕ} (hP : 0 < P) :
    (((upperEndpoint n h) / P - (2 * n) / P : ℕ) : ℝ) ≤
      (h : ℝ) / (P : ℝ) + 1 := by
  have hAB : (2 * n) / P ≤ upperEndpoint n h / P :=
    Nat.div_le_div_right (two_mul_le_upperEndpoint n h)
  rw [Nat.cast_sub hAB]
  have hupper := cast_natDiv_le_realDiv (upperEndpoint n h) P
  have hlower := realDiv_sub_one_lt_cast_natDiv (2 * n) P hP
  have hupper' : ((upperEndpoint n h / P : ℕ) : ℝ) ≤
      (2 * (n : ℝ)) / (P : ℝ) + (h : ℝ) / (P : ℝ) := by
    calc
      _ ≤ (upperEndpoint n h : ℝ) / (P : ℝ) := hupper
      _ = (2 * (n : ℝ)) / (P : ℝ) + (h : ℝ) / (P : ℝ) := by
        rw [upperEndpoint, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        ring
  have hlower' : (2 * (n : ℝ)) / (P : ℝ) - 1 <
      (((2 * n) / P : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlower
  calc
    ((upperEndpoint n h / P : ℕ) : ℝ) - (((2 * n) / P : ℕ) : ℝ) ≤
        ((2 * (n : ℝ)) / (P : ℝ) + (h : ℝ) / (P : ℝ)) -
          ((2 * (n : ℝ)) / (P : ℝ) - 1) :=
      sub_le_sub hupper' hlower'.le
    _ = (h : ℝ) / (P : ℝ) + 1 := by ring

private theorem eventually_bankOrdinary_multiplicity_le_cap
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ Q : ℚ,
      20 < Q → Q ≤ (yNat n : ℚ) →
        0 < bankOrdinaryMultiplicityCap c n Q ∧
        ∀ P ∈ bankEligibleMarkers
            (bankOrdinaryEligibleRelation n
              (upperEndpoint n (upperTailLength c n)) Q),
          bankDonorMultiplicity
              (bankOrdinaryEligibleRelation n
                (upperEndpoint n (upperTailLength c n)) Q) P ≤
            bankOrdinaryMultiplicityCap c n Q := by
  have htailUpper : ∀ᶠ n : ℕ in atTop,
      (upperTailLength c n : ℝ) / secondOrderScale n ≤ 2 * c :=
    (upperTailLength_normalized_tendsto hc).eventually
      (eventually_le_nhds (by linarith : c < 2 * c))
  filter_upwards [htailUpper, eventually_secondOrderScale_pos,
      eventually_gt_atTop 3] with n htail hscale hn
  intro Q hQ _hQY
  have hQposRat : (0 : ℚ) < Q := by linarith
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQposRat
  have hlogN : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hcapPos : 0 < bankOrdinaryMultiplicityCap c n Q := by
    have hone : (1 : ℝ) ≤
        2 * c * (Q : ℝ) / Real.log (n : ℝ) + 2 := by
      have : 0 < 2 * c * (Q : ℝ) / Real.log (n : ℝ) := by positivity
      linarith
    have hceil : (1 : ℝ) ≤
        (⌈2 * c * (Q : ℝ) / Real.log (n : ℝ) + 2⌉₊ : ℝ) :=
      hone.trans (Nat.le_ceil _)
    exact_mod_cast hceil
  refine ⟨hcapPos, ?_⟩
  intro P hPmarker
  rcases Finset.mem_image.mp hPmarker with ⟨⟨P', u⟩, hpair, hfirst⟩
  dsimp only [Prod.fst] at hfirst
  subst P'
  have hpData := mem_bankOrdinaryEligibleRelation.mp hpair
  have hPpos : 0 < P := hpData.2.1.pos
  have hmarker := hpData.2.2.2.1
  have hfiber := bankOrdinary_donorMultiplicity_le_div_sub_div
    (n := n) (M := upperEndpoint n (upperTailLength c n))
    (Q := Q) hPpos
  have hfiberCast :
      (bankDonorMultiplicity
        (bankOrdinaryEligibleRelation n
          (upperEndpoint n (upperTailLength c n)) Q) P : ℝ) ≤
        (upperTailLength c n : ℝ) / (P : ℝ) + 1 := by
    have hfiberR :
        (bankDonorMultiplicity
          (bankOrdinaryEligibleRelation n
            (upperEndpoint n (upperTailLength c n)) Q) P : ℝ) ≤
          (((upperEndpoint n (upperTailLength c n)) / P -
            (2 * n) / P : ℕ) : ℝ) := by
      exact_mod_cast hfiber
    exact hfiberR.trans (cast_div_sub_div_le_tail_div_add_one hPpos)
  have htailCast : (upperTailLength c n : ℝ) ≤
      2 * c * secondOrderScale n :=
    (div_le_iff₀ hscale).mp htail
  have hmarkerQ :
      4 * (n : ℝ) < 3 * (Q : ℝ) * (P : ℝ) := by
    exact_mod_cast hmarker.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hPcast : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hratio :
      (upperTailLength c n : ℝ) / (P : ℝ) ≤
        3 * c / 2 * (Q : ℝ) / Real.log (n : ℝ) := by
    rw [secondOrderScale] at htailCast
    apply (div_le_iff₀ hPcast).2
    calc
      (upperTailLength c n : ℝ) ≤
          2 * c * ((n : ℝ) / Real.log (n : ℝ)) := htailCast
      _ ≤ (3 * c / 2 * (Q : ℝ) / Real.log (n : ℝ)) * (P : ℝ) := by
        field_simp [hlogN.ne']
        nlinarith [hmarkerQ]
  have htoCeil :
      (bankDonorMultiplicity
        (bankOrdinaryEligibleRelation n
          (upperEndpoint n (upperTailLength c n)) Q) P : ℝ) ≤
        (bankOrdinaryMultiplicityCap c n Q : ℝ) := by
    calc
      _ ≤ (upperTailLength c n : ℝ) / (P : ℝ) + 1 := hfiberCast
      _ ≤ 2 * c * (Q : ℝ) / Real.log (n : ℝ) + 2 := by
        have hnonneg : 0 ≤ c * (Q : ℝ) / Real.log (n : ℝ) := by positivity
        have hratio' : (upperTailLength c n : ℝ) / (P : ℝ) ≤
            (3 / 2 : ℝ) * (c * (Q : ℝ) / Real.log (n : ℝ)) := by
          calc
            _ ≤ 3 * c / 2 * (Q : ℝ) / Real.log (n : ℝ) := hratio
            _ = (3 / 2 : ℝ) *
                (c * (Q : ℝ) / Real.log (n : ℝ)) := by ring
        calc
          (upperTailLength c n : ℝ) / (P : ℝ) + 1 ≤
              (3 / 2 : ℝ) *
                (c * (Q : ℝ) / Real.log (n : ℝ)) + 1 :=
            by simpa only [add_comm] using add_le_add_right hratio' 1
          _ ≤ 2 * (c * (Q : ℝ) / Real.log (n : ℝ)) + 2 := by
            nlinarith
          _ = 2 * c * (Q : ℝ) / Real.log (n : ℝ) + 2 := by ring
      _ ≤ (bankOrdinaryMultiplicityCap c n Q : ℝ) := by
        exact Nat.le_ceil _
  exact_mod_cast htoCeil

/-- Exact finite-combinatorial form of the marker lower bound. -/
theorem eventually_bankOrdinary_occurrenceCeilDiv_le_markerCount
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ Q : ℚ,
      20 < Q → Q ≤ (yNat n : ℚ) →
        bankMarkerOccurrenceTotal
            (bankOrdinaryEligibleRelation n
              (upperEndpoint n (upperTailLength c n)) Q) ⌈/⌉
            bankOrdinaryMultiplicityCap c n Q ≤
          bankEligibleMarkerCount
            (bankOrdinaryEligibleRelation n
              (upperEndpoint n (upperTailLength c n)) Q) := by
  filter_upwards [eventually_bankOrdinary_multiplicity_le_cap hc] with n hn
  intro Q hQ hQY
  exact bankOccurrenceCeilDiv_le_markerCount _ _
    (hn Q hQ hQY).1 (hn Q hQ hQY).2

/-- The paper's marker-signature lower bound
`K_Q ≫_c (n/log n)/max(Q,log n)`, uniformly for fixed or moving
`20 < Q ≤ n^(2/9)`. -/
theorem exists_eventually_bankOrdinary_markerCount_lower
    {c : ℝ} (hc : 0 < c) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ᶠ n : ℕ in atTop, ∀ Q : ℚ,
        20 < Q → Q ≤ (yNat n : ℚ) →
          rho * secondOrderScale n /
              max (Q : ℝ) (Real.log (n : ℝ)) ≤
            (bankEligibleMarkerCount
              (bankOrdinaryEligibleRelation n
                (upperEndpoint n (upperTailLength c n)) Q) : ℝ) := by
  obtain ⟨eta, heta, hoccurrence⟩ :=
    exists_eventually_bankOrdinary_occurrenceTotal_lower hc
  let D : ℝ := 4 * c + 6
  have hD : 0 < D := by dsimp only [D]; positivity
  let rho : ℝ := eta / D
  refine ⟨rho, div_pos heta hD, ?_⟩
  have hmultiplicity := eventually_bankOrdinary_multiplicity_le_cap hc
  filter_upwards [hoccurrence, hmultiplicity,
      eventually_gt_atTop 3] with n hocc hmult hn
  intro Q hQ hQY
  let eligible := bankOrdinaryEligibleRelation n
    (upperEndpoint n (upperTailLength c n)) Q
  let m := bankOrdinaryMultiplicityCap c n Q
  have hQpos : (0 : ℝ) < (Q : ℝ) := by
    exact_mod_cast (show (0 : ℚ) < Q by linarith)
  have hlogN : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hmaxPos : 0 < max (Q : ℝ) (Real.log (n : ℝ)) :=
    lt_of_lt_of_le hQpos (le_max_left _ _)
  have hmData := hmult Q hQ hQY
  have hfinite := bankMarkerOccurrenceTotal_le_mul_markerCount
    eligible m hmData.2
  have hmUpper : (m : ℝ) ≤
      D * max (Q : ℝ) (Real.log (n : ℝ)) /
        Real.log (n : ℝ) := by
    have hceil : (m : ℝ) <
        2 * c * (Q : ℝ) / Real.log (n : ℝ) + 3 := by
      dsimp only [m, bankOrdinaryMultiplicityCap]
      convert
        (Nat.ceil_lt_add_one
          (by positivity : (0 : ℝ) ≤
            2 * c * (Q : ℝ) / Real.log (n : ℝ) + 2)) using 1
      ring
    have hqMax : (Q : ℝ) ≤
        max (Q : ℝ) (Real.log (n : ℝ)) := le_max_left _ _
    have hlogMax : Real.log (n : ℝ) ≤
        max (Q : ℝ) (Real.log (n : ℝ)) := le_max_right _ _
    dsimp only [D]
    apply hceil.le.trans
    apply (le_div_iff₀ hlogN).2
    calc
      (2 * c * (Q : ℝ) / Real.log (n : ℝ) + 3) *
          Real.log (n : ℝ) =
        2 * c * (Q : ℝ) + 3 * Real.log (n : ℝ) := by
          field_simp [hlogN.ne']
      _ ≤ 2 * c * max (Q : ℝ) (Real.log (n : ℝ)) +
          3 * max (Q : ℝ) (Real.log (n : ℝ)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hqMax (by positivity))
          (mul_le_mul_of_nonneg_left hlogMax (by norm_num))
      _ ≤ (4 * c + 6) * max (Q : ℝ) (Real.log (n : ℝ)) := by
        have hmaxNonneg : 0 ≤ max (Q : ℝ) (Real.log (n : ℝ)) := hmaxPos.le
        have hc2 : 2 * c ≤ 4 * c := by linarith
        have hthree : (3 : ℝ) ≤ 6 := by norm_num
        nlinarith [mul_le_mul_of_nonneg_right hc2 hmaxNonneg,
          mul_le_mul_of_nonneg_right hthree hmaxNonneg]
  have hoccLower := hocc Q hQ hQY
  have hfiniteR :
      (bankMarkerOccurrenceTotal eligible : ℝ) ≤
        (m : ℝ) * (bankEligibleMarkerCount eligible : ℝ) := by
    exact_mod_cast hfinite
  have hupper :
      (bankMarkerOccurrenceTotal eligible : ℝ) ≤
        (D * max (Q : ℝ) (Real.log (n : ℝ)) /
          Real.log (n : ℝ)) *
            (bankEligibleMarkerCount eligible : ℝ) := by
    exact hfiniteR.trans (mul_le_mul_of_nonneg_right hmUpper (by positivity))
  change rho * secondOrderScale n /
      max (Q : ℝ) (Real.log (n : ℝ)) ≤
    (bankEligibleMarkerCount eligible : ℝ)
  dsimp only [rho]
  have hcombined :
      eta * secondOrderScale n / Real.log (n : ℝ) ≤
        (D * max (Q : ℝ) (Real.log (n : ℝ)) /
          Real.log (n : ℝ)) *
            (bankEligibleMarkerCount eligible : ℝ) :=
    hoccLower.trans hupper
  have hcancel := mul_le_mul_of_nonneg_right hcombined hlogN.le
  field_simp [hlogN.ne'] at hcancel
  calc
    eta / D * secondOrderScale n /
        max (Q : ℝ) (Real.log (n : ℝ)) =
      (eta * secondOrderScale n) /
        (D * max (Q : ℝ) (Real.log (n : ℝ))) := by
          field_simp [hD.ne', hmaxPos.ne']
    _ ≤ (bankEligibleMarkerCount eligible : ℝ) := by
      apply (div_le_iff₀ (mul_pos hD hmaxPos)).2
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hcancel

/-! ## The five fixed nonbottom scales -/

private theorem natDiv_fixed_endpoint_ratio_tendsto
    {m : ℕ → ℕ} {a : ℝ}
    (hm : Tendsto (fun n : ℕ ↦ (m n : ℝ) / (n : ℝ))
      atTop (nhds a)) (u : ℕ) (hu : 0 < u) :
    Tendsto (fun n : ℕ ↦ ((m n / u : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (a / (u : ℝ))) := by
  have hmain := hm.div_const (u : ℝ)
  have hinv : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ))
      atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  have hlower : Tendsto
      (fun n : ℕ ↦ ((m n : ℝ) / (n : ℝ)) / (u : ℝ) -
        1 / (n : ℝ)) atTop (nhds (a / (u : ℝ))) := by
    simpa only [sub_zero] using hmain.sub hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hmain
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hfloor := realDiv_sub_one_lt_cast_natDiv (m n) u hu
    calc
      ((m n : ℝ) / (n : ℝ)) / (u : ℝ) - 1 / (n : ℝ) =
          ((m n : ℝ) / (u : ℝ) - 1) / (n : ℝ) := by
            field_simp
      _ ≤ ((m n / u : ℕ) : ℝ) / (n : ℝ) :=
        div_le_div_of_nonneg_right hfloor.le hnR.le
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    calc
      ((m n / u : ℕ) : ℝ) / (n : ℝ) ≤
          ((m n : ℝ) / (u : ℝ)) / (n : ℝ) :=
        div_le_div_of_nonneg_right (cast_natDiv_le_realDiv (m n) u) hnR.le
      _ = ((m n : ℝ) / (n : ℝ)) / (u : ℝ) := by
        field_simp

private theorem twoNat_ratio_tendsto :
    Tendsto (fun n : ℕ ↦ ((2 * n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 2) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  push_cast
  field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne']

private theorem upperEndpoint_ratio_tendsto_two
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦
      (upperEndpoint n (upperTailLength c n) : ℝ) / (n : ℝ))
      atTop (nhds 2) := by
  have h := (tendsto_const_nhds : Tendsto (fun _n : ℕ ↦ (2 : ℝ))
      atTop (nhds 2)).add (upperTailLength_ratio_tendsto_zero hc)
  have h' : Tendsto
      (fun n : ℕ ↦ 2 + (upperTailLength c n : ℝ) / (n : ℝ))
      atTop (nhds 2) := by
    simpa only [add_zero] using h
  apply h'.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [upperEndpoint, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne']

private theorem fixedDonor_gap_normalized_tendsto
    {c : ℝ} (hc : 0 < c) {u : ℕ} (hu : 0 < u) :
    Tendsto
      (fun n : ℕ ↦
        (((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) -
          (((2 * n) / u : ℕ) : ℝ)) / secondOrderScale n)
      atTop (nhds (c / (u : ℝ))) := by
  have hmain := (upperTailLength_normalized_tendsto hc).div_const (u : ℝ)
  have hinv : Tendsto (fun n : ℕ ↦ 1 / secondOrderScale n)
      atTop (nhds 0) := by
    simpa only [one_div] using secondOrderScale_tendsto_atTop.inv_tendsto_atTop
  have hlower : Tendsto
      (fun n : ℕ ↦ (upperTailLength c n : ℝ) /
        secondOrderScale n / (u : ℝ) - 1 / secondOrderScale n)
      atTop (nhds (c / (u : ℝ))) := by
    simpa only [sub_zero] using hmain.sub hinv
  have hupper : Tendsto
      (fun n : ℕ ↦ (upperTailLength c n : ℝ) /
        secondOrderScale n / (u : ℝ) + 1 / secondOrderScale n)
      atTop (nhds (c / (u : ℝ))) := by
    simpa only [add_zero] using hmain.add hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_secondOrderScale_pos] with n hscale
    have hMlower := realDiv_sub_one_lt_cast_natDiv
      (upperEndpoint n (upperTailLength c n)) u hu
    have hNupper := cast_natDiv_le_realDiv (2 * n) u
    rw [upperEndpoint, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hMlower
    have hnum : (upperTailLength c n : ℝ) / (u : ℝ) - 1 ≤
        ((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) -
          (((2 * n) / u : ℕ) : ℝ) := by
      calc
        (upperTailLength c n : ℝ) / (u : ℝ) - 1 =
            ((2 * (n : ℝ) + upperTailLength c n) / (u : ℝ) - 1) -
              (2 * (n : ℝ)) / (u : ℝ) := by ring
        _ ≤ ((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) -
              (((2 * n) / u : ℕ) : ℝ) := by
          apply sub_le_sub hMlower.le
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using hNupper
    calc
      (upperTailLength c n : ℝ) / secondOrderScale n / (u : ℝ) -
          1 / secondOrderScale n =
        ((upperTailLength c n : ℝ) / (u : ℝ) - 1) /
          secondOrderScale n := by field_simp
      _ ≤ (((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) -
          (((2 * n) / u : ℕ) : ℝ)) / secondOrderScale n :=
        div_le_div_of_nonneg_right hnum hscale.le
  · filter_upwards [eventually_secondOrderScale_pos] with n hscale
    have hMupper := cast_natDiv_le_realDiv
      (upperEndpoint n (upperTailLength c n)) u
    have hNlower := realDiv_sub_one_lt_cast_natDiv (2 * n) u hu
    rw [upperEndpoint, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hMupper
    have hnum :
        ((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) -
            (((2 * n) / u : ℕ) : ℝ) ≤
          (upperTailLength c n : ℝ) / (u : ℝ) + 1 := by
      calc
        ((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) -
            (((2 * n) / u : ℕ) : ℝ) ≤
          (2 * (n : ℝ) + upperTailLength c n) / (u : ℝ) -
            ((2 * (n : ℝ)) / (u : ℝ) - 1) := by
          apply sub_le_sub hMupper
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using hNlower.le
        _ = (upperTailLength c n : ℝ) / (u : ℝ) + 1 := by ring
    calc
      (((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) -
          (((2 * n) / u : ℕ) : ℝ)) / secondOrderScale n ≤
        ((upperTailLength c n : ℝ) / (u : ℝ) + 1) /
          secondOrderScale n :=
        div_le_div_of_nonneg_right hnum hscale.le
      _ = (upperTailLength c n : ℝ) / secondOrderScale n / (u : ℝ) +
          1 / secondOrderScale n := by field_simp

/-- At any fixed donor, the exact product interval contains asymptotically
`(c/u)n/log(n)^2` primes. -/
theorem bankOrdinaryPrimeChoices_fixedDonor_normalized_tendsto
    {c : ℝ} (hc : 0 < c) {u : ℕ} (hu : 0 < u) :
    Tendsto
      (fun n : ℕ ↦
        ((bankOrdinaryPrimeChoices n
          (upperEndpoint n (upperTailLength c n)) u).card : ℝ) /
            SafePrimeCounting.shortIntervalPrimeScale n)
      atTop (nhds (c / (u : ℝ))) := by
  have hlower := natDiv_fixed_endpoint_ratio_tendsto
    twoNat_ratio_tendsto u hu
  have hupper := natDiv_fixed_endpoint_ratio_tendsto
    (upperEndpoint_ratio_tendsto_two hc) u hu
  have hgap := fixedDonor_gap_normalized_tendsto hc hu
  have horder : ∀ᶠ n : ℕ in atTop,
      (2 * n) / u ≤ upperEndpoint n (upperTailLength c n) / u :=
    Eventually.of_forall fun n ↦
      Nat.div_le_div_right (two_mul_le_upperEndpoint n (upperTailLength c n))
  simpa only [bankOrdinaryPrimeChoices, bankPrimeInterval] using
    SafePrimeCounting.prime_Ioc_shortMovingInterval_normalized_tendsto
      (div_pos (by norm_num) (by exact_mod_cast hu)) hlower hupper hgap horder

private theorem eventually_smallPrimeChoice_pairs_eligible
    {c : ℝ} (hc : 0 < c) (scale : SmallDescentScale) :
    ∀ᶠ n : ℕ in atTop, ∀ P ∈
      bankOrdinaryPrimeChoices n
        (upperEndpoint n (upperTailLength c n))
        (bankOrdinarySmallDonor scale),
      (P, bankOrdinarySmallDonor scale) ∈
        bankOrdinaryEligibleRelation n
          (upperEndpoint n (upperTailLength c n))
          (smallDescentScaleValue scale) := by
  have hY : ∀ᶠ n : ℕ in atTop, 23 ≤ yNat n :=
    yNat_tendsto_atTop.eventually (eventually_ge_atTop 23)
  have htail : ∀ᶠ n : ℕ in atTop,
      2 * (smallDescentScaleValue scale : ℝ) *
          (upperTailLength c n : ℝ) ≤
        (3 * (bankOrdinarySmallDonor scale : ℝ) -
          4 * (smallDescentScaleValue scale : ℝ)) * (n : ℝ) := by
    have hmargin : 0 <
        3 * (bankOrdinarySmallDonor scale : ℝ) -
          4 * (smallDescentScaleValue scale : ℝ) := by
      cases scale <;>
        norm_num [bankOrdinarySmallDonor, smallDescentScaleValue,
          smallDescentScaleNumerator, smallDescentScaleDenominator]
    have hscaleValue : 0 < (smallDescentScaleValue scale : ℝ) := by
      cases scale <;>
        norm_num [smallDescentScaleValue, smallDescentScaleNumerator,
          smallDescentScaleDenominator]
    have hden : 0 < 2 * (smallDescentScaleValue scale : ℝ) := by positivity
    have hratio := (upperTailLength_ratio_tendsto_zero hc).eventually
      (eventually_lt_nhds (div_pos hmargin hden))
    filter_upwards [hratio, eventually_gt_atTop 0] with n hn hnpos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hlt : (upperTailLength c n : ℝ) <
        ((3 * (bankOrdinarySmallDonor scale : ℝ) -
            4 * (smallDescentScaleValue scale : ℝ)) * (n : ℝ)) /
          (2 * (smallDescentScaleValue scale : ℝ)) := by
      calc
        (upperTailLength c n : ℝ) =
            ((upperTailLength c n : ℝ) / (n : ℝ)) * (n : ℝ) := by
              field_simp [hnR.ne']
        _ < ((3 * (bankOrdinarySmallDonor scale : ℝ) -
              4 * (smallDescentScaleValue scale : ℝ)) /
              (2 * (smallDescentScaleValue scale : ℝ))) *
              (n : ℝ) := mul_lt_mul_of_pos_right hn hnR
        _ = ((3 * (bankOrdinarySmallDonor scale : ℝ) -
              4 * (smallDescentScaleValue scale : ℝ)) * (n : ℝ)) /
              (2 * (smallDescentScaleValue scale : ℝ)) := by
                field_simp [hden.ne']
    have hmul := (lt_div_iff₀ hden).mp hlt
    nlinarith
  filter_upwards [hY, htail] with n hYn htailn
  intro P hP
  have huPos := bankOrdinarySmallDonor_pos scale
  have hscaleValue : 0 < (smallDescentScaleValue scale : ℝ) := by
    cases scale <;>
      norm_num [smallDescentScaleValue, smallDescentScaleNumerator,
        smallDescentScaleDenominator]
  have hPData := (mem_bankOrdinaryPrimeChoices huPos).mp hP
  apply bankOrdinarySmallPair_mem_eligible scale hYn hPData.1
  · unfold InOrdinaryBankMarkerInterval
    have hwindow := bankOrdinarySmallDonor_mem_window scale
    have htailLowerQ :
        2 * (n : ℝ) < (P : ℝ) *
          (bankOrdinarySmallDonor scale : ℝ) := by
      exact_mod_cast hPData.2.1
    have htailUpperQ :
        (P : ℝ) * (bankOrdinarySmallDonor scale : ℝ) ≤
          upperEndpoint n (upperTailLength c n) := by
      exact_mod_cast hPData.2.2
    have hwindowLower :
        4 * (smallDescentScaleValue scale : ℝ) ≤
          3 * (bankOrdinarySmallDonor scale : ℝ) := by
      exact_mod_cast hwindow.1
    have hwindowUpper :
        2 * (bankOrdinarySmallDonor scale : ℝ) ≤
          3 * (smallDescentScaleValue scale : ℝ) := by
      exact_mod_cast hwindow.2
    have hMcast :
        (upperEndpoint n (upperTailLength c n) : ℝ) =
          2 * (n : ℝ) + upperTailLength c n := by
      simp [upperEndpoint]
    constructor
    · have hPnonneg : (0 : ℝ) ≤ P := by positivity
      have hwindowUpperP :=
        mul_le_mul_of_nonneg_right hwindowUpper hPnonneg
      have htailTwice := mul_lt_mul_of_pos_left htailLowerQ
        (by norm_num : (0 : ℝ) < 2)
      have hreal : 4 * (n : ℝ) <
          3 * (smallDescentScaleValue scale : ℝ) * (P : ℝ) := by
        calc
          4 * (n : ℝ) = 2 * (2 * (n : ℝ)) := by ring
          _ < 2 * ((P : ℝ) * bankOrdinarySmallDonor scale) := htailTwice
          _ ≤ 3 * smallDescentScaleValue scale * (P : ℝ) := by
            ring_nf at hwindowUpperP ⊢
            exact hwindowUpperP
      exact_mod_cast hreal
    · rw [hMcast] at htailUpperQ
      have hscaledTail := mul_le_mul_of_nonneg_left htailUpperQ
        (show (0 : ℝ) ≤ 2 * smallDescentScaleValue scale by positivity)
      have huR : (0 : ℝ) < bankOrdinarySmallDonor scale := by
        exact_mod_cast huPos
      have hmul :
          (2 * smallDescentScaleValue scale * (P : ℝ)) *
              bankOrdinarySmallDonor scale ≤
            (3 * (n : ℝ)) * bankOrdinarySmallDonor scale := by
        ring_nf at hscaledTail htailn ⊢
        nlinarith
      have hcancel :
          2 * (smallDescentScaleValue scale : ℝ) * (P : ℝ) ≤
            3 * (n : ℝ) := le_of_mul_le_mul_right hmul huR
      exact_mod_cast hcancel
  · exact hPData.2.1
  · exact hPData.2.2

/-- The five exceptional fixed donors each give a positive occurrence
constant on the same `n/log(n)^2` scale. -/
theorem bankOrdinary_smallScale_occurrenceTotal_lower
    {c : ℝ} (hc : 0 < c) (scale : SmallDescentScale) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ᶠ n : ℕ in atTop,
        eta * secondOrderScale n / Real.log (n : ℝ) ≤
          (bankMarkerOccurrenceTotal
            (bankOrdinaryEligibleRelation n
              (upperEndpoint n (upperTailLength c n))
              (smallDescentScaleValue scale)) : ℝ) := by
  let eta : ℝ := c / (2 * bankOrdinarySmallDonor scale)
  have heta : 0 < eta := by
    dsimp only [eta]
    have huR : (0 : ℝ) < bankOrdinarySmallDonor scale := by
      exact_mod_cast bankOrdinarySmallDonor_pos scale
    exact div_pos hc (mul_pos (by norm_num) huR)
  refine ⟨eta, heta, ?_⟩
  have hlimit := bankOrdinaryPrimeChoices_fixedDonor_normalized_tendsto
    hc (bankOrdinarySmallDonor_pos scale)
  have hlower : ∀ᶠ n : ℕ in atTop,
      c / (2 * bankOrdinarySmallDonor scale) ≤
        ((bankOrdinaryPrimeChoices n
          (upperEndpoint n (upperTailLength c n))
          (bankOrdinarySmallDonor scale)).card : ℝ) /
            SafePrimeCounting.shortIntervalPrimeScale n :=
    hlimit.eventually (eventually_ge_nhds (by
      have hu : (0 : ℝ) < bankOrdinarySmallDonor scale := by
        exact_mod_cast bankOrdinarySmallDonor_pos scale
      have : c / (2 * (bankOrdinarySmallDonor scale : ℝ)) <
          c / (bankOrdinarySmallDonor scale : ℝ) := by
        calc
          c / (2 * (bankOrdinarySmallDonor scale : ℝ)) =
              (c / (bankOrdinarySmallDonor scale : ℝ)) / 2 := by
                field_simp [hu.ne']
          _ < c / (bankOrdinarySmallDonor scale : ℝ) :=
            half_lt_self (div_pos hc hu)
      exact this))
  have heligible := eventually_smallPrimeChoice_pairs_eligible hc scale
  filter_upwards [hlower, heligible, eventually_secondOrderScale_pos,
      eventually_gt_atTop 2] with n hprime helig hscale hn
  have hlogN : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hshortPos : 0 < SafePrimeCounting.shortIntervalPrimeScale n :=
    by
      rw [SafePrimeCounting.shortIntervalPrimeScale]
      exact div_pos hscale hlogN
  have hprimeLower : eta * secondOrderScale n / Real.log (n : ℝ) ≤
      ((bankOrdinaryPrimeChoices n
        (upperEndpoint n (upperTailLength c n))
        (bankOrdinarySmallDonor scale)).card : ℝ) := by
    have hmul := (le_div_iff₀ hshortPos).mp hprime
    dsimp only [eta]
    simpa only [SafePrimeCounting.shortIntervalPrimeScale, mul_div_assoc] using hmul
  have hinj : (bankOrdinaryPrimeChoices n
      (upperEndpoint n (upperTailLength c n))
      (bankOrdinarySmallDonor scale)).card ≤
      (bankOrdinaryEligibleRelation n
        (upperEndpoint n (upperTailLength c n))
        (smallDescentScaleValue scale)).card := by
    apply Finset.card_le_card_of_injOn
      (fun P : ℕ ↦ (P, bankOrdinarySmallDonor scale))
    · intro P hP
      exact helig P hP
    · intro P _ P' _ hpair
      exact congrArg Prod.fst hpair
  exact hprimeLower.trans (by exact_mod_cast hinj)

/-- The fixed donor at each small scale also gives distinct actual markers.
This is the marker-count form needed by the request allocation: no division
by a donor-multiplicity estimate is needed because the displayed donor is
fixed and the prime coordinate itself is the marker. -/
theorem bankOrdinary_smallScale_markerCount_lower
    {c : ℝ} (hc : 0 < c) (scale : SmallDescentScale) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ᶠ n : ℕ in atTop,
        rho * secondOrderScale n / Real.log (n : ℝ) ≤
          (bankEligibleMarkerCount
            (bankOrdinaryEligibleRelation n
              (upperEndpoint n (upperTailLength c n))
              (smallDescentScaleValue scale)) : ℝ) := by
  let rho : ℝ := c / (2 * bankOrdinarySmallDonor scale)
  have hrho : 0 < rho := by
    dsimp only [rho]
    have huR : (0 : ℝ) < bankOrdinarySmallDonor scale := by
      exact_mod_cast bankOrdinarySmallDonor_pos scale
    exact div_pos hc (mul_pos (by norm_num) huR)
  refine ⟨rho, hrho, ?_⟩
  have hlimit := bankOrdinaryPrimeChoices_fixedDonor_normalized_tendsto
    hc (bankOrdinarySmallDonor_pos scale)
  have hlower : ∀ᶠ n : ℕ in atTop,
      c / (2 * bankOrdinarySmallDonor scale) ≤
        ((bankOrdinaryPrimeChoices n
          (upperEndpoint n (upperTailLength c n))
          (bankOrdinarySmallDonor scale)).card : ℝ) /
            SafePrimeCounting.shortIntervalPrimeScale n :=
    hlimit.eventually (eventually_ge_nhds (by
      have hu : (0 : ℝ) < bankOrdinarySmallDonor scale := by
        exact_mod_cast bankOrdinarySmallDonor_pos scale
      have : c / (2 * (bankOrdinarySmallDonor scale : ℝ)) <
          c / (bankOrdinarySmallDonor scale : ℝ) := by
        calc
          c / (2 * (bankOrdinarySmallDonor scale : ℝ)) =
              (c / (bankOrdinarySmallDonor scale : ℝ)) / 2 := by
                field_simp [hu.ne']
          _ < c / (bankOrdinarySmallDonor scale : ℝ) :=
            half_lt_self (div_pos hc hu)
      exact this))
  have heligible := eventually_smallPrimeChoice_pairs_eligible hc scale
  filter_upwards [hlower, heligible, eventually_secondOrderScale_pos,
      eventually_gt_atTop 2] with n hprime helig hscale hn
  have hlogN : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hshortPos : 0 < SafePrimeCounting.shortIntervalPrimeScale n :=
    by
      rw [SafePrimeCounting.shortIntervalPrimeScale]
      exact div_pos hscale hlogN
  have hprimeLower : rho * secondOrderScale n / Real.log (n : ℝ) ≤
      ((bankOrdinaryPrimeChoices n
        (upperEndpoint n (upperTailLength c n))
        (bankOrdinarySmallDonor scale)).card : ℝ) := by
    have hmul := (le_div_iff₀ hshortPos).mp hprime
    dsimp only [rho]
    simpa only [SafePrimeCounting.shortIntervalPrimeScale, mul_div_assoc] using hmul
  have hsubset :
      bankOrdinaryPrimeChoices n
          (upperEndpoint n (upperTailLength c n))
          (bankOrdinarySmallDonor scale) ⊆
        bankEligibleMarkers
          (bankOrdinaryEligibleRelation n
            (upperEndpoint n (upperTailLength c n))
            (smallDescentScaleValue scale)) := by
    intro P hP
    rw [bankEligibleMarkers, Finset.mem_image]
    exact ⟨(P, bankOrdinarySmallDonor scale), helig P hP, rfl⟩
  have hcard := Finset.card_le_card hsubset
  exact hprimeLower.trans (by exact_mod_cast hcard)

end

end Erdos390.WholePaper
