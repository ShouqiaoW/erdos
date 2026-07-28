import Erdos390.WholePaper.CompleteRoughRowPartition
import Erdos390.WholePaper.CentralAnchorTailDivisibility
import Erdos390.Full.StructuredCells
import Mathlib.Data.Nat.Totient

/-!
# The literal head-compatible finite raw point

This file constructs the first finite point in the guarded rough selector.
The upper block `E`, the high lower block `H`, and the broad lower block `J`
are literal natural-number half-open intervals.  Head freedom is imposed by
coprimality with the product of all primes up to `W`, and the raw weight is
defined pointwise from those finite sets.

The second half proves the exact deterministic identities used before any
HT--Saias or prime-number estimate: finite Möbius inclusion--exclusion,
reindexing of smooth multiples by division, and the resulting physical-block
shift through every divisor of the head modulus.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full.HeadPattern
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Literal physical intervals -/

/-- The upper tail block `E = (2n, 2n+h]`. -/
def roughUpperBlock (n h : ℕ) : Finset ℕ :=
  Finset.Ioc (2 * n) (2 * n + h)

/-- The high lower block `H = (2n-Kh, 2n]`. -/
def roughHighLowerBlock (n h K : ℕ) : Finset ℕ :=
  Finset.Ioc (2 * n - K * h) (2 * n)

/-- The broad lower block `J = (n, 2n-Kh]`. -/
def roughBroadLowerBlock (n h K : ℕ) : Finset ℕ :=
  Finset.Ioc n (2 * n - K * h)

/-- The complete raw candidate set before numerical guards. -/
def roughRawCandidateSet (n h K : ℕ) : Finset ℕ :=
  roughHighLowerBlock n h K ∪ roughBroadLowerBlock n h K

/-- The two lower physical blocks are disjoint at their common endpoint. -/
theorem roughHighLowerBlock_disjoint_roughBroadLowerBlock
    (n h K : ℕ) :
    Disjoint (roughHighLowerBlock n h K)
      (roughBroadLowerBlock n h K) := by
  rw [Finset.disjoint_left]
  intro a haHigh haBroad
  simp only [roughHighLowerBlock, roughBroadLowerBlock,
    Finset.mem_Ioc] at haHigh haBroad
  omega

/-- Under the paper's interval-size condition, the two raw blocks exhaust
the whole lower interval `(n,2n]`. -/
theorem roughRawCandidateSet_eq_Ioc
    {n h K : ℕ} (hKh : K * h ≤ n) :
    roughRawCandidateSet n h K = Finset.Ioc n (2 * n) := by
  ext a
  simp only [roughRawCandidateSet, roughHighLowerBlock,
    roughBroadLowerBlock, Finset.mem_union, Finset.mem_Ioc]
  omega

/-- The upper tail is disjoint from every raw lower candidate. -/
theorem roughUpperBlock_disjoint_rawCandidateSet
    (n h K : ℕ) :
    Disjoint (roughUpperBlock n h) (roughRawCandidateSet n h K) := by
  rw [Finset.disjoint_left]
  intro a haUpper haLower
  simp only [roughUpperBlock, roughRawCandidateSet,
    roughHighLowerBlock, roughBroadLowerBlock, Finset.mem_Ioc,
    Finset.mem_union] at haUpper haLower
  rcases haLower with haHigh | haBroad <;> omega

/-- The upper interval contains exactly `h` integer tokens. -/
theorem roughUpperBlock_card (n h : ℕ) :
    (roughUpperBlock n h).card = h := by
  simp only [roughUpperBlock, Nat.card_Ioc]
  omega

/-- The high lower interval has its literal real-length cardinality. -/
theorem roughHighLowerBlock_card
    {n h K : ℕ} (hKh : K * h ≤ n) :
    (roughHighLowerBlock n h K).card = K * h := by
  simp only [roughHighLowerBlock, Nat.card_Ioc]
  omega

/-- The broad lower interval has its literal real-length cardinality. -/
theorem roughBroadLowerBlock_card
    {n h K : ℕ} (hKh : K * h ≤ n) :
    (roughBroadLowerBlock n h K).card = n - K * h := by
  simp only [roughBroadLowerBlock, Nat.card_Ioc]
  omega

/-! ## The finite head and raw weights -/

/-- The paper's head-prime product `P_hd`, with every prime `p ≤ W`. -/
def roughHeadModulus (W : ℕ) : ℕ :=
  (primesUpTo W).prod id

/-- The zero-valuation head pattern whose matches are precisely the positive
integers coprime to `roughHeadModulus W`. -/
def roughHeadZeroPattern (W : ℕ) : Erdos390.Full.HeadPattern.Pattern where
  primes := primesUpTo W
  exponent := fun _p ↦ 0
  prime_mem := fun _p hp ↦ (mem_primesUpTo.mp hp).1

@[simp]
theorem roughHeadZeroPattern_modulus (W : ℕ) :
    (roughHeadZeroPattern W).modulus = roughHeadModulus W := rfl

@[simp]
theorem roughHeadZeroPattern_factor (W : ℕ) :
    (roughHeadZeroPattern W).factor = 1 := by
  simp [roughHeadZeroPattern, Erdos390.Full.HeadPattern.Pattern.factor]

/-- The head modulus is always positive, including for an empty head. -/
theorem roughHeadModulus_pos (W : ℕ) :
    0 < roughHeadModulus W := by
  rw [← roughHeadZeroPattern_modulus]
  exact Nat.pos_of_ne_zero (roughHeadZeroPattern W).modulus_ne_zero

/-- The paper's fixed reduced-residue density
`delta_hd = phi(P_hd) / P_hd`. -/
def roughHeadDensity (W : ℕ) : ℝ :=
  ((roughHeadModulus W).totient : ℝ) / (roughHeadModulus W : ℝ)

/-- The complete zero-head stratum has strictly positive density. -/
theorem roughHeadDensity_pos (W : ℕ) :
    0 < roughHeadDensity W := by
  have hmod : (0 : ℝ) < (roughHeadModulus W : ℝ) := by
    exact_mod_cast roughHeadModulus_pos W
  have htot : (0 : ℝ) < ((roughHeadModulus W).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (roughHeadModulus_pos W)
  exact div_pos htot hmod

/-- The literal choice
`alpha = (h / delta_hd - (beta/L) |J|) / |H|`, with the already-proved
integer lengths `|H| = K*h` and `|J| = n-K*h` written directly. -/
def roughHeadBalancedAlpha
    (W n h K : ℕ) (beta L : ℝ) : ℝ :=
  (((h : ℕ) : ℝ) / roughHeadDensity W -
      (beta / L) * (((n - K * h : ℕ) : ℝ))) /
    (((K * h : ℕ) : ℝ))

/-- The defining quotient for `roughHeadBalancedAlpha` gives the exact
real-length balance as soon as the high block has positive length. -/
theorem roughHeadBalancedAlpha_length_normalization
    {W n h K : ℕ} {beta L : ℝ} (hKhPos : 0 < K * h) :
    roughHeadDensity W *
        (roughHeadBalancedAlpha W n h K beta L *
            (((K * h : ℕ) : ℝ)) +
          (beta / L) * (((n - K * h : ℕ) : ℝ))) =
      ((h : ℕ) : ℝ) := by
  have hdelta : roughHeadDensity W ≠ 0 :=
    (roughHeadDensity_pos W).ne'
  have hKhReal : (((K * h : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast hKhPos.ne'
  rw [roughHeadBalancedAlpha, div_mul_cancel₀ _ hKhReal,
    sub_add_cancel]
  calc
    roughHeadDensity W * (((h : ℕ) : ℝ) / roughHeadDensity W) =
        ((((h : ℕ) : ℝ) * roughHeadDensity W) /
          roughHeadDensity W) := by ring
    _ = ((h : ℕ) : ℝ) := mul_div_cancel_right₀ _ hdelta

/-- Cardinality form of the exact normalization appearing in the paper. -/
theorem roughHeadBalancedAlpha_card_normalization
    {W n h K : ℕ} {beta L : ℝ}
    (hKh : K * h ≤ n) (hKhPos : 0 < K * h) :
    roughHeadDensity W *
        (roughHeadBalancedAlpha W n h K beta L *
            ((roughHighLowerBlock n h K).card : ℝ) +
          (beta / L) * ((roughBroadLowerBlock n h K).card : ℝ)) =
      ((roughUpperBlock n h).card : ℝ) := by
  rw [roughHighLowerBlock_card hKh, roughBroadLowerBlock_card hKh,
    roughUpperBlock_card]
  exact roughHeadBalancedAlpha_length_normalization hKhPos

/-- Restrict an arbitrary finite set to integers coprime to the complete
head-prime product. -/
def roughHeadFree (W : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.filter (fun a ↦ Nat.Coprime a (roughHeadModulus W))

@[simp]
theorem mem_roughHeadFree
    {W a : ℕ} {A : Finset ℕ} :
    a ∈ roughHeadFree W A ↔
      a ∈ A ∧ Nat.Coprime a (roughHeadModulus W) := by
  simp [roughHeadFree]

/-- The indicator of membership in a finite natural-number set. -/
def roughFiniteIndicator (A : Finset ℕ) (a : ℕ) : ℝ :=
  if a ∈ A then 1 else 0

/-- The literal head-compatible raw weight from the paper. -/
def roughHeadCompatibleRawWeight
    (W n h K : ℕ) (α β L : ℝ) (a : ℕ) : ℝ :=
  if Nat.Coprime a (roughHeadModulus W) then
    α * roughFiniteIndicator (roughHighLowerBlock n h K) a +
      (β / L) * roughFiniteIndicator (roughBroadLowerBlock n h K) a
  else 0

/-- The actual finite vector obtained by inserting the paper's balanced
choice of `alpha` into the raw weight and restricting its coordinate type
to the literal candidate set. -/
def roughHeadCompatibleRawPoint
    (W n h K : ℕ) (beta L : ℝ) :
    ↑(roughRawCandidateSet n h K) → ℝ :=
  fun a ↦ roughHeadCompatibleRawWeight W n h K
    (roughHeadBalancedAlpha W n h K beta L) beta L a.1

@[simp]
theorem roughHeadCompatibleRawPoint_apply
    (W n h K : ℕ) (beta L : ℝ)
    (a : ↑(roughRawCandidateSet n h K)) :
    roughHeadCompatibleRawPoint W n h K beta L a =
      roughHeadCompatibleRawWeight W n h K
        (roughHeadBalancedAlpha W n h K beta L) beta L a.1 := rfl

/-- Outside the literal raw candidate set the constructed weight vanishes. -/
theorem roughHeadCompatibleRawWeight_eq_zero_of_not_mem
    {W n h K a : ℕ} {α β L : ℝ}
    (ha : a ∉ roughRawCandidateSet n h K) :
    roughHeadCompatibleRawWeight W n h K α β L a = 0 := by
  have haHigh : a ∉ roughHighLowerBlock n h K := by
    intro haHigh
    exact ha (Finset.mem_union_left _ haHigh)
  have haBroad : a ∉ roughBroadLowerBlock n h K := by
    intro haBroad
    exact ha (Finset.mem_union_right _ haBroad)
  simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
    haHigh, haBroad]

/-- In its paper domain, the raw point vanishes off `(n,2n]`. -/
theorem roughHeadCompatibleRawWeight_eq_zero_of_not_mem_Ioc
    {W n h K a : ℕ} {α β L : ℝ}
    (hKh : K * h ≤ n) (ha : a ∉ Finset.Ioc n (2 * n)) :
    roughHeadCompatibleRawWeight W n h K α β L a = 0 := by
  apply roughHeadCompatibleRawWeight_eq_zero_of_not_mem
  rwa [roughRawCandidateSet_eq_Ioc hKh]

/-- The two physical pieces make the raw weight automatically feasible
whenever their two constant levels lie in `[0,1]`. -/
theorem roughHeadCompatibleRawWeight_mem_unitInterval
    {W n h K : ℕ} {α β L : ℝ}
    (hα : 0 ≤ α ∧ α ≤ 1)
    (hβ : 0 ≤ β / L ∧ β / L ≤ 1)
    (a : ℕ) :
    0 ≤ roughHeadCompatibleRawWeight W n h K α β L a ∧
      roughHeadCompatibleRawWeight W n h K α β L a ≤ 1 := by
  by_cases hcop : Nat.Coprime a (roughHeadModulus W)
  · rw [roughHeadCompatibleRawWeight, if_pos hcop]
    by_cases haHigh : a ∈ roughHighLowerBlock n h K
    · have haBroad : a ∉ roughBroadLowerBlock n h K := by
        intro haBroad
        exact Finset.disjoint_left.mp
          (roughHighLowerBlock_disjoint_roughBroadLowerBlock n h K)
          haHigh haBroad
      simpa [roughFiniteIndicator, haHigh, haBroad] using hα
    · by_cases haBroad : a ∈ roughBroadLowerBlock n h K
      · simpa [roughFiniteIndicator, haHigh, haBroad] using hβ
      · simp [roughFiniteIndicator, haHigh, haBroad]
  · simp [roughHeadCompatibleRawWeight, hcop]

/-- Feasibility of the literal finite point is reduced exactly to the two
parameter bounds whose eventual verification is analytic. -/
theorem roughHeadCompatibleRawPoint_mem_unitInterval
    {W n h K : ℕ} {beta L : ℝ}
    (hα : 0 ≤ roughHeadBalancedAlpha W n h K beta L ∧
      roughHeadBalancedAlpha W n h K beta L ≤ 1)
    (hbeta : 0 ≤ beta / L ∧ beta / L ≤ 1)
    (a : ↑(roughRawCandidateSet n h K)) :
    0 ≤ roughHeadCompatibleRawPoint W n h K beta L a ∧
      roughHeadCompatibleRawPoint W n h K beta L a ≤ 1 := by
  rw [roughHeadCompatibleRawPoint_apply]
  exact roughHeadCompatibleRawWeight_mem_unitInterval hα hbeta a.1

/-- Exact total mass of the raw point: no asymptotic head density has yet
replaced either finite head-free count. -/
theorem sum_roughHeadCompatibleRawWeight
    (W n h K : ℕ) (α β L : ℝ) :
    ∑ a ∈ roughRawCandidateSet n h K,
        roughHeadCompatibleRawWeight W n h K α β L a =
      α * ((roughHeadFree W (roughHighLowerBlock n h K)).card : ℝ) +
        (β / L) *
          ((roughHeadFree W (roughBroadLowerBlock n h K)).card : ℝ) := by
  have hdisjoint :=
    roughHighLowerBlock_disjoint_roughBroadLowerBlock n h K
  have hhigh :
      (∑ a ∈ roughHighLowerBlock n h K,
          roughHeadCompatibleRawWeight W n h K α β L a) =
        α * ((roughHeadFree W
          (roughHighLowerBlock n h K)).card : ℝ) := by
    calc
      ∑ a ∈ roughHighLowerBlock n h K,
          roughHeadCompatibleRawWeight W n h K α β L a =
        ∑ a ∈ roughHighLowerBlock n h K,
          if Nat.Coprime a (roughHeadModulus W) then α else 0 := by
        apply Finset.sum_congr rfl
        intro a haHigh
        have haBroad : a ∉ roughBroadLowerBlock n h K := by
          intro haBroad
          exact Finset.disjoint_left.mp hdisjoint haHigh haBroad
        by_cases hcop : Nat.Coprime a (roughHeadModulus W) <;>
          simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
            haHigh, haBroad, hcop]
      _ = α * ((roughHeadFree W
          (roughHighLowerBlock n h K)).card : ℝ) := by
        rw [← Finset.sum_filter]
        simp [roughHeadFree]
        ring
  have hbroad :
      (∑ a ∈ roughBroadLowerBlock n h K,
          roughHeadCompatibleRawWeight W n h K α β L a) =
        (β / L) * ((roughHeadFree W
          (roughBroadLowerBlock n h K)).card : ℝ) := by
    calc
      ∑ a ∈ roughBroadLowerBlock n h K,
          roughHeadCompatibleRawWeight W n h K α β L a =
        ∑ a ∈ roughBroadLowerBlock n h K,
          if Nat.Coprime a (roughHeadModulus W) then β / L else 0 := by
        apply Finset.sum_congr rfl
        intro a haBroad
        have haHigh : a ∉ roughHighLowerBlock n h K := by
          intro haHigh
          exact Finset.disjoint_left.mp hdisjoint haHigh haBroad
        by_cases hcop : Nat.Coprime a (roughHeadModulus W) <;>
          simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
            haHigh, haBroad, hcop]
      _ = (β / L) * ((roughHeadFree W
          (roughBroadLowerBlock n h K)).card : ℝ) := by
        rw [← Finset.sum_filter]
        simp [roughHeadFree]
        ring
  rw [roughRawCandidateSet, Finset.sum_union hdisjoint, hhigh, hbroad]

/-- The same exact mass formula on the paper's full domain `(n,2n]`. -/
theorem sum_roughHeadCompatibleRawWeight_Ioc
    {W n h K : ℕ} {α β L : ℝ} (hKh : K * h ≤ n) :
    ∑ a ∈ Finset.Ioc n (2 * n),
        roughHeadCompatibleRawWeight W n h K α β L a =
      α * ((roughHeadFree W (roughHighLowerBlock n h K)).card : ℝ) +
        (β / L) *
          ((roughHeadFree W (roughBroadLowerBlock n h K)).card : ℝ) := by
  rw [← roughRawCandidateSet_eq_Ioc hKh]
  exact sum_roughHeadCompatibleRawWeight W n h K α β L

/-- The literal raw mass in one complete rough row. -/
def roughHeadCompatibleRawRowMass
    (W n h K y label : ℕ) (α β L : ℝ) : ℝ :=
  ∑ a ∈ completeRoughRowFiber y (roughRawCandidateSet n h K) label,
    roughHeadCompatibleRawWeight W n h K α β L a

/-- Exact decomposition of the constructed raw point into the canonical
complete rough rows already used by floating rounding. -/
theorem sum_roughHeadCompatibleRawRowMass
    (W n h K y : ℕ) (α β L : ℝ) :
    ∑ a ∈ roughRawCandidateSet n h K,
        roughHeadCompatibleRawWeight W n h K α β L a =
      ∑ label ∈ completeRoughLabelSet y (roughRawCandidateSet n h K),
        roughHeadCompatibleRawRowMass W n h K y label α β L := by
  simpa only [roughHeadCompatibleRawRowMass] using
    sum_eq_sum_completeRoughRowFibers y (roughRawCandidateSet n h K)
      (roughHeadCompatibleRawWeight W n h K α β L)

/-! ## Exact head inclusion--exclusion and smooth physical shifts -/

/-- Exact finite Möbius inclusion--exclusion for head freedom on an
arbitrary finite set. -/
theorem roughHeadFree_card_eq_moebiusDivisorCounts
    (W : ℕ) (A : Finset ℕ) :
    ((roughHeadFree W A).card : ℤ) =
      ∑ d ∈ (roughHeadModulus W).divisors,
        ArithmeticFunction.moebius d *
          (((A.filter (d ∣ ·)).card : ℕ) : ℤ) := by
  let P : Erdos390.Full.HeadPattern.Pattern := roughHeadZeroPattern W
  rw [roughHeadFree, Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  change
    (∑ a ∈ A,
      if Nat.Coprime a P.modulus then (1 : ℤ) else 0) =
      ∑ d ∈ P.modulus.divisors,
        ArithmeticFunction.moebius d *
          (((A.filter (d ∣ ·)).card : ℕ) : ℤ)
  calc
    (∑ a ∈ A,
        if Nat.Coprime a P.modulus then (1 : ℤ) else 0) =
      ∑ a ∈ A, ∑ d ∈ P.modulus.divisors,
        if d ∣ a then ArithmeticFunction.moebius d else 0 := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [← P.coprimeWeight_eq_indicator,
        P.coprimeWeight_eq_divisor_sum]
    _ = ∑ d ∈ P.modulus.divisors, ∑ a ∈ A,
        if d ∣ a then ArithmeticFunction.moebius d else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ P.modulus.divisors,
        ArithmeticFunction.moebius d *
          (((A.filter (d ∣ ·)).card : ℕ) : ℤ) := by
      apply Finset.sum_congr rfl
      intro d _hd
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
        Nat.cast_one, Nat.cast_zero, Finset.mul_sum, mul_ite,
        mul_one, mul_zero]

/-- The head modulus is smooth at any cutoff `y ≥ W`; its divisors inherit
this property in the divisor-shift theorem below. -/
theorem roughHeadModulus_mem_smoothNumbers
    {W y : ℕ} (hWy : W ≤ y) :
    roughHeadModulus W ∈ Nat.smoothNumbers (y + 1) := by
  let P : Erdos390.Full.HeadPattern.Pattern := roughHeadZeroPattern W
  change P.modulus ∈ Nat.smoothNumbers (y + 1)
  apply modulus_mem_smoothNumbers P
  intro p hp
  change p ∈ primesUpTo W at hp
  exact (mem_primesUpTo.mp hp).2.trans hWy

/-- Head-free smooth integers in one literal half-open interval. -/
def roughHeadFreeSmoothInterval
    (W lo hi y : ℕ) : Finset ℕ :=
  roughHeadFree W (smoothInterval lo hi y)

/-- Exact inclusion--exclusion followed by the exact quotient-interval
reindexing for each head divisor. -/
theorem roughHeadFreeSmoothInterval_card_eq_divisorShift
    {W lo hi y : ℕ} (hWy : W ≤ y) :
    ((roughHeadFreeSmoothInterval W lo hi y).card : ℤ) =
      ∑ d ∈ (roughHeadModulus W).divisors,
        ArithmeticFunction.moebius d *
          (((smoothInterval (lo / d) (hi / d) y).card : ℕ) : ℤ) := by
  rw [roughHeadFreeSmoothInterval,
    roughHeadFree_card_eq_moebiusDivisorCounts]
  apply Finset.sum_congr rfl
  intro d hd
  have hdDvd : d ∣ roughHeadModulus W := (Nat.mem_divisors.mp hd).1
  have hdPos : 0 < d :=
    Nat.pos_of_dvd_of_pos hdDvd (roughHeadModulus_pos W)
  have hdSmooth : d ∈ Nat.smoothNumbers (y + 1) :=
    Nat.mem_smoothNumbers_of_dvd
      (roughHeadModulus_mem_smoothNumbers hWy) hdDvd
  rw [smooth_multiple_card_eq_quotient_interval hdPos hdSmooth]

/-- Real-cast form of the exact shifted smooth-interval identity. -/
theorem roughHeadFreeSmoothInterval_card_real_eq_divisorShift
    {W lo hi y : ℕ} (hWy : W ≤ y) :
    ((roughHeadFreeSmoothInterval W lo hi y).card : ℝ) =
      ∑ d ∈ (roughHeadModulus W).divisors,
        (ArithmeticFunction.moebius d : ℝ) *
          ((smoothInterval (lo / d) (hi / d) y).card : ℝ) := by
  have hZ := roughHeadFreeSmoothInterval_card_eq_divisorShift
    (W := W) (lo := lo) (hi := hi) (y := y) hWy
  have hR := congrArg (fun z : ℤ ↦ (z : ℝ)) hZ
  simpa only [Int.cast_natCast, Int.cast_sum, Int.cast_mul] using hR

/-- An unrestricted two-piece smooth physical block, with all integer
endpoint effects retained in the two finite cardinalities. -/
def roughSmoothPhysicalBlock
    (lo split hi y : ℕ) (α broad : ℝ) : ℝ :=
  α * ((smoothInterval split hi y).card : ℝ) +
    broad * ((smoothInterval lo split y).card : ℝ)

/-- The same physical block after imposing head coprimality. -/
def roughHeadFreeSmoothPhysicalBlock
    (W lo split hi y : ℕ) (α broad : ℝ) : ℝ :=
  α * ((roughHeadFreeSmoothInterval W split hi y).card : ℝ) +
    broad * ((roughHeadFreeSmoothInterval W lo split y).card : ℝ)

/-- Literal physical-shift identity: finite head inclusion--exclusion
turns the head-free physical block into the signed sum of unrestricted
blocks with every endpoint divided by the same head divisor. -/
theorem roughHeadFreeSmoothPhysicalBlock_eq_divisorShift
    {W lo split hi y : ℕ} {α broad : ℝ}
    (hWy : W ≤ y) :
    roughHeadFreeSmoothPhysicalBlock W lo split hi y α broad =
      ∑ d ∈ (roughHeadModulus W).divisors,
        (ArithmeticFunction.moebius d : ℝ) *
          roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
            α broad := by
  rw [roughHeadFreeSmoothPhysicalBlock,
    roughHeadFreeSmoothInterval_card_real_eq_divisorShift
      (W := W) (lo := split) (hi := hi) (y := y) hWy,
    roughHeadFreeSmoothInterval_card_real_eq_divisorShift
      (W := W) (lo := lo) (hi := split) (y := y) hWy,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [roughSmoothPhysicalBlock]
  ring

end

end Erdos390.WholePaper
