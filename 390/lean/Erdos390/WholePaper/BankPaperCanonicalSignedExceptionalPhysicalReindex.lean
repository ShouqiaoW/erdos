import Erdos390.WholePaper.BankPaperFourFiveRoughChamberReduction

/-!
# Exact physical reindexing of the signed exceptional smooth core

This file is the finite, endpoint-exact bridge between the core-first
exceptional ledger and the four-to-five rough chamber.

The paper's exceptional condition is the literal real inequality

`2 * n / R < n ^ deltaStar`.

Accordingly, the natural lower endpoint for a rough label is the floor of
`2 * n / n ^ deltaStar`, not the quotient formed from the safe natural
ceiling used elsewhere for clean-list estimates.  After fixing a positive
smooth core `b`, multiplication by `b` gives a bijection between each
exceptional physical fibre and a rough interval whose lower endpoint is
clipped by that real exceptional floor.

The last theorem specializes the identity to the actual paper depth
`K0 + 1`, balanced alpha, upper-tail length, and logarithmic scale.  No
rough-counting estimate or asymptotic input occurs here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## The literal real exceptional floor -/

/-- The largest natural rough label which can fail the paper's strict real
exceptional inequality.  Thus, for a positive rough label `r`,

`roughCanonicalRealExceptionalRoughCutoff n deltaStar < r`

is exactly `2*n/r < n^deltaStar`. -/
def roughCanonicalRealExceptionalRoughCutoff
    (n : Nat) (deltaStar : Real) : Nat :=
  ⌊2 * (n : Real) / (n : Real) ^ deltaStar⌋₊

/-- Exact conversion of the literal real exceptional inequality to the
strict natural cutoff supplied by the preceding floor. -/
theorem roughCanonicalRealExceptionalRoughCutoff_lt_iff
    {n r : Nat} {deltaStar : Real}
    (hn : 0 < n) (hr : 0 < r) :
    roughCanonicalRealExceptionalRoughCutoff n deltaStar < r ↔
      RoughCanonicalExceptionalLabel n deltaStar r := by
  have hnReal : (0 : Real) < (n : Real) := by
    exact_mod_cast hn
  have hrReal : (0 : Real) < (r : Real) := by
    exact_mod_cast hr
  have hpow : 0 < (n : Real) ^ deltaStar :=
    Real.rpow_pos_of_pos hnReal deltaStar
  rw [roughCanonicalRealExceptionalRoughCutoff,
    Nat.floor_lt' hr.ne']
  unfold RoughCanonicalExceptionalLabel
  rw [div_lt_iff₀ hpow, div_lt_iff₀ hrReal]
  simp only [mul_comm]

/-! ## Three clipped rough physical intervals -/

/-- Rough labels in the physical interval obtained from `(lo,hi]` after
fixing the smooth core `b`, with the lower endpoint clipped by the literal
real exceptional floor. -/
def roughCanonicalExceptionalClippedRoughInterval
    (n : Nat) (deltaStar : Real) (b lo hi : Nat) : Finset Nat :=
  fourFiveRoughInterval (yNat n)
    (max (lo / b)
      (roughCanonicalRealExceptionalRoughCutoff n deltaStar))
    (hi / b)

/-- The clipped upper piece corresponding to `(2n,2n+h]`. -/
def roughCanonicalExceptionalUpperPhysicalRoughInterval
    (n h : Nat) (deltaStar : Real) (b : Nat) : Finset Nat :=
  roughCanonicalExceptionalClippedRoughInterval
    n deltaStar b (2 * n) (2 * n + h)

/-- The clipped high lower piece corresponding to `(2n-Kh,2n]`. -/
def roughCanonicalExceptionalHighPhysicalRoughInterval
    (n h K : Nat) (deltaStar : Real) (b : Nat) : Finset Nat :=
  roughCanonicalExceptionalClippedRoughInterval
    n deltaStar b (2 * n - K * h) (2 * n)

/-- The clipped broad lower piece corresponding to `(n,2n-Kh]`. -/
def roughCanonicalExceptionalBroadPhysicalRoughInterval
    (n h K : Nat) (deltaStar : Real) (b : Nat) : Finset Nat :=
  roughCanonicalExceptionalClippedRoughInterval
    n deltaStar b n (2 * n - K * h)

/-- Membership in a clipped interval is precisely intrinsic roughness,
literal real exceptionality, and membership of `b*r` in the original
physical interval. -/
@[simp]
theorem mem_roughCanonicalExceptionalClippedRoughInterval
    {n b lo hi r : Nat} {deltaStar : Real}
    (hn : 0 < n) (hb : 0 < b) :
    r ∈ roughCanonicalExceptionalClippedRoughInterval
        n deltaStar b lo hi ↔
      IsCompleteRoughLabel (yNat n) r ∧
        RoughCanonicalExceptionalLabel n deltaStar r ∧
        lo < b * r ∧ b * r ≤ hi := by
  rw [roughCanonicalExceptionalClippedRoughInterval,
    mem_fourFiveRoughInterval]
  constructor
  · rintro ⟨hrLower, hrUpper, hrough⟩
    have hrPos : 0 < r := by
      exact lt_of_le_of_lt (Nat.zero_le _) hrLower
    have hrLowerData := (max_lt_iff.mp hrLower)
    have hlo : lo < b * r := by
      have hlo' := (Nat.div_lt_iff_lt_mul hb).mp hrLowerData.1
      simpa only [Nat.mul_comm] using hlo'
    have hhi : b * r ≤ hi := by
      have hhi' := (Nat.le_div_iff_mul_le hb).mp hrUpper
      simpa only [Nat.mul_comm] using hhi'
    have hlabel : IsCompleteRoughLabel (yNat n) r := by
      refine ⟨hrPos, ?_⟩
      intro q hqFactor
      have hqMem : q ∈ r.primeFactorsList := by
        rw [← Nat.primeFactorsList_count_eq] at hqFactor
        exact List.count_pos_iff.mp (Nat.pos_of_ne_zero hqFactor)
      exact hrough q hqMem
    exact ⟨hlabel,
      (roughCanonicalRealExceptionalRoughCutoff_lt_iff
        hn hrPos).mp hrLowerData.2,
      hlo, hhi⟩
  · rintro ⟨hlabel, hexceptional, hlo, hhi⟩
    refine ⟨max_lt_iff.mpr ⟨?_, ?_⟩, ?_, ?_⟩
    · have hlo' := (Nat.div_lt_iff_lt_mul hb).mpr
        (by simpa only [Nat.mul_comm] using hlo)
      exact hlo'
    · exact
        (roughCanonicalRealExceptionalRoughCutoff_lt_iff
          hn hlabel.1).mpr hexceptional
    · exact (Nat.le_div_iff_mul_le hb).mpr
        (by simpa only [Nat.mul_comm] using hhi)
    · intro q hqMem
      apply hlabel.2 q
      rw [← Nat.primeFactorsList_count_eq]
      exact (List.count_pos_iff.mpr hqMem).ne'

/-! ## A generic physical smooth fibre -/

/-- Positive integers in `(lo,hi]` which lie in an exceptional complete
rough row and have complete smooth part exactly `b`. -/
def roughCanonicalExceptionalPhysicalSmoothFiber
    (n lo hi : Nat) (deltaStar : Real) (b : Nat) : Finset Nat := by
  classical
  exact (Finset.Ioc lo hi).filter fun a =>
    RoughCanonicalExceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) a) ∧
        completeSmoothPart (yNat n) a = b

@[simp]
theorem mem_roughCanonicalExceptionalPhysicalSmoothFiber
    {n lo hi a b : Nat} {deltaStar : Real} :
    a ∈ roughCanonicalExceptionalPhysicalSmoothFiber
        n lo hi deltaStar b ↔
      lo < a ∧ a ≤ hi ∧
        RoughCanonicalExceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) a) ∧
        completeSmoothPart (yNat n) a = b := by
  classical
  simp only [roughCanonicalExceptionalPhysicalSmoothFiber,
    Finset.mem_filter, Finset.mem_Ioc]
  tauto

/-- The complementary factor of an intrinsic rough label times a positive
smooth integer is exactly that smooth integer. -/
theorem completeSmoothPart_mul_eq_of_isCompleteRoughLabel_of_smooth
    {y r b : Nat}
    (hr : IsCompleteRoughLabel y r)
    (hb : b ∈ Nat.smoothNumbers (y + 1)) :
    completeSmoothPart y (r * b) = b := by
  have hrough :=
    completeRoughLabel_mul_eq_of_isCompleteRoughLabel_of_smooth hr hb
  have hdecomp := completeRoughLabel_mul_completeSmoothPart y (r * b)
  rw [hrough] at hdecomp
  exact Nat.mul_left_cancel hr.1 hdecomp

/-- Fixing a positive smooth core makes multiplication by that core a
bijection from the exceptional physical fibre to its clipped rough
interval. -/
theorem roughCanonicalExceptionalPhysicalSmoothFiber_card_eq_clippedRoughInterval
    {n b lo hi : Nat} {deltaStar : Real}
    (hn : 0 < n) (hb : 0 < b)
    (hbSmooth : b ∈ Nat.smoothNumbers (yNat n + 1)) :
    (roughCanonicalExceptionalPhysicalSmoothFiber
        n lo hi deltaStar b).card =
      (roughCanonicalExceptionalClippedRoughInterval
        n deltaStar b lo hi).card := by
  apply Finset.card_bij
    (fun a _ha => completeRoughLabel (yNat n) a)
  · intro a ha
    have haData :=
      mem_roughCanonicalExceptionalPhysicalSmoothFiber.mp ha
    have haPos : 0 < a := by omega
    let r := completeRoughLabel (yNat n) a
    have hr : IsCompleteRoughLabel (yNat n) r := by
      refine ⟨completeRoughLabel_pos (yNat n) a, ?_⟩
      intro p hp
      exact completeRoughLabel_factorization_support hp
    have hproduct :
        b * completeRoughLabel (yNat n) a = a := by
      simpa only [haData.2.2.2, Nat.mul_comm] using
        completeRoughLabel_mul_completeSmoothPart (yNat n) a
    apply
      (mem_roughCanonicalExceptionalClippedRoughInterval hn hb).mpr
    exact ⟨hr, haData.2.2.1,
      by simpa only [hproduct] using haData.1,
      by simpa only [hproduct] using haData.2.1⟩
  · intro a₁ ha₁ a₂ ha₂ heq
    have ha₁Data :=
      mem_roughCanonicalExceptionalPhysicalSmoothFiber.mp ha₁
    have ha₂Data :=
      mem_roughCanonicalExceptionalPhysicalSmoothFiber.mp ha₂
    calc
      a₁ = completeRoughLabel (yNat n) a₁ *
          completeSmoothPart (yNat n) a₁ :=
        (completeRoughLabel_mul_completeSmoothPart (yNat n) a₁).symm
      _ = completeRoughLabel (yNat n) a₂ *
          completeSmoothPart (yNat n) a₂ := by
        rw [heq, ha₁Data.2.2.2, ha₂Data.2.2.2]
      _ = a₂ :=
        completeRoughLabel_mul_completeSmoothPart (yNat n) a₂
  · intro r hrMem
    have hrData :=
      (mem_roughCanonicalExceptionalClippedRoughInterval hn hb).mp hrMem
    have hrough :=
      completeRoughLabel_mul_eq_of_isCompleteRoughLabel_of_smooth
        hrData.1 hbSmooth
    have hsmooth :=
      completeSmoothPart_mul_eq_of_isCompleteRoughLabel_of_smooth
        hrData.1 hbSmooth
    refine ⟨r * b, ?_, ?_⟩
    · apply
        mem_roughCanonicalExceptionalPhysicalSmoothFiber.mpr
      refine ⟨?_, ?_, ?_, hsmooth⟩
      · simpa only [Nat.mul_comm] using hrData.2.2.1
      · simpa only [Nat.mul_comm] using hrData.2.2.2
      · simpa only [hrough] using hrData.2.1
    · exact hrough

/-! ## Identification of the literal upper and lower fibres -/

/-- The already-defined literal upper exceptional fibre is the generic
physical smooth fibre on `(2n,2n+h]`. -/
theorem paperExceptionalSmoothFiber_eq_physicalSmoothFiber
    (n h b : Nat) (deltaStar : Real) :
    paperExceptionalSmoothFiber n h deltaStar b =
      roughCanonicalExceptionalPhysicalSmoothFiber
        n (2 * n) (2 * n + h) deltaStar b := by
  ext a
  simp only [mem_paperExceptionalSmoothFiber,
    mem_paperExceptionalUpperFactors, roughUpperBlock,
    Finset.mem_Ioc,
    mem_roughCanonicalExceptionalPhysicalSmoothFiber,
    RoughCanonicalExceptionalLabel]
  tauto

/-- Exact upper-fibre cardinality in the clipped rough interval. -/
theorem paperExceptionalSmoothFiber_card_eq_upperPhysicalRoughInterval
    {n h b : Nat} {deltaStar : Real}
    (hn : 0 < n) (hb : 0 < b)
    (hbSmooth : b ∈ Nat.smoothNumbers (yNat n + 1)) :
    (paperExceptionalSmoothFiber n h deltaStar b).card =
      (roughCanonicalExceptionalUpperPhysicalRoughInterval
        n h deltaStar b).card := by
  rw [paperExceptionalSmoothFiber_eq_physicalSmoothFiber]
  exact
    roughCanonicalExceptionalPhysicalSmoothFiber_card_eq_clippedRoughInterval
      hn hb hbSmooth

/-- The exceptional lower smooth fibre is the disjoint union of its high
and broad physical pieces. -/
theorem roughCanonicalExceptionalRawLowerSmoothFiber_eq_physical_union
    (n h K b : Nat) (deltaStar : Real) :
    roughCanonicalExceptionalRawLowerSmoothFiber
        n h K deltaStar b =
      roughCanonicalExceptionalPhysicalSmoothFiber
          n (2 * n - K * h) (2 * n) deltaStar b ∪
        roughCanonicalExceptionalPhysicalSmoothFiber
          n n (2 * n - K * h) deltaStar b := by
  ext a
  simp only [mem_roughCanonicalExceptionalRawLowerSmoothFiber,
    mem_roughCanonicalExceptionalRawLowerSet,
    roughRawCandidateSet, roughHighLowerBlock,
    roughBroadLowerBlock, Finset.mem_union, Finset.mem_Ioc,
    mem_roughCanonicalExceptionalPhysicalSmoothFiber,
    RoughCanonicalExceptionalLabel]
  tauto

/-- The high and broad exceptional physical fibres remain disjoint after
all exceptional and smooth-core filters. -/
theorem roughCanonicalExceptionalPhysicalSmoothFiber_high_disjoint_broad
    (n h K b : Nat) (deltaStar : Real) :
    Disjoint
      (roughCanonicalExceptionalPhysicalSmoothFiber
        n (2 * n - K * h) (2 * n) deltaStar b)
      (roughCanonicalExceptionalPhysicalSmoothFiber
        n n (2 * n - K * h) deltaStar b) := by
  rw [Finset.disjoint_left]
  intro a haHigh haBroad
  have haHighData :=
    mem_roughCanonicalExceptionalPhysicalSmoothFiber.mp haHigh
  have haBroadData :=
    mem_roughCanonicalExceptionalPhysicalSmoothFiber.mp haBroad
  omega

/-- Multiplication by the complete rough label does not affect fixed-head
coprimality.  Thus head freedom of a positive factor is exactly head
freedom of its complete smooth core. -/
theorem coprime_roughHeadModulus_iff_completeSmoothPart
    {W y a : Nat} (hWy : W ≤ y) (_ha : 0 < a) :
    Nat.Coprime a (roughHeadModulus W) ↔
      Nat.Coprime (completeSmoothPart y a) (roughHeadModulus W) := by
  let r := completeRoughLabel y a
  let b := completeSmoothPart y a
  have hr : IsCompleteRoughLabel y r := by
    refine ⟨completeRoughLabel_pos y a, ?_⟩
    intro p hp
    exact completeRoughLabel_factorization_support hp
  have hrCop :
      Nat.Coprime r (roughHeadModulus W) :=
    isCompleteRoughLabel_coprime_roughHeadModulus hWy hr
  have hproduct : r * b = a :=
    completeRoughLabel_mul_completeSmoothPart y a
  constructor
  · intro haCop
    rw [← hproduct] at haCop
    exact (Nat.coprime_mul_iff_left.mp haCop).2
  · intro hbCop
    rw [← hproduct]
    exact Nat.coprime_mul_iff_left.mpr ⟨hrCop, hbCop⟩

/-- On the exceptional high fibre the raw weight is the one constant
selected by head freedom of the fixed smooth core. -/
theorem roughHeadCompatibleRawWeight_eq_highCoreCoefficient
    {W n h K a b : Nat} {deltaStar alpha beta logScale : Real}
    (hWy : W ≤ yNat n)
    (ha : a ∈ roughCanonicalExceptionalPhysicalSmoothFiber
      n (2 * n - K * h) (2 * n) deltaStar b) :
    roughHeadCompatibleRawWeight
        W n h K alpha beta logScale a =
      if Nat.Coprime b (roughHeadModulus W) then alpha else 0 := by
  have haData :=
    mem_roughCanonicalExceptionalPhysicalSmoothFiber.mp ha
  have haPos : 0 < a := by omega
  have hcop :=
    coprime_roughHeadModulus_iff_completeSmoothPart hWy haPos
  rw [haData.2.2.2] at hcop
  have haHigh : a ∈ roughHighLowerBlock n h K := by
    simpa only [roughHighLowerBlock, Finset.mem_Ioc] using
      And.intro haData.1 haData.2.1
  have haBroad : a ∉ roughBroadLowerBlock n h K := by
    intro haBroad
    exact
      (Finset.disjoint_left.mp
        (roughHighLowerBlock_disjoint_roughBroadLowerBlock n h K))
        haHigh haBroad
  by_cases hbCop : Nat.Coprime b (roughHeadModulus W)
  · have haCop : Nat.Coprime a (roughHeadModulus W) :=
      hcop.mpr hbCop
    rw [roughHeadCompatibleRawWeight, if_pos haCop, if_pos hbCop]
    simp only [roughFiniteIndicator, if_pos haHigh, if_neg haBroad,
      mul_one, mul_zero, add_zero]
  · have haCop : ¬Nat.Coprime a (roughHeadModulus W) := by
      exact fun h => hbCop (hcop.mp h)
    rw [roughHeadCompatibleRawWeight, if_neg haCop, if_neg hbCop]

/-- On the exceptional broad fibre the raw weight is the broad constant
selected by head freedom of the fixed smooth core. -/
theorem roughHeadCompatibleRawWeight_eq_broadCoreCoefficient
    {W n h K a b : Nat} {deltaStar alpha beta logScale : Real}
    (hWy : W ≤ yNat n)
    (ha : a ∈ roughCanonicalExceptionalPhysicalSmoothFiber
      n n (2 * n - K * h) deltaStar b) :
    roughHeadCompatibleRawWeight
        W n h K alpha beta logScale a =
      if Nat.Coprime b (roughHeadModulus W) then
        beta / logScale else 0 := by
  have haData :=
    mem_roughCanonicalExceptionalPhysicalSmoothFiber.mp ha
  have haPos : 0 < a := by omega
  have hcop :=
    coprime_roughHeadModulus_iff_completeSmoothPart hWy haPos
  rw [haData.2.2.2] at hcop
  have haBroad : a ∈ roughBroadLowerBlock n h K := by
    simpa only [roughBroadLowerBlock, Finset.mem_Ioc] using
      And.intro haData.1 haData.2.1
  have haHigh : a ∉ roughHighLowerBlock n h K := by
    intro haHigh
    exact
      (Finset.disjoint_left.mp
        (roughHighLowerBlock_disjoint_roughBroadLowerBlock n h K))
        haHigh haBroad
  by_cases hbCop : Nat.Coprime b (roughHeadModulus W)
  · have haCop : Nat.Coprime a (roughHeadModulus W) :=
      hcop.mpr hbCop
    rw [roughHeadCompatibleRawWeight, if_pos haCop, if_pos hbCop]
    simp only [roughFiniteIndicator, if_neg haHigh, if_pos haBroad,
      mul_zero, mul_one, zero_add]
  · have haCop : ¬Nat.Coprime a (roughHeadModulus W) := by
      exact fun h => hbCop (hcop.mp h)
    rw [roughHeadCompatibleRawWeight, if_neg haCop, if_neg hbCop]

/-- Exact weighted lower-fibre reindexing into the two clipped rough
physical intervals. -/
theorem sum_roughCanonicalExceptionalRawLowerSmoothFiber_rawWeight_eq_twoPhysicalIntervals
    {W n h K b : Nat} {deltaStar alpha beta logScale : Real}
    (hn : 0 < n) (hb : 0 < b) (hWy : W ≤ yNat n)
    (hbSmooth : b ∈ Nat.smoothNumbers (yNat n + 1)) :
    (∑ a ∈ roughCanonicalExceptionalRawLowerSmoothFiber
        n h K deltaStar b,
      roughHeadCompatibleRawWeight
        W n h K alpha beta logScale a) =
      (if Nat.Coprime b (roughHeadModulus W) then alpha else 0) *
          ((roughCanonicalExceptionalHighPhysicalRoughInterval
            n h K deltaStar b).card : Real) +
        (if Nat.Coprime b (roughHeadModulus W) then
            beta / logScale else 0) *
          ((roughCanonicalExceptionalBroadPhysicalRoughInterval
            n h K deltaStar b).card : Real) := by
  let highFiber :=
    roughCanonicalExceptionalPhysicalSmoothFiber
      n (2 * n - K * h) (2 * n) deltaStar b
  let broadFiber :=
    roughCanonicalExceptionalPhysicalSmoothFiber
      n n (2 * n - K * h) deltaStar b
  let highCoefficient : Real :=
    if Nat.Coprime b (roughHeadModulus W) then alpha else 0
  let broadCoefficient : Real :=
    if Nat.Coprime b (roughHeadModulus W) then
      beta / logScale else 0
  have hhigh :
      (∑ a ∈ highFiber,
        roughHeadCompatibleRawWeight
          W n h K alpha beta logScale a) =
        highCoefficient * (highFiber.card : Real) := by
    calc
      (∑ a ∈ highFiber,
          roughHeadCompatibleRawWeight
            W n h K alpha beta logScale a) =
          ∑ _a ∈ highFiber, highCoefficient := by
        apply Finset.sum_congr rfl
        intro a ha
        exact
          roughHeadCompatibleRawWeight_eq_highCoreCoefficient
            hWy ha
      _ = highCoefficient * (highFiber.card : Real) := by
        simp [mul_comm]
  have hbroad :
      (∑ a ∈ broadFiber,
        roughHeadCompatibleRawWeight
          W n h K alpha beta logScale a) =
        broadCoefficient * (broadFiber.card : Real) := by
    calc
      (∑ a ∈ broadFiber,
          roughHeadCompatibleRawWeight
            W n h K alpha beta logScale a) =
          ∑ _a ∈ broadFiber, broadCoefficient := by
        apply Finset.sum_congr rfl
        intro a ha
        exact
          roughHeadCompatibleRawWeight_eq_broadCoreCoefficient
            hWy ha
      _ = broadCoefficient * (broadFiber.card : Real) := by
        simp [mul_comm]
  have hhighCard :
      highFiber.card =
        (roughCanonicalExceptionalHighPhysicalRoughInterval
          n h K deltaStar b).card := by
    exact
      roughCanonicalExceptionalPhysicalSmoothFiber_card_eq_clippedRoughInterval
        hn hb hbSmooth
  have hbroadCard :
      broadFiber.card =
        (roughCanonicalExceptionalBroadPhysicalRoughInterval
          n h K deltaStar b).card := by
    exact
      roughCanonicalExceptionalPhysicalSmoothFiber_card_eq_clippedRoughInterval
        hn hb hbSmooth
  rw [roughCanonicalExceptionalRawLowerSmoothFiber_eq_physical_union,
    Finset.sum_union
      (roughCanonicalExceptionalPhysicalSmoothFiber_high_disjoint_broad
        n h K b deltaStar)]
  change
    (∑ a ∈ highFiber,
        roughHeadCompatibleRawWeight
          W n h K alpha beta logScale a) +
      (∑ a ∈ broadFiber,
        roughHeadCompatibleRawWeight
          W n h K alpha beta logScale a) = _
  rw [hhigh, hbroad, hhighCard, hbroadCard]

/-! ## The exact three-piece core identity -/

/-- For a positive smooth core, the literal signed exceptional core mass is
exactly the upper clipped rough count minus the two raw-weighted clipped
lower rough counts. -/
theorem roughCanonicalSignedExceptionalCoreMass_eq_threePhysicalIntervals
    {W n h K b : Nat} {deltaStar alpha beta logScale : Real}
    (hn : 0 < n) (hb : 0 < b) (hWy : W ≤ yNat n)
    (hbSmooth : b ∈ Nat.smoothNumbers (yNat n + 1)) :
    roughCanonicalSignedExceptionalCoreMass
        n h K deltaStar
        (roughHeadCompatibleRawWeight
          W n h K alpha beta logScale) b =
      ((roughCanonicalExceptionalUpperPhysicalRoughInterval
        n h deltaStar b).card : Real) -
        ((if Nat.Coprime b (roughHeadModulus W) then alpha else 0) *
            ((roughCanonicalExceptionalHighPhysicalRoughInterval
              n h K deltaStar b).card : Real) +
          (if Nat.Coprime b (roughHeadModulus W) then
              beta / logScale else 0) *
            ((roughCanonicalExceptionalBroadPhysicalRoughInterval
              n h K deltaStar b).card : Real)) := by
  unfold roughCanonicalSignedExceptionalCoreMass
  rw [paperExceptionalSmoothFiber_card_eq_upperPhysicalRoughInterval
      hn hb hbSmooth,
    sum_roughCanonicalExceptionalRawLowerSmoothFiber_rawWeight_eq_twoPhysicalIntervals
      hn hb hWy hbSmooth]

/-- Every positive core in the canonical common prefix is automatically
`yNat n`-smooth once the whole prefix lies below `yNat n`. -/
theorem smooth_of_mem_exceptionalCorePrefix
    {n b : Nat} {deltaStar : Real}
    (hb : b ∈ Finset.Icc 1
      (2 * tangentPaperExceptionalCutoff deltaStar n))
    (hcutY : 2 * tangentPaperExceptionalCutoff deltaStar n ≤ yNat n) :
    b ∈ Nat.smoothNumbers (yNat n + 1) := by
  have hbData := Finset.mem_Icc.mp hb
  apply Nat.mem_smoothNumbers_of_lt hbData.1
  exact Nat.lt_succ_of_le (hbData.2.trans hcutY)

/-- Core-prefix form of the exact three-piece identity.  This is the form
needed by both the deep prefix and the one cutoff band. -/
theorem roughCanonicalSignedExceptionalCoreMass_eq_threePhysicalIntervals_of_mem_prefix
    {W n h K b : Nat} {deltaStar alpha beta logScale : Real}
    (hn : 0 < n) (hWy : W ≤ yNat n)
    (hb : b ∈ Finset.Icc 1
      (2 * tangentPaperExceptionalCutoff deltaStar n))
    (hcutY : 2 * tangentPaperExceptionalCutoff deltaStar n ≤ yNat n) :
    roughCanonicalSignedExceptionalCoreMass
        n h K deltaStar
        (roughHeadCompatibleRawWeight
          W n h K alpha beta logScale) b =
      ((roughCanonicalExceptionalUpperPhysicalRoughInterval
        n h deltaStar b).card : Real) -
        ((if Nat.Coprime b (roughHeadModulus W) then alpha else 0) *
            ((roughCanonicalExceptionalHighPhysicalRoughInterval
              n h K deltaStar b).card : Real) +
          (if Nat.Coprime b (roughHeadModulus W) then
              beta / logScale else 0) *
            ((roughCanonicalExceptionalBroadPhysicalRoughInterval
              n h K deltaStar b).card : Real)) := by
  exact roughCanonicalSignedExceptionalCoreMass_eq_threePhysicalIntervals
    hn (Finset.mem_Icc.mp hb).1 hWy
      (smooth_of_mem_exceptionalCorePrefix hb hcutY)

/-- Paper-parameter specialization: actual upper-tail length, actual
balanced alpha, logarithmic scale `L n`, and the required positive chamber
depth `K0 + 1`.  This is still a finite equality; positivity and size
conditions for later kernel freezing are intentionally not hidden here. -/
theorem roughCanonicalSignedExceptionalCoreMass_paper_K0_succ_eq_threePhysicalIntervals
    {W n K0 b : Nat} {c deltaStar beta : Real}
    (hn : 0 < n) (hWy : W ≤ yNat n)
    (hb : b ∈ Finset.Icc 1
      (2 * tangentPaperExceptionalCutoff deltaStar n))
    (hcutY : 2 * tangentPaperExceptionalCutoff deltaStar n ≤ yNat n) :
    roughCanonicalSignedExceptionalCoreMass
        n (upperTailLength c n) (K0 + 1) deltaStar
        (roughHeadCompatibleRawWeight
          W n (upperTailLength c n) (K0 + 1)
          (roughHeadBalancedAlpha
            W n (upperTailLength c n) (K0 + 1) beta (L n))
          beta (L n)) b =
      ((roughCanonicalExceptionalUpperPhysicalRoughInterval
        n (upperTailLength c n) deltaStar b).card : Real) -
        ((if Nat.Coprime b (roughHeadModulus W) then
            roughHeadBalancedAlpha
              W n (upperTailLength c n) (K0 + 1) beta (L n)
          else 0) *
            ((roughCanonicalExceptionalHighPhysicalRoughInterval
              n (upperTailLength c n) (K0 + 1) deltaStar b).card : Real) +
          (if Nat.Coprime b (roughHeadModulus W) then
              beta / L n else 0) *
            ((roughCanonicalExceptionalBroadPhysicalRoughInterval
              n (upperTailLength c n) (K0 + 1) deltaStar b).card :
                Real)) := by
  exact
    roughCanonicalSignedExceptionalCoreMass_eq_threePhysicalIntervals_of_mem_prefix
      hn hWy hb hcutY

end BankPaperRealization

end

end Erdos390.WholePaper
