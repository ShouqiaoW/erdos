import Erdos390.WholePaper.RoughSaiasWeightedTransition
import Erdos390.WholePaper.CompleteRoughDecomposition
import Erdos390.WholePaper.CanonicalCompleteRoughRows

/-!
# Canonical-row consumer for the weighted Saias block

The analytic four-endpoint expression is useful to the construction only
after it is tied back to the literal complete-rough row used by floating
rounding.  This file supplies that consumer-facing bridge.  The sum over a
canonical `rowSet` is identified unconditionally with the already-defined
literal raw row mass.  The upper quota minus that mass is then connected to
`roughPhysicalFriableCombination` and hence to the weighted Saias bound.

The upper endpoint identification is an exact equality.  Finite head
inclusion--exclusion and the fixed-head physical shift occur between the
literal raw mass and the density-scaled four-endpoint block in the paper,
so their error is retained as a separate explicit allowance.  It is not
silently folded into the HT--Saias hypothesis.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-- The literal upper-row quota attached to a complete rough label. -/
def roughUpperCompleteRoughRowTarget
    (n h y label : ℕ) : ℕ :=
  (completeRoughRowFiber y (roughUpperBlock n h) label).card

/-- The unrestricted two-piece lower smooth mass at the three physical
endpoints. -/
def roughPhysicalLowerFriableMass
    (α β L : ℝ) (X Xminus Xhalf y : ℕ) : ℝ :=
  α * ((FriableAsymptotic.friableCount X y : ℝ) -
      (FriableAsymptotic.friableCount Xminus y : ℝ)) +
    (β / L) * ((FriableAsymptotic.friableCount Xminus y : ℝ) -
      (FriableAsymptotic.friableCount Xhalf y : ℝ))

/-- Intrinsic characterization needed to reindex one complete-rough row:
the label is positive and every factorization coordinate in its support is
strictly above the smooth cutoff. -/
def IsCompleteRoughLabel (y label : ℕ) : Prop :=
  0 < label ∧ ∀ p, label.factorization p ≠ 0 → y < p

/-- Every attained canonical row label has the intrinsic complete-rough
support property. -/
theorem isCompleteRoughLabel_of_canonicalCompleteRoughRow
    {y : ℕ} {A : Finset ℕ}
    (row : CanonicalCompleteRoughRow y A) :
    IsCompleteRoughLabel y row.1 := by
  constructor
  · exact canonicalCompleteRoughRow_label_pos y A row
  · obtain ⟨a, _ha, hlabel⟩ := mem_completeRoughLabelSet.mp row.2
    intro p hp
    rw [← hlabel] at hp
    exact completeRoughLabel_factorization_support hp

/-- Multiplying an intrinsic complete-rough label by a positive smooth
integer leaves that complete rough label unchanged. -/
theorem completeRoughLabel_mul_eq_of_isCompleteRoughLabel_of_smooth
    {y label s : ℕ}
    (hlabel : IsCompleteRoughLabel y label)
    (hs : s ∈ Nat.smoothNumbers (y + 1)) :
    completeRoughLabel y (label * s) = label := by
  have hsPos : 0 < s :=
    (Nat.mem_smoothNumbers.mp hs).1.bot_lt
  have hsSupport : ∀ p, s.factorization p ≠ 0 → p ≤ y := by
    intro p hp
    have hpPrime : p.Prime := by
      by_contra hnotPrime
      rw [Nat.factorization_eq_zero_of_not_prime s hnotPrime] at hp
      exact hp rfl
    have hpDvd : p ∣ s := Nat.dvd_of_factorization_pos hp
    have hpLt := (Nat.mem_smoothNumbers').mp hs p hpPrime hpDvd
    omega
  have hunique := completeRoughDecomposition_unique
    (y := y) (a := label * s) (rough := label) (smooth := s)
      hlabel.1.ne' hsPos.ne' rfl hlabel.2 hsSupport
  exact hunique.1.symm

/-- Exact row-to-smooth-quotient reindexing on an arbitrary natural
half-open interval. -/
theorem completeRoughRowFiber_Ioc_card_eq_smoothInterval
    {lo hi y label : ℕ} (hlabel : IsCompleteRoughLabel y label) :
    (completeRoughRowFiber y (Finset.Ioc lo hi) label).card =
      (Erdos390.Full.StructuredCells.smoothInterval
        (lo / label) (hi / label) y).card := by
  apply Finset.card_bij (fun a _ha ↦ a / label)
  · intro a ha
    rw [mem_completeRoughRowFiber] at ha
    have haInterval := Finset.mem_Ioc.mp ha.1
    have hdvd : label ∣ a := by
      rw [← ha.2]
      exact completeRoughLabel_dvd y a
    apply Erdos390.Full.StructuredCells.mem_smoothInterval.mpr
    constructor
    · apply (Nat.div_lt_iff_lt_mul hlabel.1).mpr
      simpa [Nat.div_mul_cancel hdvd] using haInterval.1
    · constructor
      · apply (Nat.le_div_iff_mul_le hlabel.1).mpr
        simpa [Nat.div_mul_cancel hdvd] using haInterval.2
      · have haPos : 0 < a := Nat.zero_lt_of_lt haInterval.1
        simpa only [completeSmoothPart, ha.2] using
          completeSmoothPart_mem_smoothNumbers (y := y) haPos
  · intro a₁ ha₁ a₂ ha₂ heq
    rw [mem_completeRoughRowFiber] at ha₁ ha₂
    have hdvd₁ : label ∣ a₁ := by
      rw [← ha₁.2]
      exact completeRoughLabel_dvd y a₁
    have hdvd₂ : label ∣ a₂ := by
      rw [← ha₂.2]
      exact completeRoughLabel_dvd y a₂
    calc
      a₁ = a₁ / label * label := (Nat.div_mul_cancel hdvd₁).symm
      _ = a₂ / label * label := by rw [heq]
      _ = a₂ := Nat.div_mul_cancel hdvd₂
  · intro s hs
    have hsData :=
      Erdos390.Full.StructuredCells.mem_smoothInterval.mp hs
    refine ⟨label * s, ?_, ?_⟩
    · apply mem_completeRoughRowFiber.mpr
      constructor
      · apply Finset.mem_Ioc.mpr
        constructor
        · have hlo := (Nat.div_lt_iff_lt_mul hlabel.1).mp hsData.1
          simpa only [Nat.mul_comm] using hlo
        · have hhi := (Nat.le_div_iff_mul_le hlabel.1).mp hsData.2.1
          simpa only [Nat.mul_comm] using hhi
      · exact completeRoughLabel_mul_eq_of_isCompleteRoughLabel_of_smooth
          hlabel hsData.2.2
    · simpa only [Nat.mul_comm] using Nat.mul_div_left s hlabel.1

/-- A complete-rough label is coprime to the fixed head modulus whenever
the head cutoff is at most the smooth cutoff. -/
theorem isCompleteRoughLabel_coprime_roughHeadModulus
    {W y label : ℕ} (hWy : W ≤ y)
    (hlabel : IsCompleteRoughLabel y label) :
    Nat.Coprime label (roughHeadModulus W) := by
  by_contra hnot
  obtain ⟨p, hpPrime, hpLabel, hpHead⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hpFactor := hpPrime.factorization_pos_of_dvd hlabel.1.ne' hpLabel
  have hpHigh : y < p := hlabel.2 p hpFactor.ne'
  have hheadSmooth : roughHeadModulus W ∈
      Nat.smoothNumbers (y + 1) :=
    roughHeadModulus_mem_smoothNumbers hWy
  have hpLow :=
    (Nat.mem_smoothNumbers').mp hheadSmooth p hpPrime hpHead
  omega

/-- Head-free version of the exact row-to-smooth-quotient reindexing. -/
theorem completeRoughRowFiber_headFreeIoc_card_eq_headFreeSmoothInterval
    {W lo hi y label : ℕ}
    (hlabel : IsCompleteRoughLabel y label)
    (hcop : Nat.Coprime label (roughHeadModulus W)) :
    (completeRoughRowFiber y
        (roughHeadFree W (Finset.Ioc lo hi)) label).card =
      (roughHeadFreeSmoothInterval W (lo / label) (hi / label) y).card := by
  apply Finset.card_bij (fun a _ha ↦ a / label)
  · intro a ha
    rw [mem_completeRoughRowFiber] at ha
    have haHead := mem_roughHeadFree.mp ha.1
    have haInterval := Finset.mem_Ioc.mp haHead.1
    have hdvd : label ∣ a := by
      rw [← ha.2]
      exact completeRoughLabel_dvd y a
    apply mem_roughHeadFree.mpr
    constructor
    · apply Erdos390.Full.StructuredCells.mem_smoothInterval.mpr
      constructor
      · apply (Nat.div_lt_iff_lt_mul hlabel.1).mpr
        simpa [Nat.div_mul_cancel hdvd] using haInterval.1
      · constructor
        · apply (Nat.le_div_iff_mul_le hlabel.1).mpr
          simpa [Nat.div_mul_cancel hdvd] using haInterval.2
        · have haPos : 0 < a := Nat.zero_lt_of_lt haInterval.1
          simpa only [completeSmoothPart, ha.2] using
            completeSmoothPart_mem_smoothNumbers (y := y) haPos
    · rw [← Nat.div_mul_cancel hdvd] at haHead
      exact (Nat.coprime_mul_iff_left.mp haHead.2).1
  · intro a₁ ha₁ a₂ ha₂ heq
    rw [mem_completeRoughRowFiber] at ha₁ ha₂
    have hdvd₁ : label ∣ a₁ := by
      rw [← ha₁.2]
      exact completeRoughLabel_dvd y a₁
    have hdvd₂ : label ∣ a₂ := by
      rw [← ha₂.2]
      exact completeRoughLabel_dvd y a₂
    calc
      a₁ = a₁ / label * label := (Nat.div_mul_cancel hdvd₁).symm
      _ = a₂ / label * label := by rw [heq]
      _ = a₂ := Nat.div_mul_cancel hdvd₂
  · intro s hs
    have hsHead := mem_roughHeadFree.mp hs
    have hsData :=
      Erdos390.Full.StructuredCells.mem_smoothInterval.mp hsHead.1
    refine ⟨label * s, ?_, ?_⟩
    · apply mem_completeRoughRowFiber.mpr
      constructor
      · apply mem_roughHeadFree.mpr
        constructor
        · apply Finset.mem_Ioc.mpr
          constructor
          · have hlo := (Nat.div_lt_iff_lt_mul hlabel.1).mp hsData.1
            simpa only [Nat.mul_comm] using hlo
          · have hhi := (Nat.le_div_iff_mul_le hlabel.1).mp hsData.2.1
            simpa only [Nat.mul_comm] using hhi
        · exact Nat.coprime_mul_iff_left.mpr ⟨hcop, hsHead.2⟩
      · exact completeRoughLabel_mul_eq_of_isCompleteRoughLabel_of_smooth
          hlabel hsData.2.2
    · simpa only [Nat.mul_comm] using Nat.mul_div_left s hlabel.1

/-- The literal upper canonical-row quota is exactly the difference of the
two friable counts at the quotient endpoints. -/
theorem roughUpperCompleteRoughRowTarget_eq_friableEndpoints
    {n h K y : ℕ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) :
    (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) =
      (FriableAsymptotic.friableCount ((2 * n + h) / row.1) y : ℝ) -
        (FriableAsymptotic.friableCount ((2 * n) / row.1) y : ℝ) := by
  have hlabel :=
    isCompleteRoughLabel_of_canonicalCompleteRoughRow row
  have hlohi : (2 * n) / row.1 ≤ (2 * n + h) / row.1 :=
    Nat.div_le_div_right (by omega)
  have hmono := FriableAsymptotic.friableCount_mono_left (y := y) hlohi
  have hcard : roughUpperCompleteRoughRowTarget n h y row.1 =
      FriableAsymptotic.friableCount ((2 * n + h) / row.1) y -
        FriableAsymptotic.friableCount ((2 * n) / row.1) y := by
    unfold roughUpperCompleteRoughRowTarget roughUpperBlock
    rw [completeRoughRowFiber_Ioc_card_eq_smoothInterval hlabel,
      Erdos390.Full.StructuredCells.smoothInterval_card_eq_psi_sub hlohi]
    rfl
  rw [hcard, Nat.cast_sub hmono]

/-- Exact decomposition of one literal raw row into its head-free high and
broad row cardinalities. -/
theorem roughHeadCompatibleRawRowMass_eq_headFreeRowCards
    (W n h K y label : ℕ) (α β L : ℝ) :
    roughHeadCompatibleRawRowMass W n h K y label α β L =
      α * ((completeRoughRowFiber y
        (roughHeadFree W (roughHighLowerBlock n h K)) label).card : ℝ) +
      (β / L) * ((completeRoughRowFiber y
        (roughHeadFree W (roughBroadLowerBlock n h K)) label).card : ℝ) := by
  let labelPred : ℕ → Prop := fun a ↦ completeRoughLabel y a = label
  have hblocks :=
    roughHighLowerBlock_disjoint_roughBroadLowerBlock n h K
  have hfiltered : Disjoint
      ((roughHighLowerBlock n h K).filter labelPred)
      ((roughBroadLowerBlock n h K).filter labelPred) :=
    hblocks.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hhigh :
      (∑ a ∈ (roughHighLowerBlock n h K).filter labelPred,
        roughHeadCompatibleRawWeight W n h K α β L a) =
      α * ((completeRoughRowFiber y
        (roughHeadFree W (roughHighLowerBlock n h K)) label).card : ℝ) := by
    calc
      (∑ a ∈ (roughHighLowerBlock n h K).filter labelPred,
          roughHeadCompatibleRawWeight W n h K α β L a) =
        ∑ a ∈ (roughHighLowerBlock n h K).filter labelPred,
          if Nat.Coprime a (roughHeadModulus W) then α else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        have haHigh := (Finset.mem_filter.mp ha).1
        have haBroad : a ∉ roughBroadLowerBlock n h K := by
          intro haBroad
          exact Finset.disjoint_left.mp hblocks haHigh haBroad
        by_cases hcop : Nat.Coprime a (roughHeadModulus W) <;>
          simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
            haHigh, haBroad, hcop]
      _ = α * ((completeRoughRowFiber y
          (roughHeadFree W (roughHighLowerBlock n h K)) label).card : ℝ) := by
        rw [← Finset.sum_filter]
        simp [completeRoughRowFiber, roughHeadFree, labelPred,
          Finset.filter_filter, and_comm]
        ring
  have hbroad :
      (∑ a ∈ (roughBroadLowerBlock n h K).filter labelPred,
        roughHeadCompatibleRawWeight W n h K α β L a) =
      (β / L) * ((completeRoughRowFiber y
        (roughHeadFree W (roughBroadLowerBlock n h K)) label).card : ℝ) := by
    calc
      (∑ a ∈ (roughBroadLowerBlock n h K).filter labelPred,
          roughHeadCompatibleRawWeight W n h K α β L a) =
        ∑ a ∈ (roughBroadLowerBlock n h K).filter labelPred,
          if Nat.Coprime a (roughHeadModulus W) then β / L else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        have haBroad := (Finset.mem_filter.mp ha).1
        have haHigh : a ∉ roughHighLowerBlock n h K := by
          intro haHigh
          exact Finset.disjoint_left.mp hblocks haHigh haBroad
        by_cases hcop : Nat.Coprime a (roughHeadModulus W) <;>
          simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
            haHigh, haBroad, hcop]
      _ = (β / L) * ((completeRoughRowFiber y
          (roughHeadFree W (roughBroadLowerBlock n h K)) label).card : ℝ) := by
        rw [← Finset.sum_filter]
        simp [completeRoughRowFiber, roughHeadFree, labelPred,
          Finset.filter_filter, and_comm]
        ring
  rw [roughHeadCompatibleRawRowMass, completeRoughRowFiber,
    roughRawCandidateSet, Finset.filter_union,
    Finset.sum_union hfiltered, hhigh, hbroad]

/-- The literal raw mass on a canonical row is exactly the head-free smooth
physical block at the four natural quotient endpoints.  No asymptotic or
fixed-head approximation is used here. -/
theorem roughHeadCompatibleRawRowMass_eq_headFreeSmoothPhysicalBlock
    {W n h K y : ℕ} (hWy : W ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (α β L : ℝ) :
    roughHeadCompatibleRawRowMass W n h K y row.1 α β L =
      roughHeadFreeSmoothPhysicalBlock W
        (n / row.1) ((2 * n - K * h) / row.1)
          ((2 * n) / row.1) y α (β / L) := by
  have hlabel :=
    isCompleteRoughLabel_of_canonicalCompleteRoughRow row
  have hcop := isCompleteRoughLabel_coprime_roughHeadModulus hWy hlabel
  rw [roughHeadCompatibleRawRowMass_eq_headFreeRowCards]
  unfold roughHighLowerBlock roughBroadLowerBlock
  rw [completeRoughRowFiber_headFreeIoc_card_eq_headFreeSmoothInterval
      hlabel hcop,
    completeRoughRowFiber_headFreeIoc_card_eq_headFreeSmoothInterval
      hlabel hcop]
  rfl

/-- Exact finite head inclusion--exclusion on one canonical raw row.  This
is the starting point for the separate fixed-head analytic allowance in the
selector-facing theorem. -/
theorem roughHeadCompatibleRawRowMass_eq_headDivisorShift
    {W n h K y : ℕ} (hWy : W ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (α β L : ℝ) :
    roughHeadCompatibleRawRowMass W n h K y row.1 α β L =
      ∑ d ∈ (roughHeadModulus W).divisors,
        (ArithmeticFunction.moebius d : ℝ) *
          roughSmoothPhysicalBlock
            ((n / row.1) / d)
            (((2 * n - K * h) / row.1) / d)
            (((2 * n) / row.1) / d) y α (β / L) := by
  rw [roughHeadCompatibleRawRowMass_eq_headFreeSmoothPhysicalBlock
    hWy row α β L,
    roughHeadFreeSmoothPhysicalBlock_eq_divisorShift hWy]

/-- Exact finite-head error ledger.  The literal raw row differs from the
density-scaled unrestricted physical block by at most the sum of the
individual fixed-divisor block shifts.  Thus the canonical consumer needs
only a block-scale fixed-head estimate, never independent endpoint shifts. -/
theorem roughHeadCompatibleRawRowMass_sub_densityPhysicalBlock_abs_le
    {W n h K y : ℕ} (hWy : W ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (α β L : ℝ) :
    |roughHeadCompatibleRawRowMass W n h K y row.1 α β L -
        roughHeadDensity W *
          roughSmoothPhysicalBlock
            (n / row.1) ((2 * n - K * h) / row.1)
              ((2 * n) / row.1) y α (β / L)| ≤
      ∑ d ∈ (roughHeadModulus W).divisors,
        |(ArithmeticFunction.moebius d : ℝ)| *
          |roughSmoothPhysicalBlock
              ((n / row.1) / d)
              (((2 * n - K * h) / row.1) / d)
              (((2 * n) / row.1) / d) y α (β / L) -
            roughSmoothPhysicalBlock
              (n / row.1) ((2 * n - K * h) / row.1)
                ((2 * n) / row.1) y α (β / L) / (d : ℝ)| := by
  let B : ℝ := roughSmoothPhysicalBlock
    (n / row.1) ((2 * n - K * h) / row.1)
      ((2 * n) / row.1) y α (β / L)
  rw [roughHeadCompatibleRawRowMass_eq_headDivisorShift hWy row α β L,
    ← roughHead_moebius_inv_sum_eq_density W, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  change
    |∑ d ∈ (roughHeadModulus W).divisors,
      ((ArithmeticFunction.moebius d : ℝ) *
          roughSmoothPhysicalBlock
            ((n / row.1) / d)
            (((2 * n - K * h) / row.1) / d)
            (((2 * n) / row.1) / d) y α (β / L) -
        ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) * B)| ≤ _
  calc
    _ = |∑ d ∈ (roughHeadModulus W).divisors,
        (ArithmeticFunction.moebius d : ℝ) *
          (roughSmoothPhysicalBlock
              ((n / row.1) / d)
              (((2 * n - K * h) / row.1) / d)
              (((2 * n) / row.1) / d) y α (β / L) -
            B / (d : ℝ))| := by
      congr 1
      apply Finset.sum_congr rfl
      intro d _hd
      ring
    _ ≤ ∑ d ∈ (roughHeadModulus W).divisors,
        |(ArithmeticFunction.moebius d : ℝ) *
          (roughSmoothPhysicalBlock
              ((n / row.1) / d)
              (((2 * n - K * h) / row.1) / d)
              (((2 * n) / row.1) / d) y α (β / L) -
            B / (d : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ (roughHeadModulus W).divisors,
        |(ArithmeticFunction.moebius d : ℝ)| *
          |roughSmoothPhysicalBlock
              ((n / row.1) / d)
              (((2 * n - K * h) / row.1) / d)
              (((2 * n) / row.1) / d) y α (β / L) -
            roughSmoothPhysicalBlock
              (n / row.1) ((2 * n - K * h) / row.1)
                ((2 * n) / row.1) y α (β / L) / (d : ℝ)| := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [abs_mul]

/-- Named finite ledger for the fixed-head shift on one canonical row. -/
def roughCanonicalFixedHeadShiftLedger
    (W n h K y : ℕ) (α β L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) : ℝ :=
  ∑ d ∈ (roughHeadModulus W).divisors,
    |(ArithmeticFunction.moebius d : ℝ)| *
      |roughSmoothPhysicalBlock
          ((n / row.1) / d)
          (((2 * n - K * h) / row.1) / d)
          (((2 * n) / row.1) / d) y α (β / L) -
        roughSmoothPhysicalBlock
          (n / row.1) ((2 * n - K * h) / row.1)
            ((2 * n) / row.1) y α (β / L) / (d : ℝ)|

/-- The exact finite-head ledger bounds precisely the `headAllowance`
expected by the literal selector theorem. -/
theorem roughHeadCompatibleRawRowMass_sub_densityLower_abs_le
    {W n h K y : ℕ} (hWy : W ≤ y) (hKh : K * h ≤ n)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (α β L : ℝ) :
    |roughHeadCompatibleRawRowMass W n h K y row.1 α β L -
      roughHeadDensity W * roughPhysicalLowerFriableMass α β L
        ((2 * n) / row.1) ((2 * n - K * h) / row.1)
          (n / row.1) y| ≤
      roughCanonicalFixedHeadShiftLedger W n h K y α β L row := by
  have hloSplit : n / row.1 ≤ (2 * n - K * h) / row.1 := by
    apply Nat.div_le_div_right
    omega
  have hSplitHi : (2 * n - K * h) / row.1 ≤ (2 * n) / row.1 :=
    Nat.div_le_div_right (Nat.sub_le _ _)
  have hlower : roughPhysicalLowerFriableMass α β L
        ((2 * n) / row.1) ((2 * n - K * h) / row.1)
          (n / row.1) y =
      roughSmoothPhysicalBlock
        (n / row.1) ((2 * n - K * h) / row.1)
          ((2 * n) / row.1) y α (β / L) := by
    simpa only [roughPhysicalLowerFriableMass] using
      (roughSmoothPhysicalBlock_eq_friableEndpoints
        (alpha := α) (broad := β / L) hloSplit hSplitHi).symm
  rw [hlower]
  simpa only [roughCanonicalFixedHeadShiftLedger] using
    roughHeadCompatibleRawRowMass_sub_densityPhysicalBlock_abs_le
      hWy row α β L

/-- The canonical row sum of the head-compatible raw weight is exactly the
ambient raw row mass.  This is the literal bridge from the finite point to
the canonical row type consumed by exactification. -/
theorem sum_canonicalCompleteRoughRowSet_rawWeight_eq_rawRowMass
    (W n h K y : ℕ) (α β L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) :
    ∑ a ∈ rowSet
        (canonicalCompleteRoughRow y (roughRawCandidateSet n h K)) row,
      roughHeadCompatibleRawWeight W n h K α β L
        (canonicalCompleteRoughCandidateValue
          (roughRawCandidateSet n h K) a) =
      roughHeadCompatibleRawRowMass W n h K y row.1 α β L := by
  simpa only [roughHeadCompatibleRawRowMass] using
    sum_canonicalCompleteRoughRowSet_eq_sum_completeRoughRowFiber
      y (roughRawCandidateSet n h K)
        (roughHeadCompatibleRawWeight W n h K α β L) row

/-- The quota error on the literal canonical complete-rough row. -/
def roughCanonicalRawRowQuotaError
    (W n h K y : ℕ) (α β L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) : ℝ :=
  (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) -
    ∑ a ∈ rowSet
        (canonicalCompleteRoughRow y (roughRawCandidateSet n h K)) row,
      roughHeadCompatibleRawWeight W n h K α β L
        (canonicalCompleteRoughCandidateValue
          (roughRawCandidateSet n h K) a)

/-- Ambient form of the canonical quota error. -/
theorem roughCanonicalRawRowQuotaError_eq_target_sub_rawRowMass
    (W n h K y : ℕ) (α β L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) :
    roughCanonicalRawRowQuotaError W n h K y α β L row =
      (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) -
        roughHeadCompatibleRawRowMass W n h K y row.1 α β L := by
  rw [roughCanonicalRawRowQuotaError,
    sum_canonicalCompleteRoughRowSet_rawWeight_eq_rawRowMass]

/-- Algebraic endpoint bridge.  `hupper` is the exact smooth-quotient count
for the upper row.  `hraw` is the exact density-scaled physical-block value
after the fixed-head step.  With those two finite identifications exposed,
the canonical quota error is literally the existing four-endpoint
combination. -/
theorem roughCanonicalRawRowQuotaError_eq_physicalFriableCombination
    {W n h K y : ℕ} {α β L δ : ℝ}
    {Xplus X Xminus Xhalf : ℕ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hupper : (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) =
      (FriableAsymptotic.friableCount Xplus y : ℝ) -
        (FriableAsymptotic.friableCount X y : ℝ))
    (hraw : roughHeadCompatibleRawRowMass
        W n h K y row.1 α β L =
      δ * roughPhysicalLowerFriableMass
        α β L X Xminus Xhalf y) :
    roughCanonicalRawRowQuotaError W n h K y α β L row =
      roughPhysicalFriableCombination δ α β L
        Xplus X Xminus Xhalf y := by
  rw [roughCanonicalRawRowQuotaError_eq_target_sub_rawRowMass,
    hupper, hraw, roughPhysicalFriableCombination, Fin.sum_univ_four]
  unfold roughPhysicalLowerFriableMass
  change
    ((FriableAsymptotic.friableCount Xplus y : ℝ) -
        (FriableAsymptotic.friableCount X y : ℝ)) -
      δ * (α *
          ((FriableAsymptotic.friableCount X y : ℝ) -
            (FriableAsymptotic.friableCount Xminus y : ℝ)) +
        (β / L) *
          ((FriableAsymptotic.friableCount Xminus y : ℝ) -
            (FriableAsymptotic.friableCount Xhalf y : ℝ))) =
      1 * (FriableAsymptotic.friableCount Xplus y : ℝ) +
        (-(1 + δ * α)) *
          (FriableAsymptotic.friableCount X y : ℝ) +
        δ * (α - β / L) *
          (FriableAsymptotic.friableCount Xminus y : ℝ) +
        δ * (β / L) *
          (FriableAsymptotic.friableCount Xhalf y : ℝ)
  ring

/-- With the exact upper endpoint identification, the discrepancy between
the literal canonical quota error and the four-endpoint analytic block is
exactly the fixed-head physical-shift discrepancy. -/
theorem roughCanonicalRawRowQuotaError_sub_physicalFriableCombination_abs
    {W n h K y : ℕ} {α β L δ : ℝ}
    {Xplus X Xminus Xhalf : ℕ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hupper : (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) =
      (FriableAsymptotic.friableCount Xplus y : ℝ) -
        (FriableAsymptotic.friableCount X y : ℝ)) :
    |roughCanonicalRawRowQuotaError W n h K y α β L row -
        roughPhysicalFriableCombination δ α β L
          Xplus X Xminus Xhalf y| =
      |roughHeadCompatibleRawRowMass W n h K y row.1 α β L -
        δ * roughPhysicalLowerFriableMass
          α β L X Xminus Xhalf y| := by
  rw [roughCanonicalRawRowQuotaError_eq_target_sub_rawRowMass,
    hupper, roughPhysicalFriableCombination, Fin.sum_univ_four]
  unfold roughPhysicalLowerFriableMass
  change
    |(((FriableAsymptotic.friableCount Xplus y : ℝ) -
          (FriableAsymptotic.friableCount X y : ℝ)) -
        roughHeadCompatibleRawRowMass W n h K y row.1 α β L) -
      (1 * (FriableAsymptotic.friableCount Xplus y : ℝ) +
        (-(1 + δ * α)) *
          (FriableAsymptotic.friableCount X y : ℝ) +
        δ * (α - β / L) *
          (FriableAsymptotic.friableCount Xminus y : ℝ) +
        δ * (β / L) *
          (FriableAsymptotic.friableCount Xhalf y : ℝ))| =
      |roughHeadCompatibleRawRowMass W n h K y row.1 α β L -
        δ * (α *
          ((FriableAsymptotic.friableCount X y : ℝ) -
            (FriableAsymptotic.friableCount Xminus y : ℝ)) +
        (β / L) *
          ((FriableAsymptotic.friableCount Xminus y : ℝ) -
            (FriableAsymptotic.friableCount Xhalf y : ℝ)))|
  rw [show
    (((FriableAsymptotic.friableCount Xplus y : ℝ) -
          (FriableAsymptotic.friableCount X y : ℝ)) -
        roughHeadCompatibleRawRowMass W n h K y row.1 α β L) -
      (1 * (FriableAsymptotic.friableCount Xplus y : ℝ) +
        (-(1 + δ * α)) *
          (FriableAsymptotic.friableCount X y : ℝ) +
        δ * (α - β / L) *
          (FriableAsymptotic.friableCount Xminus y : ℝ) +
        δ * (β / L) *
          (FriableAsymptotic.friableCount Xhalf y : ℝ)) =
      -(roughHeadCompatibleRawRowMass W n h K y row.1 α β L -
        δ * (α *
          ((FriableAsymptotic.friableCount X y : ℝ) -
            (FriableAsymptotic.friableCount Xminus y : ℝ)) +
        (β / L) *
          ((FriableAsymptotic.friableCount Xminus y : ℝ) -
            (FriableAsymptotic.friableCount Xhalf y : ℝ)))) by ring,
    abs_neg]

/-- Selector-facing paper-scale closure.  The conclusion is about the
literal canonical-row quota error, while all HT--Saias work is delegated to
the weighted four-endpoint theorem.  The fixed-head shift is a third,
separate allowance and is not silently dropped. -/
theorem roughCanonicalRawRowQuotaError_abs_le_of_saiasPaperScale
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ W n h K y : ℕ}
    {α β L δ mainAllowance transitionAllowance headAllowance : ℝ}
    {Xplus X Xminus Xhalf : ℕ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hupper : (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) =
      (FriableAsymptotic.friableCount Xplus y : ℝ) -
        (FriableAsymptotic.friableCount X y : ℝ))
    (hhead : |roughHeadCompatibleRawRowMass
        W n h K y row.1 α β L -
      δ * roughPhysicalLowerFriableMass
        α β L X Xminus Xhalf y| ≤ headAllowance)
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hhalf : 0 < Xhalf) (hHalfMinus : Xhalf ≤ Xminus)
    (hMinusX : Xminus ≤ X) (hXPlus : X ≤ Xplus)
    (hlogs : ∀ i : Fin 4,
      Real.log
          (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) ≤
        5 * Real.log (y : ℝ))
    (hmain : roughPhysicalDickmanTransitionLedger δ α β L
        Xplus X Xminus Xhalf y ≤ mainAllowance)
    (htransition : roughPhysicalSaiasTransitionBudget eta δ α β L
        Xplus X Xminus Xhalf y ≤ transitionAllowance) :
    |roughCanonicalRawRowQuotaError W n h K y α β L row| ≤
      mainAllowance + transitionAllowance + headAllowance := by
  have hblock := roughPhysicalFriableCombination_abs_le_of_saiasPaperScale
    hBV happrox hY hy2 hhalf hHalfMinus hMinusX hXPlus hlogs
      hmain htransition
  have hdiff :=
    roughCanonicalRawRowQuotaError_sub_physicalFriableCombination_abs
      (W := W) (α := α) (β := β) (L := L) (δ := δ)
      (Xplus := Xplus) (X := X) (Xminus := Xminus) (Xhalf := Xhalf)
      row hupper
  calc
    |roughCanonicalRawRowQuotaError W n h K y α β L row| =
      |(roughCanonicalRawRowQuotaError W n h K y α β L row -
          roughPhysicalFriableCombination δ α β L
            Xplus X Xminus Xhalf y) +
        roughPhysicalFriableCombination δ α β L
          Xplus X Xminus Xhalf y| := by
      congr 1
      ring
    _ ≤ |roughCanonicalRawRowQuotaError W n h K y α β L row -
          roughPhysicalFriableCombination δ α β L
            Xplus X Xminus Xhalf y| +
        |roughPhysicalFriableCombination δ α β L
          Xplus X Xminus Xhalf y| := abs_add_le _ _
    _ ≤ headAllowance +
        (mainAllowance + transitionAllowance) := by
      rw [hdiff]
      exact add_le_add hhead hblock
    _ = mainAllowance + transitionAllowance + headAllowance := by ring

/-- Fully literal endpoint specialization used by the selector.  The four
natural endpoints are the quotient endpoints of
`(2n,2n+h]`, `(2n-Kh,2n]`, and `(n,2n-Kh]` in the canonical row.  Thus the
upper endpoint bridge is discharged by the finite row-to-smooth bijection
above; only the fixed-head allowance and the two paper-scale analytic
allowances remain. -/
theorem roughCanonicalRawRowQuotaError_abs_le_of_literalSaiasPaperScale
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ W n h K y : ℕ}
    {α β L δ mainAllowance transitionAllowance headAllowance : ℝ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hrowN : row.1 ≤ n) (hKh : K * h ≤ n)
    (hhead : |roughHeadCompatibleRawRowMass
        W n h K y row.1 α β L -
      δ * roughPhysicalLowerFriableMass α β L
        ((2 * n) / row.1) ((2 * n - K * h) / row.1)
          (n / row.1) y| ≤ headAllowance)
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hlogs : ∀ i : Fin 4,
      Real.log (roughPhysicalNatEndpoint
          ((2 * n + h) / row.1) ((2 * n) / row.1)
          ((2 * n - K * h) / row.1) (n / row.1) i : ℝ) ≤
        5 * Real.log (y : ℝ))
    (hmain : roughPhysicalDickmanTransitionLedger δ α β L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤
      mainAllowance)
    (htransition : roughPhysicalSaiasTransitionBudget eta δ α β L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤
      transitionAllowance) :
    |roughCanonicalRawRowQuotaError W n h K y α β L row| ≤
      mainAllowance + transitionAllowance + headAllowance := by
  have hlabel : 0 < row.1 :=
    canonicalCompleteRoughRow_label_pos y
      (roughRawCandidateSet n h K) row
  have hhalf : 0 < n / row.1 := Nat.div_pos hrowN hlabel
  have hHalfMinus : n / row.1 ≤ (2 * n - K * h) / row.1 := by
    apply Nat.div_le_div_right
    omega
  have hMinusX : (2 * n - K * h) / row.1 ≤ (2 * n) / row.1 := by
    exact Nat.div_le_div_right (Nat.sub_le _ _)
  have hXPlus : (2 * n) / row.1 ≤ (2 * n + h) / row.1 := by
    exact Nat.div_le_div_right (by omega)
  exact roughCanonicalRawRowQuotaError_abs_le_of_saiasPaperScale
    hBV row (roughUpperCompleteRoughRowTarget_eq_friableEndpoints row)
      hhead happrox hY hy2 hhalf hHalfMinus hMinusX hXPlus hlogs
      hmain htransition

/-- Canonical selector closure with every finite row and head operation
discharged.  The only remaining estimates are the HT--Saias endpoint
envelope, the deterministic main-ledger allowance, the weighted transition
allowance, and the displayed finite fixed-head block-shift ledger. -/
theorem roughCanonicalRawRowQuotaError_abs_le_of_literalSaiasAndHeadLedger
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ W n h K y : ℕ}
    {α β L mainAllowance transitionAllowance : ℝ}
    (hWy : W ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hrowN : row.1 ≤ n) (hKh : K * h ≤ n)
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hlogs : ∀ i : Fin 4,
      Real.log (roughPhysicalNatEndpoint
          ((2 * n + h) / row.1) ((2 * n) / row.1)
          ((2 * n - K * h) / row.1) (n / row.1) i : ℝ) ≤
        5 * Real.log (y : ℝ))
    (hmain : roughPhysicalDickmanTransitionLedger
        (roughHeadDensity W) α β L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤
      mainAllowance)
    (htransition : roughPhysicalSaiasTransitionBudget eta
        (roughHeadDensity W) α β L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤
      transitionAllowance) :
    |roughCanonicalRawRowQuotaError W n h K y α β L row| ≤
      mainAllowance + transitionAllowance +
        roughCanonicalFixedHeadShiftLedger W n h K y α β L row := by
  exact roughCanonicalRawRowQuotaError_abs_le_of_literalSaiasPaperScale
    hBV row hrowN hKh
      (roughHeadCompatibleRawRowMass_sub_densityLower_abs_le
        hWy hKh row α β L)
      happrox hY hy2 hlogs hmain htransition

/-- Finite active-row form.  If the deterministic four-endpoint ledger, the
weighted HT--Saias ledger, and the fixed-head block ledger are each at most
the same paper-scale allowance `E`, then the literal canonical row error is
at most `3*E`.  Taking `E = C_W*(X_R/L^2+1)` is exactly the boxed active-row
estimate in the paper. -/
theorem roughCanonicalRawRowQuotaError_abs_le_three_mul_paperAllowance
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ W n h K y : ℕ}
    {α β L E : ℝ}
    (hWy : W ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hrowN : row.1 ≤ n) (hKh : K * h ≤ n)
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hlogs : ∀ i : Fin 4,
      Real.log (roughPhysicalNatEndpoint
          ((2 * n + h) / row.1) ((2 * n) / row.1)
          ((2 * n - K * h) / row.1) (n / row.1) i : ℝ) ≤
        5 * Real.log (y : ℝ))
    (hmain : roughPhysicalDickmanTransitionLedger
        (roughHeadDensity W) α β L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤ E)
    (htransition : roughPhysicalSaiasTransitionBudget eta
        (roughHeadDensity W) α β L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤ E)
    (hhead : roughCanonicalFixedHeadShiftLedger
        W n h K y α β L row ≤ E) :
    |roughCanonicalRawRowQuotaError W n h K y α β L row| ≤ 3 * E := by
  have h :=
    roughCanonicalRawRowQuotaError_abs_le_of_literalSaiasAndHeadLedger
      hBV hWy row hrowN hKh happrox hY hy2 hlogs hmain htransition
  nlinarith

end

end Erdos390.WholePaper
