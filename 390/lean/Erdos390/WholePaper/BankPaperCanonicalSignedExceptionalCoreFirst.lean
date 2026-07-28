import Erdos390.WholePaper.BankPaperCanonicalSignedGuardResidual
import Erdos390.WholePaper.BankPaperFixedExceptionalChargeAsymptotic
import Erdos390.Full.LocalFugacityBounds

/-!
# Core-first cancellation for the signed exceptional residual

The exceptional term in Section 9 cannot be estimated by separating its
positive and negative halves.  The paper first fixes the complete smooth
core `b`, sums all physical rough pieces with that core, and only then takes
absolute values.  This file makes that order of summation literal.

The first part is completely finite.  It partitions both halves of
`roughCanonicalSignedExceptionalResidual` by `completeSmoothPart (yNat n)`,
transfers every low-prime valuation to that smooth part, and reindexes both
halves over one common positive prefix.  Thus the sign in each core is the
actual upper cardinality minus the actual weighted lower mass.

The second part records the elementary fixed-head cancellation used on the
leading term.  Its periodic coefficient has uniformly bounded partial sums;
finite Abel summation therefore bounds it against every sequence with the
paper's prime-power-by-prime-power variation estimate.  No rough-counting
asymptotic is used in these arguments.

The last part isolates the one genuinely new analytic input: the signed
four-to-five-prime chamber expansion for a fixed smooth core, before any
valuation sum or triangle inequality.  All subsequent core, valuation, and
endpoint ledgers are finite consequences of that expansion.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Erdos390.Full.LocalFugacityBounds

noncomputable section

namespace BankPaperRealization

/-! ## The literal common smooth-core partition -/

/-- Smooth cores which actually occur in the exceptional raw lower set. -/
def roughCanonicalExceptionalRawLowerSmoothParts
    (n h K : Nat) (deltaStar : Real) : Finset Nat :=
  (roughCanonicalExceptionalRawLowerSet n h K deltaStar).image
    (completeSmoothPart (yNat n))

/-- The exceptional raw lower factors with prescribed complete smooth core. -/
def roughCanonicalExceptionalRawLowerSmoothFiber
    (n h K : Nat) (deltaStar : Real) (b : Nat) : Finset Nat :=
  (roughCanonicalExceptionalRawLowerSet n h K deltaStar).filter
    (fun a => completeSmoothPart (yNat n) a = b)

@[simp]
theorem mem_roughCanonicalExceptionalRawLowerSmoothParts
    {n h K b : Nat} {deltaStar : Real} :
    b ∈ roughCanonicalExceptionalRawLowerSmoothParts n h K deltaStar ↔
      ∃ a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar,
        completeSmoothPart (yNat n) a = b := by
  simp only [roughCanonicalExceptionalRawLowerSmoothParts,
    Finset.mem_image]

@[simp]
theorem mem_roughCanonicalExceptionalRawLowerSmoothFiber
    {n h K a b : Nat} {deltaStar : Real} :
    a ∈ roughCanonicalExceptionalRawLowerSmoothFiber n h K deltaStar b ↔
      a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar ∧
        completeSmoothPart (yNat n) a = b := by
  simp only [roughCanonicalExceptionalRawLowerSmoothFiber,
    Finset.mem_filter]

/-- Every literal raw lower candidate is positive and at most `2*n`. -/
theorem roughRawCandidateSet_pos_le_two_mul
    {n h K a : Nat} (ha : a ∈ roughRawCandidateSet n h K) :
    0 < a ∧ a ≤ 2 * n := by
  rw [roughRawCandidateSet, Finset.mem_union] at ha
  rcases ha with ha | ha
  · rw [roughHighLowerBlock, Finset.mem_Ioc] at ha
    omega
  · rw [roughBroadLowerBlock, Finset.mem_Ioc] at ha
    omega

/-- In an exceptional lower row the complete smooth core is already below
the paper's real exceptional cutoff.  No enlargement to a positive charge
has occurred here. -/
theorem completeSmoothPart_cast_lt_realExceptionalCutoff_of_rawLower
    {n h K a : Nat} {deltaStar : Real}
    (ha : a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar) :
    (completeSmoothPart (yNat n) a : Real) < (n : Real) ^ deltaStar := by
  have haData := mem_roughCanonicalExceptionalRawLowerSet.mp ha
  have haBounds := roughRawCandidateSet_pos_le_two_mul haData.1
  let rough := completeRoughLabel (yNat n) a
  let smooth := completeSmoothPart (yNat n) a
  have hroughPos : 0 < rough := completeRoughLabel_pos (yNat n) a
  have hroughReal : (0 : Real) < (rough : Real) := by
    exact_mod_cast hroughPos
  have hsmoothLe : (smooth : Real) ≤ (a : Real) / (rough : Real) := by
    exact Nat.cast_div_le
  have haLeReal : (a : Real) ≤ 2 * (n : Real) := by
    exact_mod_cast haBounds.2
  have hdivLe : (a : Real) / (rough : Real) ≤
      2 * (n : Real) / (rough : Real) :=
    div_le_div_of_nonneg_right haLeReal hroughReal.le
  have hexceptional :
      2 * (n : Real) / (rough : Real) < (n : Real) ^ deltaStar := by
    simpa only [rough, RoughCanonicalExceptionalLabel] using haData.2
  exact hsmoothLe.trans_lt (hdivLe.trans_lt hexceptional)

/-- Natural-ceiling form of the preceding strict smooth-core cutoff. -/
theorem completeSmoothPart_lt_exceptionalCutoff_of_rawLower
    {n h K a : Nat} {deltaStar : Real}
    (ha : a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar) :
    completeSmoothPart (yNat n) a <
      tangentPaperExceptionalCutoff deltaStar n := by
  have hsmooth :=
    completeSmoothPart_cast_lt_realExceptionalCutoff_of_rawLower ha
  have hcut := tangentPaperExceptionalCutoff_cast_ge deltaStar n
  exact_mod_cast hsmooth.trans_le hcut

/-- All lower smooth cores lie in the same safe prefix already used for the
upper exceptional factors. -/
theorem roughCanonicalExceptionalRawLowerSmoothParts_subset_Icc_two_mul_cutoff
    {n h K : Nat} {deltaStar : Real} :
    roughCanonicalExceptionalRawLowerSmoothParts n h K deltaStar ⊆
      Finset.Icc 1 (2 * tangentPaperExceptionalCutoff deltaStar n) := by
  intro b hb
  obtain ⟨a, ha, hab⟩ :=
    mem_roughCanonicalExceptionalRawLowerSmoothParts.mp hb
  have haData := mem_roughCanonicalExceptionalRawLowerSet.mp ha
  have haPos := (roughRawCandidateSet_pos_le_two_mul haData.1).1
  have hbPos : 0 < b := by
    simpa only [hab] using
      completeSmoothPart_pos (y := yNat n) (a := a) haPos
  have hbLt : b < tangentPaperExceptionalCutoff deltaStar n := by
    simpa only [hab] using
      completeSmoothPart_lt_exceptionalCutoff_of_rawLower ha
  exact Finset.mem_Icc.mpr ⟨hbPos, by omega⟩

/-- A low-prime valuation lives entirely on the complete smooth core. -/
theorem factorization_eq_completeSmoothPart_factorization_of_le
    {n a p : Nat} (hp : p ≤ yNat n) :
    (a.factorization p : Real) =
      ((completeSmoothPart (yNat n) a).factorization p : Real) := by
  rw [completeSmoothPart_factorization_apply, if_pos hp]

/-- A prescribed upper smooth fibre is empty when its core is not in the
corresponding image. -/
theorem paperExceptionalSmoothFiber_eq_empty_of_not_mem
    {n h b : Nat} {deltaStar : Real}
    (hb : b ∉ paperExceptionalSmoothParts n h deltaStar) :
    paperExceptionalSmoothFiber n h deltaStar b = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have haData := mem_paperExceptionalSmoothFiber.mp ha
  exact hb (mem_paperExceptionalSmoothParts.mpr
    ⟨a, haData.1, haData.2⟩)

/-- A prescribed lower smooth fibre is empty when its core is not in the
corresponding image. -/
theorem roughCanonicalExceptionalRawLowerSmoothFiber_eq_empty_of_not_mem
    {n h K b : Nat} {deltaStar : Real}
    (hb : b ∉ roughCanonicalExceptionalRawLowerSmoothParts
      n h K deltaStar) :
    roughCanonicalExceptionalRawLowerSmoothFiber n h K deltaStar b = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have haData := mem_roughCanonicalExceptionalRawLowerSmoothFiber.mp ha
  exact hb (mem_roughCanonicalExceptionalRawLowerSmoothParts.mpr
    ⟨a, haData.1, haData.2⟩)

/-- The signed physical mass after fixing the complete smooth core `b`.
This is the literal upper count minus the literal weighted lower count. -/
def roughCanonicalSignedExceptionalCoreMass
    (n h K : Nat) (deltaStar : Real)
    (rawWeight : Nat → Real) (b : Nat) : Real :=
  ((paperExceptionalSmoothFiber n h deltaStar b).card : Real) -
    ∑ a ∈ roughCanonicalExceptionalRawLowerSmoothFiber
        n h K deltaStar b, rawWeight a

/-- The upper valuation sum grouped first by its complete smooth core. -/
theorem sum_paperExceptionalUpperFactors_factorization_eq_corePrefix
    {n h p : Nat} {deltaStar : Real}
    (hdelta : 0 ≤ deltaStar) (hn : 1 ≤ n) (hh : h ≤ n)
    (hp : p ≤ yNat n) :
    (∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
        (a.factorization p : Real)) =
      ∑ b ∈ Finset.Icc 1
          (2 * tangentPaperExceptionalCutoff deltaStar n),
        (b.factorization p : Real) *
          ((paperExceptionalSmoothFiber n h deltaStar b).card : Real) := by
  let smoothParts := paperExceptionalSmoothParts n h deltaStar
  have hsubset : smoothParts ⊆ Finset.Icc 1
      (2 * tangentPaperExceptionalCutoff deltaStar n) :=
    paperExceptionalSmoothParts_subset_Icc_two_mul_cutoff
      hdelta hn hh
  have hprod :=
    paperExceptionalUpperFactors_prod_factorization_eq_smoothFiberSum
      (n := n) (h := h) (p := p) (deltaStar := deltaStar) hp
  calc
    (∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
        (a.factorization p : Real)) =
        (((paperExceptionalUpperFactors n h deltaStar).prod id).factorization p :
          Real) :=
      sum_paperExceptionalUpperFactors_factorization_eq_prod
        n h deltaStar p
    _ = ∑ b ∈ smoothParts,
        (b.factorization p : Real) *
          ((paperExceptionalSmoothFiber n h deltaStar b).card : Real) := by
      exact_mod_cast hprod
    _ = ∑ b ∈ Finset.Icc 1
          (2 * tangentPaperExceptionalCutoff deltaStar n),
        (b.factorization p : Real) *
          ((paperExceptionalSmoothFiber n h deltaStar b).card : Real) := by
      apply Finset.sum_subset hsubset
      intro b _hbPrefix hbNotSmooth
      rw [paperExceptionalSmoothFiber_eq_empty_of_not_mem hbNotSmooth]
      simp

/-- The weighted lower valuation sum grouped first by its complete smooth
core and extended by zero to the same prefix as the upper half. -/
theorem sum_roughCanonicalExceptionalRawLower_factorization_eq_corePrefix
    {n h K p : Nat} {deltaStar : Real} {rawWeight : Nat → Real}
    (hp : p ≤ yNat n) :
    (∑ a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar,
        rawWeight a * (a.factorization p : Real)) =
      ∑ b ∈ Finset.Icc 1
          (2 * tangentPaperExceptionalCutoff deltaStar n),
        (b.factorization p : Real) *
          (∑ a ∈ roughCanonicalExceptionalRawLowerSmoothFiber
              n h K deltaStar b, rawWeight a) := by
  let lower := roughCanonicalExceptionalRawLowerSet n h K deltaStar
  let smooth := completeSmoothPart (yNat n)
  let smoothParts :=
    roughCanonicalExceptionalRawLowerSmoothParts n h K deltaStar
  have hsubset : smoothParts ⊆ Finset.Icc 1
      (2 * tangentPaperExceptionalCutoff deltaStar n) :=
    roughCanonicalExceptionalRawLowerSmoothParts_subset_Icc_two_mul_cutoff
  calc
    (∑ a ∈ lower, rawWeight a * (a.factorization p : Real)) =
        ∑ a ∈ lower,
          rawWeight a * ((smooth a).factorization p : Real) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [factorization_eq_completeSmoothPart_factorization_of_le hp]
    _ = ∑ b ∈ smoothParts,
        ∑ a ∈ lower.filter (fun a => smooth a = b),
          rawWeight a * ((smooth a).factorization p : Real) := by
      exact (Finset.sum_fiberwise_of_maps_to
        (s := lower) (t := lower.image smooth) (g := smooth)
        (fun a ha => Finset.mem_image_of_mem smooth ha)
        (fun a => rawWeight a * ((smooth a).factorization p : Real))).symm
    _ = ∑ b ∈ smoothParts,
        ∑ a ∈ roughCanonicalExceptionalRawLowerSmoothFiber
            n h K deltaStar b,
          rawWeight a * (b.factorization p : Real) := by
      apply Finset.sum_congr rfl
      intro b _hb
      apply Finset.sum_congr
      · rfl
      · intro a ha
        have hab : smooth a = b := (Finset.mem_filter.mp ha).2
        rw [hab]
    _ = ∑ b ∈ smoothParts,
        (b.factorization p : Real) *
          (∑ a ∈ roughCanonicalExceptionalRawLowerSmoothFiber
              n h K deltaStar b, rawWeight a) := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ = ∑ b ∈ Finset.Icc 1
          (2 * tangentPaperExceptionalCutoff deltaStar n),
        (b.factorization p : Real) *
          (∑ a ∈ roughCanonicalExceptionalRawLowerSmoothFiber
              n h K deltaStar b, rawWeight a) := by
      apply Finset.sum_subset hsubset
      intro b _hbPrefix hbNotSmooth
      rw [roughCanonicalExceptionalRawLowerSmoothFiber_eq_empty_of_not_mem
        hbNotSmooth]
      simp

/-- Exact core-first identity for the signed exceptional residual.  The
subtraction remains inside the `b`-sum; no positive-parts majorant appears. -/
theorem roughCanonicalSignedExceptionalResidual_eq_coreFirst
    {n h K p : Nat} {deltaStar : Real} {rawWeight : Nat → Real}
    (hdelta : 0 ≤ deltaStar) (hn : 1 ≤ n) (hh : h ≤ n)
    (hp : p ≤ yNat n) :
    roughCanonicalSignedExceptionalResidual n h K deltaStar
        rawWeight p =
      ∑ b ∈ Finset.Icc 1
          (2 * tangentPaperExceptionalCutoff deltaStar n),
        (b.factorization p : Real) *
          roughCanonicalSignedExceptionalCoreMass n h K deltaStar
            rawWeight b := by
  rw [roughCanonicalSignedExceptionalResidual,
    sum_paperExceptionalUpperFactors_factorization_eq_corePrefix
      hdelta hn hh hp,
    sum_roughCanonicalExceptionalRawLower_factorization_eq_corePrefix hp,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _hb
  unfold roughCanonicalSignedExceptionalCoreMass
  ring

/-! ## The fixed-head periodic coefficient -/

/-- The paper's mean-zero fixed-head coefficient
`c_hd(b)=1-delta_hd^{-1} 1_{(b,P_hd)=1}`. -/
def roughHeadPeriodicCoreCoefficient (W b : Nat) : Real :=
  1 - if Nat.Coprime b (roughHeadModulus W) then
    1 / roughHeadDensity W else 0

/-- Multiplication by an integer coprime to the head modulus preserves the
periodic core coefficient exactly. -/
theorem roughHeadPeriodicCoreCoefficient_mul_left
    {W D b : Nat} (hD : Nat.Coprime D (roughHeadModulus W)) :
    roughHeadPeriodicCoreCoefficient W (D * b) =
      roughHeadPeriodicCoreCoefficient W b := by
  unfold roughHeadPeriodicCoreCoefficient
  by_cases hb : Nat.Coprime b (roughHeadModulus W)
  · have hDb : Nat.Coprime (D * b) (roughHeadModulus W) :=
      (Nat.coprime_mul_iff_left).2 ⟨hD, hb⟩
    rw [if_pos hDb, if_pos hb]
  · have hDb : ¬Nat.Coprime (D * b) (roughHeadModulus W) := by
      intro h
      exact hb (Nat.coprime_mul_iff_left.mp h).2
    rw [if_neg hDb, if_neg hb]

/-- Partial sum of the fixed-head periodic coefficient. -/
def roughHeadPeriodicCorePrefix (W B : Nat) : Real :=
  ∑ b ∈ Finset.Icc 1 B, roughHeadPeriodicCoreCoefficient W b

/-- The partial sum is exactly the reduced-residue discrepancy divided by
the fixed density. -/
theorem roughHeadPeriodicCorePrefix_eq
    (W B : Nat) :
    roughHeadPeriodicCorePrefix W B =
      (B : Real) -
        ((roughHeadFree W (Finset.Icc 1 B)).card : Real) /
          roughHeadDensity W := by
  have hcard : (Finset.Icc 1 B).card = B := by simp
  unfold roughHeadPeriodicCorePrefix roughHeadPeriodicCoreCoefficient
  calc
    (∑ b ∈ Finset.Icc 1 B,
        (1 - if Nat.Coprime b (roughHeadModulus W) then
          1 / roughHeadDensity W else 0)) =
        (∑ _b ∈ Finset.Icc 1 B, (1 : Real)) -
          ∑ b ∈ Finset.Icc 1 B,
            (if Nat.Coprime b (roughHeadModulus W) then
              1 / roughHeadDensity W else 0) := by
      rw [Finset.sum_sub_distrib]
    _ = ((Finset.Icc 1 B).card : Real) -
          ((roughHeadFree W (Finset.Icc 1 B)).card : Real) /
            roughHeadDensity W := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [show (∑ b ∈ Finset.Icc 1 B,
          if Nat.Coprime b (roughHeadModulus W) then
            1 / roughHeadDensity W else 0) =
          ((roughHeadFree W (Finset.Icc 1 B)).card : Real) /
            roughHeadDensity W by
        rw [← Finset.sum_filter]
        simp [roughHeadFree]
        ring]
    _ = (B : Real) -
          ((roughHeadFree W (Finset.Icc 1 B)).card : Real) /
            roughHeadDensity W := by rw [hcard]

/-- Every partial sum of the mean-zero coefficient is bounded by one fixed
head-modulus constant. -/
theorem abs_roughHeadPeriodicCorePrefix_le
    (W B : Nat) :
    |roughHeadPeriodicCorePrefix W B| ≤
      (roughHeadModulus W : Real) / roughHeadDensity W := by
  have hset : Finset.Icc 1 B = Finset.Ioc 0 B := by
    ext b
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hcount := roughHeadFree_Ioc_card_error_le
    (W := W) (lo := 0) (hi := B) (Nat.zero_le B)
  rw [Nat.cast_sub (Nat.zero_le B), Nat.cast_zero, sub_zero] at hcount
  have hdelta : 0 < roughHeadDensity W := roughHeadDensity_pos W
  rw [roughHeadPeriodicCorePrefix_eq, hset]
  have hidentity :
      (B : Real) -
          ((roughHeadFree W (Finset.Ioc 0 B)).card : Real) /
            roughHeadDensity W =
        -(((roughHeadFree W (Finset.Ioc 0 B)).card : Real) -
            roughHeadDensity W * (B : Real)) /
          roughHeadDensity W := by
    field_simp [hdelta.ne']
    ring
  rw [hidentity, abs_div, abs_neg, abs_of_pos hdelta]
  exact div_le_div_of_nonneg_right hcount hdelta.le

/-- Prefix with a fixed coprime multiplier in the periodic argument. -/
def roughHeadPeriodicCoreMulPrefix (W D B : Nat) : Real :=
  ∑ b ∈ Finset.Icc 1 B, roughHeadPeriodicCoreCoefficient W (D * b)

/-- A coprime multiplier leaves every periodic prefix unchanged. -/
theorem roughHeadPeriodicCoreMulPrefix_eq
    {W D B : Nat} (hD : Nat.Coprime D (roughHeadModulus W)) :
    roughHeadPeriodicCoreMulPrefix W D B =
      roughHeadPeriodicCorePrefix W B := by
  unfold roughHeadPeriodicCoreMulPrefix roughHeadPeriodicCorePrefix
  apply Finset.sum_congr rfl
  intro b _hb
  exact roughHeadPeriodicCoreCoefficient_mul_left hD

/-- Consequently the same explicit prefix bound is uniform in every
coprime multiplier. -/
theorem abs_roughHeadPeriodicCoreMulPrefix_le
    {W D B : Nat} (hD : Nat.Coprime D (roughHeadModulus W)) :
    |roughHeadPeriodicCoreMulPrefix W D B| ≤
      (roughHeadModulus W : Real) / roughHeadDensity W := by
  rw [roughHeadPeriodicCoreMulPrefix_eq hD]
  exact abs_roughHeadPeriodicCorePrefix_le W B

/-! ## Finite Abel cancellation -/

/-- Total discrete variation relevant to Abel summation on `1,...,B`.
The value is zero for the empty prefix. -/
def roughCoreDiscreteVariation (F : Nat → Real) (B : Nat) : Real :=
  if B = 0 then 0 else
    |F B| + ∑ b ∈ Finset.Ioc 0 (B - 1), |F b - F (b + 1)|

/-- Weighted periodic core sum with a fixed multiplier. -/
def roughHeadPeriodicWeightedCoreSum
    (W D : Nat) (F : Nat → Real) (B : Nat) : Real :=
  ∑ b ∈ Finset.Icc 1 B,
    F b * roughHeadPeriodicCoreCoefficient W (D * b)

/-- The zero-extended periodic coefficient has the expected positive
prefix sum. -/
theorem sum_range_succ_zeroExtendedPeriodicCore_eq
    (W D B : Nat) :
    (∑ b ∈ Finset.range (B + 1),
        if b = 0 then 0 else
          roughHeadPeriodicCoreCoefficient W (D * b)) =
      roughHeadPeriodicCoreMulPrefix W D B := by
  rw [Nat.range_eq_Icc_zero_sub_one _ (Nat.add_one_ne_zero B),
    Nat.add_sub_cancel_right]
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le B), Finset.sum_cons,
    ← Finset.Icc_add_one_left_eq_Ioc]
  unfold roughHeadPeriodicCoreMulPrefix
  simp only [if_pos, zero_add]
  apply Finset.sum_congr rfl
  intro b hb
  have hbOne : 1 ≤ b := (Finset.mem_Icc.mp hb).1
  have hb0 : b ≠ 0 := by omega
  simp only [hb0, if_false]

/-- Exact finite Abel identity for the weighted periodic core sum. -/
theorem roughHeadPeriodicWeightedCoreSum_eq_abel
    {W D B : Nat} {F : Nat → Real} (hB : 1 ≤ B) :
    roughHeadPeriodicWeightedCoreSum W D F B =
      F B * roughHeadPeriodicCoreMulPrefix W D B +
        ∑ b ∈ Finset.Ioc 0 (B - 1),
          (F b - F (b + 1)) *
            roughHeadPeriodicCoreMulPrefix W D b := by
  have hBpos : 0 < B := by omega
  have habel := Finset.sum_Ioc_by_parts
    (f := F)
    (g := fun b : Nat => if b = 0 then 0 else
      roughHeadPeriodicCoreCoefficient W (D * b))
    (m := 0) (n := B) hBpos
  have hIoc : Finset.Ioc 0 B = Finset.Icc 1 B := by
    simpa only [zero_add] using
      (Finset.Icc_add_one_left_eq_Ioc 0 B).symm
  rw [hIoc] at habel
  simp_rw [sum_range_succ_zeroExtendedPeriodicCore_eq] at habel
  have hlhs :
      (∑ b ∈ Finset.Icc 1 B,
        F b • (if b = 0 then 0 else
          roughHeadPeriodicCoreCoefficient W (D * b))) =
        roughHeadPeriodicWeightedCoreSum W D F B := by
    unfold roughHeadPeriodicWeightedCoreSum
    apply Finset.sum_congr rfl
    intro b hb
    have hbOne : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have hb0 : b ≠ 0 := by omega
    simp only [hb0, if_false, smul_eq_mul]
  rw [hlhs] at habel
  simp only [smul_eq_mul, zero_add] at habel
  have hprefixZero : roughHeadPeriodicCoreMulPrefix W D 0 = 0 := by
    simp [roughHeadPeriodicCoreMulPrefix]
  rw [hprefixZero, mul_zero, sub_zero] at habel
  have hneg :
      -(∑ b ∈ Finset.Ioc 0 (B - 1),
          (F (b + 1) - F b) * roughHeadPeriodicCoreMulPrefix W D b) =
        ∑ b ∈ Finset.Ioc 0 (B - 1),
          (F b - F (b + 1)) *
            roughHeadPeriodicCoreMulPrefix W D b := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b _hb
    ring
  calc
    roughHeadPeriodicWeightedCoreSum W D F B =
        F B * roughHeadPeriodicCoreMulPrefix W D B -
          ∑ b ∈ Finset.Ioc 0 (B - 1),
            (F (b + 1) - F b) *
              roughHeadPeriodicCoreMulPrefix W D b := habel
    _ = _ := by rw [sub_eq_add_neg, hneg]

/-- A bounded periodic prefix controls every finite weighted sum by the
discrete variation of its weight. -/
theorem abs_roughHeadPeriodicWeightedCoreSum_le_variation
    {W D B : Nat} {F : Nat → Real}
    (hD : Nat.Coprime D (roughHeadModulus W)) :
    |roughHeadPeriodicWeightedCoreSum W D F B| ≤
      ((roughHeadModulus W : Real) / roughHeadDensity W) *
        roughCoreDiscreteVariation F B := by
  by_cases hB0 : B = 0
  · subst B
    simp [roughHeadPeriodicWeightedCoreSum, roughCoreDiscreteVariation]
  have hB : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr hB0
  rw [roughHeadPeriodicWeightedCoreSum_eq_abel hB,
    roughCoreDiscreteVariation, if_neg hB0]
  have hprefix (b : Nat) :
      |roughHeadPeriodicCoreMulPrefix W D b| ≤
        (roughHeadModulus W : Real) / roughHeadDensity W :=
    abs_roughHeadPeriodicCoreMulPrefix_le hD
  have hconstantNonneg :
      0 ≤ (roughHeadModulus W : Real) / roughHeadDensity W := by
    exact div_nonneg (Nat.cast_nonneg _) (roughHeadDensity_pos W).le
  calc
    |F B * roughHeadPeriodicCoreMulPrefix W D B +
        ∑ b ∈ Finset.Ioc 0 (B - 1),
          (F b - F (b + 1)) *
            roughHeadPeriodicCoreMulPrefix W D b| ≤
      |F B * roughHeadPeriodicCoreMulPrefix W D B| +
        |∑ b ∈ Finset.Ioc 0 (B - 1),
          (F b - F (b + 1)) *
            roughHeadPeriodicCoreMulPrefix W D b| := abs_add_le _ _
    _ ≤ |F B| * ((roughHeadModulus W : Real) / roughHeadDensity W) +
        ∑ b ∈ Finset.Ioc 0 (B - 1),
          |F b - F (b + 1)| *
            ((roughHeadModulus W : Real) / roughHeadDensity W) := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hprefix B) (abs_nonneg _)
      · exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun b _hb => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hprefix b) (abs_nonneg _))
    _ = ((roughHeadModulus W : Real) / roughHeadDensity W) *
        (|F B| + ∑ b ∈ Finset.Ioc 0 (B - 1),
          |F b - F (b + 1)|) := by
      rw [mul_add, Finset.mul_sum]
      apply congrArg₂ (fun x y : Real => x + y)
      · ring
      · apply Finset.sum_congr rfl
        intro b _hb
        ring

/-! ## Prime-power expansion of the periodic leading ledger -/

/-- Exact reindexing of a weighted divisibility column by division. -/
theorem sum_Icc_mul_divInd_eq_quotientSum
    {D B : Nat} (hD : 0 < D) (F : Nat → Real) :
    (∑ b ∈ Finset.Icc 1 B, F b * divInd D b) =
      ∑ m ∈ Finset.Icc 1 (B / D), F (D * m) := by
  have hfilter :
      (∑ b ∈ Finset.Icc 1 B, F b * divInd D b) =
        ∑ b ∈ (Finset.Icc 1 B).filter (fun b => D ∣ b), F b := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _hb
    by_cases hDb : D ∣ b <;> simp [divInd, hDb]
  rw [hfilter]
  symm
  apply Finset.sum_bij (fun m _hm => D * m)
  · intro m hm
    have hmData := Finset.mem_Icc.mp hm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, Nat.dvd_mul_right D m⟩
    · exact mul_pos hD hmData.1
    · simpa only [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le hD).mp hmData.2
  · intro m₁ _hm₁ m₂ _hm₂ heq
    exact Nat.mul_left_cancel hD heq
  · intro b hb
    have hbData := Finset.mem_filter.mp hb
    have hbIcc := Finset.mem_Icc.mp hbData.1
    have hDLeB : D ≤ b := Nat.le_of_dvd hbIcc.1 hbData.2
    refine ⟨b / D, Finset.mem_Icc.mpr ⟨Nat.div_pos hDLeB hD,
      Nat.div_le_div_right hbIcc.2⟩, ?_⟩
    simpa only [Nat.mul_comm] using Nat.mul_div_cancel' hbData.2
  · intro m _hm
    rfl

/-- The complete periodic leading ledger at one prime. -/
def roughHeadPeriodicValuationCoreSum
    (W p : Nat) (F : Nat → Real) (B : Nat) : Real :=
  ∑ b ∈ Finset.Icc 1 B,
    (b.factorization p : Real) *
      roughHeadPeriodicCoreCoefficient W b * F b

/-- Expanding the valuation into prime-power divisibility columns and then
dividing by `p^k` gives the exact sum of periodic Abel blocks. -/
theorem roughHeadPeriodicValuationCoreSum_eq_primePowerBlocks
    {W p B : Nat} (hp : p.Prime) (F : Nat → Real) :
    roughHeadPeriodicValuationCoreSum W p F B =
      ∑ k ∈ positiveExponents B,
        roughHeadPeriodicWeightedCoreSum W (p ^ k)
          (fun m => F (p ^ k * m)) (B / p ^ k) := by
  unfold roughHeadPeriodicValuationCoreSum
  calc
    (∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : Real) *
          roughHeadPeriodicCoreCoefficient W b * F b) =
      ∑ b ∈ Finset.Icc 1 B,
        (∑ k ∈ positiveExponents B, divInd (p ^ k) b) *
          roughHeadPeriodicCoreCoefficient W b * F b := by
      apply Finset.sum_congr rfl
      intro b hb
      have hbData := Finset.mem_Icc.mp hb
      have hvaluation :=
        valuation_eq_sum_divInd_of_le hp hbData.1 hbData.2
      change valuation p b * roughHeadPeriodicCoreCoefficient W b * F b = _
      rw [hvaluation]
    _ = ∑ b ∈ Finset.Icc 1 B,
        ∑ k ∈ positiveExponents B,
          (roughHeadPeriodicCoreCoefficient W b * F b) *
            divInd (p ^ k) b := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ = ∑ k ∈ positiveExponents B,
        ∑ b ∈ Finset.Icc 1 B,
          (roughHeadPeriodicCoreCoefficient W b * F b) *
            divInd (p ^ k) b := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ positiveExponents B,
        ∑ m ∈ Finset.Icc 1 (B / p ^ k),
          roughHeadPeriodicCoreCoefficient W (p ^ k * m) *
            F (p ^ k * m) := by
      apply Finset.sum_congr rfl
      intro k _hk
      simpa only [mul_comm] using
        (sum_Icc_mul_divInd_eq_quotientSum
          (pow_pos hp.pos k)
          (fun b => roughHeadPeriodicCoreCoefficient W b * F b))
    _ = ∑ k ∈ positiveExponents B,
        roughHeadPeriodicWeightedCoreSum W (p ^ k)
          (fun m => F (p ^ k * m)) (B / p ^ k) := by
      apply Finset.sum_congr rfl
      intro k _hk
      unfold roughHeadPeriodicWeightedCoreSum
      apply Finset.sum_congr rfl
      intro m _hm
      ring

/-- The paper's periodic prime-power lemma in its exact reusable form.  The
only hypothesis on `F` is the `O(1/p^k)` discrete variation which a bounded
`C^1` logarithmic kernel divided by its argument satisfies. -/
theorem abs_roughHeadPeriodicValuationCoreSum_le
    {W p B : Nat} {F : Nat → Real} {variationConstant : Real}
    (hp : p.Prime) (hWp : W < p) (hvariationNonneg : 0 ≤ variationConstant)
    (hvariation : ∀ k ∈ positiveExponents B,
      roughCoreDiscreteVariation (fun m => F (p ^ k * m))
          (B / p ^ k) ≤ variationConstant / ((p ^ k : Nat) : Real)) :
    |roughHeadPeriodicValuationCoreSum W p F B| ≤
      2 * ((roughHeadModulus W : Real) / roughHeadDensity W) *
        variationConstant / (p : Real) := by
  rw [roughHeadPeriodicValuationCoreSum_eq_primePowerBlocks hp F]
  have hpReal : (0 : Real) < (p : Real) := by exact_mod_cast hp.pos
  have hheadNonneg :
      0 ≤ (roughHeadModulus W : Real) / roughHeadDensity W := by
    exact div_nonneg (Nat.cast_nonneg _) (roughHeadDensity_pos W).le
  have hblock (k : Nat) (hk : k ∈ positiveExponents B) :
      |roughHeadPeriodicWeightedCoreSum W (p ^ k)
          (fun m => F (p ^ k * m)) (B / p ^ k)| ≤
        ((roughHeadModulus W : Real) / roughHeadDensity W) *
          (variationConstant / ((p ^ k : Nat) : Real)) := by
    have hcop : Nat.Coprime (p ^ k) (roughHeadModulus W) :=
      (prime_coprime_roughHeadModulus_of_cutoff_lt hp hWp).pow_left k
    exact (abs_roughHeadPeriodicWeightedCoreSum_le_variation
      (F := fun m => F (p ^ k * m)) (B := B / p ^ k) hcop).trans
        (mul_le_mul_of_nonneg_left (hvariation k hk) hheadNonneg)
  calc
    |∑ k ∈ positiveExponents B,
        roughHeadPeriodicWeightedCoreSum W (p ^ k)
          (fun m => F (p ^ k * m)) (B / p ^ k)| ≤
      ∑ k ∈ positiveExponents B,
        |roughHeadPeriodicWeightedCoreSum W (p ^ k)
          (fun m => F (p ^ k * m)) (B / p ^ k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ positiveExponents B,
        ((roughHeadModulus W : Real) / roughHeadDensity W) *
          (variationConstant / ((p ^ k : Nat) : Real)) :=
      Finset.sum_le_sum hblock
    _ = ((roughHeadModulus W : Real) / roughHeadDensity W) *
        variationConstant *
          (∑ k ∈ positiveExponents B,
            1 / ((p ^ k : Nat) : Real)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ ≤ ((roughHeadModulus W : Real) / roughHeadDensity W) *
        variationConstant * (2 / (p : Real)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [positiveExponents, zero_add, pow_one] using
          (sum_inv_pow_tail_le (p := p) (r := 0) (A := B) hp.two_le)
      · exact mul_nonneg hheadNonneg hvariationNonneg
    _ = 2 * ((roughHeadModulus W : Real) / roughHeadDensity W) *
        variationConstant / (p : Real) := by ring

/-! ## Elementary valuation ledgers for the analytic remainders -/

/-- A pointwise `A/b+E` core error sums with the two standard valuation
prefixes and no loss beyond their literal constants. -/
theorem abs_sum_factorization_mul_error_le
    {p B : Nat} {error : Nat → Real} {A E : Real}
    (hp : p.Prime) (hB : 1 ≤ B) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (herror : ∀ b ∈ Finset.Icc 1 B,
      |error b| ≤ A / (b : Real) + E) :
    |∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : Real) * error b| ≤
      A * (2 * (1 + Real.log (B : Real)) / (p : Real)) +
        E * (2 * (B : Real) / (p : Real)) := by
  have hpReal : (0 : Real) < (p : Real) := by exact_mod_cast hp.pos
  have hweighted :=
    weightedFactorizationSum_le_two_mul_one_add_log_div_prime
      (p := p) (B := B) hp hB
  have hunweighted :=
    sum_factorization_Icc_cast_le_two_mul_div_prime
      (p := p) (B := B) hp
  have hmainNonneg : 0 ≤ A := hA
  have hendNonneg : 0 ≤ E := hE
  calc
    |∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : Real) * error b| ≤
      ∑ b ∈ Finset.Icc 1 B,
        |(b.factorization p : Real) * error b| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : Real) * |error b| := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ ∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : Real) * (A / (b : Real) + E) := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (herror b hb) (Nat.cast_nonneg _)
    _ = A * (∑ b ∈ Finset.Icc 1 B,
          (b.factorization p : Real) / (b : Real)) +
        E * (∑ b ∈ Finset.Icc 1 B,
          (b.factorization p : Real)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _hb
      ring
    _ ≤ A * (2 * (1 + Real.log (B : Real)) / (p : Real)) +
        E * (2 * (B : Real) / (p : Real)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hweighted hmainNonneg)
        (mul_le_mul_of_nonneg_left hunweighted hendNonneg)

/-- The valuation count in the single cutoff band is bounded by the full
prefix count. -/
theorem sum_factorization_cutoffBand_le_four_mul_div_prime
    {p X : Nat} (hp : p.Prime) (_hX : 1 ≤ X) :
    (∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        (b.factorization p : Real)) ≤
      4 * (X : Real) / (p : Real) := by
  have hsubset : Finset.Ioc (X / 2) (2 * X) ⊆
      Finset.Icc 1 (2 * X) := by
    intro b hb
    have hbData := Finset.mem_Ioc.mp hb
    exact Finset.mem_Icc.mpr ⟨by omega, hbData.2⟩
  calc
    (∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        (b.factorization p : Real)) ≤
      ∑ b ∈ Finset.Icc 1 (2 * X),
        (b.factorization p : Real) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _b _hbPrefix _hbBand => Nat.cast_nonneg _)
    _ ≤ 2 * ((2 * X : Nat) : Real) / (p : Real) :=
      sum_factorization_Icc_cast_le_two_mul_div_prime hp
    _ = 4 * (X : Real) / (p : Real) := by
      push_cast
      ring

/-- Because every member of the cutoff band is larger than `X/2`, its
harmonically weighted valuation sum is `O(1/p)`, not `O(log X/p)`. -/
theorem weightedFactorizationSum_cutoffBand_le_eight_div_prime
    {p X : Nat} (hp : p.Prime) (hX : 1 ≤ X) :
    (∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        (b.factorization p : Real) / (b : Real)) ≤
      8 / (p : Real) := by
  have hXReal : (0 : Real) < (X : Real) := by exact_mod_cast hX
  have hpReal : (0 : Real) < (p : Real) := by exact_mod_cast hp.pos
  have hpoint (b : Nat) (hb : b ∈ Finset.Ioc (X / 2) (2 * X)) :
      (b.factorization p : Real) / (b : Real) ≤
        (2 / (X : Real)) * (b.factorization p : Real) := by
    have hbData := Finset.mem_Ioc.mp hb
    have hbPos : 0 < b := by omega
    have hbReal : (0 : Real) < (b : Real) := by exact_mod_cast hbPos
    have hXLe : X ≤ 2 * b := by omega
    have hrecip : 1 / (b : Real) ≤ 2 / (X : Real) := by
      apply (div_le_div_iff₀ hbReal hXReal).2
      have hXLeReal : (X : Real) ≤ 2 * (b : Real) := by
        exact_mod_cast hXLe
      simpa only [one_mul] using hXLeReal
    calc
      (b.factorization p : Real) / (b : Real) =
          (1 / (b : Real)) * (b.factorization p : Real) := by ring
      _ ≤ (2 / (X : Real)) * (b.factorization p : Real) :=
        mul_le_mul_of_nonneg_right hrecip (Nat.cast_nonneg _)
  calc
    (∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        (b.factorization p : Real) / (b : Real)) ≤
      ∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        (2 / (X : Real)) * (b.factorization p : Real) :=
      Finset.sum_le_sum hpoint
    _ = (2 / (X : Real)) *
        (∑ b ∈ Finset.Ioc (X / 2) (2 * X),
          (b.factorization p : Real)) := by rw [Finset.mul_sum]
    _ ≤ (2 / (X : Real)) * (4 * (X : Real) / (p : Real)) :=
      mul_le_mul_of_nonneg_left
        (sum_factorization_cutoffBand_le_four_mul_div_prime hp hX)
        (by positivity)
    _ = 8 / (p : Real) := by
      field_simp [hXReal.ne', hpReal.ne']; ring

/-- A pointwise `A/b+E` error on the single cutoff band therefore costs
`8A/p+4EX/p`, including every endpoint `+1`. -/
theorem abs_sum_factorization_mul_cutoffBand_error_le
    {p X : Nat} {error : Nat → Real} {A E : Real}
    (hp : p.Prime) (hX : 1 ≤ X) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (herror : ∀ b ∈ Finset.Ioc (X / 2) (2 * X),
      |error b| ≤ A / (b : Real) + E) :
    |∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        (b.factorization p : Real) * error b| ≤
      A * (8 / (p : Real)) +
        E * (4 * (X : Real) / (p : Real)) := by
  have hweighted :=
    weightedFactorizationSum_cutoffBand_le_eight_div_prime hp hX
  have hunweighted :=
    sum_factorization_cutoffBand_le_four_mul_div_prime hp hX
  calc
    |∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        (b.factorization p : Real) * error b| ≤
      ∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        |(b.factorization p : Real) * error b| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        (b.factorization p : Real) * |error b| := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ ∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        (b.factorization p : Real) * (A / (b : Real) + E) := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (herror b hb) (Nat.cast_nonneg _)
    _ = A * (∑ b ∈ Finset.Ioc (X / 2) (2 * X),
          (b.factorization p : Real) / (b : Real)) +
        E * (∑ b ∈ Finset.Ioc (X / 2) (2 * X),
          (b.factorization p : Real)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _hb
      ring
    _ ≤ A * (8 / (p : Real)) +
        E * (4 * (X : Real) / (p : Real)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hweighted hA)
        (mul_le_mul_of_nonneg_left hunweighted hE)

/-! ## The isolated four-to-five chamber input -/

/-- The deep smooth-core prefix used before the cutoff band. -/
def roughCanonicalExceptionalDeepCoreSet
    (deltaStar : Real) (n : Nat) : Finset Nat :=
  Finset.Icc 1 (tangentPaperExceptionalCutoff deltaStar n / 2)

/-- The one fixed-ratio cutoff band `X0/2 < b ≤ 2X0`. -/
def roughCanonicalExceptionalCutoffCoreSet
    (deltaStar : Real) (n : Nat) : Finset Nat :=
  Finset.Ioc (tangentPaperExceptionalCutoff deltaStar n / 2)
    (2 * tangentPaperExceptionalCutoff deltaStar n)

/-- Deep prefix and cutoff band are disjoint. -/
theorem roughCanonicalExceptionalDeepCoreSet_disjoint_cutoffCoreSet
    (deltaStar : Real) (n : Nat) :
    Disjoint (roughCanonicalExceptionalDeepCoreSet deltaStar n)
      (roughCanonicalExceptionalCutoffCoreSet deltaStar n) := by
  rw [Finset.disjoint_left]
  intro b hbDeep hbBand
  simp only [roughCanonicalExceptionalDeepCoreSet,
    roughCanonicalExceptionalCutoffCoreSet, Finset.mem_Icc,
    Finset.mem_Ioc] at hbDeep hbBand
  omega

/-- Deep prefix and cutoff band exhaust the common core prefix. -/
theorem roughCanonicalExceptionalDeepCoreSet_union_cutoffCoreSet
    (deltaStar : Real) (n : Nat) :
    roughCanonicalExceptionalDeepCoreSet deltaStar n ∪
        roughCanonicalExceptionalCutoffCoreSet deltaStar n =
      Finset.Icc 1 (2 * tangentPaperExceptionalCutoff deltaStar n) := by
  ext b
  simp only [roughCanonicalExceptionalDeepCoreSet,
    roughCanonicalExceptionalCutoffCoreSet, Finset.mem_union,
    Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- Exact split of an arbitrary common-prefix sum into the paper's deep
range and its single cutoff band. -/
theorem sum_exceptionalCorePrefix_eq_deep_add_cutoff
    (deltaStar : Real) (n : Nat) (F : Nat → Real) :
    (∑ b ∈ Finset.Icc 1
        (2 * tangentPaperExceptionalCutoff deltaStar n), F b) =
      (∑ b ∈ roughCanonicalExceptionalDeepCoreSet deltaStar n, F b) +
        ∑ b ∈ roughCanonicalExceptionalCutoffCoreSet deltaStar n, F b := by
  rw [← Finset.sum_union
    (roughCanonicalExceptionalDeepCoreSet_disjoint_cutoffCoreSet
      deltaStar n),
    roughCanonicalExceptionalDeepCoreSet_union_cutoffCoreSet]

/-- Smallest new analytic statement left by the finite reduction.

For each deep core it is precisely the signed four-to-five-prime expansion
after the three physical pieces have already been summed.  `kernelWeight`
contains the factor `K(log(2n/b)/log y)/b`; its prime-power discrete
variation records bounded `C^1` norm of `K`.  The cutoff-band clause is the
positive three-interval estimate.  Neither clause mentions valuations or
the target `N/(pL)` bound.
-/
def RoughCanonicalSignedExceptionalCoreChamberEstimate
    (W n h K : Nat) (deltaStar : Real) (rawWeight : Nat → Real)
    (kernelWeight coreError : Nat → Real)
    (deepConstant cutoffConstant variationConstant : Real) : Prop :=
  (∀ b ∈ roughCanonicalExceptionalDeepCoreSet deltaStar n,
      roughCanonicalSignedExceptionalCoreMass n h K deltaStar rawWeight b =
        ((h : Real) / Real.log (yNat n : Real)) *
          roughHeadPeriodicCoreCoefficient W b * kernelWeight b +
            coreError b) ∧
  (∀ b ∈ roughCanonicalExceptionalDeepCoreSet deltaStar n,
      |coreError b| ≤
        deepConstant * ((n : Real) / ((b : Real) * L n ^ 3) + 1)) ∧
  (∀ b ∈ roughCanonicalExceptionalCutoffCoreSet deltaStar n,
      |roughCanonicalSignedExceptionalCoreMass n h K deltaStar rawWeight b| ≤
        cutoffConstant * ((n : Real) / ((b : Real) * L n ^ 2) + 1)) ∧
  (∀ p : Nat, p.Prime → W < p →
      ∀ k ∈ positiveExponents
          (tangentPaperExceptionalCutoff deltaStar n / 2),
        roughCoreDiscreteVariation
            (fun m => kernelWeight (p ^ k * m))
            ((tangentPaperExceptionalCutoff deltaStar n / 2) / p ^ k) ≤
          variationConstant / ((p ^ k : Nat) : Real))

/-- Finite conclusion of the complete core-first argument.  Its right-hand
side displays separately the periodic leading term, the deep chamber error,
the deep endpoint allowance, the cutoff-band error, and the cutoff endpoint
allowance. -/
theorem abs_roughCanonicalSignedExceptionalResidual_le_coreFirstFinite
    {W n h K p : Nat} {deltaStar : Real} {rawWeight : Nat → Real}
    {kernelWeight coreError : Nat → Real}
    {deepConstant cutoffConstant variationConstant : Real}
    (hdelta : 0 ≤ deltaStar) (hn : 1 ≤ n) (hh : h ≤ n)
    (hp : p.Prime) (hWp : W < p) (hpY : p ≤ yNat n)
    (hcut : 2 ≤ tangentPaperExceptionalCutoff deltaStar n)
    (hdeepConstant : 0 ≤ deepConstant)
    (hcutoffConstant : 0 ≤ cutoffConstant)
    (hvariationConstant : 0 ≤ variationConstant)
    (hchamber : RoughCanonicalSignedExceptionalCoreChamberEstimate
      W n h K deltaStar rawWeight kernelWeight coreError
        deepConstant cutoffConstant variationConstant) :
    |roughCanonicalSignedExceptionalResidual n h K deltaStar rawWeight p| ≤
      ((h : Real) / Real.log (yNat n : Real)) *
          (2 * ((roughHeadModulus W : Real) / roughHeadDensity W) *
            variationConstant / (p : Real)) +
        (deepConstant * (n : Real) / L n ^ 3) *
          (2 * (1 + Real.log
            ((tangentPaperExceptionalCutoff deltaStar n / 2 : Nat) : Real)) /
              (p : Real)) +
        deepConstant *
          (2 * ((tangentPaperExceptionalCutoff deltaStar n / 2 : Nat) : Real) /
            (p : Real)) +
        (cutoffConstant * (n : Real) / L n ^ 2) *
          (8 / (p : Real)) +
        cutoffConstant *
          (4 * (tangentPaperExceptionalCutoff deltaStar n : Real) /
            (p : Real)) := by
  let X := tangentPaperExceptionalCutoff deltaStar n
  let B := X / 2
  have hB : 1 ≤ B := by omega
  have hX : 1 ≤ X := by omega
  have hlogYPos : 0 < Real.log (yNat n : Real) := by
    have hyTwo : 2 ≤ yNat n := hp.two_le.trans hpY
    exact Real.log_pos (by exact_mod_cast hyTwo)
  have hnTwo : 1 < n := by
    by_contra hnot
    have hnEq : n = 1 := by omega
    subst n
    norm_num [yNat, y] at hpY
    have hpTwo : 2 ≤ p := hp.two_le
    omega
  have hLPos : 0 < L n := L_pos hnTwo
  have hleadNonneg : 0 ≤ (h : Real) / Real.log (yNat n : Real) := by
    positivity
  obtain ⟨hdeep, hdeepError, hband, hvariation⟩ := hchamber
  have hperiodic := abs_roughHeadPeriodicValuationCoreSum_le
    hp hWp hvariationConstant (hvariation p hp hWp)
  have hdeepError' : ∀ b ∈ Finset.Icc 1 B,
      |coreError b| ≤
        (deepConstant * (n : Real) / L n ^ 3) / (b : Real) +
          deepConstant := by
    intro b hb
    have hbDeep : b ∈ roughCanonicalExceptionalDeepCoreSet deltaStar n := by
      simpa only [roughCanonicalExceptionalDeepCoreSet, B, X] using hb
    calc
      |coreError b| ≤
          deepConstant * ((n : Real) / ((b : Real) * L n ^ 3) + 1) :=
        hdeepError b hbDeep
      _ = (deepConstant * (n : Real) / L n ^ 3) / (b : Real) +
          deepConstant := by ring
  have hdeepLedger := abs_sum_factorization_mul_error_le
    hp hB (by positivity : 0 ≤ deepConstant * (n : Real) / L n ^ 3)
      hdeepConstant hdeepError'
  have hband' : ∀ b ∈ Finset.Ioc (X / 2) (2 * X),
      |roughCanonicalSignedExceptionalCoreMass n h K deltaStar rawWeight b| ≤
        (cutoffConstant * (n : Real) / L n ^ 2) / (b : Real) +
          cutoffConstant := by
    intro b hb
    have hbBand : b ∈ roughCanonicalExceptionalCutoffCoreSet deltaStar n := by
      simpa only [roughCanonicalExceptionalCutoffCoreSet, X] using hb
    calc
      |roughCanonicalSignedExceptionalCoreMass n h K deltaStar rawWeight b| ≤
          cutoffConstant *
            ((n : Real) / ((b : Real) * L n ^ 2) + 1) := hband b hbBand
      _ = (cutoffConstant * (n : Real) / L n ^ 2) / (b : Real) +
          cutoffConstant := by ring
  have hbandLedger := abs_sum_factorization_mul_cutoffBand_error_le
    hp hX (by positivity : 0 ≤ cutoffConstant * (n : Real) / L n ^ 2)
      hcutoffConstant hband'
  have hdeepIdentity :
      (∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : Real) *
          roughCanonicalSignedExceptionalCoreMass
            n h K deltaStar rawWeight b) =
        ((h : Real) / Real.log (yNat n : Real)) *
            roughHeadPeriodicValuationCoreSum W p kernelWeight B +
          ∑ b ∈ Finset.Icc 1 B,
            (b.factorization p : Real) * coreError b := by
    unfold roughHeadPeriodicValuationCoreSum
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    have hbDeep : b ∈ roughCanonicalExceptionalDeepCoreSet deltaStar n := by
      simpa only [roughCanonicalExceptionalDeepCoreSet, B, X] using hb
    rw [hdeep b hbDeep]
    ring
  rw [roughCanonicalSignedExceptionalResidual_eq_coreFirst
    hdelta hn hh hpY,
    sum_exceptionalCorePrefix_eq_deep_add_cutoff]
  change
    |(∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : Real) *
          roughCanonicalSignedExceptionalCoreMass
            n h K deltaStar rawWeight b) +
      ∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        (b.factorization p : Real) *
          roughCanonicalSignedExceptionalCoreMass
            n h K deltaStar rawWeight b| ≤ _
  rw [hdeepIdentity]
  have hleadLedger :
      |((h : Real) / Real.log (yNat n : Real)) *
          roughHeadPeriodicValuationCoreSum W p kernelWeight B| ≤
        ((h : Real) / Real.log (yNat n : Real)) *
          (2 * ((roughHeadModulus W : Real) / roughHeadDensity W) *
            variationConstant / (p : Real)) := by
    rw [abs_mul, abs_of_nonneg hleadNonneg]
    exact mul_le_mul_of_nonneg_left hperiodic hleadNonneg
  calc
    |((h : Real) / Real.log (yNat n : Real)) *
          roughHeadPeriodicValuationCoreSum W p kernelWeight B +
        (∑ b ∈ Finset.Icc 1 B,
          (b.factorization p : Real) * coreError b) +
        ∑ b ∈ Finset.Ioc (X / 2) (2 * X),
          (b.factorization p : Real) *
            roughCanonicalSignedExceptionalCoreMass
              n h K deltaStar rawWeight b| ≤
      |((h : Real) / Real.log (yNat n : Real)) *
          roughHeadPeriodicValuationCoreSum W p kernelWeight B| +
        |∑ b ∈ Finset.Icc 1 B,
          (b.factorization p : Real) * coreError b| +
        |∑ b ∈ Finset.Ioc (X / 2) (2 * X),
          (b.factorization p : Real) *
            roughCanonicalSignedExceptionalCoreMass
              n h K deltaStar rawWeight b| := by
      exact (abs_add_le _ _).trans
        (add_le_add_left (abs_add_le _ _) _)
    _ ≤ ((h : Real) / Real.log (yNat n : Real)) *
          (2 * ((roughHeadModulus W : Real) / roughHeadDensity W) *
            variationConstant / (p : Real)) +
        ((deepConstant * (n : Real) / L n ^ 3) *
          (2 * (1 + Real.log (B : Real)) / (p : Real)) +
        deepConstant * (2 * (B : Real) / (p : Real))) +
        ((cutoffConstant * (n : Real) / L n ^ 2) *
          (8 / (p : Real)) +
        cutoffConstant * (4 * (X : Real) / (p : Real))) := by
      exact add_le_add (add_le_add hleadLedger hdeepLedger) hbandLedger
    _ = _ := by
      simp only [B, X]
      ring

/-! ## Endpoint absorption at the strict paper scale -/

/-- Normalized size of the exceptional smooth-core endpoint allowance. -/
def roughCanonicalExceptionalEndpointRatio
    (deltaStar : Real) (n : Nat) : Real :=
  (tangentPaperExceptionalCutoff deltaStar n : Real) * L n ^ 2 /
    (n : Real)

/-- A positive exceptional exponent makes the natural cutoff tend to
infinity. -/
theorem tangentPaperExceptionalCutoff_tendsto_atTop
    {deltaStar : Real} (hdelta : 0 < deltaStar) :
    Tendsto (tangentPaperExceptionalCutoff deltaStar) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro A
  have hpower : Tendsto (fun n : Nat => (n : Real) ^ deltaStar)
      atTop atTop :=
    (tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop
  have hpowerGe : ∀ᶠ n : Nat in atTop,
      (A : Real) ≤ (n : Real) ^ deltaStar :=
    hpower.eventually (eventually_ge_atTop (A : Real))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hpowerGe
  refine ⟨N, fun n hn => ?_⟩
  have hcut := tangentPaperExceptionalCutoff_cast_ge deltaStar n
  exact_mod_cast (hN n hn).trans hcut

/-- The cutoff endpoint allowance `X0*L^2/n` tends to zero for every fixed
`deltaStar<1`. -/
theorem roughCanonicalExceptionalEndpointRatio_tendsto_zero
    {deltaStar : Real} (hdeltaUpper : deltaStar < 1) :
    Tendsto (roughCanonicalExceptionalEndpointRatio deltaStar)
      atTop (nhds 0) := by
  have hexponent : 0 < 1 - deltaStar := sub_pos.mpr hdeltaUpper
  have hrealMain : Tendsto
      (fun x : Real => Real.log x ^ (2 : Real) /
        x ^ (1 - deltaStar)) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : Real) hexponent).tendsto_div_nhds_zero
  have hmain : Tendsto
      (fun n : Nat => L n ^ 2 / (n : Real) ^ (1 - deltaStar))
      atTop (nhds 0) := by
    simpa [Function.comp_def, L, Real.rpow_natCast] using
      hrealMain.comp tendsto_natCast_atTop_atTop
  have hrealEndpoint : Tendsto
      (fun x : Real => Real.log x ^ (2 : Real) / x ^ (1 : Real))
      atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : Real)
      (by norm_num : (0 : Real) < 1)).tendsto_div_nhds_zero
  have hendpoint : Tendsto
      (fun n : Nat => L n ^ 2 / (n : Real)) atTop (nhds 0) := by
    simpa [Function.comp_def, L, Real.rpow_natCast, Real.rpow_one] using
      hrealEndpoint.comp tendsto_natCast_atTop_atTop
  have hmodel : Tendsto
      (fun n : Nat => ((n : Real) ^ deltaStar + 1) * L n ^ 2 /
        (n : Real)) atTop (nhds 0) := by
    have hadd := hmain.add hendpoint
    have heq :
        (fun n : Nat =>
            L n ^ 2 / (n : Real) ^ (1 - deltaStar) +
              L n ^ 2 / (n : Real)) =ᶠ[atTop]
          (fun n : Nat =>
            ((n : Real) ^ deltaStar + 1) * L n ^ 2 / (n : Real)) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hn
      have hpowPos : (0 : Real) < (n : Real) ^ (1 - deltaStar) :=
        Real.rpow_pos_of_pos hnReal _
      have hpow :
          (n : Real) ^ deltaStar * (n : Real) ^ (1 - deltaStar) =
            (n : Real) := by
        rw [← Real.rpow_add hnReal]
        ring_nf
        exact Real.rpow_one _
      have hquot :
          (n : Real) ^ deltaStar / (n : Real) =
            1 / (n : Real) ^ (1 - deltaStar) := by
        calc
          (n : Real) ^ deltaStar / (n : Real) =
              ((n : Real) ^ deltaStar * (n : Real) ^ (1 - deltaStar)) /
                ((n : Real) * (n : Real) ^ (1 - deltaStar)) := by
            field_simp [hnReal.ne', hpowPos.ne']
          _ = (n : Real) /
                ((n : Real) * (n : Real) ^ (1 - deltaStar)) := by rw [hpow]
          _ = 1 / (n : Real) ^ (1 - deltaStar) := by
            field_simp [hnReal.ne', hpowPos.ne']
      calc
        L n ^ 2 / (n : Real) ^ (1 - deltaStar) +
            L n ^ 2 / (n : Real) =
          ((n : Real) ^ deltaStar / (n : Real)) * L n ^ 2 +
            L n ^ 2 / (n : Real) := by rw [hquot]; ring
        _ = ((n : Real) ^ deltaStar + 1) * L n ^ 2 /
            (n : Real) := by ring
    simpa using hadd.congr' heq
  apply squeeze_zero'
  · filter_upwards [eventually_gt_atTop 0] with n hn
    unfold roughCanonicalExceptionalEndpointRatio
    positivity
  · filter_upwards [eventually_gt_atTop 1] with n hn
    have hnReal : (0 : Real) < (n : Real) := by positivity
    have hcut := tangentPaperExceptionalCutoff_cast_lt_add_one
      deltaStar n
    unfold roughCanonicalExceptionalEndpointRatio
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcut.le (sq_nonneg (L n))) hnReal.le
  · exact hmodel

/-- Eventually every exceptional endpoint `+1` is absorbed by
`n/L^2`. -/
theorem eventually_tangentPaperExceptionalCutoff_le_self_div_L_sq
    {deltaStar : Real} (hdeltaUpper : deltaStar < 1) :
    ∀ᶠ n : Nat in atTop,
      (tangentPaperExceptionalCutoff deltaStar n : Real) ≤
        (n : Real) / L n ^ 2 := by
  have hratio : ∀ᶠ n : Nat in atTop,
      roughCanonicalExceptionalEndpointRatio deltaStar n ≤ 1 :=
    (roughCanonicalExceptionalEndpointRatio_tendsto_zero hdeltaUpper).eventually
      (eventually_le_nhds (by norm_num : (0 : Real) < 1))
  filter_upwards [hratio, eventually_gt_atTop 1] with n hnRatio hn
  have hnReal : (0 : Real) < (n : Real) := by positivity
  have hL : 0 < L n := L_pos hn
  unfold roughCanonicalExceptionalEndpointRatio at hnRatio
  have hproduct :
      (tangentPaperExceptionalCutoff deltaStar n : Real) * L n ^ 2 ≤
        (n : Real) := by
    have hratioProduct := (div_le_iff₀ hnReal).mp hnRatio
    simpa only [one_mul] using hratioProduct
  exact (le_div_iff₀ (sq_pos_of_pos hL)).2 hproduct

/-! ## Uniform paper-scale packaging -/

/-- Eventual form of the isolated chamber estimate for the literal balanced
raw point.  The constants are fixed before `n`, while the kernel and its
literal finite remainder may depend on `n`. -/
def RoughCanonicalSignedExceptionalCoreChamberEventually
    (W K : Nat) (c deltaStar beta : Real)
    (deepConstant cutoffConstant variationConstant : Real) : Prop :=
  ∀ᶠ n : Nat in atTop,
    ∃ kernelWeight coreError : Nat → Real,
      RoughCanonicalSignedExceptionalCoreChamberEstimate
        W n (upperTailLength c n) K deltaStar
        (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
          (roughHeadBalancedAlpha W n (upperTailLength c n) K beta (L n))
          beta (L n))
        kernelWeight coreError deepConstant cutoffConstant variationConstant

/-- One fixed constant which pays all five terms in the finite core-first
ledger. -/
def roughCanonicalSignedExceptionalCoreBoundConstant
    (W : Nat) (c deltaStar deepConstant cutoffConstant
      variationConstant : Real) : Real :=
  20 * c * ((roughHeadModulus W : Real) / roughHeadDensity W) *
      variationConstant +
    (4 * deltaStar + 2) * deepConstant +
    12 * cutoffConstant

/-- The constant is nonnegative under the natural positivity hypotheses. -/
theorem roughCanonicalSignedExceptionalCoreBoundConstant_nonneg
    {W : Nat} {c deltaStar deepConstant cutoffConstant
      variationConstant : Real}
    (hc : 0 ≤ c) (hdelta : 0 ≤ deltaStar)
    (hdeep : 0 ≤ deepConstant) (hcutoff : 0 ≤ cutoffConstant)
    (hvariation : 0 ≤ variationConstant) :
    0 ≤ roughCanonicalSignedExceptionalCoreBoundConstant W c deltaStar
      deepConstant cutoffConstant variationConstant := by
  unfold roughCanonicalSignedExceptionalCoreBoundConstant
  have hhead : 0 ≤
      (roughHeadModulus W : Real) / roughHeadDensity W := by
    exact div_nonneg (Nat.cast_nonneg _) (roughHeadDensity_pos W).le
  positivity

/-- Once the isolated four-to-five chamber estimate is supplied, all
remaining finite and asymptotic ledgers give the paper's strict
`N/(pL)` bound, uniformly for `W<p≤y`. -/
theorem eventually_roughCanonicalSignedExceptionalResidualBound_of_coreChamber
    {W K : Nat} {c deltaStar beta : Real}
    {deepConstant cutoffConstant variationConstant : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18)
    (hdeep : 0 ≤ deepConstant) (hcutoff : 0 ≤ cutoffConstant)
    (hvariation : 0 ≤ variationConstant)
    (hchamber : RoughCanonicalSignedExceptionalCoreChamberEventually
      W K c deltaStar beta deepConstant cutoffConstant variationConstant) :
    ∀ᶠ n : Nat in atTop, ∀ p : Nat,
      p.Prime → W < p → p ≤ yNat n →
      RoughCanonicalSignedExceptionalResidualBound
        n (upperTailLength c n) K deltaStar
        (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
          (roughHeadBalancedAlpha W n (upperTailLength c n) K beta (L n))
          beta (L n))
        p
        (roughCanonicalSignedExceptionalCoreBoundConstant W c deltaStar
          deepConstant cutoffConstant variationConstant *
            secondOrderScale n / ((p : Real) * L n)) := by
  unfold RoughCanonicalSignedExceptionalCoreChamberEventually at hchamber
  have hcutTop := tangentPaperExceptionalCutoff_tendsto_atTop hdelta
  have hcutTwo : ∀ᶠ n : Nat in atTop,
      2 ≤ tangentPaperExceptionalCutoff deltaStar n :=
    hcutTop.eventually (eventually_ge_atTop 2)
  have hdeltaOne : deltaStar < 1 := hdeltaUpper.trans (by norm_num)
  filter_upwards [hchamber, eventually_ge_atTop 3,
      eventually_upperTailLength_le hc,
      eventually_upperTailLength_cast_le_two_mul_secondOrderScale hc,
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
      eventually_one_add_log_two_mul_exceptionalCutoff_le hdelta,
      eventually_tangentPaperExceptionalCutoff_le_self_div_L_sq hdeltaOne,
      hcutTwo]
      with n hnChamber hn htail htailScale hlogY hlogCut hendpoint hcut
  obtain ⟨kernelWeight, coreError, hcore⟩ := hnChamber
  intro p hp hWp hpY
  let rawWeight :=
    roughHeadCompatibleRawWeight W n (upperTailLength c n) K
      (roughHeadBalancedAlpha W n (upperTailLength c n) K beta (L n))
      beta (L n)
  let X := tangentPaperExceptionalCutoff deltaStar n
  let B := X / 2
  have hnTwo : 1 < n := by omega
  have hnReal : (0 : Real) < (n : Real) := by positivity
  have hpReal : (0 : Real) < (p : Real) := by exact_mod_cast hp.pos
  have hL : 0 < L n := L_pos hnTwo
  have hlogYPos : 0 < Real.log (yNat n : Real) :=
    (mul_pos (by norm_num : (0 : Real) < 1 / 5) hL).trans_le hlogY
  have hB : 1 ≤ B := by omega
  have hBReal : (0 : Real) < (B : Real) := by exact_mod_cast hB
  have hXReal : (0 : Real) < (X : Real) := by positivity
  have hheadNonneg : 0 ≤
      (roughHeadModulus W : Real) / roughHeadDensity W := by
    exact div_nonneg (Nat.cast_nonneg _) (roughHeadDensity_pos W).le
  have hfinite :=
    abs_roughCanonicalSignedExceptionalResidual_le_coreFirstFinite
      hdelta.le (by omega) htail hp hWp hpY hcut hdeep hcutoff hvariation hcore
  have hinvLog : 1 / Real.log (yNat n : Real) ≤ 5 / L n := by
    apply (div_le_div_iff₀ hlogYPos hL).2
    nlinarith [hlogY]
  have htailScale' :
      (upperTailLength c n : Real) ≤ 2 * c * (n : Real) / L n := by
    calc
      (upperTailLength c n : Real) ≤
          2 * c * secondOrderScale n := htailScale
      _ = 2 * c * (n : Real) / L n := by
        unfold secondOrderScale L
        ring
  have hleadingScale :
      (upperTailLength c n : Real) / Real.log (yNat n : Real) ≤
        10 * c * (n : Real) / L n ^ 2 := by
    calc
      (upperTailLength c n : Real) / Real.log (yNat n : Real) =
          (upperTailLength c n : Real) *
            (1 / Real.log (yNat n : Real)) := by ring
      _ ≤ (2 * c * (n : Real) / L n) * (5 / L n) :=
        mul_le_mul htailScale' hinvLog (by positivity) (by positivity)
      _ = 10 * c * (n : Real) / L n ^ 2 := by ring
  have hBLe : B ≤ 2 * X := by omega
  have hlogB : Real.log (B : Real) ≤ Real.log (2 * X : Nat) :=
    Real.log_le_log hBReal (by exact_mod_cast hBLe)
  have hdeepLog :
      1 + Real.log (B : Real) ≤ 2 * deltaStar * L n := by
    have hlogCut' :
        1 + Real.log ((2 * X : Nat) : Real) ≤ 2 * deltaStar * L n := by
      simpa only [X] using hlogCut
    linarith
  let baseScale := (n : Real) / ((p : Real) * L n ^ 2)
  have hbase : 0 ≤ baseScale := by
    dsimp [baseScale]
    positivity
  have hleadTerm :
      ((upperTailLength c n : Real) / Real.log (yNat n : Real)) *
          (2 * ((roughHeadModulus W : Real) / roughHeadDensity W) *
            variationConstant / (p : Real)) ≤
        (20 * c *
          ((roughHeadModulus W : Real) / roughHeadDensity W) *
            variationConstant) * baseScale := by
    have hfactorNonneg : 0 ≤
        2 * ((roughHeadModulus W : Real) / roughHeadDensity W) *
          variationConstant / (p : Real) := by positivity
    calc
      _ ≤ (10 * c * (n : Real) / L n ^ 2) *
          (2 * ((roughHeadModulus W : Real) / roughHeadDensity W) *
            variationConstant / (p : Real)) :=
        mul_le_mul_of_nonneg_right hleadingScale hfactorNonneg
      _ = _ := by
        dsimp [baseScale]
        ring
  have hdeepMain :
      (deepConstant * (n : Real) / L n ^ 3) *
          (2 * (1 + Real.log (B : Real)) / (p : Real)) ≤
        (4 * deltaStar * deepConstant) * baseScale := by
    have hfirstNonneg : 0 ≤ deepConstant * (n : Real) / L n ^ 3 := by
      positivity
    have hsecond :
        2 * (1 + Real.log (B : Real)) / (p : Real) ≤
          4 * deltaStar * L n / (p : Real) := by
      have hnumerator :
          2 * (1 + Real.log (B : Real)) ≤
            4 * deltaStar * L n := by
        nlinarith [hdeepLog]
      exact div_le_div_of_nonneg_right hnumerator hpReal.le
    calc
      _ ≤ (deepConstant * (n : Real) / L n ^ 3) *
          (4 * deltaStar * L n / (p : Real)) :=
        mul_le_mul_of_nonneg_left hsecond hfirstNonneg
      _ = _ := by
        dsimp [baseScale]
        field_simp [hL.ne', hpReal.ne']
  have hdeepEndpoint :
      deepConstant * (2 * (B : Real) / (p : Real)) ≤
        (2 * deepConstant) * baseScale := by
    have hBX : (B : Real) ≤ (X : Real) := by exact_mod_cast (Nat.div_le_self X 2)
    have hBscale : (B : Real) ≤ (n : Real) / L n ^ 2 :=
      hBX.trans hendpoint
    have hscaled :
        2 * (B : Real) / (p : Real) ≤
          2 * ((n : Real) / L n ^ 2) / (p : Real) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hBscale (by norm_num)) hpReal.le
    calc
      deepConstant * (2 * (B : Real) / (p : Real)) ≤
          deepConstant * (2 * ((n : Real) / L n ^ 2) / (p : Real)) := by
        exact mul_le_mul_of_nonneg_left hscaled hdeep
      _ = _ := by
        dsimp [baseScale]
        ring
  have hbandMain :
      (cutoffConstant * (n : Real) / L n ^ 2) *
          (8 / (p : Real)) =
        (8 * cutoffConstant) * baseScale := by
    dsimp [baseScale]
    ring
  have hbandEndpoint :
      cutoffConstant * (4 * (X : Real) / (p : Real)) ≤
        (4 * cutoffConstant) * baseScale := by
    have hscaled :
        4 * (X : Real) / (p : Real) ≤
          4 * ((n : Real) / L n ^ 2) / (p : Real) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hendpoint (by norm_num)) hpReal.le
    calc
      cutoffConstant * (4 * (X : Real) / (p : Real)) ≤
          cutoffConstant *
            (4 * ((n : Real) / L n ^ 2) / (p : Real)) := by
        exact mul_le_mul_of_nonneg_left hscaled hcutoff
      _ = _ := by
        dsimp [baseScale]
        ring
  have htotal :
      ((upperTailLength c n : Real) / Real.log (yNat n : Real)) *
          (2 * ((roughHeadModulus W : Real) / roughHeadDensity W) *
            variationConstant / (p : Real)) +
        (deepConstant * (n : Real) / L n ^ 3) *
          (2 * (1 + Real.log (B : Real)) / (p : Real)) +
        deepConstant * (2 * (B : Real) / (p : Real)) +
        (cutoffConstant * (n : Real) / L n ^ 2) *
          (8 / (p : Real)) +
        cutoffConstant * (4 * (X : Real) / (p : Real)) ≤
      roughCanonicalSignedExceptionalCoreBoundConstant W c deltaStar
          deepConstant cutoffConstant variationConstant * baseScale := by
    calc
      _ ≤ (20 * c *
              ((roughHeadModulus W : Real) / roughHeadDensity W) *
                variationConstant) * baseScale +
            (4 * deltaStar * deepConstant) * baseScale +
            (2 * deepConstant) * baseScale +
            (8 * cutoffConstant) * baseScale +
            (4 * cutoffConstant) * baseScale := by
        exact add_le_add
          (add_le_add
            (add_le_add
              (add_le_add hleadTerm hdeepMain)
              hdeepEndpoint)
            (le_of_eq hbandMain))
          hbandEndpoint
      _ = roughCanonicalSignedExceptionalCoreBoundConstant W c deltaStar
            deepConstant cutoffConstant variationConstant * baseScale := by
        unfold roughCanonicalSignedExceptionalCoreBoundConstant
        ring
  unfold RoughCanonicalSignedExceptionalResidualBound
  apply hfinite.trans
  calc
    _ ≤ roughCanonicalSignedExceptionalCoreBoundConstant W c deltaStar
          deepConstant cutoffConstant variationConstant * baseScale := by
      simpa only [B, X] using htotal
    _ = roughCanonicalSignedExceptionalCoreBoundConstant W c deltaStar
          deepConstant cutoffConstant variationConstant *
            secondOrderScale n / ((p : Real) * L n) := by
      dsimp [baseScale, secondOrderScale, L]
      field_simp [hL.ne', hpReal.ne']

end BankPaperRealization

end

end Erdos390.WholePaper
