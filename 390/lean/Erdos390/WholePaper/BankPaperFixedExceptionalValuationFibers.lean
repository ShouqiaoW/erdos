import Erdos390.WholePaper.BankPaperFixedExceptionalBacking
import Erdos390.WholePaper.BankAnchorCollisionFree
import Erdos390.WholePaper.TangentExceptionalCanonicalBounds

/-!
# Finite valuation fibres for the literal fixed exceptional factors

This file gives the first finite low-prime bridge for the paper's literal
fixed exceptional set.  The exceptional upper factors are partitioned by
their complete smooth part at the canonical cutoff `yNat n`.  At a prime
`p ≤ yNat n`, the factorization charge is therefore the corresponding
smooth-part valuation times the size of each fibre.

Each actual fibre injects, by its complete rough label, into the physical
reduced-residue interval obtained by dividing `(2n,2n+h]` by that smooth
part.  The last theorem substitutes the already proved canonical finite
Selberg estimate for these candidate intervals.  No smooth-number census,
valuation-sum estimate, or asymptotic exceptional-charge bound is asserted
here.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Canonical smooth fibres and their rough candidates -/

/-- The complete smooth parts which actually occur among the literal
exceptional upper factors. -/
def paperExceptionalSmoothParts
    (n h : ℕ) (deltaStar : ℝ) : Finset ℕ :=
  (paperExceptionalUpperFactors n h deltaStar).image
    (completeSmoothPart (yNat n))

/-- The literal exceptional upper factors having a prescribed complete
smooth part at the canonical rough cutoff. -/
def paperExceptionalSmoothFiber
    (n h : ℕ) (deltaStar : ℝ) (b : ℕ) : Finset ℕ :=
  (paperExceptionalUpperFactors n h deltaStar).filter
    (fun a ↦ completeSmoothPart (yNat n) a = b)

/-- Possible complete rough labels in the physical upper interval once the
smooth part `b` is fixed.  Coprimality to the rough-head modulus is retained
literally, while the exceptional lower cutoff on the rough label is
deliberately discarded, exactly as in the paper's Selberg overcount. -/
def paperExceptionalRoughCandidates
    (n h y b : ℕ) : Finset ℕ :=
  reducedResidueIoc (roughHeadModulus y)
    ((2 * n) / b) ((2 * n + h) / b)

@[simp]
theorem mem_paperExceptionalSmoothParts
    {n h b : ℕ} {deltaStar : ℝ} :
    b ∈ paperExceptionalSmoothParts n h deltaStar ↔
      ∃ a ∈ paperExceptionalUpperFactors n h deltaStar,
        completeSmoothPart (yNat n) a = b := by
  simp only [paperExceptionalSmoothParts, Finset.mem_image]

@[simp]
theorem mem_paperExceptionalSmoothFiber
    {n h a b : ℕ} {deltaStar : ℝ} :
    a ∈ paperExceptionalSmoothFiber n h deltaStar b ↔
      a ∈ paperExceptionalUpperFactors n h deltaStar ∧
        completeSmoothPart (yNat n) a = b := by
  simp only [paperExceptionalSmoothFiber, Finset.mem_filter]

@[simp]
theorem mem_paperExceptionalRoughCandidates
    {n h y b r : ℕ} :
    r ∈ paperExceptionalRoughCandidates n h y b ↔
      (2 * n) / b < r ∧ r ≤ (2 * n + h) / b ∧
        Nat.Coprime r (roughHeadModulus y) := by
  simp only [paperExceptionalRoughCandidates, reducedResidueIoc,
    Finset.mem_filter, Finset.mem_Ioc, and_assoc]

/-- Every literal exceptional upper factor is positive. -/
theorem paperExceptionalUpperFactors_pos
    {n h a : ℕ} {deltaStar : ℝ}
    (ha : a ∈ paperExceptionalUpperFactors n h deltaStar) :
    0 < a := by
  have haInterval : a ∈ Finset.Ioc (2 * n) (2 * n + h) := by
    simpa only [roughUpperBlock] using
      (paperExceptionalUpperFactors_subset_upperBlock n h deltaStar ha)
  exact lt_of_le_of_lt (Nat.zero_le (2 * n))
    (Finset.mem_Ioc.mp haInterval).1

/-! ## Exact low-prime valuation partition -/

/-- At a low prime, the full literal exceptional product has exactly the
smooth-part weighted fibre decomposition. -/
theorem paperExceptionalUpperFactors_prod_factorization_eq_smoothFiberSum
    {n h p : ℕ} {deltaStar : ℝ} (hp : p ≤ yNat n) :
    ((paperExceptionalUpperFactors n h deltaStar).prod id).factorization p =
      ∑ b ∈ paperExceptionalSmoothParts n h deltaStar,
        b.factorization p *
          (paperExceptionalSmoothFiber n h deltaStar b).card := by
  have hfactorization :
      ((paperExceptionalUpperFactors n h deltaStar).prod id).factorization p =
        ∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
          a.factorization p :=
    Nat.factorization_prod_apply
      (fun a ha ↦ (paperExceptionalUpperFactors_pos ha).ne')
  rw [hfactorization]
  calc
    (∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
        a.factorization p) =
        ∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
          (completeSmoothPart (yNat n) a).factorization p := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [completeSmoothPart_factorization_apply, if_pos hp]
    _ = ∑ b ∈ paperExceptionalSmoothParts n h deltaStar,
          ∑ a ∈ paperExceptionalSmoothFiber n h deltaStar b,
            (completeSmoothPart (yNat n) a).factorization p := by
      symm
      simpa only [paperExceptionalSmoothParts,
        paperExceptionalSmoothFiber] using
        (Finset.sum_fiberwise_of_maps_to
          (s := paperExceptionalUpperFactors n h deltaStar)
          (t := (paperExceptionalUpperFactors n h deltaStar).image
            (completeSmoothPart (yNat n)))
          (g := completeSmoothPart (yNat n))
          (fun a ha ↦ Finset.mem_image_of_mem
            (completeSmoothPart (yNat n)) ha)
          (fun a ↦ (completeSmoothPart (yNat n) a).factorization p))
    _ = ∑ b ∈ paperExceptionalSmoothParts n h deltaStar,
          b.factorization p *
            (paperExceptionalSmoothFiber n h deltaStar b).card := by
      apply Finset.sum_congr rfl
      intro b hb
      calc
        (∑ a ∈ paperExceptionalSmoothFiber n h deltaStar b,
            (completeSmoothPart (yNat n) a).factorization p) =
            (paperExceptionalSmoothFiber n h deltaStar b).card *
              b.factorization p := by
          apply Finset.sum_const_nat
          intro a ha
          rw [(mem_paperExceptionalSmoothFiber.mp ha).2]
        _ = b.factorization p *
              (paperExceptionalSmoothFiber n h deltaStar b).card :=
          Nat.mul_comm _ _

/-! ## Injection of each actual fibre into a reduced-residue interval -/

/-- Fixing the smooth part makes the complete rough label injective on one
literal exceptional fibre. -/
theorem completeRoughLabel_injOn_paperExceptionalSmoothFiber
    {n h b : ℕ} {deltaStar : ℝ} :
    Set.InjOn (completeRoughLabel (yNat n))
      (paperExceptionalSmoothFiber n h deltaStar b : Set ℕ) := by
  intro a₁ ha₁ a₂ ha₂ hrough
  have hsmooth₁ := (mem_paperExceptionalSmoothFiber.mp ha₁).2
  have hsmooth₂ := (mem_paperExceptionalSmoothFiber.mp ha₂).2
  calc
    a₁ = completeRoughLabel (yNat n) a₁ *
        completeSmoothPart (yNat n) a₁ :=
      (completeRoughLabel_mul_completeSmoothPart (yNat n) a₁).symm
    _ = completeRoughLabel (yNat n) a₂ *
        completeSmoothPart (yNat n) a₂ := by
      rw [hrough, hsmooth₁, hsmooth₂]
    _ = a₂ := completeRoughLabel_mul_completeSmoothPart (yNat n) a₂

/-- A complete rough label from an actual smooth fibre lies in its claimed
physical reduced-residue interval. -/
theorem completeRoughLabel_mem_paperExceptionalRoughCandidates
    {n h a b : ℕ} {deltaStar : ℝ}
    (ha : a ∈ paperExceptionalSmoothFiber n h deltaStar b) :
    completeRoughLabel (yNat n) a ∈
      paperExceptionalRoughCandidates n h (yNat n) b := by
  have haData := mem_paperExceptionalSmoothFiber.mp ha
  have haBounds : 2 * n < a ∧ a ≤ 2 * n + h := by
    simpa only [roughUpperBlock, Finset.mem_Ioc] using
      (mem_paperExceptionalUpperFactors.mp haData.1).1
  have haPos : 0 < a := paperExceptionalUpperFactors_pos haData.1
  have hbPos : 0 < b := by
    have hsmoothPos := completeSmoothPart_pos
      (y := yNat n) (a := a) haPos
    simpa only [haData.2] using hsmoothPos
  have hdecomp : completeRoughLabel (yNat n) a * b = a := by
    simpa only [haData.2] using
      completeRoughLabel_mul_completeSmoothPart (yNat n) a
  rw [mem_paperExceptionalRoughCandidates]
  refine ⟨?_, ?_, completeRoughLabel_coprime_roughHeadModulus (yNat n) a⟩
  · apply (Nat.div_lt_iff_lt_mul hbPos).mpr
    simpa only [hdecomp] using haBounds.1
  · apply (Nat.le_div_iff_mul_le hbPos).mpr
    simpa only [hdecomp] using haBounds.2

/-- Fibrewise canonical reduction: the actual exceptional fibre injects
into the reduced-residue rough-label interval. -/
theorem paperExceptionalSmoothFiber_card_le_roughCandidates
    {n h b : ℕ} {deltaStar : ℝ} :
    (paperExceptionalSmoothFiber n h deltaStar b).card ≤
      (paperExceptionalRoughCandidates n h (yNat n) b).card := by
  calc
    (paperExceptionalSmoothFiber n h deltaStar b).card =
        ((paperExceptionalSmoothFiber n h deltaStar b).image
          (completeRoughLabel (yNat n))).card :=
      (Finset.card_image_of_injOn
        completeRoughLabel_injOn_paperExceptionalSmoothFiber).symm
    _ ≤ (paperExceptionalRoughCandidates n h (yNat n) b).card := by
      apply Finset.card_le_card
      intro r hr
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
      exact completeRoughLabel_mem_paperExceptionalRoughCandidates ha

/-! ## The fixed exceptional product -/

namespace BankPaperRealization

/-- The fixed set difference has no more low-prime charge than the exact
smooth-fibre decomposition of the full literal exceptional set. -/
theorem paperFixedExceptionalFactors_prod_factorization_le_smoothFiberSum
    {n h p : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    {deltaStar : ℝ} (hp : p ≤ yNat n) :
    ((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p ≤
      ∑ b ∈ paperExceptionalSmoothParts n h deltaStar,
        b.factorization p *
          (paperExceptionalSmoothFiber n h deltaStar b).card := by
  have hsubset : R.paperFixedExceptionalFactors deltaStar ⊆
      paperExceptionalUpperFactors n h deltaStar := by
    intro a ha
    rw [paperFixedExceptionalFactors, Finset.mem_sdiff] at ha
    exact ha.1
  calc
    ((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p =
        ∑ a ∈ R.paperFixedExceptionalFactors deltaStar,
          a.factorization p := by
      exact Nat.factorization_prod_apply fun a ha ↦
        (paperExceptionalUpperFactors_pos (hsubset ha)).ne'
    _ ≤ ∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
          a.factorization p := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _a _haUpper _haFixed ↦ Nat.zero_le _)
    _ = ((paperExceptionalUpperFactors n h deltaStar).prod id).factorization p := by
      symm
      exact Nat.factorization_prod_apply fun a ha ↦
        (paperExceptionalUpperFactors_pos ha).ne'
    _ = ∑ b ∈ paperExceptionalSmoothParts n h deltaStar,
          b.factorization p *
            (paperExceptionalSmoothFiber n h deltaStar b).card :=
      paperExceptionalUpperFactors_prod_factorization_eq_smoothFiberSum hp

/-- The first honest finite upper bound for the canonical fixed exceptional
charge: each smooth-part valuation is weighted by the cardinality of its
canonical reduced-residue rough-label interval. -/
theorem paperFixedExceptionalFactors_prod_factorization_le_roughCandidateSum
    {n h p : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    {deltaStar : ℝ} (hp : p ≤ yNat n) :
    ((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p ≤
      ∑ b ∈ paperExceptionalSmoothParts n h deltaStar,
        b.factorization p *
          (paperExceptionalRoughCandidates n h (yNat n) b).card := by
  calc
    ((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p ≤
        ∑ b ∈ paperExceptionalSmoothParts n h deltaStar,
          b.factorization p *
            (paperExceptionalSmoothFiber n h deltaStar b).card :=
      R.paperFixedExceptionalFactors_prod_factorization_le_smoothFiberSum hp
    _ ≤ ∑ b ∈ paperExceptionalSmoothParts n h deltaStar,
          b.factorization p *
            (paperExceptionalRoughCandidates n h (yNat n) b).card := by
      apply Finset.sum_le_sum
      intro b hb
      exact Nat.mul_le_mul_left _
        paperExceptionalSmoothFiber_card_le_roughCandidates

end BankPaperRealization

/-! ## Canonical Selberg substitution on each candidate interval -/

/-- The existing canonical lambda-square sieve applies verbatim to every
rough-candidate fibre, uniformly in its physical parameters. -/
theorem eventually_paperExceptionalRoughCandidates_card_le_canonicalLambdaSquare :
    ∀ᶠ y : ℕ in atTop, ∀ n h b : ℕ,
      ((paperExceptionalRoughCandidates n h y b).card : ℝ) ≤
        ((((2 * n + h) / b - (2 * n) / b : ℕ) : ℝ) *
            (tangentSelbergCanonicalMainConstant /
              Real.log (y : ℝ)) +
          tangentSelbergCanonicalLambdaConstant ^ 2 * (y : ℝ) ^ 4 /
            Real.log (y : ℝ) ^ 2) := by
  filter_upwards
    [eventually_reducedResidueIoc_card_le_canonicalLambdaSquare_roughHead]
      with y hy
  intro n h b
  simpa only [paperExceptionalRoughCandidates] using
    hy ((2 * n) / b) ((2 * n + h) / b)

/-- At the paper's canonical cutoff, every actual smooth fibre inherits the
canonical lambda-square interval estimate. -/
theorem eventually_paperExceptionalSmoothFiber_card_le_canonicalLambdaSquare :
    ∀ᶠ n : ℕ in atTop, ∀ h b : ℕ, ∀ deltaStar : ℝ,
      ((paperExceptionalSmoothFiber n h deltaStar b).card : ℝ) ≤
        ((((2 * n + h) / b - (2 * n) / b : ℕ) : ℝ) *
            (tangentSelbergCanonicalMainConstant /
              Real.log (yNat n : ℝ)) +
          tangentSelbergCanonicalLambdaConstant ^ 2 *
              (yNat n : ℝ) ^ 4 /
            Real.log (yNat n : ℝ) ^ 2) := by
  filter_upwards
    [bankAnchor_yNat_tendsto_atTop.eventually
      eventually_paperExceptionalRoughCandidates_card_le_canonicalLambdaSquare]
      with n hn
  intro h b deltaStar
  have hcardCast :
      ((paperExceptionalSmoothFiber n h deltaStar b).card : ℝ) ≤
        ((paperExceptionalRoughCandidates n h (yNat n) b).card : ℝ) := by
    exact_mod_cast
      (paperExceptionalSmoothFiber_card_le_roughCandidates
        (n := n) (h := h) (b := b) (deltaStar := deltaStar))
  exact hcardCast.trans (hn n h b)

end

end Erdos390.WholePaper
