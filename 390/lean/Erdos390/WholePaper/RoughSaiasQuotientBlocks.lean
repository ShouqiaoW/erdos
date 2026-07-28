import Erdos390.WholePaper.RoughSaiasBaseChange

/-!
# Hyperbola blocks for the Saias base variation

The transformed sawtooth kernel has a fixed natural quotient on each fibre
of `m ↦ X / m`.  This file records the elementary, but useful, fact that
those fibres are honest intervals and gives a fibrewise decomposition of
finite sums.  No estimate is used here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-- The bases in `(y,Z]` having the fixed hyperbola quotient `q`. -/
def roughSaiasQuotientBlock (X q y Z : ℕ) : Finset ℕ :=
  (Finset.Ioc y Z).filter (fun m => X / m = q)

/-- The finite set of quotient values met by the bases in `(y,Z]`. -/
def roughSaiasQuotientValues (X y Z : ℕ) : Finset ℕ :=
  (Finset.Ioc y Z).image (fun m => X / m)

/-- A natural quotient is `q` exactly between its two multiplication
inequalities.  The positive-denominator hypothesis is the only boundary
condition needed. -/
theorem natDiv_eq_iff_mul_bounds
    {X m q : ℕ} (hm : 0 < m) :
    X / m = q ↔ q * m ≤ X ∧ X < (q + 1) * m := by
  constructor
  · intro h
    constructor
    · apply (Nat.le_div_iff_mul_le hm).mp
      rw [h]
    · apply (Nat.div_lt_iff_lt_mul hm).mp
      rw [h]
      omega
  · rintro ⟨hlo, hhi⟩
    apply Nat.le_antisymm
    · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hm).mpr hhi)
    · exact (Nat.le_div_iff_mul_le hm).mpr hlo

/-- Positive quotient fibres have the usual hyperbola interval
description `(X/(q+1), X/q]`. -/
theorem natDiv_eq_iff_mem_hyperbolaIoc
    {X m q : ℕ} (hm : 0 < m) (hq : 0 < q) :
    X / m = q ↔ X / (q + 1) < m ∧ m ≤ X / q := by
  rw [natDiv_eq_iff_mul_bounds hm]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (Nat.div_lt_iff_lt_mul (by omega : 0 < q + 1)).mpr
      simpa [Nat.mul_comm] using hhi
    · apply (Nat.le_div_iff_mul_le hq).mpr
      simpa [Nat.mul_comm] using hlo
  · rintro ⟨hlo, hhi⟩
    constructor
    · have h := (Nat.le_div_iff_mul_le hq).mp hhi
      simpa [Nat.mul_comm] using h
    · have h :=
        (Nat.div_lt_iff_lt_mul (by omega : 0 < q + 1)).mp hlo
      simpa [Nat.mul_comm] using h

@[simp]
theorem mem_roughSaiasQuotientBlock
    {X q y Z m : ℕ} :
    m ∈ roughSaiasQuotientBlock X q y Z ↔
      y < m ∧ m ≤ Z ∧ X / m = q := by
  simp only [roughSaiasQuotientBlock, Finset.mem_filter,
    Finset.mem_Ioc]
  tauto

/-- The fixed-quotient fibre is order convex.  This is the precise reason
that consecutive-base estimates may be summed one block at a time. -/
theorem natDiv_eq_of_between
    {X q a b m : ℕ} (ha : X / a = q) (hb : X / b = q)
    (haPos : 0 < a) (ham : a ≤ m) (hmb : m ≤ b) :
    X / m = q := by
  have hm : 0 < m := haPos.trans_le ham
  have hbPos : 0 < b := hm.trans_le hmb
  have haBounds := (natDiv_eq_iff_mul_bounds (X := X) (q := q)
    (m := a) haPos).mp ha
  have hbBounds := (natDiv_eq_iff_mul_bounds (X := X) (q := q)
    (m := b) hbPos).mp hb
  apply (natDiv_eq_iff_mul_bounds hm).mpr
  constructor
  · exact (Nat.mul_le_mul_left q hmb).trans hbBounds.1
  · exact haBounds.2.trans_le (Nat.mul_le_mul_left (q + 1) ham)

/-- Intersecting a positive quotient fibre with `(y,Z]` merely intersects
two explicit natural intervals. -/
theorem roughSaiasQuotientBlock_eq_hyperbola_filter
    {X q y Z : ℕ} (hq : 0 < q) :
    roughSaiasQuotientBlock X q y Z =
      (Finset.Ioc y Z).filter
        (fun m => X / (q + 1) < m ∧ m ≤ X / q) := by
  ext m
  by_cases hm : 0 < m
  · simp only [roughSaiasQuotientBlock, Finset.mem_filter]
    rw [natDiv_eq_iff_mem_hyperbolaIoc hm hq]
  · have hm0 : m = 0 := by omega
    subst m
    simp [roughSaiasQuotientBlock]

/-- A positive quotient block is contained in its untruncated hyperbola
interval. -/
theorem roughSaiasQuotientBlock_subset_hyperbolaIoc
    {X q y Z : ℕ} (hq : 0 < q) :
    roughSaiasQuotientBlock X q y Z ⊆
      Finset.Ioc (X / (q + 1)) (X / q) := by
  intro m hm
  have hmData := mem_roughSaiasQuotientBlock.mp hm
  have hmPos : 0 < m := by omega
  rw [Finset.mem_Ioc,
    ← natDiv_eq_iff_mem_hyperbolaIoc hmPos hq]
  exact hmData.2.2

/-- In particular, a quotient block has at most the exact hyperbola-interval
length `X/q-X/(q+1)`. -/
theorem roughSaiasQuotientBlock_card_le
    {X q y Z : ℕ} (hq : 0 < q) :
    (roughSaiasQuotientBlock X q y Z).card ≤
      X / q - X / (q + 1) := by
  have hcard := Finset.card_le_card
    (roughSaiasQuotientBlock_subset_hyperbolaIoc
      (X := X) (y := y) (Z := Z) hq)
  simpa only [Nat.card_Ioc] using hcard

/-- Every quotient met above `y` is at most `X/(y+1)`. -/
theorem roughSaiasQuotientValues_subset_Iic
    (X y Z : ℕ) :
    roughSaiasQuotientValues X y Z ⊆
      Finset.Iic (X / (y + 1)) := by
  intro q hq
  rw [roughSaiasQuotientValues, Finset.mem_image] at hq
  obtain ⟨m, hm, rfl⟩ := hq
  rw [Finset.mem_Iic]
  apply (Nat.le_div_iff_mul_le (by omega : 0 < y + 1)).mpr
  have hym : y + 1 ≤ m := by
    rw [Finset.mem_Ioc] at hm
    omega
  exact (Nat.mul_le_mul_left (X / m) hym).trans
    (Nat.div_mul_le_self X m)

/-- Hence the number of nonempty quotient fibres is at most
`X/(y+1)+1`. -/
theorem roughSaiasQuotientValues_card_le
    (X y Z : ℕ) :
    (roughSaiasQuotientValues X y Z).card ≤ X / (y + 1) + 1 := by
  have hcard := Finset.card_le_card
    (roughSaiasQuotientValues_subset_Iic X y Z)
  simpa only [Nat.card_Iic] using hcard

/-! ## The dual hyperbola partition -/

/-- The quotient interval dual to the base cell `[m,m+1]`.  Its members
are exactly the positive denominators `q` for which `X / q = m`. -/
def roughSaiasDualQuotientInterval (X m : ℕ) : Finset ℕ :=
  Finset.Ioc (X / (m + 1)) (X / m)

@[simp]
theorem mem_roughSaiasDualQuotientInterval
    {X m q : ℕ} (hm : 0 < m) (hq : 0 < q) :
    q ∈ roughSaiasDualQuotientInterval X m ↔ X / q = m := by
  rw [roughSaiasDualQuotientInterval, Finset.mem_Ioc,
    ← natDiv_eq_iff_mem_hyperbolaIoc hq hm]

/-- The dual interval has exactly the natural quotient drop as its
cardinality. -/
theorem card_roughSaiasDualQuotientInterval (X m : ℕ) :
    (roughSaiasDualQuotientInterval X m).card =
      X / m - X / (m + 1) := by
  simp only [roughSaiasDualQuotientInterval, Nat.card_Ioc]

/-- Below the square-root transition the quotient drops strictly on every
cell. -/
theorem natDiv_succ_lt_of_le_sqrt
    {X m : ℕ} (hm : 0 < m) (hmsqrt : m ≤ Nat.sqrt X) :
    X / (m + 1) < X / m := by
  have hsq : m ^ 2 ≤ X := Nat.le_sqrt'.mp hmsqrt
  have hmq : m ≤ X / m := by
    apply (Nat.le_div_iff_mul_le hm).mpr
    simpa only [pow_two] using hsq
  have hbounds :=
    (natDiv_eq_iff_mul_bounds (X := X) (m := m) (q := X / m) hm).mp rfl
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < m + 1)).mpr
  calc
    X < (X / m + 1) * m := hbounds.2
    _ ≤ (X / m) * (m + 1) := by nlinarith

/-- Consequently, the dual interval of a cell below `sqrt X` is nonempty. -/
theorem roughSaiasDualQuotientInterval_nonempty_of_le_sqrt
    {X m : ℕ} (hm : 0 < m) (hmsqrt : m ≤ Nat.sqrt X) :
    (roughSaiasDualQuotientInterval X m).Nonempty := by
  use X / m
  rw [roughSaiasDualQuotientInterval, Finset.mem_Ioc]
  exact ⟨natDiv_succ_lt_of_le_sqrt hm hmsqrt, le_rfl⟩

/-- The hyperbola involution sends a cell on or below the square-root
diagonal to denominators on or above that diagonal. -/
theorem le_of_mem_roughSaiasDualQuotientInterval_of_le_sqrt
    {X m q : ℕ} (hm : 0 < m) (hmsqrt : m ≤ Nat.sqrt X)
    (hq : q ∈ roughSaiasDualQuotientInterval X m) :
    m ≤ q := by
  have hsq : m ^ 2 ≤ X := Nat.le_sqrt'.mp hmsqrt
  have hqData := Finset.mem_Ioc.mp hq
  have hpredProduct : (m - 1) * (m + 1) ≤ m ^ 2 := by
    cases m with
    | zero => omega
    | succ k =>
        simp only [Nat.add_sub_cancel, pow_two]
        nlinarith
  have hlower : m - 1 ≤ X / (m + 1) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < m + 1)).mpr
    exact hpredProduct.trans hsq
  omega

/-- Membership form of the dual partition.  The reciprocal image of
`(X/M,X/y]` is exactly the family of base cells `[y,M)`. -/
theorem mem_div_Ioc_iff_exists_mem_roughSaiasDualQuotientInterval
    {X y M q : ℕ} (hy : 0 < y) (hyM : y ≤ M) :
    q ∈ Finset.Ioc (X / M) (X / y) ↔
      ∃ m ∈ Finset.Ico y M,
        q ∈ roughSaiasDualQuotientInterval X m := by
  have hM : 0 < M := hy.trans_le hyM
  constructor
  · intro hq
    have hqData := Finset.mem_Ioc.mp hq
    have hqPos : 0 < q := by
      have hzero : 0 ≤ X / M := Nat.zero_le _
      omega
    have hyMul : y * q ≤ X := by
      have h := (Nat.le_div_iff_mul_le hy).mp hqData.2
      simpa only [Nat.mul_comm] using h
    have hyDiv : y ≤ X / q :=
      (Nat.le_div_iff_mul_le hqPos).mpr hyMul
    have hDivM : X / q < M := by
      apply (Nat.div_lt_iff_lt_mul hqPos).mpr
      have h := (Nat.div_lt_iff_lt_mul hM).mp hqData.1
      simpa only [Nat.mul_comm] using h
    exact ⟨X / q, Finset.mem_Ico.mpr ⟨hyDiv, hDivM⟩,
      (mem_roughSaiasDualQuotientInterval
        (hy.trans_le hyDiv) hqPos).mpr rfl⟩
  · rintro ⟨m, hm, hq⟩
    have hmData := Finset.mem_Ico.mp hm
    have hmPos : 0 < m := hy.trans_le hmData.1
    have hqData := Finset.mem_Ioc.mp hq
    have hqPos : 0 < q := by
      have hzero : 0 ≤ X / (m + 1) := Nat.zero_le _
      omega
    have hdiv :=
      (mem_roughSaiasDualQuotientInterval hmPos hqPos).mp hq
    rw [Finset.mem_Ioc]
    constructor
    · apply (Nat.div_lt_iff_lt_mul hM).mpr
      have h := (Nat.div_lt_iff_lt_mul hqPos).mp (by
        rw [hdiv]
        exact hmData.2)
      simpa only [Nat.mul_comm] using h
    · apply (Nat.le_div_iff_mul_le hy).mpr
      have hyDiv : y ≤ X / q := by
        rw [hdiv]
        exact hmData.1
      have h := (Nat.le_div_iff_mul_le hqPos).mp hyDiv
      simpa only [Nat.mul_comm] using h

/-- If the base interval ends at the square-root transition, its dual
range is entirely on the upper side of the hyperbola. -/
theorem natDiv_le_self_of_mem_div_Ioc_of_le_sqrt_succ
    {X y M q : ℕ} (hy : 0 < y) (hyM : y ≤ M)
    (hM : M ≤ Nat.sqrt X + 1)
    (hq : q ∈ Finset.Ioc (X / M) (X / y)) :
    X / q ≤ q := by
  obtain ⟨m, hm, hqm⟩ :=
    (mem_div_Ioc_iff_exists_mem_roughSaiasDualQuotientInterval
      hy hyM).mp hq
  have hmData := Finset.mem_Ico.mp hm
  have hmPos : 0 < m := hy.trans_le hmData.1
  have hqPos : 0 < q := by
    have hqData := Finset.mem_Ioc.mp hqm
    have hzero : 0 ≤ X / (m + 1) := Nat.zero_le _
    omega
  have hmsqrt : m ≤ Nat.sqrt X := by omega
  have hdiag :=
    le_of_mem_roughSaiasDualQuotientInterval_of_le_sqrt
      hmPos hmsqrt hqm
  have hdiv :=
    (mem_roughSaiasDualQuotientInterval hmPos hqPos).mp hqm
  simpa only [hdiv] using hdiag

/-- The dual quotient intervals of consecutive base cells partition one
large hyperbola interval. -/
theorem sum_Ico_sum_roughSaiasDualQuotientInterval
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) (X : ℕ)
    {y M : ℕ} (hy : 0 < y) (hyM : y ≤ M) :
    (∑ m ∈ Finset.Ico y M,
        ∑ q ∈ roughSaiasDualQuotientInterval X m, f q) =
      ∑ q ∈ Finset.Ioc (X / M) (X / y), f q := by
  induction M, hyM using Nat.le_induction with
  | base => simp [roughSaiasDualQuotientInterval]
  | succ M hyM ih =>
      have hM : 0 < M := hy.trans_le hyM
      have hleft : X / (M + 1) ≤ X / M :=
        Nat.div_le_div_left (a := X) (Nat.le_succ M) hM
      have hright : X / M ≤ X / y :=
        Nat.div_le_div_left (a := X) hyM hy
      rw [Finset.sum_Ico_succ_top hyM, ih]
      simpa only [roughSaiasDualQuotientInterval, add_comm] using
        (Finset.sum_Ioc_consecutive f hleft hright)

/-- Dependent form of the dual partition.  Replacing the lower cell index
by `X/q` makes the involution literal on every summand. -/
theorem sum_Ico_sum_roughSaiasDualQuotientInterval_involution
    {A : Type*} [AddCommMonoid A] (f : ℕ → ℕ → A) (X : ℕ)
    {y M : ℕ} (hy : 0 < y) (hyM : y ≤ M) :
    (∑ m ∈ Finset.Ico y M,
        ∑ q ∈ roughSaiasDualQuotientInterval X m, f m q) =
      ∑ q ∈ Finset.Ioc (X / M) (X / y), f (X / q) q := by
  calc
    (∑ m ∈ Finset.Ico y M,
        ∑ q ∈ roughSaiasDualQuotientInterval X m, f m q) =
      ∑ m ∈ Finset.Ico y M,
        ∑ q ∈ roughSaiasDualQuotientInterval X m, f (X / q) q := by
          apply Finset.sum_congr rfl
          intro m hmI
          apply Finset.sum_congr rfl
          intro q hqI
          have hmPos : 0 < m := hy.trans_le (Finset.mem_Ico.mp hmI).1
          have hqPos : 0 < q := by
            have hqData := Finset.mem_Ioc.mp hqI
            have hzero : 0 ≤ X / (m + 1) := Nat.zero_le _
            omega
          rw [(mem_roughSaiasDualQuotientInterval hmPos hqPos).mp hqI]
    _ = ∑ q ∈ Finset.Ioc (X / M) (X / y), f (X / q) q :=
      sum_Ico_sum_roughSaiasDualQuotientInterval
        (fun q => f (X / q) q) X hy hyM

/-- Every finite base sum is the disjoint sum of its quotient fibres. -/
theorem sum_Ioc_eq_sum_roughSaiasQuotientBlocks
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) (X y Z : ℕ) :
    (∑ m ∈ Finset.Ioc y Z, f m) =
      ∑ q ∈ roughSaiasQuotientValues X y Z,
        ∑ m ∈ roughSaiasQuotientBlock X q y Z, f m := by
  symm
  unfold roughSaiasQuotientValues roughSaiasQuotientBlock
  exact Finset.sum_fiberwise_of_maps_to
    (fun m hm => Finset.mem_image_of_mem (fun n => X / n) hm) f

/-- Inside one quotient fibre the natural theta-weight difference is the
fixed-`q` base-free difference. -/
theorem roughSaiasNaturalQuotientThetaWeight_diff_eq_on_quotientBlock
    {X q y Z m : ℕ} (hm2 : 2 ≤ m)
    (hm : m ∈ roughSaiasQuotientBlock X q y Z)
    (hmsucc : m + 1 ∈ roughSaiasQuotientBlock X q y Z) :
    roughSaiasNaturalQuotientThetaWeight X (m + 1) -
        roughSaiasNaturalQuotientThetaWeight X m =
      roughSaiasBaseFreeNaturalThetaWeight q (m + 1) -
        roughSaiasBaseFreeNaturalThetaWeight q m := by
  exact roughSaiasNaturalQuotientThetaWeight_diff_eq_baseFree_on_block
    hm2 (mem_roughSaiasQuotientBlock.mp hmsucc).2.2
      (mem_roughSaiasQuotientBlock.mp hm).2.2

/-! ## Adjacent edges: stable quotient fibres and quotient jumps -/

/-- Adjacent bases in the Abel variation range on which `m ↦ X / m`
does not jump. -/
def roughSaiasStableQuotientEdges (X y Z : ℕ) : Finset ℕ :=
  (Finset.Ioc y (Z - 1)).filter
    (fun m => X / (m + 1) = X / m)

/-- The complementary adjacent edges on which the hyperbola quotient
strictly changes. -/
def roughSaiasJumpQuotientEdges (X y Z : ℕ) : Finset ℕ :=
  (Finset.Ioc y (Z - 1)).filter
    (fun m => X / (m + 1) ≠ X / m)

/-- Quotient values met by stable adjacent edges. -/
def roughSaiasStableQuotientValues (X y Z : ℕ) : Finset ℕ :=
  (roughSaiasStableQuotientEdges X y Z).image (fun m => X / m)

/-- The stable adjacent edges carrying a fixed quotient `q`. -/
def roughSaiasStableQuotientEdgeBlock
    (X q y Z : ℕ) : Finset ℕ :=
  (roughSaiasStableQuotientEdges X y Z).filter (fun m => X / m = q)

@[simp]
theorem mem_roughSaiasStableQuotientEdges
    {X y Z m : ℕ} :
    m ∈ roughSaiasStableQuotientEdges X y Z ↔
      y < m ∧ m ≤ Z - 1 ∧ X / (m + 1) = X / m := by
  simp only [roughSaiasStableQuotientEdges, Finset.mem_filter,
    Finset.mem_Ioc]
  tauto

@[simp]
theorem mem_roughSaiasJumpQuotientEdges
    {X y Z m : ℕ} :
    m ∈ roughSaiasJumpQuotientEdges X y Z ↔
      y < m ∧ m ≤ Z - 1 ∧ X / (m + 1) ≠ X / m := by
  simp only [roughSaiasJumpQuotientEdges, Finset.mem_filter,
    Finset.mem_Ioc]
  tauto

@[simp]
theorem mem_roughSaiasStableQuotientEdgeBlock
    {X q y Z m : ℕ} :
    m ∈ roughSaiasStableQuotientEdgeBlock X q y Z ↔
      y < m ∧ m ≤ Z - 1 ∧ X / m = q ∧ X / (m + 1) = q := by
  simp only [roughSaiasStableQuotientEdgeBlock,
    roughSaiasStableQuotientEdges, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨⟨hym, hmZ⟩, hstable⟩, hq⟩
    exact ⟨hym, hmZ, hq, hstable.trans hq⟩
  · rintro ⟨hym, hmZ, hq, hnext⟩
    exact ⟨⟨⟨hym, hmZ⟩, hnext.trans hq.symm⟩, hq⟩

/-- A fixed stable edge is exactly a pair of consecutive members of the
same quotient block. -/
theorem mem_roughSaiasStableQuotientEdgeBlock_iff_pair_mem
    {X q y Z m : ℕ} :
    m ∈ roughSaiasStableQuotientEdgeBlock X q y Z ↔
      m ∈ roughSaiasQuotientBlock X q y Z ∧
        m + 1 ∈ roughSaiasQuotientBlock X q y Z := by
  constructor
  · intro hm
    obtain ⟨hym, hmZ, hq, hnext⟩ :=
      mem_roughSaiasStableQuotientEdgeBlock.mp hm
    constructor
    · exact mem_roughSaiasQuotientBlock.mpr
        ⟨hym, by omega, hq⟩
    · exact mem_roughSaiasQuotientBlock.mpr
        ⟨by omega, by omega, hnext⟩
  · rintro ⟨hm, hnext⟩
    obtain ⟨hym, _hmZ, hq⟩ := mem_roughSaiasQuotientBlock.mp hm
    obtain ⟨_hyNext, hnextZ, hnextq⟩ :=
      mem_roughSaiasQuotientBlock.mp hnext
    exact mem_roughSaiasStableQuotientEdgeBlock.mpr
      ⟨hym, by omega, hq, hnextq⟩

/-- Every adjacent Abel edge is either internal to one quotient fibre or is
a quotient-jump edge. -/
theorem sum_Ioc_eq_sum_stableQuotientEdges_add_jumpEdges
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) (X y Z : ℕ) :
    (∑ m ∈ Finset.Ioc y (Z - 1), f m) =
      (∑ m ∈ roughSaiasStableQuotientEdges X y Z, f m) +
        ∑ m ∈ roughSaiasJumpQuotientEdges X y Z, f m := by
  classical
  simpa only [roughSaiasStableQuotientEdges,
    roughSaiasJumpQuotientEdges] using
      (Finset.sum_filter_add_sum_filter_not
        (Finset.Ioc y (Z - 1))
        (fun m => X / (m + 1) = X / m) f).symm

/-- There are no stable quotient edges strictly below the square-root
transition. -/
theorem roughSaiasStableQuotientEdges_eq_empty_of_le_sqrt_succ
    {X y Z : ℕ} (hZ : Z ≤ Nat.sqrt X + 1) :
    roughSaiasStableQuotientEdges X y Z = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro m hm
  obtain ⟨hym, hmZ, hstable⟩ :=
    mem_roughSaiasStableQuotientEdges.mp hm
  have hmPos : 0 < m := by omega
  have hmsqrt : m ≤ Nat.sqrt X := by omega
  exact (ne_of_lt (natDiv_succ_lt_of_le_sqrt hmPos hmsqrt)) hstable

/-- Equivalently, every edge in that lower range is a quotient-jump edge. -/
theorem roughSaiasJumpQuotientEdges_eq_Ioc_of_le_sqrt_succ
    {X y Z : ℕ} (hZ : Z ≤ Nat.sqrt X + 1) :
    roughSaiasJumpQuotientEdges X y Z = Finset.Ioc y (Z - 1) := by
  unfold roughSaiasJumpQuotientEdges
  apply Finset.filter_eq_self.mpr
  intro m hm
  have hmData := Finset.mem_Ioc.mp hm
  have hmPos : 0 < m := by omega
  have hmsqrt : m ≤ Nat.sqrt X := by omega
  exact ne_of_lt (natDiv_succ_lt_of_le_sqrt hmPos hmsqrt)

/-- Stable adjacent edges decompose exactly into their fixed-quotient
fibres. -/
theorem sum_roughSaiasStableQuotientEdges_eq_sum_edgeBlocks
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) (X y Z : ℕ) :
    (∑ m ∈ roughSaiasStableQuotientEdges X y Z, f m) =
      ∑ q ∈ roughSaiasStableQuotientValues X y Z,
        ∑ m ∈ roughSaiasStableQuotientEdgeBlock X q y Z, f m := by
  classical
  symm
  unfold roughSaiasStableQuotientValues
    roughSaiasStableQuotientEdgeBlock
  exact Finset.sum_fiberwise_of_maps_to
    (fun m hm => Finset.mem_image_of_mem (fun n => X / n) hm) f

/-- On every stable edge fibre, the natural theta-weight variation is the
fixed-quotient base-free variation.  The auxiliary coefficient is retained,
so this applies directly to the finite Abel error term. -/
theorem sum_stableNaturalThetaWeight_diff_mul_eq_baseFree_edgeBlocks
    (a : ℕ → ℝ) {X y Z : ℕ} (hy2 : 2 ≤ y) :
    (∑ m ∈ roughSaiasStableQuotientEdges X y Z,
        (roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m) * a m) =
      ∑ q ∈ roughSaiasStableQuotientValues X y Z,
        ∑ m ∈ roughSaiasStableQuotientEdgeBlock X q y Z,
          (roughSaiasBaseFreeNaturalThetaWeight q (m + 1) -
            roughSaiasBaseFreeNaturalThetaWeight q m) * a m := by
  rw [sum_roughSaiasStableQuotientEdges_eq_sum_edgeBlocks]
  apply Finset.sum_congr rfl
  intro q _hq
  apply Finset.sum_congr rfl
  intro m hm
  have hpair :=
    mem_roughSaiasStableQuotientEdgeBlock_iff_pair_mem.mp hm
  have hmData := mem_roughSaiasQuotientBlock.mp hpair.1
  rw [roughSaiasNaturalQuotientThetaWeight_diff_eq_on_quotientBlock
    (hy2.trans hmData.1.le) hpair.1 hpair.2]

/-- Exact quotient-fibre/jump decomposition of the weighted discrete
variation occurring in finite Abel summation. -/
theorem sum_Ioc_naturalThetaWeight_diff_mul_eq_edgeBlocks_add_jumps
    (a : ℕ → ℝ) {X y Z : ℕ} (hy2 : 2 ≤ y) :
    (∑ m ∈ Finset.Ioc y (Z - 1),
        (roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m) * a m) =
      (∑ q ∈ roughSaiasStableQuotientValues X y Z,
        ∑ m ∈ roughSaiasStableQuotientEdgeBlock X q y Z,
          (roughSaiasBaseFreeNaturalThetaWeight q (m + 1) -
            roughSaiasBaseFreeNaturalThetaWeight q m) * a m) +
        ∑ m ∈ roughSaiasJumpQuotientEdges X y Z,
          (roughSaiasNaturalQuotientThetaWeight X (m + 1) -
            roughSaiasNaturalQuotientThetaWeight X m) * a m := by
  rw [sum_Ioc_eq_sum_stableQuotientEdges_add_jumpEdges,
    sum_stableNaturalThetaWeight_diff_mul_eq_baseFree_edgeBlocks a hy2]

/-- Without an auxiliary coefficient, all quotient-jump increments pair
exactly with the endpoints and the internal fixed-fibre increments.  This is
the algebraic boundary cancellation that is lost by taking the absolute
value of each jump separately. -/
theorem sum_jumpQuotientEdges_succ_sub_eq_endpoints_sub_stable
    (w : ℕ → ℝ) {X y Z : ℕ} (hyZ : y < Z) :
    (∑ m ∈ roughSaiasJumpQuotientEdges X y Z,
        (w (m + 1) - w m)) =
      w Z - w (y + 1) -
        ∑ m ∈ roughSaiasStableQuotientEdges X y Z,
          (w (m + 1) - w m) := by
  have hsplit := sum_Ioc_eq_sum_stableQuotientEdges_add_jumpEdges
    (fun m => w (m + 1) - w m) X y Z
  have htel :
      (∑ m ∈ Finset.Ioc y (Z - 1), (w (m + 1) - w m)) =
        w Z - w (y + 1) := by
    simpa only [← Finset.Ico_add_one_add_one_eq_Ioc,
      Nat.sub_add_cancel (Nat.one_le_of_lt hyZ)] using
        (Finset.sum_Ico_sub w (show y + 1 ≤ Z by omega))
  rw [hsplit] at htel
  linarith

/-- With an auxiliary coefficient, quotient-jump increments still telescope
exactly after one discrete product rule.  Thus the cost of retaining the
sign across jump boundaries is a single coefficient-increment sum, rather
than the sum of the absolute sizes of the jumps. -/
theorem sum_jumpQuotientEdges_weighted_succ_sub_eq_endpoints_sub_residual_sub_stable
    (w a : ℕ → ℝ) {X y Z : ℕ} (hyZ : y < Z) :
    (∑ m ∈ roughSaiasJumpQuotientEdges X y Z,
        (w (m + 1) - w m) * a m) =
      w Z * a Z - w (y + 1) * a (y + 1) -
        (∑ m ∈ Finset.Ioc y (Z - 1),
          w (m + 1) * (a (m + 1) - a m)) -
        ∑ m ∈ roughSaiasStableQuotientEdges X y Z,
          (w (m + 1) - w m) * a m := by
  have hsplit := sum_Ioc_eq_sum_stableQuotientEdges_add_jumpEdges
    (fun m => (w (m + 1) - w m) * a m) X y Z
  have htel :
      (∑ m ∈ Finset.Ioc y (Z - 1),
          (w (m + 1) * a (m + 1) - w m * a m)) =
        w Z * a Z - w (y + 1) * a (y + 1) := by
    simpa only [← Finset.Ico_add_one_add_one_eq_Ioc,
      Nat.sub_add_cancel (Nat.one_le_of_lt hyZ)] using
        (Finset.sum_Ico_sub (fun n => w n * a n)
          (show y + 1 ≤ Z by omega))
  have hall :
      (∑ m ∈ Finset.Ioc y (Z - 1),
          (w (m + 1) - w m) * a m) =
        w Z * a Z - w (y + 1) * a (y + 1) -
          ∑ m ∈ Finset.Ioc y (Z - 1),
            w (m + 1) * (a (m + 1) - a m) := by
    calc
      (∑ m ∈ Finset.Ioc y (Z - 1),
          (w (m + 1) - w m) * a m) =
          ∑ m ∈ Finset.Ioc y (Z - 1),
            ((w (m + 1) * a (m + 1) - w m * a m) -
              w (m + 1) * (a (m + 1) - a m)) := by
                apply Finset.sum_congr rfl
                intro m _hm
                ring
      _ = (∑ m ∈ Finset.Ioc y (Z - 1),
              (w (m + 1) * a (m + 1) - w m * a m)) -
            ∑ m ∈ Finset.Ioc y (Z - 1),
              w (m + 1) * (a (m + 1) - a m) := by
                rw [Finset.sum_sub_distrib]
      _ = _ := by rw [htel]
  rw [hsplit] at hall
  linarith

/-- The increment of the cumulative prime-logarithm error is the local
prime mass minus Lebesgue mass. -/
theorem roughSaiasPrimeLogError_succ_sub (m : ℕ) :
    (FriableAsymptotic.primeLogSumUpTo (m + 1) - ((m + 1 : ℕ) : ℝ)) -
        (FriableAsymptotic.primeLogSumUpTo m - (m : ℝ)) =
      FriableAsymptotic.primeLogIncrement (m + 1) - 1 := by
  have hincr :
      FriableAsymptotic.primeLogSumUpTo (m + 1) =
        FriableAsymptotic.primeLogSumUpTo m +
          FriableAsymptotic.primeLogIncrement (m + 1) := by
    calc
      FriableAsymptotic.primeLogSumUpTo (m + 1) =
          ∑ k ∈ Finset.range ((m + 1) + 1),
            FriableAsymptotic.primeLogIncrement k :=
        (FriableAsymptotic.sum_range_primeLogIncrement (m + 1)).symm
      _ = (∑ k ∈ Finset.range (m + 1),
              FriableAsymptotic.primeLogIncrement k) +
            FriableAsymptotic.primeLogIncrement (m + 1) := by
              rw [Finset.sum_range_succ]
      _ = _ := by
        rw [FriableAsymptotic.sum_range_primeLogIncrement m]
  rw [hincr, Nat.cast_add, Nat.cast_one]
  ring

/-- The weighted natural-theta jump term has an exact boundary telescope.
After the product rule, its only new interior term is the explicit local
prime-error residual `primeLogIncrement (m+1) - 1`; stable edges remain
available for the fixed-quotient base-free estimate. -/
theorem sum_jumpNaturalThetaWeight_diff_mul_primeLogError_eq_endpoints_sub_residual_sub_stable
    {X y Z : ℕ} (hyZ : y < Z) :
    (∑ m ∈ roughSaiasJumpQuotientEdges X y Z,
        (roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m) *
            (FriableAsymptotic.primeLogSumUpTo m - (m : ℝ))) =
      roughSaiasNaturalQuotientThetaWeight X Z *
          (FriableAsymptotic.primeLogSumUpTo Z - (Z : ℝ)) -
        roughSaiasNaturalQuotientThetaWeight X (y + 1) *
          (FriableAsymptotic.primeLogSumUpTo (y + 1) -
            ((y + 1 : ℕ) : ℝ)) -
        (∑ m ∈ Finset.Ioc y (Z - 1),
          roughSaiasNaturalQuotientThetaWeight X (m + 1) *
            (FriableAsymptotic.primeLogIncrement (m + 1) - 1)) -
        ∑ m ∈ roughSaiasStableQuotientEdges X y Z,
          (roughSaiasNaturalQuotientThetaWeight X (m + 1) -
            roughSaiasNaturalQuotientThetaWeight X m) *
              (FriableAsymptotic.primeLogSumUpTo m - (m : ℝ)) := by
  simpa only [roughSaiasPrimeLogError_succ_sub] using
    (sum_jumpQuotientEdges_weighted_succ_sub_eq_endpoints_sub_residual_sub_stable
      (w := roughSaiasNaturalQuotientThetaWeight X)
      (a := fun m => FriableAsymptotic.primeLogSumUpTo m - (m : ℝ)) hyZ)

/-- After the weighted boundary telescope is inserted in the full finite
Abel formula, both global endpoint products and the stable-edge sum cancel.
The entire natural theta transfer is therefore exactly one signed local
prime-minus-integer residual. -/
theorem roughSaiasNaturalThetaErrorTransfer_eq_localPrimeErrorResidual
    {X y Z : ℕ} (hyZ : y < Z) :
    roughSaiasNaturalThetaErrorTransfer X y Z =
      ∑ m ∈ Finset.Ioc y Z,
        roughSaiasNaturalQuotientThetaWeight X m *
          (FriableAsymptotic.primeLogIncrement m - 1) := by
  unfold roughSaiasNaturalThetaErrorTransfer
  rw [FriableAsymptotic.primeThetaWeightedInterval_eq_Ioc,
    FriableAsymptotic.integerAbelMain_eq_sum_Ioc _ hyZ,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _hm
  ring

end

end Erdos390.WholePaper
