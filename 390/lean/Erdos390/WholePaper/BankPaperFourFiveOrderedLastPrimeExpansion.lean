import Erdos390.WholePaper.BankPaperFourFivePrimeEndpoint
import Erdos390.WholePaper.SafeShortIntervalPrimeCounting
import Mathlib.Data.Fin.Tuple.Finset

/-!
# Exact last-prime expansion in the four/five chamber

This file exposes the last prime in each ordered layer before any analytic
approximation is made.  The existing finite reduction represents ordered
prime factors by lists.  Here those lists are identified with fixed-length
tuples, a tuple of length `m + 1` is split into its first `m` entries and its
last entry, and the last-entry fibre is identified with the literal prime
interval

`(max y (A / q), B / q]`,  where `q` is the prefix product.

The final theorem applies the uniform `pi-li` endpoint theorem at these exact
moving endpoints and sums its errors.  In particular, no relative estimate
for a short prime interval is used or assumed.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

/-! ## Fixed-length tuples and the existing ordered-list layer -/

/-- Prime coordinates available to a tuple whose total product is at most
`B`.  The upper bound is redundant after imposing the product condition, but
makes the ambient tuple set finite. -/
def fourFivePrimeCoordinateBand (y B : Nat) : Finset Nat :=
  (Finset.Ioc y B).filter Nat.Prime

/-- The literal fixed-length ordered-prime tuples with product in `(A,B]`. -/
def fourFiveOrderedPrimeTupleSet (j y A B : Nat) :
    Finset (Fin j -> Nat) :=
  (Fintype.piFinset
      (fun _i : Fin j => fourFivePrimeCoordinateBand y B)).filter
    (fun p => A < ∏ i, p i ∧ (∏ i, p i) <= B)

@[simp]
theorem mem_fourFivePrimeCoordinateBand {y B p : Nat} :
    p ∈ fourFivePrimeCoordinateBand y B ↔
      y < p ∧ p <= B ∧ p.Prime := by
  simp [fourFivePrimeCoordinateBand, and_assoc, and_left_comm,
    and_comm]

@[simp]
theorem mem_fourFiveOrderedPrimeTupleSet
    {j y A B : Nat} {p : Fin j -> Nat} :
    p ∈ fourFiveOrderedPrimeTupleSet j y A B ↔
      A < ∏ i, p i ∧ (∏ i, p i) <= B ∧
        ∀ i, y < p i ∧ p i <= B ∧ (p i).Prime := by
  simp only [fourFiveOrderedPrimeTupleSet, Finset.mem_filter,
    Fintype.mem_piFinset, mem_fourFivePrimeCoordinateBand]
  tauto

/-- The injective conversion from a fixed-length tuple to its coordinate
list. -/
def fourFiveTupleToListEmbedding (j : Nat) :
    (Fin j -> Nat) ↪ List Nat where
  toFun := List.ofFn
  inj' := List.ofFn_injective

/-- The fixed-length tuple set maps exactly onto the ordered-list set used by
the finite rough-chamber reduction. -/
theorem map_fourFiveOrderedPrimeTupleSet_eq_factorLists
    (j y A B : Nat) :
    (fourFiveOrderedPrimeTupleSet j y A B).map
        (fourFiveTupleToListEmbedding j) =
      fourFiveOrderedPrimeFactorLists j y A B := by
  ext l
  constructor
  · intro hl
    rw [Finset.mem_map] at hl
    obtain ⟨p, hp, rfl⟩ := hl
    have hpData := mem_fourFiveOrderedPrimeTupleSet.mp hp
    apply mem_fourFiveOrderedPrimeFactorLists_iff.mpr
    refine ⟨List.length_ofFn, ?_, ?_, ?_⟩
    · change A < (List.ofFn p).prod
      simpa only [List.prod_ofFn] using hpData.1
    · change (List.ofFn p).prod <= B
      simpa only [List.prod_ofFn] using hpData.2.1
    · change ∀ x ∈ List.ofFn p, x.Prime ∧ y < x
      rw [List.forall_mem_ofFn_iff]
      intro i
      exact ⟨(hpData.2.2 i).2.2, (hpData.2.2 i).1⟩
  · intro hl
    have hlData := mem_fourFiveOrderedPrimeFactorLists_iff.mp hl
    obtain ⟨hlength, hA, hB, hprime⟩ := hlData
    subst j
    let p : Fin l.length -> Nat := l.get
    have hprod : (∏ i, p i) = l.prod := by
      rw [← List.prod_ofFn, List.ofFn_get]
    have hp : p ∈ fourFiveOrderedPrimeTupleSet l.length y A B := by
      apply mem_fourFiveOrderedPrimeTupleSet.mpr
      refine ⟨by simpa only [hprod] using hA,
        by simpa only [hprod] using hB, ?_⟩
      intro i
      have hmem : p i ∈ l := List.get_mem l i
      have hq := hprime (p i) hmem
      have hleProd : p i <= l.prod :=
        List.single_le_prod
          (fun x hx => (hprime x hx).1.one_le) (p i) hmem
      exact ⟨hq.2, hleProd.trans hB, hq.1⟩
    apply Finset.mem_map.mpr
    exact ⟨p, hp, List.ofFn_get l⟩

/-- Cardinal form of the tuple/list identification. -/
theorem fourFiveOrderedPrimeTupleSet_card_eq_layerMass
    (j y A B : Nat) :
    (fourFiveOrderedPrimeTupleSet j y A B).card =
      fourFiveOrderedPrimeLayerMass j y A B := by
  rw [← fourFiveOrderedPrimeFactorLists_card]
  rw [← map_fourFiveOrderedPrimeTupleSet_eq_factorLists]
  exact (Finset.card_map _).symm

/-! ## Splitting off the last coordinate -/

/-- Ambient tuples for the first `m` prime coordinates. -/
def fourFiveOrderedPrimePrefixSet (m y B : Nat) :
    Finset (Fin m -> Nat) :=
  Fintype.piFinset
    (fun _i : Fin m => fourFivePrimeCoordinateBand y B)

@[simp]
theorem mem_fourFiveOrderedPrimePrefixSet
    {m y B : Nat} {q : Fin m -> Nat} :
    q ∈ fourFiveOrderedPrimePrefixSet m y B ↔
      ∀ i, y < q i ∧ q i <= B ∧ (q i).Prime := by
  simp [fourFiveOrderedPrimePrefixSet]

/-- The allowed last primes after fixing the prefix `q`. -/
def fourFiveLastPrimeFiber
    {m : Nat} (q : Fin m -> Nat) (y A B : Nat) : Finset Nat :=
  (fourFivePrimeCoordinateBand y B).filter
    (fun p => A < (∏ i, q i) * p ∧ (∏ i, q i) * p <= B)

@[simp]
theorem mem_fourFiveLastPrimeFiber
    {m y A B : Nat} {q : Fin m -> Nat} {p : Nat} :
    p ∈ fourFiveLastPrimeFiber q y A B ↔
      y < p ∧ p <= B ∧ p.Prime ∧
        A < (∏ i, q i) * p ∧ (∏ i, q i) * p <= B := by
  simp only [fourFiveLastPrimeFiber, Finset.mem_filter,
    mem_fourFivePrimeCoordinateBand]
  tauto

/-- The finite set of prefix/last-prime pairs before reassembling them as
tuples of length `m + 1`. -/
def fourFiveLastPrimeSplitSet (m y A B : Nat) :
    Finset ((Fin m -> Nat) × Nat) :=
  ((fourFiveOrderedPrimePrefixSet m y B) ×ˢ
      fourFivePrimeCoordinateBand y B).filter
    (fun qp => A < (∏ i, qp.1 i) * qp.2 ∧
      (∏ i, qp.1 i) * qp.2 <= B)

@[simp]
theorem mem_fourFiveLastPrimeSplitSet
    {m y A B : Nat} {q : Fin m -> Nat} {p : Nat} :
    (q, p) ∈ fourFiveLastPrimeSplitSet m y A B ↔
      q ∈ fourFiveOrderedPrimePrefixSet m y B ∧
        p ∈ fourFiveLastPrimeFiber q y A B := by
  simp only [fourFiveLastPrimeSplitSet, Finset.mem_filter,
    Finset.mem_product]
  constructor
  · rintro ⟨⟨hq, hpBand⟩, hA, hB⟩
    exact ⟨hq, (mem_fourFiveLastPrimeFiber.mpr
      ⟨(mem_fourFivePrimeCoordinateBand.mp hpBand).1,
        (mem_fourFivePrimeCoordinateBand.mp hpBand).2.1,
        (mem_fourFivePrimeCoordinateBand.mp hpBand).2.2, hA, hB⟩)⟩
  · rintro ⟨hq, hp⟩
    have hpData := mem_fourFiveLastPrimeFiber.mp hp
    exact ⟨⟨hq, mem_fourFivePrimeCoordinateBand.mpr
      ⟨hpData.1, hpData.2.1, hpData.2.2.1⟩⟩,
      hpData.2.2.2.1, hpData.2.2.2.2⟩

/-- Append the last coordinate to a prefix, as an embedding. -/
def fourFiveSnocEmbedding (m : Nat) :
    ((Fin m -> Nat) × Nat) ↪ (Fin (m + 1) -> Nat) where
  toFun qp := Fin.snoc qp.1 qp.2
  inj' := by
    intro a b h
    apply Prod.ext
    · simpa using congrArg Fin.init h
    · simpa using congrFun h (Fin.last m)

/-- Reassembling a split pair by `Fin.snoc` gives exactly the full ordered
tuple set. -/
theorem map_fourFiveLastPrimeSplitSet_eq_tupleSet
    (m y A B : Nat) :
    (fourFiveLastPrimeSplitSet m y A B).map
        (fourFiveSnocEmbedding m) =
      fourFiveOrderedPrimeTupleSet (m + 1) y A B := by
  ext r
  constructor
  · intro hr
    rw [Finset.mem_map] at hr
    obtain ⟨qp, hqp, rfl⟩ := hr
    rcases qp with ⟨q, p⟩
    have hsplit := mem_fourFiveLastPrimeSplitSet.mp hqp
    have hq := mem_fourFiveOrderedPrimePrefixSet.mp hsplit.1
    have hp := mem_fourFiveLastPrimeFiber.mp hsplit.2
    apply mem_fourFiveOrderedPrimeTupleSet.mpr
    change A < (∏ i, (Fin.snoc q p : Fin (m + 1) → Nat) i) ∧
      (∏ i, (Fin.snoc q p : Fin (m + 1) → Nat) i) <= B ∧
        ∀ i, y < (Fin.snoc q p : Fin (m + 1) → Nat) i ∧
          (Fin.snoc q p : Fin (m + 1) → Nat) i <= B ∧
          ((Fin.snoc q p : Fin (m + 1) → Nat) i).Prime
    rw [Fin.prod_snoc]
    refine ⟨hp.2.2.2.1, hp.2.2.2.2, ?_⟩
    intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simpa using ⟨hp.1, hp.2.1, hp.2.2.1⟩
    · simpa using hq k
  · intro hr
    have hrData := mem_fourFiveOrderedPrimeTupleSet.mp hr
    let q : Fin m -> Nat := Fin.init r
    let p : Nat := r (Fin.last m)
    have hq : q ∈ fourFiveOrderedPrimePrefixSet m y B := by
      apply mem_fourFiveOrderedPrimePrefixSet.mpr
      intro i
      exact hrData.2.2 i.castSucc
    have hp : p ∈ fourFiveLastPrimeFiber q y A B := by
      apply mem_fourFiveLastPrimeFiber.mpr
      have hpCoord := hrData.2.2 (Fin.last m)
      have hprod :
          (∏ i, q i) * p = ∏ i, r i := by
        simpa only [q, p, Fin.init_def] using
          (Fin.prod_univ_castSucc r).symm
      refine ⟨hpCoord.1, hpCoord.2.1, hpCoord.2.2, ?_, ?_⟩
      · rw [hprod]
        exact hrData.1
      · rw [hprod]
        exact hrData.2.1
    apply Finset.mem_map.mpr
    refine ⟨(q, p), mem_fourFiveLastPrimeSplitSet.mpr ⟨hq, hp⟩, ?_⟩
    exact Fin.snoc_init_self r

/-- The split set is the disjoint sum of its literal last-prime fibres. -/
theorem fourFiveLastPrimeSplitSet_card_eq_sum_fibers
    (m y A B : Nat) :
    (fourFiveLastPrimeSplitSet m y A B).card =
      ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
        (fourFiveLastPrimeFiber q y A B).card := by
  have hmaps :
      ((fourFiveLastPrimeSplitSet m y A B :
          Finset ((Fin m -> Nat) × Nat)) : Set ((Fin m -> Nat) × Nat)).MapsTo
        Prod.fst (fourFiveOrderedPrimePrefixSet m y B) := by
    intro qp hqp
    rcases qp with ⟨q, p⟩
    exact (mem_fourFiveLastPrimeSplitSet.mp hqp).1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro q hq
  let e : Nat ↪ ((Fin m -> Nat) × Nat) :=
    ⟨fun p => (q, p), by
      intro a b h
      exact congrArg Prod.snd h⟩
  have heq :
      {qp ∈ fourFiveLastPrimeSplitSet m y A B | qp.1 = q} =
        (fourFiveLastPrimeFiber q y A B).map e := by
    ext qp
    rcases qp with ⟨q', p⟩
    simp only [Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨hpair, hq'q⟩
      subst q'
      exact ⟨p, (mem_fourFiveLastPrimeSplitSet.mp hpair).2, rfl⟩
    · rintro ⟨p', hp', hpair⟩
      have hfirst : q' = q := congrArg Prod.fst hpair.symm
      have hsecond : p = p' := congrArg Prod.snd hpair.symm
      subst q'
      subst p'
      exact ⟨mem_fourFiveLastPrimeSplitSet.mpr ⟨hq, hp'⟩, rfl⟩
  rw [heq, Finset.card_map]

/-- Exact last-prime cardinal expansion of the existing ordered layer. -/
theorem fourFiveOrderedPrimeLayerMass_eq_sum_lastPrimeFibers
    (m y A B : Nat) :
    fourFiveOrderedPrimeLayerMass (m + 1) y A B =
      ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
        (fourFiveLastPrimeFiber q y A B).card := by
  rw [← fourFiveOrderedPrimeTupleSet_card_eq_layerMass]
  rw [← map_fourFiveLastPrimeSplitSet_eq_tupleSet]
  rw [Finset.card_map]
  exact fourFiveLastPrimeSplitSet_card_eq_sum_fibers m y A B

/-! ## Every last-prime fibre is an exact clipped prime interval -/

/-- Natural lower endpoint after exposing the prefix product. -/
def fourFiveLastPrimeLower
    {m : Nat} (q : Fin m -> Nat) (y A : Nat) : Nat :=
  max y (A / ∏ i, q i)

/-- Natural upper endpoint after exposing the prefix product. -/
def fourFiveLastPrimeUpper
    {m : Nat} (q : Fin m -> Nat) (B : Nat) : Nat :=
  B / ∏ i, q i

theorem fourFiveLastPrimeFiber_eq_primeInterval
    {m y A B : Nat} {q : Fin m -> Nat}
    (hqpos : 0 < ∏ i, q i) :
    fourFiveLastPrimeFiber q y A B =
      (Finset.Ioc (fourFiveLastPrimeLower q y A)
        (fourFiveLastPrimeUpper q B)).filter Nat.Prime := by
  ext p
  simp only [mem_fourFiveLastPrimeFiber, Finset.mem_filter,
    Finset.mem_Ioc]
  constructor
  · rintro ⟨hy, _hpB, hpPrime, hA, hB⟩
    refine ⟨⟨?_, ?_⟩, hpPrime⟩
    · apply (max_lt_iff).mpr
      refine ⟨hy, ?_⟩
      exact (Nat.div_lt_iff_lt_mul hqpos).mpr (by
        simpa only [mul_comm] using hA)
    · exact (Nat.le_div_iff_mul_le hqpos).mpr (by
        simpa only [mul_comm] using hB)
  · rintro ⟨⟨hlow, hupper⟩, hpPrime⟩
    have hlowerData := (max_lt_iff.mp hlow)
    have hmulUpper : p * (∏ i, q i) <= B :=
      (Nat.le_div_iff_mul_le hqpos).mp hupper
    have hpB : p <= B :=
      (Nat.le_mul_of_pos_right p hqpos).trans hmulUpper
    refine ⟨hlowerData.1, hpB, hpPrime, ?_, ?_⟩
    · have := (Nat.div_lt_iff_lt_mul hqpos).mp hlowerData.2
      simpa only [mul_comm] using this
    · simpa only [mul_comm] using hmulUpper

/-- A prime prefix has positive product. -/
theorem fourFiveOrderedPrimePrefix_prod_pos
    {m y B : Nat} {q : Fin m -> Nat}
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    0 < ∏ i, q i := by
  apply Finset.prod_pos
  intro i _hi
  exact (mem_fourFiveOrderedPrimePrefixSet.mp hq i).2.2.pos

/-- Cardinality of a nonempty last-prime fibre as a difference of the
prime-counting function. -/
theorem fourFiveLastPrimeFiber_card_eq_primeCounting_sub
    {m y A B : Nat} {q : Fin m -> Nat}
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B)
    (hLU : fourFiveLastPrimeLower q y A <=
      fourFiveLastPrimeUpper q B) :
    (fourFiveLastPrimeFiber q y A B).card =
      Nat.primeCounting (fourFiveLastPrimeUpper q B) -
        Nat.primeCounting (fourFiveLastPrimeLower q y A) := by
  rw [fourFiveLastPrimeFiber_eq_primeInterval
    (fourFiveOrderedPrimePrefix_prod_pos hq)]
  exact Erdos390.WholePaper.SafePrimeCounting.prime_Ioc_card_eq_primeCounting_sub hLU

/-! ## Applying the endpoint theorem fibrewise -/

/-- The exact logarithmic-integral main term for one last-prime fibre.  An
empty/reversed interval contributes zero. -/
def fourFiveLastPrimeIntegral
    {m : Nat} (q : Fin m -> Nat) (y A B : Nat) : Real :=
  if fourFiveLastPrimeLower q y A <= fourFiveLastPrimeUpper q B then
    ∫ v in (fourFiveLastPrimeLower q y A : Real)..
      (fourFiveLastPrimeUpper q B : Real), 1 / Real.log v
  else 0

/-- The literal fifth-log endpoint ledger for one fibre. -/
def fourFiveLastPrimeEndpointError
    {m : Nat} (C : Real) (q : Fin m -> Nat)
    (y A B : Nat) : Real :=
  if fourFiveLastPrimeLower q y A <= fourFiveLastPrimeUpper q B then
    3 * C * (fourFiveLastPrimeUpper q B : Real) /
      Real.log (fourFiveLastPrimeLower q y A : Real) ^ 5
  else 0

theorem fourFiveLastPrimeLower_ge_y
    {m y A : Nat} (q : Fin m -> Nat) :
    y <= fourFiveLastPrimeLower q y A := by
  exact le_max_left _ _

/-- Uniform endpoint estimate for one exact moving last-prime fibre. -/
theorem abs_fourFiveLastPrimeFiber_card_sub_integral_le
    {m y A B : Nat} {q : Fin m -> Nat} {C X0 : Real}
    (_hC : 0 < C) (_hX0 : 3 <= X0) (hy : X0 <= (y : Real))
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B)
    (hPNT : forall a b : Real, X0 <= a -> a <= b ->
      abs (((Nat.primeCounting ⌊b⌋₊ : Real) -
          (Nat.primeCounting ⌊a⌋₊ : Real)) -
          (∫ v in a..b, 1 / Real.log v)) <=
        3 * C * b / Real.log a ^ 5) :
    abs (((fourFiveLastPrimeFiber q y A B).card : Real) -
        fourFiveLastPrimeIntegral q y A B) <=
      fourFiveLastPrimeEndpointError C q y A B := by
  by_cases hLU : fourFiveLastPrimeLower q y A <=
      fourFiveLastPrimeUpper q B
  · have hlowerX : X0 <= (fourFiveLastPrimeLower q y A : Real) := by
      exact hy.trans (by exact_mod_cast fourFiveLastPrimeLower_ge_y q)
    have hLUReal : (fourFiveLastPrimeLower q y A : Real) <=
        (fourFiveLastPrimeUpper q B : Real) := by
      exact_mod_cast hLU
    have hcountNat := fourFiveLastPrimeFiber_card_eq_primeCounting_sub hq hLU
    have hpiMono :
        Nat.primeCounting (fourFiveLastPrimeLower q y A) <=
          Nat.primeCounting (fourFiveLastPrimeUpper q B) :=
      Nat.monotone_primeCounting hLU
    have hcountReal :
        ((fourFiveLastPrimeFiber q y A B).card : Real) =
          (Nat.primeCounting (fourFiveLastPrimeUpper q B) : Real) -
            (Nat.primeCounting (fourFiveLastPrimeLower q y A) : Real) := by
      rw [hcountNat, Nat.cast_sub hpiMono]
    have hbound := hPNT
      (fourFiveLastPrimeLower q y A : Real)
      (fourFiveLastPrimeUpper q B : Real) hlowerX hLUReal
    simp only [Nat.floor_natCast] at hbound
    simpa only [fourFiveLastPrimeIntegral,
      fourFiveLastPrimeEndpointError, hLU, if_true, hcountReal] using hbound
  · have hempty :
        Finset.Ioc (fourFiveLastPrimeLower q y A)
          (fourFiveLastPrimeUpper q B) = ∅ := by
      apply Finset.Ioc_eq_empty
      omega
    rw [fourFiveLastPrimeFiber_eq_primeInterval
      (fourFiveOrderedPrimePrefix_prod_pos hq), hempty]
    simp [fourFiveLastPrimeIntegral, fourFiveLastPrimeEndpointError, hLU]

/-- Sum of the exact last-prime logarithmic integrals in layer `m + 1`. -/
def fourFiveOrderedLastPrimeIntegralLayer
    (m y A B : Nat) : Real :=
  ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
    fourFiveLastPrimeIntegral q y A B

/-- Sum of all exact endpoint losses in layer `m + 1`. -/
def fourFiveOrderedLastPrimeEndpointErrorLayer
    (C : Real) (m y A B : Nat) : Real :=
  ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
    fourFiveLastPrimeEndpointError C q y A B

/-- The exact last-prime expansion plus the summed fifth-log endpoint
ledger.  This is the analytic handoff for the later product-measure
telescope. -/
theorem abs_fourFiveOrderedPrimeLayerMass_sub_lastPrimeIntegral_le
    {m y A B : Nat} {C X0 : Real}
    (hC : 0 < C) (hX0 : 3 <= X0) (hy : X0 <= (y : Real))
    (hPNT : forall a b : Real, X0 <= a -> a <= b ->
      abs (((Nat.primeCounting ⌊b⌋₊ : Real) -
          (Nat.primeCounting ⌊a⌋₊ : Real)) -
          (∫ v in a..b, 1 / Real.log v)) <=
        3 * C * b / Real.log a ^ 5) :
    abs ((fourFiveOrderedPrimeLayerMass (m + 1) y A B : Real) -
        fourFiveOrderedLastPrimeIntegralLayer m y A B) <=
      fourFiveOrderedLastPrimeEndpointErrorLayer C m y A B := by
  have hcardNat :=
    fourFiveOrderedPrimeLayerMass_eq_sum_lastPrimeFibers m y A B
  have hcardReal :
      (fourFiveOrderedPrimeLayerMass (m + 1) y A B : Real) =
        ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
          ((fourFiveLastPrimeFiber q y A B).card : Real) := by
    exact_mod_cast hcardNat
  rw [hcardReal]
  unfold fourFiveOrderedLastPrimeIntegralLayer
    fourFiveOrderedLastPrimeEndpointErrorLayer
  rw [← Finset.sum_sub_distrib]
  calc
    abs (∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
        (((fourFiveLastPrimeFiber q y A B).card : Real) -
          fourFiveLastPrimeIntegral q y A B)) <=
        ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
          abs (((fourFiveLastPrimeFiber q y A B).card : Real) -
            fourFiveLastPrimeIntegral q y A B) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
        fourFiveLastPrimeEndpointError C q y A B := by
      apply Finset.sum_le_sum
      intro q hq
      exact abs_fourFiveLastPrimeFiber_card_sub_integral_le
        hC hX0 hy hq hPNT

/-- Unconditional existential version, with one endpoint constant and cutoff
shared by all four ordered layers and all prefix fibres. -/
theorem exists_abs_fourFiveOrderedPrimeLayerMass_sub_lastPrimeIntegral_le :
    ∃ C : Real, 0 < C ∧ ∃ X0 : Real, 3 <= X0 ∧
      forall {m y A B : Nat}, X0 <= (y : Real) ->
        abs ((fourFiveOrderedPrimeLayerMass (m + 1) y A B : Real) -
            fourFiveOrderedLastPrimeIntegralLayer m y A B) <=
          fourFiveOrderedLastPrimeEndpointErrorLayer C m y A B := by
  obtain ⟨C, hC, X0, hX0, hPNT⟩ :=
    exists_abs_fourFivePrimeCounting_sub_integral_inv_log_le
  refine ⟨C, hC, X0, hX0, ?_⟩
  intro m y A B hy
  exact abs_fourFiveOrderedPrimeLayerMass_sub_lastPrimeIntegral_le
    hC hX0 hy hPNT

end Erdos390.WholePaper.BankPaperRealization
