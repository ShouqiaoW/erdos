import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalCoreFirst
import Erdos390.Full.DivisibilityMomentBounds
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.List.Permutation

/-!
# Finite reduction for the four-to-five rough chamber

The rough-number lemma used in the bank argument is proved in the paper by
first counting ordered tuples of large primes and only afterwards passing to
ordinary integers.  This file formalizes that finite passage independently of
the analytic prime-number-theorem input.

For a natural interval `(A,B]`, the definitions below record

* integers all of whose prime factors exceed `y`;
* their layers with exactly `j` prime factors, counted with multiplicity;
* ordered prime-factor lists, represented canonically by the distinct
  permutations of `primeFactorsList`;
* the repeated-prime exceptional set.

If `B < (y+1)^5`, every rough integer in the interval lies in one of the four
layers `1 ≤ j ≤ 4`.  On the squarefree part the ordered multiplicity is
exactly `j!`; on the nonsquarefree part its deficit is bounded by `j!`.
Consequently the ordinary rough count differs from the factorially weighted
ordered count by at most the number of repeated-prime integers.  The latter is
at most `B/y`, by exact multiple counting and the elementary reciprocal-square
tail estimate.

Thus the only analytic input left by this module is an estimate for
`fourFiveOrderedPrimeMixture`.  No PNT statement, asymptotic assumption, or
unproved declaration occurs here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

namespace BankPaperRealization

noncomputable section

/-! ## Rough intervals and their Omega-layers -/

/-- The integers in `(A,B]` all of whose prime factors are strictly larger
than `y`.  Positivity is supplied by membership in `Ioc A B`. -/
def fourFiveRoughInterval (y A B : Nat) : Finset Nat :=
  (Finset.Ioc A B).filter
    (fun r => ∀ q, q ∈ r.primeFactorsList -> y < q)

/-- The layer of the rough interval with exactly `j` prime factors, counted
with multiplicity. -/
def fourFiveRoughOmegaLayer (j y A B : Nat) : Finset Nat :=
  (fourFiveRoughInterval y A B).filter
    (fun r => ArithmeticFunction.cardFactors r = j)

/-- The nonsquarefree part of the rough interval. -/
def fourFiveRoughRepeatedInterval (y A B : Nat) : Finset Nat :=
  (fourFiveRoughInterval y A B).filter (fun r => ¬Squarefree r)

/-- The `j`-th Omega-layer inside the nonsquarefree rough interval. -/
def fourFiveRoughRepeatedOmegaLayer (j y A B : Nat) : Finset Nat :=
  (fourFiveRoughRepeatedInterval y A B).filter
    (fun r => ArithmeticFunction.cardFactors r = j)

@[simp]
theorem mem_fourFiveRoughInterval {y A B r : Nat} :
    r ∈ fourFiveRoughInterval y A B ↔
      A < r ∧ r ≤ B ∧
        ∀ q, q ∈ r.primeFactorsList -> y < q := by
  simp only [fourFiveRoughInterval, Finset.mem_filter, Finset.mem_Ioc]
  tauto

@[simp]
theorem mem_fourFiveRoughOmegaLayer {j y A B r : Nat} :
    r ∈ fourFiveRoughOmegaLayer j y A B ↔
      r ∈ fourFiveRoughInterval y A B ∧
        ArithmeticFunction.cardFactors r = j := by
  simp only [fourFiveRoughOmegaLayer, Finset.mem_filter]

@[simp]
theorem mem_fourFiveRoughRepeatedInterval {y A B r : Nat} :
    r ∈ fourFiveRoughRepeatedInterval y A B ↔
      r ∈ fourFiveRoughInterval y A B ∧ ¬Squarefree r := by
  simp only [fourFiveRoughRepeatedInterval, Finset.mem_filter]

@[simp]
theorem mem_fourFiveRoughRepeatedOmegaLayer {j y A B r : Nat} :
    r ∈ fourFiveRoughRepeatedOmegaLayer j y A B ↔
      r ∈ fourFiveRoughRepeatedInterval y A B ∧
        ArithmeticFunction.cardFactors r = j := by
  simp only [fourFiveRoughRepeatedOmegaLayer, Finset.mem_filter]

/-- The two possible orders of filtering by Omega and nonsquarefreeness give
the same repeated layer. -/
theorem fourFiveRoughRepeatedOmegaLayer_eq_filter_not_squarefree
    (j y A B : Nat) :
    fourFiveRoughRepeatedOmegaLayer j y A B =
      (fourFiveRoughOmegaLayer j y A B).filter
        (fun r => ¬Squarefree r) := by
  ext r
  simp only [mem_fourFiveRoughRepeatedOmegaLayer,
    mem_fourFiveRoughRepeatedInterval, Finset.mem_filter,
    mem_fourFiveRoughOmegaLayer]
  tauto

/-- Five large prime factors already force size at least `(y+1)^5`.
Therefore the paper's endpoint condition leaves only the layers `1,...,4`. -/
theorem fourFiveRough_cardFactors_le_four
    {y A B r : Nat} (hr : r ∈ fourFiveRoughInterval y A B)
    (hB : B < (y + 1) ^ 5) :
    ArithmeticFunction.cardFactors r ≤ 4 := by
  have hrData := mem_fourFiveRoughInterval.mp hr
  have hrPos : 0 < r := by omega
  have hfactorLower :
      (y + 1) ^ r.primeFactorsList.length ≤
        r.primeFactorsList.prod :=
    List.pow_card_le_prod r.primeFactorsList (y + 1) (by
      intro q hq
      have := hrData.2.2 q hq
      omega)
  rw [Nat.prod_primeFactorsList hrPos.ne'] at hfactorLower
  by_contra hnot
  have hfive : 5 ≤ r.primeFactorsList.length := by
    rw [ArithmeticFunction.cardFactors_apply] at hnot
    omega
  have hpow : (y + 1) ^ 5 ≤ (y + 1) ^ r.primeFactorsList.length :=
    Nat.pow_le_pow_right (by omega) hfive
  omega

/-- The rough interval is exactly the union of its first four Omega-layers
under the paper's power separation. -/
theorem fourFiveRoughInterval_eq_biUnion_omegaLayers
    {y A B : Nat} (hA : 1 ≤ A) (hB : B < (y + 1) ^ 5) :
    fourFiveRoughInterval y A B =
      (Finset.Icc 1 4).biUnion
        (fun j => fourFiveRoughOmegaLayer j y A B) := by
  ext r
  constructor
  · intro hr
    have hrData := mem_fourFiveRoughInterval.mp hr
    have homegaPos : 0 < ArithmeticFunction.cardFactors r := by
      rw [ArithmeticFunction.cardFactors_pos_iff_one_lt]
      omega
    have homegaLe := fourFiveRough_cardFactors_le_four hr hB
    rw [Finset.mem_biUnion]
    exact ⟨ArithmeticFunction.cardFactors r,
      Finset.mem_Icc.mpr ⟨homegaPos, homegaLe⟩,
      mem_fourFiveRoughOmegaLayer.mpr ⟨hr, rfl⟩⟩
  · intro hr
    rw [Finset.mem_biUnion] at hr
    obtain ⟨j, _hj, hrj⟩ := hr
    exact (mem_fourFiveRoughOmegaLayer.mp hrj).1

/-- Cardinality form of the first-four-layer decomposition. -/
theorem fourFiveRoughInterval_card_eq_sum_omegaLayers
    {y A B : Nat} (hA : 1 ≤ A) (hB : B < (y + 1) ^ 5) :
    (fourFiveRoughInterval y A B).card =
      ∑ j ∈ Finset.Icc 1 4,
        (fourFiveRoughOmegaLayer j y A B).card := by
  rw [fourFiveRoughInterval_eq_biUnion_omegaLayers hA hB]
  exact Finset.card_biUnion
    (Set.pairwiseDisjoint_filter
      (fun r => ArithmeticFunction.cardFactors r)
      (Finset.Icc 1 4 : Set Nat) (fourFiveRoughInterval y A B))

/-- The repeated rough interval has the corresponding disjoint layer
decomposition. -/
theorem fourFiveRoughRepeatedInterval_card_eq_sum_omegaLayers
    {y A B : Nat} (hA : 1 ≤ A) (hB : B < (y + 1) ^ 5) :
    (fourFiveRoughRepeatedInterval y A B).card =
      ∑ j ∈ Finset.Icc 1 4,
        (fourFiveRoughRepeatedOmegaLayer j y A B).card := by
  have hsubset : fourFiveRoughRepeatedInterval y A B ⊆
      fourFiveRoughInterval y A B := Finset.filter_subset _ _
  have hall : ∀ r, r ∈ fourFiveRoughRepeatedInterval y A B ->
      ArithmeticFunction.cardFactors r ∈ Finset.Icc 1 4 := by
    intro r hr
    have hrRough := hsubset hr
    have hrData := mem_fourFiveRoughInterval.mp hrRough
    have homegaPos : 0 < ArithmeticFunction.cardFactors r := by
      rw [ArithmeticFunction.cardFactors_pos_iff_one_lt]
      omega
    exact Finset.mem_Icc.mpr
      ⟨homegaPos, fourFiveRough_cardFactors_le_four hrRough hB⟩
  change (fourFiveRoughRepeatedInterval y A B).card =
    ∑ j ∈ Finset.Icc 1 4,
      ((fourFiveRoughRepeatedInterval y A B).filter
        (fun r => ArithmeticFunction.cardFactors r = j)).card
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  rw [Finset.filter_eq_self.mpr hall]

/-! ## Ordered prime-factor lists -/

/-- Number of distinct orderings of the prime-factor multiset of `r`. -/
def fourFiveOrderedPrimeMultiplicity (r : Nat) : Nat :=
  r.primeFactorsList.permutations.toFinset.card

/-- All ordered prime-factor lists in the `j`-th rough layer.  This is the
literal finite ordered-tuple object; lists belonging to different products
are disjoint. -/
def fourFiveOrderedPrimeFactorLists
    (j y A B : Nat) : Finset (List Nat) :=
  (fourFiveRoughOmegaLayer j y A B).biUnion
    (fun r => r.primeFactorsList.permutations.toFinset)

/-- The ordered count in one Omega-layer. -/
def fourFiveOrderedPrimeLayerMass (j y A B : Nat) : Nat :=
  ∑ r ∈ fourFiveRoughOmegaLayer j y A B,
    fourFiveOrderedPrimeMultiplicity r

/-- Distinct permutations never outnumber all `Omega(r)!` generated
permutations. -/
theorem fourFiveOrderedPrimeMultiplicity_le_factorial (r : Nat) :
    fourFiveOrderedPrimeMultiplicity r ≤
      (ArithmeticFunction.cardFactors r).factorial := by
  unfold fourFiveOrderedPrimeMultiplicity
  calc
    r.primeFactorsList.permutations.toFinset.card ≤
        r.primeFactorsList.permutations.length :=
      List.toFinset_card_le
        (l := r.primeFactorsList.permutations)
    _ = r.primeFactorsList.length.factorial :=
      List.length_permutations r.primeFactorsList
    _ = (ArithmeticFunction.cardFactors r).factorial := by
      rw [ArithmeticFunction.cardFactors_apply]

/-- On a squarefree integer all permutations of the prime factors are
distinct, so the ordered multiplicity is exactly `Omega(r)!`. -/
theorem fourFiveOrderedPrimeMultiplicity_eq_factorial_of_squarefree
    {r : Nat} (hr : Squarefree r) :
    fourFiveOrderedPrimeMultiplicity r =
      (ArithmeticFunction.cardFactors r).factorial := by
  unfold fourFiveOrderedPrimeMultiplicity
  calc
    r.primeFactorsList.permutations.toFinset.card =
        r.primeFactorsList.permutations.length :=
      List.toFinset_card_of_nodup
        (List.nodup_permutations r.primeFactorsList
          hr.nodup_primeFactorsList)
    _ = r.primeFactorsList.length.factorial :=
      List.length_permutations r.primeFactorsList
    _ = (ArithmeticFunction.cardFactors r).factorial := by
      rw [ArithmeticFunction.cardFactors_apply]

@[simp]
theorem mem_fourFiveOrderedPrimeFactorLists
    {j y A B : Nat} {l : List Nat} :
    l ∈ fourFiveOrderedPrimeFactorLists j y A B ↔
      ∃ r, r ∈ fourFiveRoughOmegaLayer j y A B ∧
        List.Perm l r.primeFactorsList := by
  simp only [fourFiveOrderedPrimeFactorLists, Finset.mem_biUnion,
    List.mem_toFinset, List.mem_permutations]

/-- Intrinsic description of the ordered lists: length `j`, product in the
physical interval, and every entry a prime greater than `y`. -/
theorem mem_fourFiveOrderedPrimeFactorLists_iff
    {j y A B : Nat} {l : List Nat} :
    l ∈ fourFiveOrderedPrimeFactorLists j y A B ↔
      l.length = j ∧ A < l.prod ∧ l.prod ≤ B ∧
        ∀ q, q ∈ l -> q.Prime ∧ y < q := by
  constructor
  · intro hl
    obtain ⟨r, hr, hlr⟩ := mem_fourFiveOrderedPrimeFactorLists.mp hl
    have hrRough := (mem_fourFiveRoughOmegaLayer.mp hr).1
    have hrData := mem_fourFiveRoughInterval.mp hrRough
    have hrPos : 0 < r := by omega
    have hprod : l.prod = r :=
      hlr.prod_eq.trans (Nat.prod_primeFactorsList hrPos.ne')
    have hlength : l.length = j := by
      calc
        l.length = r.primeFactorsList.length := hlr.length_eq
        _ = ArithmeticFunction.cardFactors r := by
          rw [ArithmeticFunction.cardFactors_apply]
        _ = j := (mem_fourFiveRoughOmegaLayer.mp hr).2
    refine ⟨hlength, ?_, ?_, ?_⟩
    · simpa only [hprod] using hrData.1
    · simpa only [hprod] using hrData.2.1
    · intro q hql
      have hqr : q ∈ r.primeFactorsList := hlr.mem_iff.mp hql
      exact ⟨Nat.prime_of_mem_primeFactorsList hqr,
        hrData.2.2 q hqr⟩
  · rintro ⟨hlength, hA, hB, hprime⟩
    let r := l.prod
    have hlr : List.Perm l r.primeFactorsList := by
      apply Nat.primeFactorsList_unique
      · rfl
      · intro q hq
        exact (hprime q hq).1
    have hrRough : r ∈ fourFiveRoughInterval y A B := by
      apply mem_fourFiveRoughInterval.mpr
      refine ⟨hA, hB, ?_⟩
      intro q hqr
      have hql : q ∈ l := hlr.mem_iff.mpr hqr
      exact (hprime q hql).2
    have homega : ArithmeticFunction.cardFactors r = j := by
      calc
        ArithmeticFunction.cardFactors r = r.primeFactorsList.length :=
          ArithmeticFunction.cardFactors_apply
        _ = l.length := hlr.length_eq.symm
        _ = j := hlength
    exact mem_fourFiveOrderedPrimeFactorLists.mpr
      ⟨r, mem_fourFiveRoughOmegaLayer.mpr ⟨hrRough, homega⟩, hlr⟩

/-- Ordered-list fibres for two different products are disjoint. -/
theorem fourFiveOrderedPrimeFactorListFibers_pairwiseDisjoint
    (j y A B : Nat) :
    ((fourFiveRoughOmegaLayer j y A B : Finset Nat) : Set Nat).PairwiseDisjoint
      (fun r => r.primeFactorsList.permutations.toFinset) := by
  intro r hr s hs hrs
  change Disjoint (r.primeFactorsList.permutations.toFinset)
    (s.primeFactorsList.permutations.toFinset)
  rw [Finset.disjoint_left]
  intro l hlr hls
  have hrRough := (mem_fourFiveRoughOmegaLayer.mp hr).1
  have hsRough := (mem_fourFiveRoughOmegaLayer.mp hs).1
  have hrPos : 0 < r := by
    have := mem_fourFiveRoughInterval.mp hrRough
    omega
  have hsPos : 0 < s := by
    have := mem_fourFiveRoughInterval.mp hsRough
    omega
  have hlrPerm : List.Perm l r.primeFactorsList := by
    simpa only [List.mem_toFinset, List.mem_permutations] using hlr
  have hlsPerm : List.Perm l s.primeFactorsList := by
    simpa only [List.mem_toFinset, List.mem_permutations] using hls
  apply hrs
  calc
    r = r.primeFactorsList.prod :=
      (Nat.prod_primeFactorsList hrPos.ne').symm
    _ = l.prod := hlrPerm.prod_eq.symm
    _ = s.primeFactorsList.prod := hlsPerm.prod_eq
    _ = s := Nat.prod_primeFactorsList hsPos.ne'

/-- The cardinality of the literal ordered-list set is the layer mass. -/
theorem fourFiveOrderedPrimeFactorLists_card
    (j y A B : Nat) :
    (fourFiveOrderedPrimeFactorLists j y A B).card =
      fourFiveOrderedPrimeLayerMass j y A B := by
  unfold fourFiveOrderedPrimeFactorLists fourFiveOrderedPrimeLayerMass
  exact Finset.card_biUnion
    (fourFiveOrderedPrimeFactorListFibers_pairwiseDisjoint j y A B)

/-! ## Factorial weighting ∧ the repeated-prime deficit -/

/-- The ordered mass never exceeds `j!` times the ordinary layer count. -/
theorem fourFiveOrderedPrimeLayerMass_le_factorial_mul_card
    (j y A B : Nat) :
    fourFiveOrderedPrimeLayerMass j y A B ≤
      j.factorial * (fourFiveRoughOmegaLayer j y A B).card := by
  unfold fourFiveOrderedPrimeLayerMass
  calc
    (∑ r ∈ fourFiveRoughOmegaLayer j y A B,
        fourFiveOrderedPrimeMultiplicity r) ≤
        ∑ _r ∈ fourFiveRoughOmegaLayer j y A B, j.factorial := by
      apply Finset.sum_le_sum
      intro r hr
      have homega := (mem_fourFiveRoughOmegaLayer.mp hr).2
      simpa only [homega] using
        fourFiveOrderedPrimeMultiplicity_le_factorial r
    _ = j.factorial * (fourFiveRoughOmegaLayer j y A B).card := by
      simp [Nat.mul_comm]

/-- The possible factorial deficit is supported entirely on the repeated
prime layer. -/
theorem factorial_mul_card_le_orderedPrimeLayerMass_add_repeated
    (j y A B : Nat) :
    j.factorial * (fourFiveRoughOmegaLayer j y A B).card ≤
      fourFiveOrderedPrimeLayerMass j y A B +
        j.factorial *
          (fourFiveRoughRepeatedOmegaLayer j y A B).card := by
  let S := fourFiveRoughOmegaLayer j y A B
  let Q := S.filter (fun r => Squarefree r)
  have hmassSquare : j.factorial * Q.card ≤
      fourFiveOrderedPrimeLayerMass j y A B := by
    calc
      j.factorial * Q.card = ∑ _r ∈ Q, j.factorial := by
        simp [Nat.mul_comm]
      _ = ∑ r ∈ Q, fourFiveOrderedPrimeMultiplicity r := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrData := Finset.mem_filter.mp hr
        have homega := (mem_fourFiveRoughOmegaLayer.mp hrData.1).2
        symm
        simpa only [homega] using
          fourFiveOrderedPrimeMultiplicity_eq_factorial_of_squarefree
            hrData.2
      _ ≤ ∑ r ∈ S, fourFiveOrderedPrimeMultiplicity r := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
        intro r _hrS _hrQ
        exact Nat.zero_le _
      _ = fourFiveOrderedPrimeLayerMass j y A B := by
        rfl
  have hpartition : Q.card +
      (fourFiveRoughRepeatedOmegaLayer j y A B).card = S.card := by
    rw [fourFiveRoughRepeatedOmegaLayer_eq_filter_not_squarefree]
    change (S.filter (fun r => Squarefree r)).card +
        (S.filter (fun r => ¬Squarefree r)).card = S.card
    exact Finset.card_filter_add_card_filter_not
      (s := S) (fun r : Nat => Squarefree r)
  calc
    j.factorial * (fourFiveRoughOmegaLayer j y A B).card =
        j.factorial * S.card := by rfl
    _ = j.factorial *
        (Q.card + (fourFiveRoughRepeatedOmegaLayer j y A B).card) := by
      rw [hpartition]
    _ = j.factorial * Q.card +
        j.factorial *
          (fourFiveRoughRepeatedOmegaLayer j y A B).card := by
      rw [Nat.mul_add]
    _ ≤ fourFiveOrderedPrimeLayerMass j y A B +
        j.factorial *
          (fourFiveRoughRepeatedOmegaLayer j y A B).card :=
      Nat.add_le_add_right hmassSquare _

/-- Real normalized form of the upper factorial bound. -/
theorem fourFiveOrderedPrimeLayerRatio_le_card
    (j y A B : Nat) :
    (fourFiveOrderedPrimeLayerMass j y A B : Real) /
        (j.factorial : Real) ≤
      ((fourFiveRoughOmegaLayer j y A B).card : Real) := by
  have hfac : (0 : Real) < (j.factorial : Real) := by positivity
  apply (div_le_iff₀ hfac).2
  have hnat :=
    fourFiveOrderedPrimeLayerMass_le_factorial_mul_card j y A B
  have hreal :
      (fourFiveOrderedPrimeLayerMass j y A B : Real) ≤
        (j.factorial : Real) *
          ((fourFiveRoughOmegaLayer j y A B).card : Real) := by
    exact_mod_cast hnat
  simpa only [mul_comm] using hreal

/-- Layerwise ordered-to-unordered comparison. -/
theorem abs_fourFiveRoughOmegaLayer_card_sub_orderedRatio_le_repeated
    (j y A B : Nat) :
    abs (((fourFiveRoughOmegaLayer j y A B).card : Real) -
        (fourFiveOrderedPrimeLayerMass j y A B : Real) /
          (j.factorial : Real)) ≤
      ((fourFiveRoughRepeatedOmegaLayer j y A B).card : Real) := by
  have hratio := fourFiveOrderedPrimeLayerRatio_le_card j y A B
  have hnonneg : 0 ≤
      ((fourFiveRoughOmegaLayer j y A B).card : Real) -
        (fourFiveOrderedPrimeLayerMass j y A B : Real) /
          (j.factorial : Real) := sub_nonneg.mpr hratio
  rw [abs_of_nonneg hnonneg]
  have hfac : (0 : Real) < (j.factorial : Real) := by positivity
  have hnat :=
    factorial_mul_card_le_orderedPrimeLayerMass_add_repeated j y A B
  have hreal :
      (j.factorial : Real) *
          ((fourFiveRoughOmegaLayer j y A B).card : Real) ≤
        (fourFiveOrderedPrimeLayerMass j y A B : Real) +
          (j.factorial : Real) *
            ((fourFiveRoughRepeatedOmegaLayer j y A B).card : Real) := by
    exact_mod_cast hnat
  have hcancel :
      ((fourFiveOrderedPrimeLayerMass j y A B : Real) /
          (j.factorial : Real)) * (j.factorial : Real) =
        (fourFiveOrderedPrimeLayerMass j y A B : Real) :=
    div_mul_cancel₀ _ hfac.ne'
  nlinarith

/-- Factorially weighted ∑ of the four literal ordered-list counts. -/
def fourFiveOrderedPrimeMixture (y A B : Nat) : Real :=
  ∑ j ∈ Finset.Icc 1 4,
    (fourFiveOrderedPrimeLayerMass j y A B : Real) /
      (j.factorial : Real)

/-- The entire ordered-to-unordered discrepancy is bounded by the single
nonsquarefree rough count. -/
theorem abs_fourFiveRoughInterval_card_sub_orderedPrimeMixture_le_repeated
    {y A B : Nat} (hA : 1 ≤ A) (hB : B < (y + 1) ^ 5) :
    abs (((fourFiveRoughInterval y A B).card : Real) -
        fourFiveOrderedPrimeMixture y A B) ≤
      ((fourFiveRoughRepeatedInterval y A B).card : Real) := by
  have hcardNat := fourFiveRoughInterval_card_eq_sum_omegaLayers hA hB
  have hcardReal :
      ((fourFiveRoughInterval y A B).card : Real) =
        ∑ j ∈ Finset.Icc 1 4,
          ((fourFiveRoughOmegaLayer j y A B).card : Real) := by
    exact_mod_cast hcardNat
  have hrepeatedNat :=
    fourFiveRoughRepeatedInterval_card_eq_sum_omegaLayers hA hB
  have hrepeatedReal :
      ((fourFiveRoughRepeatedInterval y A B).card : Real) =
        ∑ j ∈ Finset.Icc 1 4,
          ((fourFiveRoughRepeatedOmegaLayer j y A B).card : Real) := by
    exact_mod_cast hrepeatedNat
  have htermNonneg : ∀ j, j ∈ Finset.Icc 1 4 -> 0 ≤
      ((fourFiveRoughOmegaLayer j y A B).card : Real) -
        (fourFiveOrderedPrimeLayerMass j y A B : Real) /
          (j.factorial : Real) := by
    intro j _hj
    exact sub_nonneg.mpr
      (fourFiveOrderedPrimeLayerRatio_le_card j y A B)
  rw [hcardReal]
  unfold fourFiveOrderedPrimeMixture
  rw [← Finset.sum_sub_distrib,
    abs_of_nonneg (Finset.sum_nonneg fun j hj => htermNonneg j hj)]
  calc
    (∑ j ∈ Finset.Icc 1 4,
        (((fourFiveRoughOmegaLayer j y A B).card : Real) -
          (fourFiveOrderedPrimeLayerMass j y A B : Real) /
            (j.factorial : Real))) ≤
        ∑ j ∈ Finset.Icc 1 4,
          ((fourFiveRoughRepeatedOmegaLayer j y A B).card : Real) := by
      apply Finset.sum_le_sum
      intro j hj
      have h :=
        abs_fourFiveRoughOmegaLayer_card_sub_orderedRatio_le_repeated
          j y A B
      simpa only [abs_of_nonneg (htermNonneg j hj)] using h
    _ = ((fourFiveRoughRepeatedInterval y A B).card : Real) :=
      hrepeatedReal.symm

/-! ## The repeated-prime square ledger -/

/-- Rough integers in `(A,B]` divisible by the square of a prime above `y`. -/
def fourFiveRepeatedPrimeSquareSet (y A B : Nat) : Finset Nat := by
  classical
  exact (Finset.Ioc A B).filter (fun r =>
    ∃ q, q.Prime ∧ y < q ∧ q * q ∣ r)

/-- Multiples of `q^2` in the positive prefix through `B`. -/
def fourFiveSquareMultiples (q B : Nat) : Finset Nat :=
  (Finset.Ioc 0 B).filter (fun r => q * q ∣ r)

@[simp]
theorem mem_fourFiveRepeatedPrimeSquareSet {y A B r : Nat} :
    r ∈ fourFiveRepeatedPrimeSquareSet y A B ↔
      A < r ∧ r ≤ B ∧
        ∃ q, q.Prime ∧ y < q ∧ q * q ∣ r := by
  simp only [fourFiveRepeatedPrimeSquareSet, Finset.mem_filter,
    Finset.mem_Ioc]
  tauto

@[simp]
theorem mem_fourFiveSquareMultiples {q B r : Nat} :
    r ∈ fourFiveSquareMultiples q B ↔
      0 < r ∧ r ≤ B ∧ q * q ∣ r := by
  simp only [fourFiveSquareMultiples, Finset.mem_filter, Finset.mem_Ioc]
  tauto

/-- Every nonsquarefree rough integer has a repeated prime factor above the
roughness threshold. -/
theorem fourFiveRoughRepeatedInterval_subset_repeatedPrimeSquareSet
    (y A B : Nat) :
    fourFiveRoughRepeatedInterval y A B ⊆
      fourFiveRepeatedPrimeSquareSet y A B := by
  intro r hr
  have hrData := mem_fourFiveRoughRepeatedInterval.mp hr
  have hrRough := mem_fourFiveRoughInterval.mp hrData.1
  have hrPos : 0 < r := by omega
  have hnSquare : ¬Squarefree r := hrData.2
  rw [Nat.squarefree_iff_prime_squarefree] at hnSquare
  push_neg at hnSquare
  obtain ⟨q, hqPrime, hqSq⟩ := hnSquare
  have hqr : q ∣ r := (Nat.dvd_mul_right q q).trans hqSq
  have hqMem : q ∈ r.primeFactorsList :=
    (Nat.mem_primeFactorsList_iff_dvd hrPos.ne' hqPrime).mpr hqr
  exact mem_fourFiveRepeatedPrimeSquareSet.mpr
    ⟨hrRough.1, hrRough.2.1,
      ⟨q, hqPrime, hrRough.2.2 q hqMem, hqSq⟩⟩

/-- The repeated-prime set is covered by square-multiple fibres indexed by
all integers in `(y,B]`; primality can be discarded for an upper bound. -/
theorem fourFiveRepeatedPrimeSquareSet_subset_biUnion_squareMultiples
    (y A B : Nat) :
    fourFiveRepeatedPrimeSquareSet y A B ⊆
      (Finset.Ioc y B).biUnion
        (fun q => fourFiveSquareMultiples q B) := by
  intro r hr
  obtain ⟨_hrA, hrB, q, _hqPrime, hyq, hqSq⟩ :=
    mem_fourFiveRepeatedPrimeSquareSet.mp hr
  have hrPos : 0 < r := by omega
  have hqr : q ∣ r := (Nat.dvd_mul_right q q).trans hqSq
  have hqB : q ≤ B := (Nat.le_of_dvd hrPos hqr).trans hrB
  rw [Finset.mem_biUnion]
  exact ⟨q, Finset.mem_Ioc.mpr ⟨hyq, hqB⟩,
    mem_fourFiveSquareMultiples.mpr ⟨hrPos, hrB, hqSq⟩⟩

/-- Exact count of positive multiples of `q^2` through `B`. -/
theorem fourFiveSquareMultiples_card (q B : Nat) :
    (fourFiveSquareMultiples q B).card = B / (q * q) := by
  exact Nat.Ioc_filter_dvd_card_eq_div B (q * q)

/-- Reciprocal-square multiple counting gives the sharp elementary bound
`B/y` for the repeated-prime exceptional set. -/
theorem fourFiveRepeatedPrimeSquareSet_card_le_div
    {y A B : Nat} (hy : 0 < y) (hyB : y ≤ B) :
    ((fourFiveRepeatedPrimeSquareSet y A B).card : Real) ≤
      (B : Real) / (y : Real) := by
  have hcardNat : (fourFiveRepeatedPrimeSquareSet y A B).card ≤
      ∑ q ∈ Finset.Ioc y B, B / (q * q) := by
    calc
      (fourFiveRepeatedPrimeSquareSet y A B).card ≤
          ((Finset.Ioc y B).biUnion
            (fun q => fourFiveSquareMultiples q B)).card :=
        Finset.card_le_card
          (fourFiveRepeatedPrimeSquareSet_subset_biUnion_squareMultiples
            y A B)
      _ ≤ ∑ q ∈ Finset.Ioc y B,
          (fourFiveSquareMultiples q B).card := Finset.card_biUnion_le
      _ = ∑ q ∈ Finset.Ioc y B, B / (q * q) := by
        apply Finset.sum_congr rfl
        intro q _hq
        exact fourFiveSquareMultiples_card q B
  have hcardReal :
      ((fourFiveRepeatedPrimeSquareSet y A B).card : Real) ≤
        ∑ q ∈ Finset.Ioc y B, ((B / (q * q) : Nat) : Real) := by
    exact_mod_cast hcardNat
  calc
    ((fourFiveRepeatedPrimeSquareSet y A B).card : Real) ≤
        ∑ q ∈ Finset.Ioc y B, ((B / (q * q) : Nat) : Real) :=
      hcardReal
    _ ≤ ∑ q ∈ Finset.Ioc y B,
        (B : Real) / ((q * q : Nat) : Real) := by
      apply Finset.sum_le_sum
      intro q _hq
      exact Nat.cast_div_le
    _ = ∑ q ∈ Finset.Ioc y B,
        (B : Real) * (((q : Real) ^ 2)⁻¹) := by
      apply Finset.sum_congr rfl
      intro q _hq
      norm_num only [Nat.cast_mul, div_eq_mul_inv, pow_two]
    _ = (B : Real) *
        (∑ q ∈ Finset.Ioc y B, (((q : Real) ^ 2)⁻¹)) := by
      rw [Finset.mul_sum]
    _ ≤ (B : Real) * ((y : Real)⁻¹ - (B : Real)⁻¹) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Ioc_inv_sq_le_sub (α := ℝ) hy.ne' hyB)
        (Nat.cast_nonneg B)
    _ ≤ (B : Real) * (y : Real)⁻¹ := by
      exact mul_le_mul_of_nonneg_left
        (sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg B)))
        (Nat.cast_nonneg B)
    _ = (B : Real) / (y : Real) := by
      rw [div_eq_mul_inv]

/-- The actual nonsquarefree rough interval inherits the same `B/y` bound. -/
theorem fourFiveRoughRepeatedInterval_card_le_div
    {y A B : Nat} (hy : 0 < y) (hyB : y ≤ B) :
    ((fourFiveRoughRepeatedInterval y A B).card : Real) ≤
      (B : Real) / (y : Real) := by
  calc
    ((fourFiveRoughRepeatedInterval y A B).card : Real) ≤
        ((fourFiveRepeatedPrimeSquareSet y A B).card : Real) := by
      exact_mod_cast Finset.card_le_card
        (fourFiveRoughRepeatedInterval_subset_repeatedPrimeSquareSet y A B)
    _ ≤ (B : Real) / (y : Real) :=
      fourFiveRepeatedPrimeSquareSet_card_le_div hy hyB

/-! ## Minimal analytic interface and transfer -/

/-- The remaining analytic assertion, stripped of all finite combinatorics:
the factorially weighted ordered-prime mixture approximates a prescribed main
term with a prescribed error. -/
def FourFiveOrderedPrimeMixtureEstimate
    (y A B : Nat) (mainTerm error : Real) : Prop :=
  abs (fourFiveOrderedPrimeMixture y A B - mainTerm) ≤ error

/-- Transfer an ordered-prime mixture estimate to the ordinary rough count.
The only loss is the explicit repeated-prime cardinality. -/
theorem abs_fourFiveRoughInterval_card_sub_mainTerm_le_of_orderedEstimate
    {y A B : Nat} {mainTerm error : Real}
    (hA : 1 ≤ A) (hB : B < (y + 1) ^ 5)
    (hordered : FourFiveOrderedPrimeMixtureEstimate
      y A B mainTerm error) :
    abs (((fourFiveRoughInterval y A B).card : Real) - mainTerm) ≤
      ((fourFiveRoughRepeatedInterval y A B).card : Real) + error := by
  have hfinite :=
    abs_fourFiveRoughInterval_card_sub_orderedPrimeMixture_le_repeated hA hB
  have hsplit :
      ((fourFiveRoughInterval y A B).card : Real) - mainTerm =
        (((fourFiveRoughInterval y A B).card : Real) -
          fourFiveOrderedPrimeMixture y A B) +
        (fourFiveOrderedPrimeMixture y A B - mainTerm) := by
    ring
  rw [hsplit]
  calc
    abs ((((fourFiveRoughInterval y A B).card : Real) -
          fourFiveOrderedPrimeMixture y A B) +
        (fourFiveOrderedPrimeMixture y A B - mainTerm)) ≤
        abs (((fourFiveRoughInterval y A B).card : Real) -
          fourFiveOrderedPrimeMixture y A B) +
        abs (fourFiveOrderedPrimeMixture y A B - mainTerm) :=
      abs_add_le _ _
    _ ≤ ((fourFiveRoughRepeatedInterval y A B).card : Real) +
        error := add_le_add hfinite hordered

/-- Fully explicit finite reduction: after the ordered-prime estimate, the
remaining combinatorial error is at most `B/y`. -/
theorem abs_fourFiveRoughInterval_card_sub_mainTerm_le_div_add_error
    {y A B : Nat} {mainTerm error : Real}
    (hA : 1 ≤ A) (hB : B < (y + 1) ^ 5)
    (hy : 0 < y) (hyB : y ≤ B)
    (hordered : FourFiveOrderedPrimeMixtureEstimate
      y A B mainTerm error) :
    abs (((fourFiveRoughInterval y A B).card : Real) - mainTerm) ≤
      (B : Real) / (y : Real) + error := by
  exact (abs_fourFiveRoughInterval_card_sub_mainTerm_le_of_orderedEstimate
    hA hB hordered).trans
      (add_le_add
        (fourFiveRoughRepeatedInterval_card_le_div hy hyB) le_rfl)

/-- Simultaneous finite-family form of the reduction.  Arbitrary signed
coefficients are allowed; all cancellation-specific choices of intervals and
weights may therefore be made before invoking the analytic ordered estimate. -/
theorem abs_sum_weighted_fourFiveRoughInterval_sub_mainTerm_le
    {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (y : Nat) (A B : ι -> Nat)
    (gamma mainTerm error : ι -> Real)
    (hy : 0 < y)
    (hA : forall i, i ∈ indices -> 1 ≤ A i)
    (hB : forall i, i ∈ indices -> B i < (y + 1) ^ 5)
    (hyB : forall i, i ∈ indices -> y ≤ B i)
    (hordered : forall i, i ∈ indices ->
      FourFiveOrderedPrimeMixtureEstimate
        y (A i) (B i) (mainTerm i) (error i)) :
    abs (∑ i ∈ indices,
      gamma i *
        (((fourFiveRoughInterval y (A i) (B i)).card : Real) -
          mainTerm i)) ≤
      ∑ i ∈ indices,
        abs (gamma i) * ((B i : Real) / (y : Real) + error i) := by
  calc
    abs (∑ i ∈ indices,
        gamma i *
          (((fourFiveRoughInterval y (A i) (B i)).card : Real) -
            mainTerm i)) ≤
        ∑ i ∈ indices,
          abs (gamma i *
            (((fourFiveRoughInterval y (A i) (B i)).card : Real) -
              mainTerm i)) := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ indices,
        abs (gamma i) *
          abs (((fourFiveRoughInterval y (A i) (B i)).card : Real) -
            mainTerm i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_mul]
    _ ≤ ∑ i ∈ indices,
        abs (gamma i) * ((B i : Real) / (y : Real) + error i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (abs_fourFiveRoughInterval_card_sub_mainTerm_le_div_add_error
          (hA i hi) (hB i hi) hy (hyB i hi) (hordered i hi))
        (abs_nonneg (gamma i))

end

end BankPaperRealization

end Erdos390.WholePaper
