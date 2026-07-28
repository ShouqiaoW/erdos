import Erdos390.WholePaper.FinitePrefixAllocationCapacity
import Erdos390.WholePaper.StationaryPrefixAnchors
import Erdos390.WholePaper.CentralAnchorTailDivisibility

/-!
# Valuation asymptotic of the actual fixed-prefix cofactor product

The cofactor product in this file is the literal product of the cofactors
attached to all realized marker primes in rows one through R.  Its exact
factorization is reduced to the actual part cardinalities, whose already
proved limits give the certified finite-prefix allocation load.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Exact valuation of the cofactor product in one realized row. -/
theorem stationaryPrefixCofactorProduct_factorization
    {r ell : ℕ} (parts : ℕ → Finset ℕ) :
    (stationaryPrefixCofactorProduct r parts).factorization ell =
      ∑ q ∈ infiniteAllocationPositiveSupport r,
        (parts q).card * q.factorization ell := by
  rw [stationaryPrefixCofactorProduct,
    Nat.factorization_prod_apply]
  · rw [stationaryPrefixMarkedPairs, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q _hq
    simp
  · intro x hx
    have hxmem := Finset.mem_sigma.mp hx
    have hqLower :=
      (Finset.mem_Icc.mp
        (mem_infiniteAllocationPositiveSupport.mp hxmem.1).1).1
    omega

theorem stationaryPrefixCofactorProduct_pos
    {r : ℕ} (parts : ℕ → Finset ℕ) :
    0 < stationaryPrefixCofactorProduct r parts := by
  apply Finset.prod_pos
  intro x hx
  have hxmem := Finset.mem_sigma.mp hx
  have hqLower :=
    (Finset.mem_Icc.mp
      (mem_infiniteAllocationPositiveSupport.mp hxmem.1).1).1
  omega

/-- Weighted summation over the positive support is exactly the concrete
allocation row load. -/
theorem sum_infiniteAllocationPositiveSupport_factorization_eq
    (r ell : ℕ) :
    (∑ q ∈ infiniteAllocationPositiveSupport r,
        (q.factorization ell : ℚ) * infiniteAllocation r q) =
      allocationPrimeRowLoad infiniteAllocation ell r := by
  rw [allocationPrimeRowLoad]
  apply Finset.sum_subset
  · intro q hq
    exact (mem_infiniteAllocationPositiveSupport.mp hq).1
  · intro q hq hqNotSupport
    have hnotPos : ¬0 < infiniteAllocation r q := by
      intro hpos
      exact hqNotSupport
        (mem_infiniteAllocationPositiveSupport.mpr ⟨hq, hpos⟩)
    have hzero : infiniteAllocation r q = 0 :=
      le_antisymm (not_lt.mp hnotPos) (infiniteAllocation_nonneg r q)
    simp only [hzero, mul_zero]

/-- The factorization of one actual row cofactor product has the exact
allocation row-load limit. -/
theorem stationaryPrefixCofactorProduct_factorization_normalized_tendsto
    (r ell : ℕ)
    (parts : ℕ → ℕ → Finset ℕ)
    (hparts :
      ∀ q ∈ infiniteAllocationPositiveSupport r,
        Tendsto
          (fun n : ℕ ↦
            ((parts n q).card : ℝ) / secondOrderScale n)
          atTop (nhds (infiniteAllocation r q : ℝ))) :
    Tendsto
      (fun n : ℕ ↦
        (((stationaryPrefixCofactorProduct r (parts n)).factorization
          ell : ℕ) : ℝ) / secondOrderScale n)
      atTop
      (nhds (allocationPrimeRowLoad infiniteAllocation ell r : ℝ)) := by
  have hsum :
      Tendsto
        (fun n : ℕ ↦
          ∑ q ∈ infiniteAllocationPositiveSupport r,
            (q.factorization ell : ℝ) *
              (((parts n q).card : ℝ) / secondOrderScale n))
        atTop
        (nhds
          (∑ q ∈ infiniteAllocationPositiveSupport r,
            (q.factorization ell : ℝ) *
              (infiniteAllocation r q : ℝ))) := by
    apply tendsto_finset_sum
    intro q hq
    exact (hparts q hq).const_mul (q.factorization ell : ℝ)
  have hmass :
      (∑ q ∈ infiniteAllocationPositiveSupport r,
          (q.factorization ell : ℝ) *
            (infiniteAllocation r q : ℝ)) =
        (allocationPrimeRowLoad infiniteAllocation ell r : ℝ) := by
    exact_mod_cast
      sum_infiniteAllocationPositiveSupport_factorization_eq r ell
  rw [hmass] at hsum
  apply hsum.congr'
  exact Eventually.of_forall fun n ↦ by
    dsimp only
    rw [stationaryPrefixCofactorProduct_factorization,
      Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro q _hq
    push_cast
    ring

/-- The product of the actual cofactor products in rows one through R. -/
def stationaryPrefixCofactorProductUpTo
    (R : ℕ)
    (parts :
      {r // r ∈ Finset.Icc 1 R} → ℕ → Finset ℕ) : ℕ :=
  ∏ r : {r // r ∈ Finset.Icc 1 R},
    stationaryPrefixCofactorProduct r.1 (parts r)

/-- Exact factorization of the finite-row product as the sum of the exact
row-product factorizations. -/
theorem stationaryPrefixCofactorProductUpTo_factorization
    (R ell : ℕ)
    (parts :
      {r // r ∈ Finset.Icc 1 R} → ℕ → Finset ℕ) :
    (stationaryPrefixCofactorProductUpTo R parts).factorization ell =
      ∑ r : {r // r ∈ Finset.Icc 1 R},
        (stationaryPrefixCofactorProduct r.1
          (parts r)).factorization ell := by
  rw [stationaryPrefixCofactorProductUpTo,
    Nat.factorization_prod_apply]
  intro r _hr
  exact (stationaryPrefixCofactorProduct_pos (parts r)).ne'

/-- The finite subtype sum of row loads is the literal prefix load. -/
theorem sum_allocationPrimeRowLoad_subtype_eq_prefix
    (R ell : ℕ) :
    (∑ r : {r // r ∈ Finset.Icc 1 R},
        allocationPrimeRowLoad infiniteAllocation ell r.1) =
      prefixAllocationPrimeLoad R ell := by
  rw [prefixAllocationPrimeLoad]
  change
    (∑ r : {r // r ∈ Finset.Icc 1 R},
      allocationPrimeRowLoad infiniteAllocation ell r.1) =
      ∑ r ∈ Finset.Icc 1 R,
        allocationPrimeRowLoad infiniteAllocation ell r
  simpa only [Finset.univ_eq_attach] using
    (Finset.sum_attach (Finset.Icc 1 R)
      (fun r ↦ allocationPrimeRowLoad infiniteAllocation ell r))

/-- The factorization of the actual finite-row cofactor product converges
to the certified concrete prefix allocation load. -/
theorem stationaryPrefixCofactorProductUpTo_factorization_normalized_tendsto
    (R ell : ℕ)
    (parts :
      ℕ → {r // r ∈ Finset.Icc 1 R} → ℕ → Finset ℕ)
    (hparts :
      ∀ r : {r // r ∈ Finset.Icc 1 R},
        ∀ q ∈ infiniteAllocationPositiveSupport r.1,
          Tendsto
            (fun n : ℕ ↦
              ((parts n r q).card : ℝ) / secondOrderScale n)
            atTop (nhds (infiniteAllocation r.1 q : ℝ))) :
    Tendsto
      (fun n : ℕ ↦
        (((stationaryPrefixCofactorProductUpTo R
          (parts n)).factorization ell : ℕ) : ℝ) /
            secondOrderScale n)
      atTop (nhds (prefixAllocationPrimeLoad R ell : ℝ)) := by
  have hrows :
      Tendsto
        (fun n : ℕ ↦
          ∑ r : {r // r ∈ Finset.Icc 1 R},
            (((stationaryPrefixCofactorProduct r.1
              (parts n r)).factorization ell : ℕ) : ℝ) /
                secondOrderScale n)
        atTop
        (nhds
          (∑ r : {r // r ∈ Finset.Icc 1 R},
            (allocationPrimeRowLoad infiniteAllocation ell r.1 : ℝ))) := by
    apply tendsto_finset_sum
    intro r _hr
    exact
      stationaryPrefixCofactorProduct_factorization_normalized_tendsto
        r.1 ell (fun n q ↦ parts n r q) (hparts r)
  have hmass :
      (∑ r : {r // r ∈ Finset.Icc 1 R},
          (allocationPrimeRowLoad infiniteAllocation ell r.1 : ℝ)) =
        (prefixAllocationPrimeLoad R ell : ℝ) := by
    exact_mod_cast sum_allocationPrimeRowLoad_subtype_eq_prefix R ell
  rw [hmass] at hrows
  apply hrows.congr'
  exact Eventually.of_forall fun n ↦ by
    dsimp only
    rw [stationaryPrefixCofactorProductUpTo_factorization,
      Nat.cast_sum, Finset.sum_div]

/-- The certified capacity gives an eventual real bound for the
factorization of the actual cofactor product. -/
theorem eventually_stationaryPrefixCofactorProductUpTo_factorization_le_real
    (R : ℕ) {ell : ℕ} (hellPrime : ell.Prime)
    {slack : ℝ} (hslack : 0 < slack)
    (parts :
      ℕ → {r // r ∈ Finset.Icc 1 R} → ℕ → Finset ℕ)
    (hparts :
      ∀ r : {r // r ∈ Finset.Icc 1 R},
        ∀ q ∈ infiniteAllocationPositiveSupport r.1,
          Tendsto
            (fun n : ℕ ↦
              ((parts n r q).card : ℝ) / secondOrderScale n)
            atTop (nhds (infiniteAllocation r.1 q : ℝ))) :
    ∀ᶠ n : ℕ in atTop,
      (((stationaryPrefixCofactorProductUpTo R
        (parts n)).factorization ell : ℕ) : ℝ) ≤
        ((C0 + slack) / (((ell - 1 : ℕ) : ℝ))) *
          secondOrderScale n := by
  have htendsto :=
    stationaryPrefixCofactorProductUpTo_factorization_normalized_tendsto
      R ell parts hparts
  have hdenominatorNat : 0 < ell - 1 := by
    have := hellPrime.two_le
    omega
  have hdenominator : 0 < (((ell - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hdenominatorNat
  have hcapacity :
      (prefixAllocationPrimeLoad R ell : ℝ) ≤
        C0 / (((ell - 1 : ℕ) : ℝ)) := by
    rw [C0_eq_ratCast_C0Rat]
    exact_mod_cast prefixAllocationPrimeLoad_le_capacity R hellPrime
  have hstrict :
      (prefixAllocationPrimeLoad R ell : ℝ) <
        (C0 + slack) / (((ell - 1 : ℕ) : ℝ)) := by
    refine hcapacity.trans_lt ?_
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_lt_mul_of_pos_right
      (lt_add_of_pos_right C0 hslack) (inv_pos.mpr hdenominator)
  have hnormalized :=
    htendsto.eventually (eventually_lt_nhds hstrict)
  filter_upwards [hnormalized, eventually_secondOrderScale_pos] with n
    hn hscale
  exact ((div_lt_iff₀ hscale).mp hn).le

/-- Natural-number floor form of the same actual-product capacity bound. -/
theorem eventually_stationaryPrefixCofactorProductUpTo_factorization_le_nat
    (R : ℕ) {ell : ℕ} (hellPrime : ell.Prime)
    {slack : ℝ} (hslack : 0 < slack)
    (parts :
      ℕ → {r // r ∈ Finset.Icc 1 R} → ℕ → Finset ℕ)
    (hparts :
      ∀ r : {r // r ∈ Finset.Icc 1 R},
        ∀ q ∈ infiniteAllocationPositiveSupport r.1,
          Tendsto
            (fun n : ℕ ↦
              ((parts n r q).card : ℝ) / secondOrderScale n)
            atTop (nhds (infiniteAllocation r.1 q : ℝ))) :
    ∀ᶠ n : ℕ in atTop,
      (stationaryPrefixCofactorProductUpTo R
        (parts n)).factorization ell ≤
        ⌊((C0 + slack) / (((ell - 1 : ℕ) : ℝ))) *
          secondOrderScale n⌋₊ := by
  filter_upwards [
    eventually_stationaryPrefixCofactorProductUpTo_factorization_le_real
      R hellPrime hslack parts hparts] with n hn
  exact Nat.le_floor hn

/-- The actual cofactor-product capacity bounds hold simultaneously for
every fixed prime in the complete cofactor range through row R. -/
theorem
    eventually_stationaryPrefixCofactorProductUpTo_factorization_le_on_primesUpTo
    (R : ℕ) {slack : ℝ} (hslack : 0 < slack)
    (parts :
      ℕ → {r // r ∈ Finset.Icc 1 R} → ℕ → Finset ℕ)
    (hparts :
      ∀ r : {r // r ∈ Finset.Icc 1 R},
        ∀ q ∈ infiniteAllocationPositiveSupport r.1,
          Tendsto
            (fun n : ℕ ↦
              ((parts n r q).card : ℝ) / secondOrderScale n)
            atTop (nhds (infiniteAllocation r.1 q : ℝ))) :
    ∀ᶠ n : ℕ in atTop,
      ∀ ell ∈ primesUpTo (2 * R + 1),
        ((((stationaryPrefixCofactorProductUpTo R
          (parts n)).factorization ell : ℕ) : ℝ) ≤
            ((C0 + slack) / (((ell - 1 : ℕ) : ℝ))) *
              secondOrderScale n) ∧
          ((stationaryPrefixCofactorProductUpTo R
            (parts n)).factorization ell ≤
              ⌊((C0 + slack) / (((ell - 1 : ℕ) : ℝ))) *
                secondOrderScale n⌋₊) := by
  rw [Finset.eventually_all]
  intro ell hell
  have hellPrime := (mem_primesUpTo.mp hell).1
  filter_upwards [
    eventually_stationaryPrefixCofactorProductUpTo_factorization_le_real
      R hellPrime hslack parts hparts,
    eventually_stationaryPrefixCofactorProductUpTo_factorization_le_nat
      R hellPrime hslack parts hparts] with n hreal hnat
  exact ⟨hreal, hnat⟩

/-- Terminal connector: the simultaneous actual partitions, their concrete
cofactor product limit, and both certified capacity bounds are obtained
together. -/
theorem exists_stationaryPrefixParts_with_valuation_capacity
    (R : ℕ) (distinguished : ℕ → ℕ)
    (hdistinguished :
      ∀ r ∈ Finset.Icc 1 R,
        distinguished r ∈ infiniteAllocationPositiveSupport r)
    {ell : ℕ} (hellPrime : ell.Prime)
    {slack : ℝ} (hslack : 0 < slack) :
    ∃ parts :
        ℕ → {r // r ∈ Finset.Icc 1 R} → ℕ → Finset ℕ,
      (∀ᶠ n : ℕ in atTop,
        ∀ r : {r // r ∈ Finset.Icc 1 R},
          (∀ q ∈ infiniteAllocationPositiveSupport r.1,
            parts n r q ⊆ stationaryPrimeLayer n r.1) ∧
          (∀ q ∈ infiniteAllocationPositiveSupport r.1,
            (parts n r q).card =
              stationaryPrefixCount n r.1 (distinguished r.1) q) ∧
          (infiniteAllocationPositiveSupport r.1 :
            Set ℕ).PairwiseDisjoint (parts n r) ∧
          (infiniteAllocationPositiveSupport r.1).biUnion
              (parts n r) =
            stationaryPrimeLayer n r.1) ∧
      Tendsto
        (fun n : ℕ ↦
          (((stationaryPrefixCofactorProductUpTo R
            (parts n)).factorization ell : ℕ) : ℝ) /
              secondOrderScale n)
        atTop (nhds (prefixAllocationPrimeLoad R ell : ℝ)) ∧
      (∀ᶠ n : ℕ in atTop,
        (((stationaryPrefixCofactorProductUpTo R
          (parts n)).factorization ell : ℕ) : ℝ) ≤
          ((C0 + slack) / (((ell - 1 : ℕ) : ℝ))) *
            secondOrderScale n) ∧
      (∀ᶠ n : ℕ in atTop,
        (stationaryPrefixCofactorProductUpTo R
          (parts n)).factorization ell ≤
          ⌊((C0 + slack) / (((ell - 1 : ℕ) : ℝ))) *
            secondOrderScale n⌋₊) := by
  obtain ⟨parts, hactual, hparts⟩ :=
    exists_stationaryPrefixParts_on_finset
      (Finset.Icc 1 R) (fun r hr ↦ (Finset.mem_Icc.mp hr).1)
      distinguished hdistinguished
  have htendsto :=
    stationaryPrefixCofactorProductUpTo_factorization_normalized_tendsto
      R ell parts hparts
  exact ⟨parts, hactual, htendsto,
    eventually_stationaryPrefixCofactorProductUpTo_factorization_le_real
      R hellPrime hslack parts hparts,
    eventually_stationaryPrefixCofactorProductUpTo_factorization_le_nat
      R hellPrime hslack parts hparts⟩

end

end Erdos390.WholePaper
