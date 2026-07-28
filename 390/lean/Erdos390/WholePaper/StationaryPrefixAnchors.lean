import Erdos390.WholePaper.CentralCarryAnchors
import Erdos390.WholePaper.StationaryPrefixRealization
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Simultaneous fixed-prefix rows and their central anchors

The analytic realization is first made simultaneous over an arbitrary
finite set of fixed rows.  For one realized row, the marked pairs
(cofactor, prime) are then sent to the literal anchor prime times cofactor.
The map is injective once the stationary primes exceed the cofactor range,
and its finite product splits exactly into marker and cofactor products.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Any finite collection of fixed positive rows can be realized
simultaneously by a single family of stationary-layer partitions. -/
theorem exists_stationaryPrefixParts_on_finset
    (rows : Finset ℕ)
    (hrows : ∀ r ∈ rows, 1 ≤ r)
    (distinguished : ℕ → ℕ)
    (hdistinguished :
      ∀ r ∈ rows,
        distinguished r ∈ infiniteAllocationPositiveSupport r) :
    ∃ parts :
        ℕ → {r // r ∈ rows} → ℕ → Finset ℕ,
      (∀ᶠ n : ℕ in atTop,
        ∀ r : {r // r ∈ rows},
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
      ∀ r : {r // r ∈ rows},
        ∀ q ∈ infiniteAllocationPositiveSupport r.1,
          Tendsto
            (fun n : ℕ ↦
              ((parts n r q).card : ℝ) / secondOrderScale n)
            atTop (nhds (infiniteAllocation r.1 q : ℝ)) := by
  have hexists (r : {r // r ∈ rows}) :=
    exists_stationaryPrefixParts r.1 (distinguished r.1)
      (hrows r.1 r.2) (hdistinguished r.1 r.2)
  choose rowParts hrowParts hrowLimit using hexists
  let parts : ℕ → {r // r ∈ rows} → ℕ → Finset ℕ :=
    fun n r q ↦ rowParts r n q
  refine ⟨parts, ?_, ?_⟩
  · rw [Filter.eventually_all]
    intro r
    simpa only [parts] using hrowParts r
  · intro r q hq
    simpa only [parts] using hrowLimit r q hq

/-- The finite type of marked pairs in one realized stationary row. -/
def stationaryPrefixMarkedPairs
    (r : ℕ) (parts : ℕ → Finset ℕ) :
    Finset (Σ _q : ℕ, ℕ) :=
  (infiniteAllocationPositiveSupport r).sigma parts

/-- The literal prefix anchor attached to a marked pair. -/
def stationaryPrefixAnchor (x : Σ _q : ℕ, ℕ) : ℕ :=
  x.2 * x.1

/-- The honest finite set of prefix anchors. -/
def stationaryPrefixAnchors
    (r : ℕ) (parts : ℕ → Finset ℕ) : Finset ℕ :=
  (stationaryPrefixMarkedPairs r parts).image stationaryPrefixAnchor

/-- Product of the marker primes appearing in the marked pairs. -/
def stationaryPrefixMarkerProduct
    (r : ℕ) (parts : ℕ → Finset ℕ) : ℕ :=
  (stationaryPrefixMarkedPairs r parts).prod fun x ↦ x.2

/-- Product of their assigned allocation cofactors. -/
def stationaryPrefixCofactorProduct
    (r : ℕ) (parts : ℕ → Finset ℕ) : ℕ :=
  (stationaryPrefixMarkedPairs r parts).prod fun x ↦ x.1

/-- A simple fixed threshold makes every prime in row r larger than the
complete row-r cofactor range. -/
theorem stationaryPrimeLayer_gt_cofactorRange
    {n r p : ℕ}
    (hn : (2 * r + 1) * (r + 1) ≤ n)
    (hp : p ∈ stationaryPrimeLayer n r) :
    2 * r + 1 < p := by
  by_contra hnot
  have hpLe : p ≤ 2 * r + 1 := Nat.le_of_not_gt hnot
  have hproduct :
      p * (r + 1) ≤ (2 * r + 1) * (r + 1) :=
    Nat.mul_le_mul_right (r + 1) hpLe
  exact (Nat.not_lt_of_ge (hproduct.trans hn))
    (mem_stationaryPrimeLayer.mp hp).2.1

/-- Every anchor made from a realized row lies in the central interval. -/
theorem stationaryPrefixAnchor_mem_centralInterval
    {n r : ℕ} {parts : ℕ → Finset ℕ}
    (hparts :
      ∀ q ∈ infiniteAllocationPositiveSupport r,
        parts q ⊆ stationaryPrimeLayer n r)
    {x : Σ _q : ℕ, ℕ}
    (hx : x ∈ stationaryPrefixMarkedPairs r parts) :
    stationaryPrefixAnchor x ∈ Finset.Ioc n (2 * n) := by
  have hxmem := Finset.mem_sigma.mp hx
  have hqRange :=
    Finset.mem_Icc.mp
      (mem_infiniteAllocationPositiveSupport.mp hxmem.1).1
  exact stationaryPrimeLayer_mul_cofactor_mem_centralInterval
    (hparts x.1 hxmem.1 hxmem.2) hqRange.1 hqRange.2

/-- The marker prime and its cofactor are both recovered from an anchor;
in particular, the anchor map is collision-free on all marked pairs. -/
theorem stationaryPrefixAnchor_injOn
    {n r : ℕ} {parts : ℕ → Finset ℕ}
    (hn : (2 * r + 1) * (r + 1) ≤ n)
    (hparts :
      ∀ q ∈ infiniteAllocationPositiveSupport r,
        parts q ⊆ stationaryPrimeLayer n r) :
    Set.InjOn stationaryPrefixAnchor
      (stationaryPrefixMarkedPairs r parts) := by
  intro x hx y hy hxy
  have hxmem := Finset.mem_sigma.mp hx
  have hymem := Finset.mem_sigma.mp hy
  have hxLayer := hparts x.1 hxmem.1 hxmem.2
  have hyLayer := hparts y.1 hymem.1 hymem.2
  have hxPrime := (mem_stationaryPrimeLayer.mp hxLayer).1
  have hyPrime := (mem_stationaryPrimeLayer.mp hyLayer).1
  have hyRange :=
    Finset.mem_Icc.mp
      (mem_infiniteAllocationPositiveSupport.mp hymem.1).1
  have hyPos : 0 < y.1 := by omega
  have hproduct :
      x.2 * x.1 = y.2 * y.1 := by
    simpa only [stationaryPrefixAnchor] using hxy
  obtain ⟨hmarker, hcofactor⟩ :=
    prime_mul_cofactor_eq_iff_of_marker_large
      hxPrime hyPrime
      (stationaryPrimeLayer_gt_cofactorRange hn hxLayer)
      hyPos hyRange.2 hproduct
  cases x with
  | mk xq xp =>
      cases y with
      | mk yq yp =>
          simp only at hmarker hcofactor
          subst yp
          subst yq
          rfl

theorem stationaryPrefixAnchors_subset_centralInterval
    {n r : ℕ} {parts : ℕ → Finset ℕ}
    (hparts :
      ∀ q ∈ infiniteAllocationPositiveSupport r,
        parts q ⊆ stationaryPrimeLayer n r) :
    stationaryPrefixAnchors r parts ⊆ Finset.Ioc n (2 * n) := by
  intro a ha
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  exact stationaryPrefixAnchor_mem_centralInterval hparts hx

theorem stationaryPrefixAnchors_card
    {n r : ℕ} {parts : ℕ → Finset ℕ}
    (hn : (2 * r + 1) * (r + 1) ≤ n)
    (hparts :
      ∀ q ∈ infiniteAllocationPositiveSupport r,
        parts q ⊆ stationaryPrimeLayer n r) :
    (stationaryPrefixAnchors r parts).card =
      (stationaryPrefixMarkedPairs r parts).card := by
  exact Finset.card_image_of_injOn
    (stationaryPrefixAnchor_injOn hn hparts)

/-- Exact product identity for the collision-free prefix-anchor set. -/
theorem stationaryPrefixAnchors_prod
    {n r : ℕ} {parts : ℕ → Finset ℕ}
    (hn : (2 * r + 1) * (r + 1) ≤ n)
    (hparts :
      ∀ q ∈ infiniteAllocationPositiveSupport r,
        parts q ⊆ stationaryPrimeLayer n r) :
    (stationaryPrefixAnchors r parts).prod id =
      stationaryPrefixMarkerProduct r parts *
        stationaryPrefixCofactorProduct r parts := by
  rw [stationaryPrefixAnchors,
    Finset.prod_image (stationaryPrefixAnchor_injOn hn hparts)]
  simp only [id_eq, stationaryPrefixAnchor,
    stationaryPrefixMarkerProduct, stationaryPrefixCofactorProduct,
    Finset.prod_mul_distrib]

/-- A realized stationary partition therefore supplies an interval-valued,
collision-free anchor set with the literal product identity. -/
theorem StationaryPrefixPartition.anchor_certificate
    {n r distinguished : ℕ}
    (partition : StationaryPrefixPartition n r distinguished)
    (hn : (2 * r + 1) * (r + 1) ≤ n) :
    stationaryPrefixAnchors r partition.parts ⊆
        Finset.Ioc n (2 * n) ∧
      (stationaryPrefixAnchors r partition.parts).card =
        (stationaryPrefixMarkedPairs r partition.parts).card ∧
      (stationaryPrefixAnchors r partition.parts).prod id =
        stationaryPrefixMarkerProduct r partition.parts *
          stationaryPrefixCofactorProduct r partition.parts := by
  exact ⟨stationaryPrefixAnchors_subset_centralInterval
      partition.parts_subset,
    stationaryPrefixAnchors_card hn partition.parts_subset,
    stationaryPrefixAnchors_prod hn partition.parts_subset⟩

end

end Erdos390.WholePaper
