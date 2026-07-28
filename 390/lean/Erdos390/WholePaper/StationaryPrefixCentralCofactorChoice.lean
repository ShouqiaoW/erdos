import Erdos390.WholePaper.CentralAnchorCutoff
import Erdos390.WholePaper.StationaryPrefixValuationAsymptotic

/-!
# Actual fixed-prefix cofactor routing at the central-anchor cutoff

An exhaustive family of stationary-row partitions determines a literal
cofactor for every large central prime.  Row-zero primes receive cofactor
one.  A prime in a positive fixed row receives the unique label of the
partition part containing it.  This file proves that the resulting total
function is an admissible large-central cofactor choice and that its honest
large-cofactor product is exactly the previously analyzed fixed-prefix
product.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The finite subtype of positive stationary rows through `R`. -/
abbrev StationaryPrefixRow (R : ℕ) :=
  {r : ℕ // r ∈ Finset.Icc 1 R}

/-- The routing data needed from simultaneous exact prefix partitions. -/
def IsStationaryPrefixPartFamily
    (R n : ℕ)
    (parts : StationaryPrefixRow R → ℕ → Finset ℕ) : Prop :=
  ∀ r : StationaryPrefixRow R,
    (∀ q ∈ infiniteAllocationPositiveSupport r.1,
      parts r q ⊆ stationaryPrimeLayer n r.1) ∧
    (infiniteAllocationPositiveSupport r.1 : Set ℕ).PairwiseDisjoint
      (parts r) ∧
    (infiniteAllocationPositiveSupport r.1).biUnion (parts r) =
      stationaryPrimeLayer n r.1

/-- The full realization certificate supplies the smaller routing API. -/
theorem isStationaryPrefixPartFamily_of_realization
    {R n : ℕ} {distinguished : ℕ → ℕ}
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    (hparts :
      ∀ r : StationaryPrefixRow R,
        (∀ q ∈ infiniteAllocationPositiveSupport r.1,
          parts r q ⊆ stationaryPrimeLayer n r.1) ∧
        (∀ q ∈ infiniteAllocationPositiveSupport r.1,
          (parts r q).card =
            stationaryPrefixCount n r.1 (distinguished r.1) q) ∧
        (infiniteAllocationPositiveSupport r.1 : Set ℕ).PairwiseDisjoint
          (parts r) ∧
        (infiniteAllocationPositiveSupport r.1).biUnion (parts r) =
          stationaryPrimeLayer n r.1) :
    IsStationaryPrefixPartFamily R n parts := by
  intro r
  exact ⟨(hparts r).1, (hparts r).2.2.1, (hparts r).2.2.2⟩

/-- The total cofactor function read from a realized fixed-prefix
partition.  Its fallback branches are irrelevant once the realization and
cutoff hypotheses hold, but make the definition total for every natural
marker. -/
noncomputable def stationaryPrefixCofactorChoice
    (R n : ℕ)
    (parts : StationaryPrefixRow R → ℕ → Finset ℕ)
    (p : ℕ) : ℕ :=
  if n < p then
    1
  else
    dite (n / p ∈ Finset.Icc 1 R)
      (fun hrow ↦
        dite
          (∃ q ∈ infiniteAllocationPositiveSupport (n / p),
            p ∈ parts ⟨n / p, hrow⟩ q)
          (fun hq ↦ Classical.choose hq)
          (fun _ ↦ 1))
      (fun _ ↦ 1)

theorem stationaryPrefixCofactorChoice_eq_one_of_rowZero
    {R n : ℕ}
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    {p : ℕ} (hp : n < p) :
    stationaryPrefixCofactorChoice R n parts p = 1 := by
  simp only [stationaryPrefixCofactorChoice, if_pos hp]

/-- In a positive row, the choice really belongs to the selected part. -/
theorem stationaryPrefixCofactorChoice_spec
    {R n : ℕ}
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    {p : ℕ} (hp : ¬n < p)
    (hrow : n / p ∈ Finset.Icc 1 R)
    (hmem :
      ∃ q ∈ infiniteAllocationPositiveSupport (n / p),
        p ∈ parts ⟨n / p, hrow⟩ q) :
    stationaryPrefixCofactorChoice R n parts p ∈
        infiniteAllocationPositiveSupport (n / p) ∧
      p ∈ parts ⟨n / p, hrow⟩
        (stationaryPrefixCofactorChoice R n parts p) := by
  rw [stationaryPrefixCofactorChoice, if_neg hp,
    dif_pos hrow, dif_pos hmem]
  exact Classical.choose_spec hmem

/-- Pairwise disjointness makes the cofactor attached to a marker in a
specified part equal to that part's label. -/
theorem stationaryPrefixCofactorChoice_eq_of_mem_part
    {R n : ℕ}
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    (hparts : IsStationaryPrefixPartFamily R n parts)
    {r : StationaryPrefixRow R} {q p : ℕ}
    (hq : q ∈ infiniteAllocationPositiveSupport r.1)
    (hp : p ∈ parts r q) :
    stationaryPrefixCofactorChoice R n parts p = q := by
  have hpLayer : p ∈ stationaryPrimeLayer n r.1 :=
    (hparts r).1 q hq hp
  have hfloor := stationaryPrimeLayer_floor_values hpLayer
  have hrPos : 1 ≤ r.1 := (Finset.mem_Icc.mp r.2).1
  have hnotRowZero : ¬n < p := by
    intro hnp
    have hzero : n / p = 0 := Nat.div_eq_of_lt hnp
    omega
  have hrow : n / p ∈ Finset.Icc 1 R := by
    simpa only [hfloor.1] using r.2
  let row' : StationaryPrefixRow R := ⟨n / p, hrow⟩
  have hrowEq : row' = r := by
    apply Subtype.ext
    exact hfloor.1
  have hqRow' :
      q ∈ infiniteAllocationPositiveSupport (n / p) := by
    simpa only [hfloor.1] using hq
  have hpRow' : p ∈ parts row' q := by
    simpa only [hrowEq] using hp
  have hmem :
      ∃ q' ∈ infiniteAllocationPositiveSupport (n / p),
        p ∈ parts row' q' :=
    ⟨q, hqRow', hpRow'⟩
  have hchosen := stationaryPrefixCofactorChoice_spec
    hnotRowZero hrow hmem
  exact (hparts row').2.1.elim_finset
    hchosen.1 hqRow' p hchosen.2 hpRow'

/-- All marked `(row, cofactor, prime)` triples in the fixed prefix. -/
def stationaryPrefixMarkedTriples
    (R : ℕ)
    (parts : StationaryPrefixRow R → ℕ → Finset ℕ) :
    Finset (Σ _r : StationaryPrefixRow R, Σ _q : ℕ, ℕ) :=
  (Finset.univ : Finset (StationaryPrefixRow R)).sigma
    (fun r ↦ stationaryPrefixMarkedPairs r.1 (parts r))

@[simp]
theorem mem_stationaryPrefixMarkedTriples
    {R : ℕ}
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    {x : Σ _r : StationaryPrefixRow R, Σ _q : ℕ, ℕ} :
    x ∈ stationaryPrefixMarkedTriples R parts ↔
      x.2.1 ∈ infiniteAllocationPositiveSupport x.1.1 ∧
        x.2.2 ∈ parts x.1 x.2.1 := by
  simp only [stationaryPrefixMarkedTriples,
    stationaryPrefixMarkedPairs, Finset.mem_sigma, Finset.mem_univ,
    true_and]

/-- The nested marked-triple product is definitionally the row-by-row
cofactor product. -/
theorem stationaryPrefixMarkedTriples_prod_cofactor
    (R : ℕ)
    (parts : StationaryPrefixRow R → ℕ → Finset ℕ) :
    (stationaryPrefixMarkedTriples R parts).prod
        (fun x ↦ x.2.1) =
      stationaryPrefixCofactorProductUpTo R parts := by
  rw [stationaryPrefixMarkedTriples, Finset.prod_sigma]
  simp only [stationaryPrefixCofactorProductUpTo,
    stationaryPrefixCofactorProduct]

/-- Every marked triple yields a positive-row large central prime. -/
theorem stationaryPrefixMarkedTriple_marker_mem_largeCentralPrimes
    {R n : ℕ}
    (hn : centralAnchorCutoffThreshold R ≤ n)
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    (hparts : IsStationaryPrefixPartFamily R n parts)
    {x : Σ _r : StationaryPrefixRow R, Σ _q : ℕ, ℕ}
    (hx : x ∈ stationaryPrefixMarkedTriples R parts) :
    x.2.2 ∈
      (largeCentralPrimes n (centralAnchorCutoff R n)).filter
        (fun p ↦ p ≤ n) := by
  have hxmem := mem_stationaryPrefixMarkedTriples.mp hx
  have hpLayer : x.2.2 ∈ stationaryPrimeLayer n x.1.1 :=
    (hparts x.1).1 x.2.1 hxmem.1 hxmem.2
  have hpPrime := (mem_stationaryPrimeLayer.mp hpLayer).1
  have hrUpper : x.1.1 ≤ R := (Finset.mem_Icc.mp x.1.2).2
  have hpCutoff : centralAnchorCutoff R n < x.2.2 := by
    by_contra hnot
    have hpLe : x.2.2 ≤ centralAnchorCutoff R n :=
      Nat.le_of_not_gt hnot
    have hproduct : x.2.2 * (x.1.1 + 1) ≤ n := by
      calc
        x.2.2 * (x.1.1 + 1) ≤
            centralAnchorCutoff R n * (x.1.1 + 1) :=
          Nat.mul_le_mul_right (x.1.1 + 1) hpLe
        _ ≤ centralAnchorCutoff R n * (R + 1) :=
          Nat.mul_le_mul_left (centralAnchorCutoff R n)
            (Nat.succ_le_succ hrUpper)
        _ ≤ n := by
          simpa only [centralAnchorCutoff] using
            Nat.div_mul_le_self n (R + 1)
    exact (Nat.not_lt_of_ge hproduct)
      (mem_stationaryPrimeLayer.mp hpLayer).2.1
  have hpSq : 2 * n < x.2.2 ^ 2 :=
    (two_mul_lt_centralAnchorCutoff_sq hn).trans
      (Nat.pow_lt_pow_left hpCutoff (by decide : 2 ≠ 0))
  have hnPos : 0 < n :=
    (centralAnchorCutoffThreshold_pos R).trans_le hn
  have hpFactorization :
      (Nat.choose (2 * n) n).factorization x.2.2 = 1 :=
    centralChoose_factorization_eq_one_of_mem_stationaryPrimeLayer_of_sq
      hnPos hpLayer hpSq
  have hchooseNe : Nat.choose (2 * n) n ≠ 0 :=
    (Nat.choose_pos (by omega)).ne'
  have hpDvd : x.2.2 ∣ Nat.choose (2 * n) n :=
    (hpPrime.dvd_iff_one_le_factorization hchooseNe).mpr (by
      rw [hpFactorization])
  have hpFactors : x.2.2 ∈ (Nat.choose (2 * n) n).primeFactors :=
    hpPrime.mem_primeFactors hpDvd hchooseNe
  have hpLarge :
      x.2.2 ∈ largeCentralPrimes n (centralAnchorCutoff R n) := by
    exact Finset.mem_filter.mpr ⟨hpFactors, hpCutoff⟩
  have hpLeN : x.2.2 ≤ n := by
    by_contra hnot
    have hnp : n < x.2.2 := Nat.lt_of_not_ge hnot
    have hzero : n / x.2.2 = 0 := Nat.div_eq_of_lt hnp
    have hfloor := stationaryPrimeLayer_floor_values hpLayer
    have hrPos : 1 ≤ x.1.1 := (Finset.mem_Icc.mp x.1.2).1
    omega
  exact Finset.mem_filter.mpr ⟨hpLarge, hpLeN⟩

/-- Marker primes determine their row, and pairwise disjointness then
determines their cofactor label. -/
theorem stationaryPrefixMarkedTriple_marker_injOn
    {R n : ℕ}
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    (hparts : IsStationaryPrefixPartFamily R n parts) :
    Set.InjOn
      (fun x : Σ _r : StationaryPrefixRow R, Σ _q : ℕ, ℕ ↦ x.2.2)
      (stationaryPrefixMarkedTriples R parts) := by
  rintro ⟨rx, ⟨qx, px⟩⟩ hx ⟨ry, ⟨qy, py⟩⟩ hy hmarker
  have hxmem := mem_stationaryPrefixMarkedTriples.mp hx
  have hymem := mem_stationaryPrefixMarkedTriples.mp hy
  have hxLayer : px ∈ stationaryPrimeLayer n rx.1 :=
    (hparts rx).1 qx hxmem.1 hxmem.2
  have hyLayer : py ∈ stationaryPrimeLayer n ry.1 :=
    (hparts ry).1 qy hymem.1 hymem.2
  change px = py at hmarker
  have hrEq : rx = ry := by
    apply Subtype.ext
    rw [← (stationaryPrimeLayer_floor_values hxLayer).1,
      ← (stationaryPrimeLayer_floor_values hyLayer).1, hmarker]
  subst ry
  subst py
  have hqEq : qx = qy :=
    (hparts rx).2.1.elim_finset
      hxmem.1 hymem.1 px hxmem.2 hymem.2
  subst qy
  rfl

/-- Conversely, every positive-row large central prime occurs in exactly
one marked triple. -/
theorem exists_stationaryPrefixMarkedTriple_of_mem_largeCentralPrimes
    {R n : ℕ}
    (hn : centralAnchorCutoffThreshold R ≤ n)
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    (hparts : IsStationaryPrefixPartFamily R n parts)
    {p : ℕ}
    (hp : p ∈
      (largeCentralPrimes n (centralAnchorCutoff R n)).filter
        (fun marker ↦ marker ≤ n)) :
    ∃ x ∈ stationaryPrefixMarkedTriples R parts, x.2.2 = p := by
  have hpFilter := Finset.mem_filter.mp hp
  have hroute := largeCentralPrime_rowZero_or_fixedPrefix hn hpFilter.1
  rcases hroute.2 with hzero |
      ⟨r, hrPos, hrUpper, _hr, hpLayer⟩
  · omega
  · let row : StationaryPrefixRow R :=
      ⟨r, Finset.mem_Icc.mpr ⟨hrPos, hrUpper⟩⟩
    have hpUnion :
        p ∈ (infiniteAllocationPositiveSupport row.1).biUnion
          (parts row) := by
      rw [(hparts row).2.2]
      simpa only [row] using hpLayer
    obtain ⟨q, hq, hpPart⟩ := Finset.mem_biUnion.mp hpUnion
    refine ⟨⟨row, ⟨q, p⟩⟩, ?_, rfl⟩
    exact mem_stationaryPrefixMarkedTriples.mpr ⟨hq, hpPart⟩

/-- The realized total function follows the complete row-zero/fixed-prefix
routing specification. -/
theorem stationaryPrefixCofactorChoice_isLargeCentralCofactorChoice
    {R n : ℕ}
    (hn : centralAnchorCutoffThreshold R ≤ n)
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    (hparts : IsStationaryPrefixPartFamily R n parts) :
    IsLargeCentralCofactorChoice n (centralAnchorCutoff R n)
      (stationaryPrefixCofactorChoice R n parts) := by
  intro p hp
  have hroute := largeCentralPrime_rowZero_or_fixedPrefix hn hp
  rcases hroute.2 with hzero |
      ⟨r, hrPos, hrUpper, hr, hpLayer⟩
  · exact Or.inl ⟨hzero.1, hzero.2,
      stationaryPrefixCofactorChoice_eq_one_of_rowZero hzero.1⟩
  · have hnotRowZero : ¬n < p := by
      intro hnp
      have hzero : n / p = 0 := Nat.div_eq_of_lt hnp
      omega
    have hrow : n / p ∈ Finset.Icc 1 R := by
      rw [← hr]
      exact Finset.mem_Icc.mpr ⟨hrPos, hrUpper⟩
    let row : StationaryPrefixRow R := ⟨n / p, hrow⟩
    have hpUnion :
        p ∈ (infiniteAllocationPositiveSupport row.1).biUnion
          (parts row) := by
      rw [(hparts row).2.2]
      simpa only [row, hr] using hpLayer
    obtain ⟨q, hq, hpPart⟩ := Finset.mem_biUnion.mp hpUnion
    have hmem :
        ∃ q' ∈ infiniteAllocationPositiveSupport (n / p),
          p ∈ parts ⟨n / p, hrow⟩ q' :=
      ⟨q, hq, hpPart⟩
    have hchosen := stationaryPrefixCofactorChoice_spec
      hnotRowZero hrow hmem
    have hqRange := Finset.mem_Icc.mp
      (mem_infiniteAllocationPositiveSupport.mp hchosen.1).1
    have hqLower :
        r + 1 ≤ stationaryPrefixCofactorChoice R n parts p := by
      simpa only [hr] using hqRange.1
    have hqUpper :
        stationaryPrefixCofactorChoice R n parts p ≤ 2 * r + 1 := by
      simpa only [hr] using hqRange.2
    exact Or.inr ⟨r, hrPos, hr, hpLayer, hqLower, hqUpper⟩

/-- Literal factorization of an admissible large-cofactor product.  This
is the bridge from the product-valued capacity theorem to the explicit
finite sum expected by the reserve algebra. -/
theorem largeCentralCofactorProduct_factorization_eq_sum
    {n X ell : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q) :
    (largeCentralCofactorProduct n X q).factorization ell =
      ∑ p ∈ largeCentralPrimes n X, (q p).factorization ell := by
  rw [largeCentralCofactorProduct, Nat.factorization_prod_apply]
  intro p hp
  exact (largeCentralCofactor_pos hq hp).ne'

/-- The cofactor product of the routed total function is exactly the
row-by-row actual product whose valuation was analyzed previously. -/
theorem largeCentralCofactorProduct_stationaryPrefixCofactorChoice
    {R n : ℕ}
    (hn : centralAnchorCutoffThreshold R ≤ n)
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    (hparts : IsStationaryPrefixPartFamily R n parts) :
    largeCentralCofactorProduct n (centralAnchorCutoff R n)
        (stationaryPrefixCofactorChoice R n parts) =
      stationaryPrefixCofactorProductUpTo R parts := by
  let large := largeCentralPrimes n (centralAnchorCutoff R n)
  let positive := large.filter (fun p ↦ p ≤ n)
  have hrestrict :
      positive.prod (stationaryPrefixCofactorChoice R n parts) =
        large.prod (stationaryPrefixCofactorChoice R n parts) := by
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro p hpLarge hpNotPositive
    have hnotLe : ¬p ≤ n := by
      intro hpLe
      exact hpNotPositive (Finset.mem_filter.mpr ⟨hpLarge, hpLe⟩)
    exact stationaryPrefixCofactorChoice_eq_one_of_rowZero
      (Nat.lt_of_not_ge hnotLe)
  have hbij :
      (stationaryPrefixMarkedTriples R parts).prod
          (fun x ↦ x.2.1) =
        positive.prod (stationaryPrefixCofactorChoice R n parts) := by
    apply Finset.prod_bij (fun x _hx ↦ x.2.2)
    · intro x hx
      simpa only [positive, large] using
        stationaryPrefixMarkedTriple_marker_mem_largeCentralPrimes
          hn hparts hx
    · intro x hx y hy hxy
      exact stationaryPrefixMarkedTriple_marker_injOn hparts hx hy hxy
    · intro p hp
      have hp' :
          p ∈ (largeCentralPrimes n (centralAnchorCutoff R n)).filter
            (fun marker ↦ marker ≤ n) := by
        simpa only [positive, large] using hp
      obtain ⟨x, hx, hmarker⟩ :=
        exists_stationaryPrefixMarkedTriple_of_mem_largeCentralPrimes
          hn hparts hp'
      exact ⟨x, hx, hmarker⟩
    · intro x hx
      have hxmem := mem_stationaryPrefixMarkedTriples.mp hx
      exact (stationaryPrefixCofactorChoice_eq_of_mem_part
        hparts hxmem.1 hxmem.2).symm
  calc
    largeCentralCofactorProduct n (centralAnchorCutoff R n)
        (stationaryPrefixCofactorChoice R n parts) =
        large.prod (stationaryPrefixCofactorChoice R n parts) := by
      rfl
    _ = positive.prod (stationaryPrefixCofactorChoice R n parts) :=
      hrestrict.symm
    _ = (stationaryPrefixMarkedTriples R parts).prod
        (fun x ↦ x.2.1) := hbij.symm
    _ = stationaryPrefixCofactorProductUpTo R parts :=
      stationaryPrefixMarkedTriples_prod_cofactor R parts

/-- The existing complete central-anchor product theorem now applies to
the actual realized prefix cofactors, with no abstract choice remaining. -/
theorem fullCentralAnchors_prod_stationaryPrefixCofactorChoice
    {R n : ℕ}
    (hn : centralAnchorCutoffThreshold R ≤ n)
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    (hparts : IsStationaryPrefixPartFamily R n parts) :
    (fullCentralAnchors n (centralAnchorCutoff R n)
        (stationaryPrefixCofactorChoice R n parts)).prod id =
      Nat.choose (2 * n) n *
        (2 ^ residualPromotionCost n (centralAnchorCutoff R n) *
          stationaryPrefixCofactorProductUpTo R parts) := by
  have hchoice :=
    stationaryPrefixCofactorChoice_isLargeCentralCofactorChoice hn hparts
  calc
    (fullCentralAnchors n (centralAnchorCutoff R n)
        (stationaryPrefixCofactorChoice R n parts)).prod id =
        Nat.choose (2 * n) n *
          centralAnchorDivisor n (centralAnchorCutoff R n)
            (stationaryPrefixCofactorChoice R n parts) :=
      fullCentralAnchors_prod_centralAnchorCutoff hn hchoice
    _ = Nat.choose (2 * n) n *
        (2 ^ residualPromotionCost n (centralAnchorCutoff R n) *
          stationaryPrefixCofactorProductUpTo R parts) := by
      rw [centralAnchorDivisor,
        largeCentralCofactorProduct_stationaryPrefixCofactorChoice
          hn hparts]

/-- For any simultaneous realization, admissibility and the exact product
identification both hold eventually. -/
theorem eventually_stationaryPrefixCofactorChoice_certificate
    (R : ℕ) (distinguished : ℕ → ℕ)
    (parts : ℕ → StationaryPrefixRow R → ℕ → Finset ℕ)
    (hparts :
      ∀ᶠ n : ℕ in atTop,
        ∀ r : StationaryPrefixRow R,
          (∀ q ∈ infiniteAllocationPositiveSupport r.1,
            parts n r q ⊆ stationaryPrimeLayer n r.1) ∧
          (∀ q ∈ infiniteAllocationPositiveSupport r.1,
            (parts n r q).card =
              stationaryPrefixCount n r.1 (distinguished r.1) q) ∧
          (infiniteAllocationPositiveSupport r.1 :
            Set ℕ).PairwiseDisjoint (parts n r) ∧
          (infiniteAllocationPositiveSupport r.1).biUnion
              (parts n r) = stationaryPrimeLayer n r.1) :
    ∀ᶠ n : ℕ in atTop,
      IsLargeCentralCofactorChoice n (centralAnchorCutoff R n)
          (stationaryPrefixCofactorChoice R n (parts n)) ∧
        largeCentralCofactorProduct n (centralAnchorCutoff R n)
            (stationaryPrefixCofactorChoice R n (parts n)) =
          stationaryPrefixCofactorProductUpTo R (parts n) ∧
        (fullCentralAnchors n (centralAnchorCutoff R n)
            (stationaryPrefixCofactorChoice R n (parts n))).prod id =
          Nat.choose (2 * n) n *
            (2 ^ residualPromotionCost n (centralAnchorCutoff R n) *
              stationaryPrefixCofactorProductUpTo R (parts n)) := by
  filter_upwards [hparts,
    eventually_ge_atTop (centralAnchorCutoffThreshold R)] with n
    hpartsN hn
  have hfamily :=
    isStationaryPrefixPartFamily_of_realization hpartsN
  exact ⟨stationaryPrefixCofactorChoice_isLargeCentralCofactorChoice
      hn hfamily,
    largeCentralCofactorProduct_stationaryPrefixCofactorChoice hn hfamily,
    fullCentralAnchors_prod_stationaryPrefixCofactorChoice hn hfamily⟩

/-- The capacity estimate is therefore a simultaneous estimate for the
literal routed large-central cofactor product, for every prime that can
occur in a prefix cofactor through row `R`. -/
theorem
    eventually_stationaryPrefixCofactorChoice_factorization_le_on_primesUpTo
    (R : ℕ) (distinguished : ℕ → ℕ)
    {slack : ℝ} (hslack : 0 < slack)
    (parts : ℕ → StationaryPrefixRow R → ℕ → Finset ℕ)
    (hactual :
      ∀ᶠ n : ℕ in atTop,
        ∀ r : StationaryPrefixRow R,
          (∀ q ∈ infiniteAllocationPositiveSupport r.1,
            parts n r q ⊆ stationaryPrimeLayer n r.1) ∧
          (∀ q ∈ infiniteAllocationPositiveSupport r.1,
            (parts n r q).card =
              stationaryPrefixCount n r.1 (distinguished r.1) q) ∧
          (infiniteAllocationPositiveSupport r.1 :
            Set ℕ).PairwiseDisjoint (parts n r) ∧
          (infiniteAllocationPositiveSupport r.1).biUnion
              (parts n r) = stationaryPrimeLayer n r.1)
    (hparts :
      ∀ r : StationaryPrefixRow R,
        ∀ q ∈ infiniteAllocationPositiveSupport r.1,
          Tendsto
            (fun n : ℕ ↦
              ((parts n r q).card : ℝ) / secondOrderScale n)
            atTop (nhds (infiniteAllocation r.1 q : ℝ))) :
    ∀ᶠ n : ℕ in atTop,
      ∀ ell ∈ primesUpTo (2 * R + 1),
        ((((largeCentralCofactorProduct n (centralAnchorCutoff R n)
          (stationaryPrefixCofactorChoice R n
            (parts n))).factorization ell : ℕ) : ℝ) ≤
            ((C0 + slack) / (((ell - 1 : ℕ) : ℝ))) *
              secondOrderScale n) ∧
          ((largeCentralCofactorProduct n (centralAnchorCutoff R n)
            (stationaryPrefixCofactorChoice R n
              (parts n))).factorization ell ≤
                ⌊((C0 + slack) / (((ell - 1 : ℕ) : ℝ))) *
                  secondOrderScale n⌋₊) := by
  filter_upwards [
    eventually_stationaryPrefixCofactorChoice_certificate
      R distinguished parts hactual,
    eventually_stationaryPrefixCofactorProductUpTo_factorization_le_on_primesUpTo
      R hslack parts hparts] with n hcertificate hcapacity
  intro ell hell
  simpa only [hcertificate.2.1] using hcapacity ell hell

end

end Erdos390.WholePaper
