import Erdos390.WholePaper.LargeCentralPrimeRouting
import Erdos390.WholePaper.CentralAnchorCollision
import Erdos390.WholePaper.LargePrimeCollision

/-!
# Exact product of all three central-anchor families

This file isolates the finite algebra behind the full central-anchor lemma.
For every large central prime, a cofactor choice is required to follow either
its row-zero route or its stationary carry row.  The resulting marker factors
are combined with every promoted low prime-power block.  Their product is
proved to be the central binomial coefficient times the literal cofactor and
promotion divisor.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- A cofactor follows either the row-zero route or one stationary carry
row, including the exact allowed cofactor interval. -/
def IsRoutedCentralCofactor (n p q : ℕ) : Prop :=
  (n < p ∧ p ≤ 2 * n ∧ q = 1) ∨
    ∃ r : ℕ, 1 ≤ r ∧ r = n / p ∧
      p ∈ stationaryPrimeLayer n r ∧ r + 1 ≤ q ∧ q ≤ 2 * r + 1

/-- A simultaneous choice of routed cofactors for all central primes above
the cutoff. -/
def IsLargeCentralCofactorChoice
    (n X : ℕ) (q : ℕ → ℕ) : Prop :=
  ∀ p ∈ largeCentralPrimes n X, IsRoutedCentralCofactor n p (q p)

/-- The canonical fallback chooses `1` in row zero and the left endpoint
`r+1` in a positive carry row. -/
def canonicalLargeCentralCofactor (n p : ℕ) : ℕ :=
  if n < p then 1 else n / p + 1

theorem routedCentralCofactor_mem_centralInterval
    {n p q : ℕ} (hq : IsRoutedCentralCofactor n p q) :
    p * q ∈ Finset.Ioc n (2 * n) := by
  rcases hq with hzero | ⟨r, _hrPos, _hr, hpRow, hqLower, hqUpper⟩
  · simpa only [hzero.2.2, mul_one] using
      (show p ∈ Finset.Ioc n (2 * n) from
        Finset.mem_Ioc.mpr ⟨hzero.1, hzero.2.1⟩)
  · exact stationaryPrimeLayer_mul_cofactor_mem_centralInterval
      hpRow hqLower hqUpper

/-- Large-central-prime routing always supplies at least one legal cofactor;
the displayed function is a concrete simultaneous choice. -/
theorem canonicalLargeCentralCofactor_isChoice
    {n X : ℕ} (hn : 0 < n) (hXsq : 2 * n < X ^ 2) :
    IsLargeCentralCofactorChoice n X
      (canonicalLargeCentralCofactor n) := by
  intro p hpMem
  have hroute := largeCentralPrime_rowZero_or_stationary hn hXsq hpMem
  rcases hroute.2 with hzero | ⟨r, hrPos, hr, hpRow⟩
  · left
    exact ⟨hzero.1, hzero.2, by
      simp only [canonicalLargeCentralCofactor, if_pos hzero.1]⟩
  · right
    have hnotZero : ¬n < p := by
      intro hnp
      have hdivZero : n / p = 0 := Nat.div_eq_of_lt hnp
      omega
    refine ⟨r, hrPos, hr, hpRow, ?_, ?_⟩
    · simp only [canonicalLargeCentralCofactor, if_neg hnotZero]
      omega
    · simp only [canonicalLargeCentralCofactor, if_neg hnotZero, ← hr]
      omega

/-- The actual marker--cofactor factor. -/
def largeCentralAnchor (q : ℕ → ℕ) (p : ℕ) : ℕ := p * q p

/-- All large marker factors, as an honest finite set. -/
def largeCentralAnchors (n X : ℕ) (q : ℕ → ℕ) : Finset ℕ :=
  (largeCentralPrimes n X).image (largeCentralAnchor q)

/-- The exact product of all chosen cofactors. -/
def largeCentralCofactorProduct (n X : ℕ) (q : ℕ → ℕ) : ℕ :=
  (largeCentralPrimes n X).prod q

theorem largeCentralAnchor_mem_centralInterval
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q)
    {p : ℕ} (hp : p ∈ largeCentralPrimes n X) :
    largeCentralAnchor q p ∈ Finset.Ioc n (2 * n) := by
  exact routedCentralCofactor_mem_centralInterval (hq p hp)

/-- The square separation prevents two different large marker primes from
occurring in the same central-interval integer. -/
theorem largeCentralAnchor_injOn
    {n X : ℕ} {q : ℕ → ℕ} (hXsq : 2 * n < X ^ 2)
    (hq : IsLargeCentralCofactorChoice n X q) :
    Set.InjOn (largeCentralAnchor q) (largeCentralPrimes n X) := by
  intro p hp p' hp' heq
  by_contra hpp'
  have hpPrime := largeCentralPrimes_prime hp
  have hp'Prime := largeCentralPrimes_prime hp'
  have haMem := largeCentralAnchor_mem_centralInterval hq hp
  have haPos : 0 < largeCentralAnchor q p := by
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp haMem).1
  have haUpper : largeCentralAnchor q p ≤ 2 * n :=
    (Finset.mem_Ioc.mp haMem).2
  apply not_two_distinct_large_primes_dvd
    hpPrime hp'Prime hpp'
    (largeCentralPrimes_gt hp).le (largeCentralPrimes_gt hp').le
    haPos haUpper (by simpa only [pow_two] using hXsq)
  constructor
  · exact dvd_mul_right p (q p)
  · rw [heq]
    exact dvd_mul_right p' (q p')

theorem largeCentralAnchors_subset_centralInterval
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q) :
    largeCentralAnchors n X q ⊆ Finset.Ioc n (2 * n) := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
  exact largeCentralAnchor_mem_centralInterval hq hp

theorem largeCentralAnchors_card
    {n X : ℕ} {q : ℕ → ℕ} (hXsq : 2 * n < X ^ 2)
    (hq : IsLargeCentralCofactorChoice n X q) :
    (largeCentralAnchors n X q).card = (largeCentralPrimes n X).card := by
  exact Finset.card_image_of_injOn (largeCentralAnchor_injOn hXsq hq)

theorem largeCentralAnchors_prod
    {n X : ℕ} {q : ℕ → ℕ} (hXsq : 2 * n < X ^ 2)
    (hq : IsLargeCentralCofactorChoice n X q) :
    (largeCentralAnchors n X q).prod id =
      (largeCentralPrimes n X).prod id *
        largeCentralCofactorProduct n X q := by
  rw [largeCentralAnchors,
    Finset.prod_image (largeCentralAnchor_injOn hXsq hq)]
  simp only [id_eq, largeCentralAnchor, largeCentralCofactorProduct,
    Finset.prod_mul_distrib]

theorem largeCentralPrimeBlocks_eq_primeProduct
    {n X : ℕ} (hn : 0 < n) (hXsq : 2 * n < X ^ 2) :
    (largeCentralPrimes n X).prod (centralPrimeBlock n) =
      (largeCentralPrimes n X).prod id := by
  apply Finset.prod_congr rfl
  intro p hp
  have hpOne :=
    (largeCentralPrime_rowZero_or_stationary hn hXsq hp).1
  simp only [centralPrimeBlock, hpOne, pow_one, id_eq]

/-- The union of promoted low blocks and routed large marker factors. -/
def fullCentralAnchors (n X : ℕ) (q : ℕ → ℕ) : Finset ℕ :=
  residualPromotedFactors n X ∪ largeCentralAnchors n X q

/-- Promotion powers of two together with all chosen large cofactors. -/
def centralAnchorDivisor (n X : ℕ) (q : ℕ → ℕ) : ℕ :=
  2 ^ residualPromotionCost n X * largeCentralCofactorProduct n X q

theorem residualPromotedFactors_disjoint_largeCentralAnchors
    {n X : ℕ} {q : ℕ → ℕ} (hXTwo : 2 ≤ X) :
    Disjoint (residualPromotedFactors n X)
      (largeCentralAnchors n X q) := by
  rw [Finset.disjoint_left]
  intro a haLow haHigh
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp haLow
  obtain ⟨P, hP, hEq⟩ := Finset.mem_image.mp haHigh
  have hpPrime := residualCentralPrimes_prime hp
  have hPPrime := largeCentralPrimes_prime hP
  apply marker_mul_ne_promotedCentralFactor
    hPPrime hpPrime hXTwo (largeCentralPrimes_gt hP)
      (residualCentralPrimes_le hp)
  simpa only [largeCentralAnchor] using hEq

theorem fullCentralAnchors_subset_centralInterval
    {n X : ℕ} {q : ℕ → ℕ} (hn : 0 < n)
    (hq : IsLargeCentralCofactorChoice n X q) :
    fullCentralAnchors n X q ⊆ Finset.Ioc n (2 * n) := by
  intro a ha
  rcases Finset.mem_union.mp ha with haLow | haHigh
  · exact residualPromotedFactors_subset_centralInterval hn haLow
  · exact largeCentralAnchors_subset_centralInterval hq haHigh

theorem fullCentralAnchors_card
    {n X : ℕ} {q : ℕ → ℕ} (hXTwo : 2 ≤ X)
    (hXsq : 2 * n < X ^ 2)
    (hq : IsLargeCentralCofactorChoice n X q) :
    (fullCentralAnchors n X q).card =
      (residualCentralPrimes n X).card +
        (largeCentralPrimes n X).card := by
  rw [fullCentralAnchors,
    Finset.card_union_of_disjoint
      (residualPromotedFactors_disjoint_largeCentralAnchors hXTwo),
    residualPromotedFactors_card,
    largeCentralAnchors_card hXsq hq]

/-- Literal exact product identity for the complete central-anchor set. -/
theorem fullCentralAnchors_prod
    {n X : ℕ} {q : ℕ → ℕ} (hn : 0 < n) (hXTwo : 2 ≤ X)
    (hXsq : 2 * n < X ^ 2)
    (hq : IsLargeCentralCofactorChoice n X q) :
    (fullCentralAnchors n X q).prod id =
      Nat.choose (2 * n) n * centralAnchorDivisor n X q := by
  have hcentral := residualPromoted_mul_largeCentralPrimeBlocks n X
  rw [largeCentralPrimeBlocks_eq_primeProduct hn hXsq] at hcentral
  rw [fullCentralAnchors,
    Finset.prod_union
      (residualPromotedFactors_disjoint_largeCentralAnchors hXTwo),
    largeCentralAnchors_prod hXsq hq]
  calc
    (residualPromotedFactors n X).prod id *
        ((largeCentralPrimes n X).prod id *
          largeCentralCofactorProduct n X q) =
      ((residualPromotedFactors n X).prod id *
        (largeCentralPrimes n X).prod id) *
          largeCentralCofactorProduct n X q := by ac_rfl
    _ = (2 ^ residualPromotionCost n X * Nat.choose (2 * n) n) *
          largeCentralCofactorProduct n X q := by rw [hcentral]
    _ = Nat.choose (2 * n) n * centralAnchorDivisor n X q := by
      simp only [centralAnchorDivisor]
      ac_rfl

end

end Erdos390.WholePaper
