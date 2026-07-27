import Erdos536.FinitePrimeEnvelope
import Erdos536.SquarefreeCapacity

/-!
# Deleting all unit exponents

For a finite prime set `E`, this file decomposes every positive integer
canonically as

`n = unitCore E n * primeProduct (unitSupport E n)`.

The second factor consists of exactly the primes of `E` occurring to
exponent one.  The first factor has no exponent equal to one at any prime
of `E`, and the chosen support is disjoint from its prime support.  We
then partition a safe family by this core and bound each section by the
finite squarefree prefix extremum.
-/

open scoped BigOperators
open Finset Nat

namespace Erdos536

/-- Primes in `E` that occur to exponent exactly one in `n`. -/
def unitSupport (E : Finset ℕ) (n : ℕ) : Finset ℕ :=
  E.filter fun p => n.factorization p = 1

/-- No prime in `E` occurs to exponent exactly one. -/
def UnitExponentFree (E : Finset ℕ) (n : ℕ) : Prop :=
  ∀ ⦃p : ℕ⦄, p ∈ E → n.factorization p ≠ 1

instance (E : Finset ℕ) (n : ℕ) : Decidable (UnitExponentFree E n) :=
  decidable_of_iff (∀ p : E, n.factorization p ≠ 1) <| by
    constructor
    · intro h p hp
      exact h ⟨p, hp⟩
    · intro h p
      exact h p.property

/-- Remove the unique copy of every prime in `unitSupport E n`. -/
def unitCore (E : Finset ℕ) (n : ℕ) : ℕ :=
  n / primeProduct (unitSupport E n)

theorem unitSupport_subset (E : Finset ℕ) (n : ℕ) :
    unitSupport E n ⊆ E :=
  Finset.filter_subset _ _

theorem isPrimeSupport_unitSupport {E : Finset ℕ}
    (hE : IsPrimeSupport E) (n : ℕ) :
    IsPrimeSupport (unitSupport E n) :=
  isPrimeSupport_mono hE (unitSupport_subset E n)

theorem mem_unitSupport_iff {E : Finset ℕ} {n p : ℕ} :
    p ∈ unitSupport E n ↔ p ∈ E ∧ n.factorization p = 1 := by
  simp [unitSupport]

theorem factorization_primeProduct_eq_ite
    {S : Finset ℕ} (hS : IsPrimeSupport S) (p : ℕ) :
    (primeProduct S).factorization p = if p ∈ S then 1 else 0 := by
  rw [primeProduct, Nat.factorization_prod_apply
    (fun q hq => (hS q hq).ne_zero)]
  by_cases hp : p ∈ S
  · rw [if_pos hp, Finset.sum_eq_single p]
    · exact (hS p hp).factorization_self
    · intro q hq hqp
      rw [(hS q hq).factorization]
      simp [hqp]
    · exact fun hpnot => (hpnot hp).elim
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro q hq
    rw [(hS q hq).factorization]
    simp [show q ≠ p from fun hqp => hp (hqp ▸ hq)]

theorem primeProduct_unitSupport_dvd {E : Finset ℕ}
    (hE : IsPrimeSupport E) (n : ℕ) :
    primeProduct (unitSupport E n) ∣ n := by
  apply Finset.prod_dvd_of_isRelPrime
  · intro p hp q hq hpq
    have hpPrime := isPrimeSupport_unitSupport hE n p hp
    have hqPrime := isPrimeSupport_unitSupport hE n q hq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes hpPrime hqPrime).mpr hpq)
  · intro p hp
    have hpPrime := isPrimeSupport_unitSupport hE n p hp
    have hfac : n.factorization p = 1 :=
      (mem_unitSupport_iff.mp hp).2
    exact Nat.dvd_of_factorization_pos (by omega)

theorem unitCore_mul_primeProduct_unitSupport {E : Finset ℕ}
    (hE : IsPrimeSupport E) (n : ℕ) :
    unitCore E n * primeProduct (unitSupport E n) = n := by
  exact Nat.div_mul_cancel (primeProduct_unitSupport_dvd hE n)

theorem unitCore_pos {E : Finset ℕ} (hE : IsPrimeSupport E)
    {n : ℕ} (hn : n ≠ 0) :
    0 < unitCore E n := by
  rw [unitCore]
  exact Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
      (primeProduct_unitSupport_dvd hE n))
    (primeProduct_pos (isPrimeSupport_unitSupport hE n))

theorem unitCore_factorization {E : Finset ℕ}
    (hE : IsPrimeSupport E) {n p : ℕ} :
    (unitCore E n).factorization p =
      n.factorization p -
        (if p ∈ unitSupport E n then 1 else 0) := by
  rw [unitCore, Nat.factorization_div
    (primeProduct_unitSupport_dvd hE n), Finsupp.tsub_apply,
    factorization_primeProduct_eq_ite
      (isPrimeSupport_unitSupport hE n)]

theorem unitCore_unitExponentFree {E : Finset ℕ}
    (hE : IsPrimeSupport E) (n : ℕ) :
    UnitExponentFree E (unitCore E n) := by
  intro p hpE
  rw [unitCore_factorization hE]
  by_cases hfac : n.factorization p = 1
  · have hpS : p ∈ unitSupport E n :=
      mem_unitSupport_iff.mpr ⟨hpE, hfac⟩
    simp [hpS, hfac]
  · have hpS : p ∉ unitSupport E n := by
      simpa [mem_unitSupport_iff, hpE] using hfac
    simp [hpS, hfac]

theorem unitSupport_disjoint_primeFactors_unitCore
    {E : Finset ℕ} (hE : IsPrimeSupport E) {n : ℕ} (hn : n ≠ 0) :
    Disjoint (unitSupport E n) (unitCore E n).primeFactors := by
  rw [Finset.disjoint_left]
  intro p hpS hpcore
  have hpPrime := isPrimeSupport_unitSupport hE n p hpS
  have hfacn : n.factorization p = 1 :=
    (mem_unitSupport_iff.mp hpS).2
  have hfacCore : (unitCore E n).factorization p = 0 := by
    rw [unitCore_factorization hE]
    simp [hpS, hfacn]
  have hpos := hpPrime.factorization_pos_of_dvd
    (unitCore_pos hE hn).ne' (Nat.dvd_of_mem_primeFactors hpcore)
  omega

/-! ## Uniqueness of the unit-exponent decomposition -/

theorem unitSupport_mul_of_unitExponentFree
    {E S : Finset ℕ} (hE : IsPrimeSupport E) {m : ℕ}
    (hm : UnitExponentFree E m) (hm0 : m ≠ 0)
    (hSE : S ⊆ E) (hdisj : Disjoint S m.primeFactors) :
    unitSupport E (m * primeProduct S) = S := by
  ext p
  rw [mem_unitSupport_iff]
  constructor
  · rintro ⟨hpE, hfac⟩
    have hpPrime := hE p hpE
    have hmprod0 := primeProduct_ne_zero (isPrimeSupport_mono hE hSE)
    rw [Nat.factorization_mul hm0 hmprod0, Finsupp.add_apply,
      factorization_primeProduct_eq_ite
        (isPrimeSupport_mono hE hSE) p] at hfac
    by_contra hpS
    rw [if_neg hpS, add_zero] at hfac
    exact hm hpE hfac
  · intro hpS
    have hpE := hSE hpS
    refine ⟨hpE, ?_⟩
    have hmprod0 := primeProduct_ne_zero (isPrimeSupport_mono hE hSE)
    rw [Nat.factorization_mul hm0 hmprod0, Finsupp.add_apply,
      factorization_primeProduct_eq_ite
        (isPrimeSupport_mono hE hSE) p, if_pos hpS]
    have hpPrime := hE p hpE
    have hpnotCore : p ∉ m.primeFactors := fun hpCore =>
      Finset.disjoint_left.mp hdisj hpS hpCore
    have hpnotDvd : ¬p ∣ m := by
      simpa [Nat.mem_primeFactors, hpPrime, hm0] using hpnotCore
    rw [Nat.factorization_eq_zero_of_not_dvd hpnotDvd]

theorem unitCore_mul_of_unitExponentFree
    {E S : Finset ℕ} (hE : IsPrimeSupport E) {m : ℕ}
    (hm : UnitExponentFree E m) (hm0 : m ≠ 0)
    (hSE : S ⊆ E) (hdisj : Disjoint S m.primeFactors) :
    unitCore E (m * primeProduct S) = m := by
  rw [unitCore, unitSupport_mul_of_unitExponentFree hE hm hm0 hSE hdisj]
  exact Nat.mul_div_cancel m
    (primeProduct_pos (isPrimeSupport_mono hE hSE))

theorem unit_decomposition_unique
    {E S : Finset ℕ} (hE : IsPrimeSupport E) {n m : ℕ}
    (hn : n = m * primeProduct S) (hm : UnitExponentFree E m)
    (hm0 : m ≠ 0) (hSE : S ⊆ E)
    (hdisj : Disjoint S m.primeFactors) :
    unitSupport E n = S ∧ unitCore E n = m := by
  subst n
  exact ⟨unitSupport_mul_of_unitExponentFree hE hm hm0 hSE hdisj,
    unitCore_mul_of_unitExponentFree hE hm hm0 hSE hdisj⟩

/-! ## Safe squarefree sections -/

/-- The support section of `A` over a fixed unit-exponent-free core `m`. -/
def unitSection (E : Finset ℕ) (A : Finset ℕ) (m : ℕ) :
    Finset (Finset ℕ) :=
  (A.filter fun n => unitCore E n = m).image (unitSupport E)

theorem card_unitSection {E A : Finset ℕ} (hE : IsPrimeSupport E)
    (m : ℕ) :
    (unitSection E A m).card =
      (A.filter fun n => unitCore E n = m).card := by
  rw [unitSection, Finset.card_image_iff]
  intro x hx y hy hsupports
  have hxcore := (Finset.mem_filter.mp hx).2
  have hycore := (Finset.mem_filter.mp hy).2
  calc
    x = unitCore E x * primeProduct (unitSupport E x) :=
      (unitCore_mul_primeProduct_unitSupport hE x).symm
    _ = unitCore E y * primeProduct (unitSupport E y) := by
      rw [hxcore, hycore, hsupports]
    _ = y :=
      unitCore_mul_primeProduct_unitSupport hE y

theorem unitSection_subset_powerset {E A : Finset ℕ} {m : ℕ} :
    unitSection E A m ⊆ E.powerset := by
  intro S hS
  rw [unitSection] at hS
  obtain ⟨n, _hn, rfl⟩ := Finset.mem_image.mp hS
  exact Finset.mem_powerset.mpr (unitSupport_subset E n)

theorem unitSection_disjoint_coreSupport
    {E A : Finset ℕ} (hE : IsPrimeSupport E) {m : ℕ}
    (hApos : ∀ ⦃n : ℕ⦄, n ∈ A → 0 < n) :
    unitSection E A m ⊆ (E \ m.primeFactors).powerset := by
  intro S hS
  rw [unitSection] at hS
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hS
  have hnA := (Finset.mem_filter.mp hn).1
  have hncore := (Finset.mem_filter.mp hn).2
  rw [Finset.mem_powerset, Finset.subset_sdiff]
  exact ⟨unitSupport_subset E n, by
    rw [← hncore]
    exact unitSupport_disjoint_primeFactors_unitCore hE (hApos hnA).ne'⟩

theorem unitSection_admissible
    {E A : Finset ℕ} (hE : IsPrimeSupport E)
    {m : ℕ} (hApos : ∀ ⦃n : ℕ⦄, n ∈ A → 0 < n)
    (hfree : LcmTriangleFree A) :
    Admissible (unitSection E A m) := by
  rw [admissible_iff_image_lcmTriangleFree]
  · intro a b c ha hb hc htri
    simp only [unitSection, Finset.image_image] at ha hb hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    have hxA := (Finset.mem_filter.mp hx).1
    have hyA := (Finset.mem_filter.mp hy).1
    have hzA := (Finset.mem_filter.mp hz).1
    have hxcore := (Finset.mem_filter.mp hx).2
    have hycore := (Finset.mem_filter.mp hy).2
    have hzcore := (Finset.mem_filter.mp hz).2
    apply hfree hxA hyA hzA
    rw [← unitCore_mul_primeProduct_unitSupport hE x,
      ← unitCore_mul_primeProduct_unitSupport hE y,
      ← unitCore_mul_primeProduct_unitSupport hE z,
      hxcore, hycore, hzcore]
    have hscaled :=
      isLcmTriangle_mul_right (unitCore_pos hE (hApos hxA).ne') htri
    rw [hxcore] at hscaled
    simpa [mul_comm] using hscaled
  · intro S hS
    exact isPrimeSupport_mono hE
      (Finset.mem_powerset.mp (unitSection_subset_powerset hS))

theorem unitSection_subset_squarefreePrefix
    {E A : Finset ℕ} (hE : IsPrimeSupport E) {N m : ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hm : 0 < m) :
    unitSection E A m ⊆ squarefreePrefix (E \ m.primeFactors) (N / m) := by
  intro S hS
  have hsub :=
    unitSection_disjoint_coreSupport hE
      (fun n hn => (Finset.mem_Icc.mp (hA hn)).1) hS
  rw [mem_squarefreePrefix_iff]
  refine ⟨Finset.mem_powerset.mp hsub, ?_⟩
  rw [unitSection] at hS
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hS
  have hnA := (Finset.mem_filter.mp hn).1
  have hncore := (Finset.mem_filter.mp hn).2
  rw [Nat.le_div_iff_mul_le hm]
  rw [← hncore]
  simpa [mul_comm] using
    (unitCore_mul_primeProduct_unitSupport hE n).le.trans
      (Finset.mem_Icc.mp (hA hnA)).2

theorem card_unitSection_le_squarefreeExtremal
    {E A : Finset ℕ} (hE : IsPrimeSupport E) {N m : ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hfree : LcmTriangleFree A)
    (hm : 0 < m) :
    (unitSection E A m).card ≤
      squarefreeExtremal (E \ m.primeFactors) (N / m) := by
  apply card_le_squarefreeExtremal
    (unitSection_subset_squarefreePrefix hE hA hm)
  exact unitSection_admissible hE
    (fun n hn => (Finset.mem_Icc.mp (hA hn)).1) hfree

/-- Eligible cores in `[1,N]`: no prime in `E` has exponent one. -/
def unitCores (E : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (UnitExponentFree E)

theorem unitCore_mem_unitCores
    {E A : Finset ℕ} (hE : IsPrimeSupport E) {N n : ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hnA : n ∈ A) :
    unitCore E n ∈ unitCores E N := by
  have hnIcc := Finset.mem_Icc.mp (hA hnA)
  have hn0 : n ≠ 0 := by omega
  rw [unitCores, Finset.mem_filter]
  exact ⟨Finset.mem_Icc.mpr ⟨unitCore_pos hE hn0,
      (Nat.le_of_dvd hnIcc.1 (show unitCore E n ∣ n from
        ⟨primeProduct (unitSupport E n),
          (unitCore_mul_primeProduct_unitSupport hE n).symm⟩)).trans
        hnIcc.2⟩,
    unitCore_unitExponentFree hE n⟩

theorem card_eq_sum_card_unitSections
    {E A : Finset ℕ} (hE : IsPrimeSupport E) {N : ℕ}
    (hA : A ⊆ Finset.Icc 1 N) :
    A.card =
      ∑ m ∈ unitCores E N,
        (unitSection E A m).card := by
  symm
  calc
    (∑ m ∈ unitCores E N, (unitSection E A m).card) =
        ∑ m ∈ unitCores E N,
          (A.filter fun n => unitCore E n = m).card := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact card_unitSection hE m
    _ = A.card := by
      simpa only [Finset.card_eq_sum_ones] using
        (Finset.sum_fiberwise_of_maps_to
          (s := A) (t := unitCores E N) (g := unitCore E)
          (fun n hn => unitCore_mem_unitCores hE hA hn) (fun _ => 1))

/-- Direct finite all-unit-deletion bound, with arbitrary primes outside
`E` absorbed into the core. -/
theorem card_le_unitExponentDeletion
    {E A : Finset ℕ} (hE : IsPrimeSupport E) {N : ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hfree : LcmTriangleFree A) :
    A.card ≤
      ∑ m ∈ unitCores E N,
        squarefreeExtremal (E \ m.primeFactors) (N / m) := by
  rw [card_eq_sum_card_unitSections hE hA]
  apply Finset.sum_le_sum
  intro m hm
  exact card_unitSection_le_squarefreeExtremal hE hA hfree
    (by
      have hm1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
      omega)

theorem f_le_unitExponentDeletion
    {E : Finset ℕ} (hE : IsPrimeSupport E) (N : ℕ) :
    f N ≤
      ∑ m ∈ unitCores E N,
        squarefreeExtremal (E \ m.primeFactors) (N / m) := by
  obtain ⟨A, hA, hfree, hcard⟩ := exists_extremal N
  rw [← hcard]
  exact card_le_unitExponentDeletion hE hA hfree

/-! ## Arithmetic core categories

For a fixed remaining support `R ⊆ E`, eligible cores have valuation zero
at every prime of `R` and valuation at least two at every prime of
`E \ R`.  Thus they are a square multiple of `primeProduct (E \ R)`
times a number coprime to `primeProduct R`.  The following finite
category makes this parameterization literal and gives its periodic
totient counting bound.
-/

/-- Cores up to `N` in the arithmetic category indexed by `R`.

Writing `D = primeProduct (E \ R)`, this is the injective image of the
positive `k ≤ N / D²` coprime to `primeProduct R` under `k ↦ D² k`.
-/
def unitCoreCategory (E R : Finset ℕ) (N : ℕ) : Finset ℕ :=
  let D2 := primeProduct (E \ R) ^ 2
  ((Finset.Icc 1 (N / D2)).filter
      fun k => (primeProduct R).Coprime k).image
    fun k => D2 * k

theorem card_unitCoreCategory
    {E R : Finset ℕ} (hE : IsPrimeSupport E) (N : ℕ) :
    (unitCoreCategory E R N).card =
      ((Finset.Icc 1 (N / (primeProduct (E \ R) ^ 2))).filter
        fun k => (primeProduct R).Coprime k).card := by
  rw [unitCoreCategory, Finset.card_image_iff]
  intro x _hx y _hy hxy
  exact Nat.mul_left_cancel
    (pow_pos (primeProduct_pos
      (isPrimeSupport_mono hE Finset.sdiff_subset)) 2) hxy

theorem mem_unitCoreCategory_of_arithmetic
    {E R : Finset ℕ} (hE : IsPrimeSupport E)
    {N m : ℕ} (hmpos : 0 < m) (hmN : m ≤ N)
    (hcop : (primeProduct R).Coprime m)
    (hdiv : primeProduct (E \ R) ^ 2 ∣ m) :
    m ∈ unitCoreCategory E R N := by
  let D2 := primeProduct (E \ R) ^ 2
  have hD2pos : 0 < D2 := by
    dsimp [D2]
    exact pow_pos (primeProduct_pos
      (isPrimeSupport_mono hE Finset.sdiff_subset)) 2
  have hkpos : 0 < m / D2 := by
    exact Nat.div_pos (Nat.le_of_dvd hmpos hdiv) hD2pos
  have hkN : m / D2 ≤ N / D2 :=
    Nat.div_le_div_right hmN
  have hkcop : (primeProduct R).Coprime (m / D2) :=
    hcop.of_dvd_right (Nat.div_dvd_of_dvd hdiv)
  rw [unitCoreCategory]
  apply Finset.mem_image.mpr
  refine ⟨m / D2, Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hkpos, hkN⟩, hkcop⟩, ?_⟩
  exact (Nat.mul_div_cancel' hdiv)

theorem unitCore_arithmetic_category
    {E : Finset ℕ} (hE : IsPrimeSupport E) {N m : ℕ}
    (hm : m ∈ unitCores E N) :
    (primeProduct (E \ m.primeFactors)).Coprime m ∧
      primeProduct (E \ (E \ m.primeFactors)) ^ 2 ∣ m := by
  have hmData := Finset.mem_filter.mp hm
  have hmIcc := Finset.mem_Icc.mp hmData.1
  have hm0 : m ≠ 0 := by omega
  have hunit : UnitExponentFree E m := hmData.2
  constructor
  · rw [primeProduct, Nat.coprime_prod_left_iff]
    intro p hp
    have hpData := Finset.mem_sdiff.mp hp
    have hpPrime := hE p hpData.1
    rw [hpPrime.coprime_iff_not_dvd]
    intro hpdvd
    exact hpData.2 (Nat.mem_primeFactors.mpr ⟨hpPrime, hpdvd, hm0⟩)
  · rw [primeProduct, ← Finset.prod_pow]
    apply Finset.prod_dvd_of_isRelPrime
    · intro p hp q hq hpq
      have hpE := (Finset.mem_sdiff.mp hp).1
      have hqE := (Finset.mem_sdiff.mp hq).1
      exact Nat.coprime_iff_isRelPrime.mp
        (((Nat.coprime_primes (hE p hpE) (hE q hqE)).mpr hpq).pow 2 2)
    · intro p hp
      have hpData := Finset.mem_sdiff.mp hp
      have hpE := hpData.1
      have hpCore : p ∈ m.primeFactors := by
        by_contra hpnot
        exact hpData.2 (Finset.mem_sdiff.mpr ⟨hpE, hpnot⟩)
      have hpPrime := hE p hpE
      rw [hpPrime.pow_dvd_iff_le_factorization hm0]
      have hfacpos := hpPrime.factorization_pos_of_dvd hm0
        (Nat.dvd_of_mem_primeFactors hpCore)
      have hfacne := hunit hpE
      omega

theorem unitCore_mem_ownCategory
    {E : Finset ℕ} (hE : IsPrimeSupport E) {N m : ℕ}
    (hm : m ∈ unitCores E N) :
    m ∈ unitCoreCategory E (E \ m.primeFactors) N := by
  have hmIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
  have hproperties := unitCore_arithmetic_category hE hm
  exact mem_unitCoreCategory_of_arithmetic hE
    (by omega) hmIcc.2 hproperties.1 hproperties.2

/-- A fully finite version of the category-density calculation.
The right side is one complete-period totient count times the number of
possibly occupied periods. -/
theorem card_unitCoreCategory_le
    {E R : Finset ℕ} (hE : IsPrimeSupport E) (hRE : R ⊆ E) (N : ℕ) :
    (unitCoreCategory E R N).card ≤
      (primeProduct R).totient *
        ((N / (primeProduct (E \ R) ^ 2)) / primeProduct R + 1) := by
  rw [card_unitCoreCategory hE]
  let K := N / (primeProduct (E \ R) ^ 2)
  have hinterval :
      Finset.Icc 1 K = Finset.Ico 1 (1 + K) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hinterval]
  simpa [K, add_comm] using
    (Nat.Ico_filter_coprime_le (a := primeProduct R) 1 K
      (primeProduct_ne_zero (isPrimeSupport_mono hE hRE)))

end Erdos536
