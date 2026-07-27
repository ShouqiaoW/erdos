import Erdos536.Extremal
import Mathlib.NumberTheory.SmoothNumbers

/-!
# The finite-prime envelope

This file gives the exact finite reduction used at the start of the
finite-prime-envelope argument.  For a finite set `P` of primes, every
positive integer is split into its `P`-factored part and its complementary
core.  A triangle-free set is then partitioned by the complementary core.
Each fibre is a triangle-free subset of the appropriate `P`-factored
prefix.

The resulting last theorem is a completely finite version of the
manuscript's inequality

`f(N) ≤ ∑_{m ≤ N, (m, ∏ p ∈ P, p) = 1} b_P(N / m)`.
-/

open Finset Nat

namespace Erdos536

/-- A finite set consists only of primes. -/
def IsPrimeSet (P : Finset ℕ) : Prop :=
  ∀ ⦃p : ℕ⦄, p ∈ P → p.Prime

/-- The part of `n` supported on the primes in `P`, with multiplicity. -/
def smoothPart (P : Finset ℕ) (n : ℕ) : ℕ :=
  (n.primeFactorsList.filter (· ∈ P)).prod

/-- The complementary part of `n`, with multiplicity. -/
def coprimeCore (P : Finset ℕ) (n : ℕ) : ℕ :=
  (n.primeFactorsList.filter (· ∉ P)).prod

theorem smoothPart_mul_coprimeCore {P : Finset ℕ} {n : ℕ} (hn : n ≠ 0) :
    smoothPart P n * coprimeCore P n = n := by
  rw [smoothPart, coprimeCore, ← List.prod_append]
  simpa only [decide_not] using
    (List.filter_append_perm (· ∈ P) n.primeFactorsList).prod_eq.trans
      (Nat.prod_primeFactorsList hn)

theorem smoothPart_ne_zero (P : Finset ℕ) (n : ℕ) :
    smoothPart P n ≠ 0 := by
  apply List.prod_ne_zero
  intro hp
  exact (Nat.pos_of_mem_primeFactorsList (List.mem_of_mem_filter hp)).ne' rfl

theorem coprimeCore_ne_zero (P : Finset ℕ) (n : ℕ) :
    coprimeCore P n ≠ 0 := by
  apply List.prod_ne_zero
  intro hp
  exact (Nat.pos_of_mem_primeFactorsList (List.mem_of_mem_filter hp)).ne' rfl

theorem smoothPart_pos (P : Finset ℕ) (n : ℕ) :
    0 < smoothPart P n :=
  Nat.pos_of_ne_zero (smoothPart_ne_zero P n)

theorem coprimeCore_pos (P : Finset ℕ) (n : ℕ) :
    0 < coprimeCore P n :=
  Nat.pos_of_ne_zero (coprimeCore_ne_zero P n)

theorem smoothPart_mem_factoredNumbers (P : Finset ℕ) (n : ℕ) :
    smoothPart P n ∈ Nat.factoredNumbers P :=
  Nat.prod_mem_factoredNumbers P n

theorem coprimeCore_coprime_prod {P : Finset ℕ} (hP : IsPrimeSet P) (n : ℕ) :
    (coprimeCore P n).Coprime (P.prod id) := by
  rw [Nat.coprime_prod_right_iff]
  intro p hp
  change (coprimeCore P n).Coprime p
  have hprime : p.Prime := hP hp
  apply Nat.Coprime.symm
  rw [hprime.coprime_iff_not_dvd]
  intro hdiv
  have hmem :
      p ∈ n.primeFactorsList.filter (· ∉ P) := by
    apply mem_list_primes_of_dvd_prod hprime.prime
    · intro q hq
      exact (Nat.prime_of_mem_primeFactorsList
        (List.mem_of_mem_filter hq)).prime
    · exact hdiv
  have hdec : decide (p ∉ P) = true := (List.mem_filter.mp hmem).2
  exact (of_decide_eq_true hdec) hp

private theorem primeFactor_not_mem_of_coprime_prod
    {P : Finset ℕ} {m p : ℕ} (hm : m.Coprime (P.prod id))
    (hp : p ∈ m.primeFactorsList) :
    p ∉ P := by
  intro hpP
  have hprime : p.Prime := Nat.prime_of_mem_primeFactorsList hp
  have hone := Nat.eq_one_of_dvd_coprimes hm
    (Nat.dvd_of_mem_primeFactorsList hp) (Finset.dvd_prod_of_mem id hpP)
  exact hprime.ne_one hone

/-- A factorization into a `P`-factored factor and a factor coprime to
`∏ p ∈ P, p` recovers the canonical `P`-part. -/
theorem smoothPart_mul_eq_left {P : Finset ℕ} {q m : ℕ}
    (hq : q ∈ Nat.factoredNumbers P) (hm0 : m ≠ 0)
    (hm : m.Coprime (P.prod id)) :
    smoothPart P (q * m) = q := by
  have hqfilter :
      q.primeFactorsList.filter (· ∈ P) = q.primeFactorsList := by
    apply List.filter_eq_self.mpr
    intro p hp
    exact decide_eq_true (hq.2 p hp)
  have hmfilter :
      m.primeFactorsList.filter (· ∈ P) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp hdec
    exact primeFactor_not_mem_of_coprime_prod hm hp (of_decide_eq_true hdec)
  have hperm :=
    (Nat.perm_primeFactorsList_mul hq.1 hm0).filter (fun p => decide (p ∈ P))
  rw [List.filter_append, hqfilter, hmfilter, List.append_nil] at hperm
  rw [smoothPart]
  exact hperm.prod_eq.trans (Nat.prod_primeFactorsList hq.1)

/-- The complementary factor in such a factorization is also canonical. -/
theorem coprimeCore_mul_eq_right {P : Finset ℕ} {q m : ℕ}
    (hq : q ∈ Nat.factoredNumbers P) (hm0 : m ≠ 0)
    (hm : m.Coprime (P.prod id)) :
    coprimeCore P (q * m) = m := by
  have hprod :=
    smoothPart_mul_coprimeCore (mul_ne_zero hq.1 hm0)
      (P := P) (n := q * m)
  rw [smoothPart_mul_eq_left hq hm0 hm] at hprod
  exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hq.1) hprod

/-- Uniqueness of the manuscript's `P`-smooth/coprime-core
factorization. -/
theorem smooth_coprimeCore_decomposition_unique
    {P : Finset ℕ} {n q m : ℕ} (hn : n = q * m)
    (hq : q ∈ Nat.factoredNumbers P) (hm0 : m ≠ 0)
    (hm : m.Coprime (P.prod id)) :
    smoothPart P n = q ∧ coprimeCore P n = m := by
  subst n
  exact ⟨smoothPart_mul_eq_left hq hm0 hm,
    coprimeCore_mul_eq_right hq hm0 hm⟩

/-- Existence and uniqueness of the finite-prime decomposition, packaged
in one statement. -/
theorem exists_unique_smooth_coprimeCore_decomposition
    {P : Finset ℕ} (hP : IsPrimeSet P) {n : ℕ} (hn : n ≠ 0) :
    ∃! qm : ℕ × ℕ,
      n = qm.1 * qm.2 ∧
        qm.1 ∈ Nat.factoredNumbers P ∧
        qm.2.Coprime (P.prod id) := by
  let q := smoothPart P n
  let m := coprimeCore P n
  refine ⟨(q, m), ?_, ?_⟩
  · exact ⟨(smoothPart_mul_coprimeCore hn).symm,
      smoothPart_mem_factoredNumbers P n,
      coprimeCore_coprime_prod hP n⟩
  · rintro ⟨q', m'⟩ ⟨hfactor, hq', hm'⟩
    have hm'0 : m' ≠ 0 := by
      intro hm'zero
      rw [hm'zero, mul_zero] at hfactor
      exact hn hfactor
    have hcanonical :=
      smooth_coprimeCore_decomposition_unique hfactor hq' hm'0 hm'
    exact Prod.ext hcanonical.1.symm hcanonical.2.symm

theorem smoothPart_le {P : Finset ℕ} {n : ℕ} (hn : n ≠ 0) :
    smoothPart P n ≤ n := by
  calc
    smoothPart P n ≤ smoothPart P n * coprimeCore P n :=
      Nat.le_mul_of_pos_right (smoothPart P n) (coprimeCore_pos P n)
    _ = n := smoothPart_mul_coprimeCore hn

theorem coprimeCore_le {P : Finset ℕ} {n : ℕ} (hn : n ≠ 0) :
    coprimeCore P n ≤ n := by
  calc
    coprimeCore P n ≤ smoothPart P n * coprimeCore P n :=
      Nat.le_mul_of_pos_left (coprimeCore P n) (smoothPart_pos P n)
    _ = n := smoothPart_mul_coprimeCore hn

/-! ## Multiplication preserves the forbidden configuration -/

theorem isLcmTriangle_mul_right {a b c m : ℕ} (hm : 0 < m)
    (h : IsLcmTriangle a b c) :
    IsLcmTriangle (a * m) (b * m) (c * m) := by
  rcases h with ⟨hcard, hab, hbc⟩
  refine ⟨?_, ?_, ?_⟩
  · have hi : Function.Injective (fun x : ℕ => x * m) := by
      intro x y hxy
      exact Nat.mul_right_cancel hm hxy
    calc
      ({a * m, b * m, c * m} : Finset ℕ).card =
          (Finset.image (fun x : ℕ => x * m) {a, b, c}).card := by simp
      _ = ({a, b, c} : Finset ℕ).card :=
        Finset.card_image_of_injective _ hi
      _ = 3 := hcard
  · simpa only [Nat.lcm_mul_right] using congrArg (fun x => x * m) hab
  · simpa only [Nat.lcm_mul_right] using congrArg (fun x => x * m) hbc

theorem lcmTriangleFree_mul_preimage {A : Finset ℕ} {m : ℕ}
    (hm : 0 < m) (hA : LcmTriangleFree A) :
    LcmTriangleFree (A.preimage (fun q : ℕ => q * m) (by
      intro _x _y _ _ h
      exact Nat.mul_right_cancel hm h)) := by
  intro a b c ha hb hc htri
  exact hA (Finset.mem_preimage.mp ha) (Finset.mem_preimage.mp hb)
    (Finset.mem_preimage.mp hc) (isLcmTriangle_mul_right hm htri)

/-! ## Smooth-prefix extremum -/

/-- The finite prefix of `P`-factored positive integers up to `T`. -/
def smoothPrefix (P : Finset ℕ) (T : ℕ) : Finset ℕ :=
  (Finset.Icc 1 T).filter (· ∈ Nat.factoredNumbers P)

/-- The largest size of a triangle-free subset of the `P`-factored prefix. -/
noncomputable def smoothExtremal (P : Finset ℕ) (T : ℕ) : ℕ :=
  by
    classical
    exact ((smoothPrefix P T).powerset.filter LcmTriangleFree).sup card

theorem card_le_smoothExtremal {P : Finset ℕ} {T : ℕ} {A : Finset ℕ}
    (hA : A ⊆ smoothPrefix P T) (hfree : LcmTriangleFree A) :
    A.card ≤ smoothExtremal P T := by
  classical
  rw [smoothExtremal]
  apply Finset.le_sup
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA, hfree⟩

/-! ## Fibres over the complementary core -/

/-- The `P`-factored parts occurring in `A` with fixed complementary core `m`. -/
def smoothFiber (P : Finset ℕ) (A : Finset ℕ) (m : ℕ) : Finset ℕ :=
  (A.filter fun n => coprimeCore P n = m).image (smoothPart P)

theorem card_smoothFiber (P : Finset ℕ) (A : Finset ℕ) (m : ℕ)
    (hApos : ∀ ⦃n : ℕ⦄, n ∈ A → 0 < n) :
    (smoothFiber P A m).card =
      (A.filter fun n => coprimeCore P n = m).card := by
  rw [smoothFiber, Finset.card_image_iff]
  intro x hx y hy hxy
  have hxcore : coprimeCore P x = m := (Finset.mem_filter.mp hx).2
  have hycore : coprimeCore P y = m := (Finset.mem_filter.mp hy).2
  have hx0 : x ≠ 0 := (hApos (Finset.mem_filter.mp hx).1).ne'
  have hy0 : y ≠ 0 := (hApos (Finset.mem_filter.mp hy).1).ne'
  calc
    x = smoothPart P x * coprimeCore P x :=
      (smoothPart_mul_coprimeCore hx0).symm
    _ = smoothPart P y * coprimeCore P y := by rw [hxy, hxcore, hycore]
    _ = y := smoothPart_mul_coprimeCore hy0

theorem smoothFiber_lcmTriangleFree {P A : Finset ℕ} {m : ℕ}
    (hApos : ∀ ⦃n : ℕ⦄, n ∈ A → 0 < n) (hfree : LcmTriangleFree A) :
    LcmTriangleFree (smoothFiber P A m) := by
  intro a b c ha hb hc htri
  rw [smoothFiber] at ha hb hc
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
  have hxA : x ∈ A := (Finset.mem_filter.mp hx).1
  have hyA : y ∈ A := (Finset.mem_filter.mp hy).1
  have hzA : z ∈ A := (Finset.mem_filter.mp hz).1
  have hxcore : coprimeCore P x = m := (Finset.mem_filter.mp hx).2
  have hycore : coprimeCore P y = m := (Finset.mem_filter.mp hy).2
  have hzcore : coprimeCore P z = m := (Finset.mem_filter.mp hz).2
  have hx0 : x ≠ 0 := (hApos hxA).ne'
  have hy0 : y ≠ 0 := (hApos hyA).ne'
  have hz0 : z ≠ 0 := (hApos hzA).ne'
  have hm : 0 < m := hxcore ▸ coprimeCore_pos P x
  apply hfree hxA hyA hzA
  rw [← smoothPart_mul_coprimeCore hx0,
    ← smoothPart_mul_coprimeCore hy0,
    ← smoothPart_mul_coprimeCore hz0,
    hxcore, hycore, hzcore]
  exact isLcmTriangle_mul_right hm htri

theorem smoothFiber_subset_prefix {P A : Finset ℕ} {N m : ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hm : 0 < m) :
    smoothFiber P A m ⊆ smoothPrefix P (N / m) := by
  intro q hq
  rw [smoothFiber] at hq
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hq
  have hnA : n ∈ A := (Finset.mem_filter.mp hn).1
  have hncore : coprimeCore P n = m := (Finset.mem_filter.mp hn).2
  have hnIcc := hA hnA
  have hn0 : n ≠ 0 := by
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnIcc).1
    omega
  rw [smoothPrefix, Finset.mem_filter]
  refine ⟨Finset.mem_Icc.mpr ⟨smoothPart_pos P n, ?_⟩,
    smoothPart_mem_factoredNumbers P n⟩
  rw [Nat.le_div_iff_mul_le hm]
  rw [← hncore, smoothPart_mul_coprimeCore hn0]
  exact (Finset.mem_Icc.mp hnIcc).2

theorem card_smoothFiber_le {P A : Finset ℕ} {N m : ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hfree : LcmTriangleFree A) (hm : 0 < m) :
    (smoothFiber P A m).card ≤ smoothExtremal P (N / m) := by
  apply card_le_smoothExtremal (smoothFiber_subset_prefix hA hm)
  exact smoothFiber_lcmTriangleFree
    (fun n hn => (Finset.mem_Icc.mp (hA hn)).1) hfree

/-- The finite set of possible complementary cores in `[1,N]`. -/
def coprimeCores (P : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (·.Coprime (P.prod id))

theorem coprimeCore_mem_coprimeCores {P A : Finset ℕ} {N n : ℕ}
    (hP : IsPrimeSet P) (hA : A ⊆ Finset.Icc 1 N) (hn : n ∈ A) :
    coprimeCore P n ∈ coprimeCores P N := by
  have hnIcc := Finset.mem_Icc.mp (hA hn)
  have hn0 : n ≠ 0 := by omega
  rw [coprimeCores, Finset.mem_filter]
  exact ⟨Finset.mem_Icc.mpr
      ⟨coprimeCore_pos P n, coprimeCore_le hn0 |>.trans hnIcc.2⟩,
    coprimeCore_coprime_prod hP n⟩

/-- Exact partition of a positive finite set by its complementary core. -/
theorem card_eq_sum_card_coreFibers {P A : Finset ℕ} {N : ℕ}
    (hP : IsPrimeSet P) (hA : A ⊆ Finset.Icc 1 N) :
    A.card =
      ∑ m ∈ coprimeCores P N,
        (A.filter fun n => coprimeCore P n = m).card := by
  rw [Finset.card_eq_sum_ones]
  symm
  simpa only [Finset.card_eq_sum_ones] using
    (Finset.sum_fiberwise_of_maps_to
      (s := A) (t := coprimeCores P N) (g := coprimeCore P)
      (fun n hn => coprimeCore_mem_coprimeCores hP hA hn) (fun _ => 1))

/-- The exact finite-prime fibre bound for an arbitrary safe subset of
`[1,N]`. -/
theorem card_le_finitePrimeEnvelope {P A : Finset ℕ} {N : ℕ}
    (hP : IsPrimeSet P) (hA : A ⊆ Finset.Icc 1 N)
    (hfree : LcmTriangleFree A) :
    A.card ≤
      ∑ m ∈ coprimeCores P N, smoothExtremal P (N / m) := by
  rw [card_eq_sum_card_coreFibers hP hA]
  apply Finset.sum_le_sum
  intro m hm
  rw [← card_smoothFiber P A m
    (fun n hn => (Finset.mem_Icc.mp (hA hn)).1)]
  exact card_smoothFiber_le hA hfree
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1

/-- Finite-prime envelope, in the finite summation form used before the
Stieltjes/inclusion-exclusion limit in the manuscript. -/
theorem f_le_finitePrimeEnvelope {P : Finset ℕ} (hP : IsPrimeSet P) (N : ℕ) :
    f N ≤ ∑ m ∈ coprimeCores P N, smoothExtremal P (N / m) := by
  obtain ⟨A, hA, hfree, hcard⟩ := exists_extremal N
  rw [← hcard]
  exact card_le_finitePrimeEnvelope hP hA hfree

end Erdos536
