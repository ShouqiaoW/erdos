import Erdos390.WholePaper.BankPaperSharpCensus
import Erdos390.WholePaper.FixedModulusReducedResidueCount
import Mathlib.NumberTheory.SelbergSieve

/-!
# Exceptional tangent rows: the verified Selberg reduction

Section 9 of the paper bounds the common multipliers with
`2n / R_y(a) < X0` by writing

`a = R_y(a) * b`

and applying an interval Selberg sieve separately for each smooth factor
`b`.  This file formalizes all of that finite reduction and connects it to
the literal common-list deletion ledger.

The analytic availability boundary is important here.  The Mathlib module
`Mathlib.NumberTheory.SelbergSieve` currently supplies the abstract theorem

`BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius`,

but it does not yet construct the paper's Lambda-squared coefficients,
diagonalize their main term, or prove the required lower bound for the
sieve-density sum.  In particular, the specialized estimate

`H / log y + y^4 / (log y)^2`

cannot honestly be deduced from the available library theorem alone.
Accordingly, this file does not assume that estimate or its desired
cardinality consequence.  It proves instead the strongest available
statement:

* the interval sieve is a literal `BoundingSieve` with `nu(d)=1/d`;
* its remainder has the sharp elementary bound `|R_d| < 1`;
* every exceptional common multiplier injects into the disjoint union of
  the corresponding rough reduced-residue intervals;
* any verified upper-Moebius coefficients therefore give an explicit real
  majorant, and its natural ceiling substitutes for the exceptional term in
  both the generic and the sharp bank deletion ledgers.

Thus, at this reduction layer, the analytic obligation is isolated exactly
as the choice and estimation of concrete upper-Moebius coefficients, rather
than hidden inside an assumed exceptional-cardinality bound.  The downstream
Lambda-square modules discharge that obligation.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## A literal interval `BoundingSieve` -/

/-- The multiplicative density `nu(d)=1/d`, made total at zero. -/
def tangentReciprocalArithmeticFunction : ArithmeticFunction ℝ :=
  ⟨fun d ↦ if d = 0 then 0 else 1 / (d : ℝ), by simp⟩

theorem tangentReciprocalArithmeticFunction_isMultiplicative :
    tangentReciprocalArithmeticFunction.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [tangentReciprocalArithmeticFunction], ?_⟩
  intro m n hm hn _hcoprime
  simp only [tangentReciprocalArithmeticFunction,
    ArithmeticFunction.coe_mk, hm, hn, mul_ne_zero hm hn, if_false,
    Nat.cast_mul]
  field_simp

@[simp]
theorem tangentReciprocalArithmeticFunction_apply_of_pos
    {d : ℕ} (hd : 0 < d) :
    tangentReciprocalArithmeticFunction d = 1 / (d : ℝ) := by
  simp [tangentReciprocalArithmeticFunction, hd.ne']

/-- The product of the distinct primes at most `y` is squarefree. -/
theorem roughHeadModulus_squarefree (y : ℕ) :
    Squarefree (roughHeadModulus y) := by
  unfold roughHeadModulus
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes
        (mem_primesUpTo.mp hp).1 (mem_primesUpTo.mp hq).1).mpr hpq)
  · intro p hp
    exact (mem_primesUpTo.mp hp).1.squarefree

/-- Every prime in a complete rough label is absent from the head-prime
product at the same cutoff. -/
theorem completeRoughLabel_coprime_roughHeadModulus (y a : ℕ) :
    Nat.Coprime (completeRoughLabel y a) (roughHeadModulus y) := by
  apply Nat.coprime_of_dvd
  intro p hp hpLabel hpHead
  have hpHigh : y < p :=
    prime_dvd_completeRoughLabel_gt hp hpLabel
  rw [roughHeadModulus] at hpHead
  obtain ⟨q, hqHead, hpq⟩ :=
    (hp.prime.dvd_finset_prod_iff id).mp hpHead
  have hq := mem_primesUpTo.mp hqHead
  have hpEq : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp hq.1).mp hpq
  omega

/-- The unweighted physical interval `(lo,hi]`, sifted by the squarefree
modulus `P`, with the exact real interval length as total mass. -/
def tangentIntervalReciprocalSieve
    (P lo hi : ℕ) (hP : Squarefree P) : BoundingSieve where
  support := Finset.Ioc lo hi
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ zero_le_one
  totalMass := ((hi - lo : ℕ) : ℝ)
  nu := tangentReciprocalArithmeticFunction
  nu_mult := tangentReciprocalArithmeticFunction_isMultiplicative
  nu_pos_of_prime := by
    intro p hp _hpP
    rw [tangentReciprocalArithmeticFunction_apply_of_pos hp.pos]
    exact one_div_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp _hpP
    rw [tangentReciprocalArithmeticFunction_apply_of_pos hp.pos]
    have hpReal : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast hp.one_lt
    simpa using
      (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hpReal)

/-- The sifted sum of the literal interval sieve is exactly the cardinality
of its reduced-residue interval. -/
theorem tangentIntervalReciprocalSieve_siftedSum
    (P lo hi : ℕ) (hP : Squarefree P) :
    (tangentIntervalReciprocalSieve P lo hi hP).siftedSum =
      ((reducedResidueIoc P lo hi).card : ℝ) := by
  simp [tangentIntervalReciprocalSieve, BoundingSieve.siftedSum,
    reducedResidueIoc, Nat.coprime_comm]

/-- Direct specialization of Mathlib's strongest currently available
Selberg theorem to a literal reduced-residue interval. -/
theorem reducedResidueIoc_card_le_abstractSelberg
    {P lo hi : ℕ} (hP : Squarefree P)
    (muPlus : ℕ → ℝ)
    (hmuPlus : BoundingSieve.IsUpperMoebius muPlus) :
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
      let s := tangentIntervalReciprocalSieve P lo hi hP
      s.totalMass * s.mainSum muPlus + s.errSum muPlus := by
  let s := tangentIntervalReciprocalSieve P lo hi hP
  have hs := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    muPlus hmuPlus
  simpa only [s, tangentIntervalReciprocalSieve_siftedSum] using hs

/-! ## The exact endpoint remainder, with constant one -/

/-- The number of multiples of `D` in `(lo,hi]` is the difference of the
two endpoint quotients. -/
theorem Ioc_filter_dvd_card_eq_div_sub_div
    {D lo hi : ℕ} (hD : 0 < D) :
    ((Finset.Ioc lo hi).filter (D ∣ ·)).card = hi / D - lo / D := by
  simpa [coprimeMultipleIoc, reducedResidueIoc] using
    (coprimeMultipleIoc_card_eq_reducedResidueIoc
      (M := 1) (D := D) (lo := lo) (hi := hi) hD
      (by simp : Nat.Coprime D 1))

/-- Exact multiple count inside the interval sieve. -/
theorem tangentIntervalReciprocalSieve_multSum
    {P lo hi D : ℕ} (hP : Squarefree P) (hD : 0 < D) :
    (tangentIntervalReciprocalSieve P lo hi hP).multSum D =
      ((hi / D - lo / D : ℕ) : ℝ) := by
  rw [BoundingSieve.multSum]
  simp only [tangentIntervalReciprocalSieve, Finset.sum_boole]
  exact_mod_cast Ioc_filter_dvd_card_eq_div_sub_div hD

/-- The elementary interval remainder costs strictly less than one for
every positive divisor.  This is the precise constant entering the
non-diagonalized abstract Selberg error sum. -/
theorem tangentIntervalReciprocalSieve_rem_abs_lt_one
    {P lo hi D : ℕ} (hP : Squarefree P) (hD : 0 < D)
    (hlohi : lo ≤ hi) :
    |(tangentIntervalReciprocalSieve P lo hi hP).rem D| < 1 := by
  rw [BoundingSieve.rem,
    tangentIntervalReciprocalSieve_multSum hP hD]
  simp only [tangentIntervalReciprocalSieve,
    tangentReciprocalArithmeticFunction_apply_of_pos hD]
  simpa [div_eq_mul_inv, mul_comm] using
    (quotientIocLength_sub_realLengthDiv_abs_lt_one hD hlohi)

/-- Total form of the remainder bound.  If the endpoints are reversed,
both the support and its declared natural length are zero, so the remainder
vanishes. -/
theorem tangentIntervalReciprocalSieve_rem_abs_lt_one_total
    {P lo hi D : ℕ} (hP : Squarefree P) (hD : 0 < D) :
    |(tangentIntervalReciprocalSieve P lo hi hP).rem D| < 1 := by
  by_cases hlohi : lo ≤ hi
  · exact tangentIntervalReciprocalSieve_rem_abs_lt_one hP hD hlohi
  · have hhilo : hi ≤ lo := (Nat.lt_of_not_ge hlohi).le
    have hsupport : Finset.Ioc lo hi = ∅ :=
      Finset.Ioc_eq_empty_of_le hhilo
    rw [BoundingSieve.rem]
    simp [tangentIntervalReciprocalSieve, hsupport,
      Nat.sub_eq_zero_of_le hhilo]

/-- Consequently the abstract error sum is bounded by the exact `l1` norm
of the chosen upper-Moebius coefficients over divisors of `P`. -/
theorem tangentIntervalReciprocalSieve_errSum_le_l1
    {P lo hi : ℕ} (hP : Squarefree P) (muPlus : ℕ → ℝ) :
    (tangentIntervalReciprocalSieve P lo hi hP).errSum muPlus ≤
      ∑ D ∈ P.divisors, |muPlus D| := by
  rw [BoundingSieve.errSum]
  apply Finset.sum_le_sum
  intro D hD
  have hDPos : 0 < D := Nat.pos_of_mem_divisors hD
  calc
    |muPlus D| *
        |(tangentIntervalReciprocalSieve P lo hi hP).rem D| ≤
        |muPlus D| * 1 :=
      mul_le_mul_of_nonneg_left
        (tangentIntervalReciprocalSieve_rem_abs_lt_one_total
          hP hDPos).le (abs_nonneg _)
    _ = |muPlus D| := mul_one _

/-- Fully explicit form of the currently verified interval Selberg
reduction: the main sum is left visible, while every interval remainder has
already been replaced by its sharp constant-one bound. -/
theorem reducedResidueIoc_card_le_abstractSelberg_l1
    {P lo hi : ℕ} (hP : Squarefree P) (muPlus : ℕ → ℝ)
    (hmuPlus : BoundingSieve.IsUpperMoebius muPlus) :
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
      ((hi - lo : ℕ) : ℝ) *
          (tangentIntervalReciprocalSieve P lo hi hP).mainSum muPlus +
        ∑ D ∈ P.divisors, |muPlus D| := by
  calc
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
        let s := tangentIntervalReciprocalSieve P lo hi hP
        s.totalMass * s.mainSum muPlus + s.errSum muPlus :=
      reducedResidueIoc_card_le_abstractSelberg hP muPlus hmuPlus
    _ ≤ ((hi - lo : ℕ) : ℝ) *
          (tangentIntervalReciprocalSieve P lo hi hP).mainSum muPlus +
        ∑ D ∈ P.divisors, |muPlus D| := by
      simpa only [tangentIntervalReciprocalSieve] using
        add_le_add_right
          (tangentIntervalReciprocalSieve_errSum_le_l1 hP muPlus)
          (((hi - lo : ℕ) : ℝ) *
            (tangentIntervalReciprocalSieve P lo hi hP).mainSum muPlus)

/-! ## Exact factorization of exceptional common multipliers -/

/-- The possible positive smooth factors `b`, with the sharper literal
condition `u*b<X0` retained. -/
def tangentExceptionalSmoothIndices (X0 u : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X0).filter (fun b ↦ u * b < X0)

/-- The exact `u*b<X0` index set has at most `X0/u` elements.  This is the
finite source of the paper's factor `X0/u` in the accumulated `y^4`
remainder. -/
theorem card_tangentExceptionalSmoothIndices_le_div
    {X0 u : ℕ} (hu : 0 < u) :
    (tangentExceptionalSmoothIndices X0 u).card ≤ X0 / u := by
  calc
    (tangentExceptionalSmoothIndices X0 u).card ≤
        (Finset.Icc 1 (X0 / u)).card := by
      apply Finset.card_le_card
      intro b hb
      have hbData := Finset.mem_filter.mp hb
      apply Finset.mem_Icc.mpr
      refine ⟨(Finset.mem_Icc.mp hbData.1).1, ?_⟩
      apply (Nat.le_div_iff_mul_le hu).mpr
      simpa only [Nat.mul_comm] using hbData.2.le
    _ ≤ X0 / u := by simp

/-- The constant-one interval errors therefore accumulate with the literal
factor `card smoothIndices`. -/
theorem tangentExceptional_l1_accumulation_eq
    (X0 y u : ℕ) (muPlus : ℕ → ℝ) :
    (∑ _b ∈ tangentExceptionalSmoothIndices X0 u,
        ∑ D ∈ (roughHeadModulus y).divisors, |muPlus D|) =
      ((tangentExceptionalSmoothIndices X0 u).card : ℝ) *
        ∑ D ∈ (roughHeadModulus y).divisors, |muPlus D| := by
  simp only [Finset.sum_const, nsmul_eq_mul]

/-- Explicit `X0/u` upper bound for the accumulated constant-one errors. -/
theorem tangentExceptional_l1_accumulation_le_div
    {X0 y u : ℕ} (hu : 0 < u) (muPlus : ℕ → ℝ) :
    (∑ _b ∈ tangentExceptionalSmoothIndices X0 u,
        ∑ D ∈ (roughHeadModulus y).divisors, |muPlus D|) ≤
      ((X0 / u : ℕ) : ℝ) *
        ∑ D ∈ (roughHeadModulus y).divisors, |muPlus D| := by
  rw [tangentExceptional_l1_accumulation_eq]
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast card_tangentExceptionalSmoothIndices_le_div hu
  · exact Finset.sum_nonneg fun D _hD ↦ abs_nonneg (muPlus D)

/-- Coefficient-estimate interface for the accumulated remainder.  Inserting
the downstream Lambda-squared estimate
`l1(muPlus) ≤ C * y^4 / (log y)^2` preserves its constant `C` and produces
exactly the factor `X0/u`. -/
theorem tangentExceptional_l1_accumulation_le_of_bound
    {X0 y u : ℕ} (hu : 0 < u) (muPlus : ℕ → ℝ) {B : ℝ}
    (hB : (∑ D ∈ (roughHeadModulus y).divisors, |muPlus D|) ≤ B) :
    (∑ _b ∈ tangentExceptionalSmoothIndices X0 u,
        ∑ D ∈ (roughHeadModulus y).divisors, |muPlus D|) ≤
      ((X0 / u : ℕ) : ℝ) * B := by
  calc
    (∑ _b ∈ tangentExceptionalSmoothIndices X0 u,
        ∑ D ∈ (roughHeadModulus y).divisors, |muPlus D|) ≤
        ((X0 / u : ℕ) : ℝ) *
          ∑ D ∈ (roughHeadModulus y).divisors, |muPlus D| :=
      tangentExceptional_l1_accumulation_le_div hu muPlus
    _ ≤ ((X0 / u : ℕ) : ℝ) * B :=
      mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg _)

/-- For one smooth factor `b`, the rough labels allowed by the common
multiplier interval.  Coprimality with the head product says exactly that
all prime factors of the label exceed `y`. -/
def tangentExceptionalRoughCandidates
    (n K h y u v b : ℕ) : Finset ℕ :=
  reducedResidueIoc (roughHeadModulus y)
    (n / (v * b)) (tangentBroadUpper n K h / (u * b))

/-- The disjoint union, indexed by the literal smooth factor, of all rough
intervals used in the exceptional-row sieve. -/
def tangentExceptionalSievePairs
    (n K h X0 y u v : ℕ) : Finset (Σ _b : ℕ, ℕ) :=
  (tangentExceptionalSmoothIndices X0 u).sigma
    (tangentExceptionalRoughCandidates n K h y u v)

/-- The exact rough/smooth coordinates attached to a multiplier. -/
def tangentRoughDecompositionIndex (y a : ℕ) : Σ _b : ℕ, ℕ :=
  ⟨completeSmoothPart y a, completeRoughLabel y a⟩

/-- Exact product recovery makes the rough/smooth coordinate map globally
injective, not merely injective on the exceptional set. -/
theorem tangentRoughDecompositionIndex_injective (y : ℕ) :
    Function.Injective (tangentRoughDecompositionIndex y) := by
  intro a₁ a₂ hindex
  have hproduct := congrArg
    (fun z : Σ _b : ℕ, ℕ ↦ z.2 * z.1) hindex
  simpa only [tangentRoughDecompositionIndex,
    completeRoughLabel_mul_completeSmoothPart] using hproduct

/-- Every exceptional multiplier in `I_uv` lands in its claimed fixed-`b`
reduced-residue interval.  The exact finite relations are

`u*b < X0`, `n/(vb) < R`, and `R ≤ (2n-Kh)/(ub)`.

The first is a sharpened consequence of the physical upper endpoint and in
particular implies the paper's deliberately looser bound `b < 2*X0/u`.
-/
theorem tangentRoughDecompositionIndex_mem_exceptionalSievePairs
    {n K h X0 y u v a : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (ha : a ∈ tangentExceptionalMultipliers n X0 y
      (tangentCommonMultiplierInterval n K h u v)) :
    tangentRoughDecompositionIndex y a ∈
      tangentExceptionalSievePairs n K h X0 y u v := by
  rw [tangentExceptionalMultipliers, Finset.mem_filter] at ha
  have haBounds := mem_tangentCommonMultiplierInterval.mp ha.1
  have haPos : 0 < a := by
    have hzero : 0 ≤ n / v := Nat.zero_le _
    omega
  let R := completeRoughLabel y a
  let b := completeSmoothPart y a
  have hRPos : 0 < R := by
    exact completeRoughLabel_pos y a
  have hbPos : 0 < b := by
    exact completeSmoothPart_pos haPos
  have hdecomp : R * b = a := by
    exact completeRoughLabel_mul_completeSmoothPart y a
  have hTwoN : 2 * n < X0 * R := by
    exact (Nat.div_lt_iff_lt_mul hRPos).mp ha.2
  have huaUpper : u * a ≤ tangentBroadUpper n K h := by
    have h := (Nat.le_div_iff_mul_le hu).mp haBounds.2
    simpa only [Nat.mul_comm] using h
  have hubLt : u * b < X0 := by
    apply (Nat.mul_lt_mul_left hRPos).mp
    calc
      R * (u * b) = u * a := by rw [← hdecomp]; ac_rfl
      _ ≤ tangentBroadUpper n K h := huaUpper
      _ ≤ 2 * n := Nat.sub_le _ _
      _ < X0 * R := hTwoN
      _ = R * X0 := Nat.mul_comm _ _
  have hbLeX0 : b ≤ X0 := by
    exact (Nat.le_mul_of_pos_left b hu).trans hubLt.le
  have hnLower : n / (v * b) < R := by
    apply (Nat.div_lt_iff_lt_mul (mul_pos hv hbPos)).mpr
    have hnva : n < v * a := by
      have h := (Nat.div_lt_iff_lt_mul hv).mp haBounds.1
      simpa only [Nat.mul_comm] using h
    calc
      n < v * a := hnva
      _ = R * (v * b) := by rw [← hdecomp]; ac_rfl
  have hRUpper : R ≤ tangentBroadUpper n K h / (u * b) := by
    apply (Nat.le_div_iff_mul_le (mul_pos hu hbPos)).mpr
    calc
      R * (u * b) = u * a := by rw [← hdecomp]; ac_rfl
      _ ≤ tangentBroadUpper n K h := huaUpper
  rw [tangentExceptionalSievePairs, Finset.mem_sigma]
  dsimp only [tangentRoughDecompositionIndex]
  constructor
  · rw [tangentExceptionalSmoothIndices, Finset.mem_filter]
    exact ⟨Finset.mem_Icc.mpr ⟨hbPos, hbLeX0⟩, hubLt⟩
  · rw [tangentExceptionalRoughCandidates, reducedResidueIoc,
      Finset.mem_filter]
    exact ⟨Finset.mem_Ioc.mpr ⟨hnLower, hRUpper⟩,
      completeRoughLabel_coprime_roughHeadModulus y a⟩

/-- Maximal unconditional finite reduction of the exceptional count to the
sum of the fixed-smooth-factor rough interval counts. -/
theorem card_tangentExceptionalMultipliers_le_sieveSum
    {n K h X0 y u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    (tangentExceptionalMultipliers n X0 y
      (tangentCommonMultiplierInterval n K h u v)).card ≤
      ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
        (tangentExceptionalRoughCandidates n K h y u v b).card := by
  classical
  let exceptional := tangentExceptionalMultipliers n X0 y
    (tangentCommonMultiplierInterval n K h u v)
  let pairs := tangentExceptionalSievePairs n K h X0 y u v
  let decompose := tangentRoughDecompositionIndex y
  calc
    exceptional.card = (exceptional.image decompose).card :=
      (Finset.card_image_of_injective exceptional
        (tangentRoughDecompositionIndex_injective y)).symm
    _ ≤ pairs.card := by
      apply Finset.card_le_card
      intro z hz
      obtain ⟨a, haExceptional, rfl⟩ := Finset.mem_image.mp hz
      exact tangentRoughDecompositionIndex_mem_exceptionalSievePairs
        hu hv haExceptional
    _ = ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
        (tangentExceptionalRoughCandidates n K h y u v b).card := by
      simp only [pairs, tangentExceptionalSievePairs, Finset.card_sigma]

/-! ## Substitution of the verified abstract sieve bound -/

/-- The real upper bound supplied by one common family of verified
upper-Moebius coefficients, summed over the exact smooth-factor index set. -/
def tangentExceptionalAbstractSelbergMajorant
    (n K h X0 y u v : ℕ) (muPlus : ℕ → ℝ) : ℝ :=
  ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
    let s := tangentIntervalReciprocalSieve
      (roughHeadModulus y)
      (n / (v * b)) (tangentBroadUpper n K h / (u * b))
      (roughHeadModulus_squarefree y)
    s.totalMass * s.mainSum muPlus + s.errSum muPlus

/-- The exceptional count is bounded by the summed abstract Selberg
majorant.  No exceptional-cardinality hypothesis occurs in this theorem. -/
theorem tangentExceptionalMultipliers_card_cast_le_abstractSelbergMajorant
    {n K h X0 y u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (muPlus : ℕ → ℝ)
    (hmuPlus : BoundingSieve.IsUpperMoebius muPlus) :
    ((tangentExceptionalMultipliers n X0 y
      (tangentCommonMultiplierInterval n K h u v)).card : ℝ) ≤
      tangentExceptionalAbstractSelbergMajorant
        n K h X0 y u v muPlus := by
  calc
    ((tangentExceptionalMultipliers n X0 y
        (tangentCommonMultiplierInterval n K h u v)).card : ℝ) ≤
        ((∑ b ∈ tangentExceptionalSmoothIndices X0 u,
          (tangentExceptionalRoughCandidates
            n K h y u v b).card : ℕ) : ℝ) := by
      exact_mod_cast card_tangentExceptionalMultipliers_le_sieveSum hu hv
    _ = ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
        ((tangentExceptionalRoughCandidates
          n K h y u v b).card : ℝ) := by
      push_cast
      rfl
    _ ≤ ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
        let s := tangentIntervalReciprocalSieve
          (roughHeadModulus y)
          (n / (v * b)) (tangentBroadUpper n K h / (u * b))
          (roughHeadModulus_squarefree y)
        s.totalMass * s.mainSum muPlus + s.errSum muPlus := by
      apply Finset.sum_le_sum
      intro b _hb
      exact reducedResidueIoc_card_le_abstractSelberg
        (roughHeadModulus_squarefree y) muPlus hmuPlus
    _ = tangentExceptionalAbstractSelbergMajorant
        n K h X0 y u v muPlus := rfl

/-- The same summed majorant after replacing every exact interval error by
the verified constant-one `l1` bound.  This form exposes precisely the two
coefficient estimates supplied by the downstream Lambda-squared
implementation. -/
def tangentExceptionalAbstractSelbergL1Majorant
    (n K h X0 y u v : ℕ) (muPlus : ℕ → ℝ) : ℝ :=
  ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
    let lo := n / (v * b)
    let hi := tangentBroadUpper n K h / (u * b)
    let s := tangentIntervalReciprocalSieve
      (roughHeadModulus y) lo hi (roughHeadModulus_squarefree y)
    ((hi - lo : ℕ) : ℝ) * s.mainSum muPlus +
      ∑ D ∈ (roughHeadModulus y).divisors, |muPlus D|

theorem tangentExceptionalMultipliers_card_cast_le_abstractSelbergL1Majorant
    {n K h X0 y u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (muPlus : ℕ → ℝ)
    (hmuPlus : BoundingSieve.IsUpperMoebius muPlus) :
    ((tangentExceptionalMultipliers n X0 y
      (tangentCommonMultiplierInterval n K h u v)).card : ℝ) ≤
      tangentExceptionalAbstractSelbergL1Majorant
        n K h X0 y u v muPlus := by
  calc
    ((tangentExceptionalMultipliers n X0 y
        (tangentCommonMultiplierInterval n K h u v)).card : ℝ) ≤
        ((∑ b ∈ tangentExceptionalSmoothIndices X0 u,
          (tangentExceptionalRoughCandidates
            n K h y u v b).card : ℕ) : ℝ) := by
      exact_mod_cast card_tangentExceptionalMultipliers_le_sieveSum hu hv
    _ = ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
        ((tangentExceptionalRoughCandidates
          n K h y u v b).card : ℝ) := by
      push_cast
      rfl
    _ ≤ ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
        let lo := n / (v * b)
        let hi := tangentBroadUpper n K h / (u * b)
        let s := tangentIntervalReciprocalSieve
          (roughHeadModulus y) lo hi (roughHeadModulus_squarefree y)
        ((hi - lo : ℕ) : ℝ) * s.mainSum muPlus +
          ∑ D ∈ (roughHeadModulus y).divisors, |muPlus D| := by
      apply Finset.sum_le_sum
      intro b _hb
      exact reducedResidueIoc_card_le_abstractSelberg_l1
        (roughHeadModulus_squarefree y) muPlus hmuPlus
    _ = tangentExceptionalAbstractSelbergL1Majorant
        n K h X0 y u v muPlus := rfl

/-- Natural ceiling of the preceding real expression.  Under the displayed
upper-Moebius premise below, it is a verified cardinality majorant suitable
for the finite deletion ledgers. -/
def tangentExceptionalAbstractSelbergNatMajorant
    (n K h X0 y u v : ℕ) (muPlus : ℕ → ℝ) : ℕ :=
  ⌈tangentExceptionalAbstractSelbergMajorant
    n K h X0 y u v muPlus⌉₊

theorem tangentExceptionalMultipliers_card_le_abstractSelbergNatMajorant
    {n K h X0 y u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (muPlus : ℕ → ℝ)
    (hmuPlus : BoundingSieve.IsUpperMoebius muPlus) :
    (tangentExceptionalMultipliers n X0 y
      (tangentCommonMultiplierInterval n K h u v)).card ≤
      tangentExceptionalAbstractSelbergNatMajorant
        n K h X0 y u v muPlus := by
  have hreal :=
    tangentExceptionalMultipliers_card_cast_le_abstractSelbergMajorant
      (n := n) (K := K) (h := h) (X0 := X0) (y := y)
      hu hv muPlus hmuPlus
  have hceil := hreal.trans
    (Nat.le_ceil (tangentExceptionalAbstractSelbergMajorant
      n K h X0 y u v muPlus))
  exact_mod_cast hceil

/-- Generic common-list deletion ledger with the exceptional cardinality
replaced by the ceiling of the genuinely verified Selberg majorant. -/
theorem tangentCommonMultiplier_abstractSelberg_finite_deletion_ledger
    {n K h Phead X0 y u v : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (dedicatedRows numericalGuards : Finset ℕ)
    (muPlus : ℕ → ℝ)
    (hmuPlus : BoundingSieve.IsUpperMoebius muPlus) :
    (tangentCommonMultiplierInterval n K h u v).card ≤
      (tangentCleanCommonMultiplierList
        n K h Phead X0 y u v dedicatedRows numericalGuards).card +
      (tangentHeadBadMultipliers Phead
        (tangentCommonMultiplierInterval n K h u v)).card +
      tangentExceptionalAbstractSelbergNatMajorant
        n K h X0 y u v muPlus +
      (tangentDedicatedRowMultipliers y dedicatedRows
        (tangentCommonMultiplierInterval n K h u v)).card +
      2 * numericalGuards.card := by
  have hledger := tangentCommonMultiplier_finite_deletion_ledger
    (n := n) (K := K) (h := h) (Phead := Phead) (X0 := X0)
      (y := y) (u := u) (v := v) hu hv dedicatedRows numericalGuards
  have hexceptional :=
    tangentExceptionalMultipliers_card_le_abstractSelbergNatMajorant
      (n := n) (K := K) (h := h) (X0 := X0) (y := y)
        (u := u) (v := v) hu hv muPlus hmuPlus
  omega

/-- Sharp actual-bank common-list ledger with exactly the same abstract
Selberg substitution.  The bank loss remains the already audited
`4 + 4 * bankPaperSharpMarkerBudget n`. -/
theorem BankPaperRealization.tangentPaperCommonMultiplier_abstractSelberg_sharp_ledger
    {c : ℝ} {depth n M W K h Phead X0 u v : ℕ}
    {left right : ℕ → ℕ} {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime)
    (muPlus : ℕ → ℝ)
    (hmuPlus : BoundingSieve.IsUpperMoebius muPlus) :
    (tangentCommonMultiplierInterval n K h u v).card ≤
      (tangentCleanCommonMultiplierList n K h Phead X0 (yNat n) u v
        R.tangentPaperDedicatedRows
        (R.tangentPaperNumericalGuardSet certificate fixedExceptional)).card +
      (tangentHeadBadMultipliers Phead
        (tangentCommonMultiplierInterval n K h u v)).card +
      tangentExceptionalAbstractSelbergNatMajorant
        n K h X0 (yNat n) u v muPlus +
      4 + 4 * bankPaperSharpMarkerBudget n := by
  have hledger := R.tangentPaperCommonMultiplier_sharp_finite_deletion_ledger
    (W := W) (K := K) (h := h) (Phead := Phead) (X0 := X0)
      (u := u) (v := v) certificate fixedExceptional hfixedTail hTwoW
        hPrefix hWv hvu huy hyCutoff huPrime hvPrime
  have hexceptional :=
    tangentExceptionalMultipliers_card_le_abstractSelbergNatMajorant
      (n := n) (K := K) (h := h) (X0 := X0) (y := yNat n)
        (u := u) (v := v) huPrime.pos hvPrime.pos muPlus hmuPlus
  omega

/-! ## The `delta_* < 1/18`, `y^4=n^(8/9)` remainder arithmetic -/

/-- The four-factor cutoff is exactly the exponent used in the paper. -/
theorem tangentExceptional_y_pow_four (n : ℕ) :
    y n ^ 4 = (n : ℝ) ^ (8 / 9 : ℝ) :=
  y_pow_four n

/-- The integral cutoff can only decrease that fourth power. -/
theorem tangentExceptional_yNat_pow_four_le (n : ℕ) :
    (yNat n : ℝ) ^ 4 ≤ (n : ℝ) ^ (8 / 9 : ℝ) := by
  have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hyFloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
  calc
    (yNat n : ℝ) ^ 4 ≤ y n ^ 4 := by gcongr
    _ = (n : ℝ) ^ (8 / 9 : ℝ) := y_pow_four n

/-- The numerical threshold in Section 9 leaves the explicit power saving
`delta_* + 8/9 - 1 < -1/18`. -/
theorem tangentExceptional_deltaStar_remainder_exponent
    {deltaStar : ℝ} (hdeltaStar : deltaStar < 1 / 18) :
    deltaStar + 8 / 9 - 1 < -(1 / 18 : ℝ) := by
  linarith

/-- In particular the power occurring before the harmless logarithmic
denominator tends to zero. -/
theorem tangentExceptional_remainderPower_tendsto_zero
    {deltaStar : ℝ} (hdeltaStar : deltaStar < 1 / 18) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ (deltaStar + 8 / 9 - 1))
      atTop (nhds 0) := by
  have hexponent : deltaStar + 8 / 9 - 1 < 0 :=
    (tangentExceptional_deltaStar_remainder_exponent hdeltaStar).trans
      (by norm_num)
  have h :=
    (tendsto_rpow_neg_atTop (neg_pos.mpr hexponent)).comp
      tendsto_natCast_atTop_atTop
  simpa only [neg_neg] using h

end

end Erdos390.WholePaper
