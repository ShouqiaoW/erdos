import Erdos536.FiniteProbability

/-!
# Finite alternative-band flattening

This file isolates the finite probability calculation used when a cube
coordinate chooses one of several disjoint candidate bands.  There are no
prime-number estimates here: a law is an explicitly weighted finite set.

For the alternative bands, pairwise factorization of first mixed moments is
the only consequence of independence that is needed.  Centering therefore
kills all cross terms, and the variance of the uniform average is the sum of
the component variances divided by the square of the number of alternatives.

For independent coordinate groups, the product density is handled by the
usual telescoping identity.  `HasIndependentPrefixes` records exactly the
finite product factorization supplied by independence of disjoint groups.
-/

open scoped BigOperators
open Finset

namespace Erdos536

/-- Expectation with respect to an explicitly weighted finite support. -/
def finiteExpectation {Ω : Type*} [DecidableEq Ω]
    (P : Finset Ω) (w : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ ω ∈ P, w ω * X ω

/-- The `L¹` distance of a density from the constant density one. -/
def finiteL1Error {Ω : Type*} [DecidableEq Ω]
    (P : Finset Ω) (w : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  finiteExpectation P w fun ω => |X ω - 1|

/-- The centered second moment of a finite density. -/
def finiteVariance {Ω : Type*} [DecidableEq Ω]
    (P : Finset Ω) (w : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  finiteExpectation P w fun ω => (X ω - 1) ^ 2

/-- The uncentered second moment of a finite density. -/
def finiteSecondMoment {Ω : Type*} [DecidableEq Ω]
    (P : Finset Ω) (w : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  finiteExpectation P w fun ω => (X ω) ^ 2

theorem finiteExpectation_nonneg {Ω : Type*} [DecidableEq Ω]
    {P : Finset Ω} {w X : Ω → ℝ}
    (hw : ∀ ω ∈ P, 0 ≤ w ω) (hX : ∀ ω ∈ P, 0 ≤ X ω) :
    0 ≤ finiteExpectation P w X := by
  exact Finset.sum_nonneg fun ω hω =>
    mul_nonneg (hw ω hω) (hX ω hω)

theorem finiteExpectation_mono {Ω : Type*} [DecidableEq Ω]
    {P : Finset Ω} {w X Y : Ω → ℝ}
    (hw : ∀ ω ∈ P, 0 ≤ w ω)
    (hXY : ∀ ω ∈ P, X ω ≤ Y ω) :
    finiteExpectation P w X ≤ finiteExpectation P w Y := by
  exact Finset.sum_le_sum fun ω hω =>
    mul_le_mul_of_nonneg_left (hXY ω hω) (hw ω hω)

theorem finiteExpectation_sum {Ω ι : Type*}
    [DecidableEq Ω] [Fintype ι]
    (P : Finset Ω) (w : Ω → ℝ) (X : ι → Ω → ℝ) :
    finiteExpectation P w (fun ω => ∑ i, X i ω) =
      ∑ i, finiteExpectation P w (X i) := by
  simp only [finiteExpectation, mul_sum]
  rw [Finset.sum_comm]

theorem finiteExpectation_const {Ω : Type*} [DecidableEq Ω]
    (P : Finset Ω) (w : Ω → ℝ) (c : ℝ) :
    finiteExpectation P w (fun _ => c) =
      (∑ ω ∈ P, w ω) * c := by
  simp only [finiteExpectation, ← Finset.sum_mul]

theorem finiteExpectation_one {Ω : Type*} [DecidableEq Ω]
    {P : Finset Ω} {w : Ω → ℝ}
    (hmass : ∑ ω ∈ P, w ω = 1) :
    finiteExpectation P w (fun _ => 1) = 1 := by
  rw [finiteExpectation_const, hmass, one_mul]

theorem finiteVariance_nonneg {Ω : Type*} [DecidableEq Ω]
    {P : Finset Ω} {w X : Ω → ℝ}
    (hw : ∀ ω ∈ P, 0 ≤ w ω) :
    0 ≤ finiteVariance P w X := by
  exact finiteExpectation_nonneg hw fun _ _ => sq_nonneg _

/-- On a probability law, Cauchy--Schwarz bounds `L¹` by the square root of
the centered second moment. -/
theorem finiteL1Error_le_sqrt_variance {Ω : Type*} [DecidableEq Ω]
    {P : Finset Ω} {w X : Ω → ℝ}
    (hw : ∀ ω ∈ P, 0 ≤ w ω)
    (hmass : ∑ ω ∈ P, w ω = 1) :
    finiteL1Error P w X ≤ Real.sqrt (finiteVariance P w X) := by
  calc
    finiteL1Error P w X =
        ∑ ω ∈ P, Real.sqrt (w ω) *
          (Real.sqrt (w ω) * |X ω - 1|) := by
      simp only [finiteL1Error, finiteExpectation]
      apply Finset.sum_congr rfl
      intro ω hω
      rw [← mul_assoc, Real.mul_self_sqrt (hw ω hω)]
    _ ≤ Real.sqrt (∑ ω ∈ P, (Real.sqrt (w ω)) ^ 2) *
          Real.sqrt (∑ ω ∈ P,
            (Real.sqrt (w ω) * |X ω - 1|) ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt P
        (fun ω => Real.sqrt (w ω))
        (fun ω => Real.sqrt (w ω) * |X ω - 1|)
    _ = Real.sqrt (finiteVariance P w X) := by
      have hfirst :
          ∑ ω ∈ P, (Real.sqrt (w ω)) ^ 2 = 1 := by
        calc
          ∑ ω ∈ P, (Real.sqrt (w ω)) ^ 2 =
              ∑ ω ∈ P, w ω := by
            apply Finset.sum_congr rfl
            intro ω hω
            exact Real.sq_sqrt (hw ω hω)
          _ = 1 := hmass
      rw [hfirst, Real.sqrt_one, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro ω hω
      rw [mul_pow, Real.sq_sqrt (hw ω hω), sq_abs]

/-- For a mean-one density, the centered second moment is its second moment
minus one. -/
theorem finiteVariance_eq_secondMoment_sub_one {Ω : Type*} [DecidableEq Ω]
    {P : Finset Ω} {w X : Ω → ℝ}
    (hmass : ∑ ω ∈ P, w ω = 1)
    (hmean : finiteExpectation P w X = 1) :
    finiteVariance P w X = finiteSecondMoment P w X - 1 := by
  calc
    finiteVariance P w X =
        ∑ ω ∈ P,
          (w ω * (X ω) ^ 2 - 2 * (w ω * X ω) + w ω) := by
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = finiteSecondMoment P w X -
          2 * finiteExpectation P w X + ∑ ω ∈ P, w ω := by
      simp only [finiteSecondMoment, finiteExpectation,
        Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = finiteSecondMoment P w X - 1 := by
      rw [hmean, hmass]
      ring

/-- Pairwise first mixed moments factor under the finite law.  Disjoint
independent alternative bands satisfy this identity. -/
def PairwiseFactorizesUnder {Ω ι : Type*}
    [DecidableEq Ω] [Fintype ι]
    (P : Finset Ω) (w : Ω → ℝ) (g : ι → Ω → ℝ) : Prop :=
  ∀ ⦃i j : ι⦄, i ≠ j →
    finiteExpectation P w (fun ω => g i ω * g j ω) =
      finiteExpectation P w (g i) * finiteExpectation P w (g j)

theorem centered_cross_expectation_eq_zero {Ω ι : Type*}
    [DecidableEq Ω] [Fintype ι]
    {P : Finset Ω} {w : Ω → ℝ} {g : ι → Ω → ℝ}
    (hmass : ∑ ω ∈ P, w ω = 1)
    (hmean : ∀ i, finiteExpectation P w (g i) = 1)
    (hfactor : PairwiseFactorizesUnder P w g)
    {i j : ι} (hij : i ≠ j) :
    finiteExpectation P w
        (fun ω => (g i ω - 1) * (g j ω - 1)) = 0 := by
  have hcross := hfactor hij
  rw [hmean i, hmean j] at hcross
  calc
    finiteExpectation P w
        (fun ω => (g i ω - 1) * (g j ω - 1)) =
        finiteExpectation P w (fun ω => g i ω * g j ω) -
          finiteExpectation P w (g i) -
          finiteExpectation P w (g j) +
          finiteExpectation P w (fun _ => 1) := by
      simp only [finiteExpectation]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = 0 := by
      rw [hcross, hmean i, hmean j, finiteExpectation_one hmass]
      ring

/-- Uniform average of `M` alternative densities. -/
noncomputable def uniformAlternativeAverage {Ω : Type*} {M : ℕ}
    (g : Fin M → Ω → ℝ) (ω : Ω) : ℝ :=
  (∑ j, g j ω) / (M : ℝ)

theorem uniformAlternativeAverage_sub_one {Ω : Type*} {M : ℕ}
    (hM : 0 < M) (g : Fin M → Ω → ℝ) (ω : Ω) :
    uniformAlternativeAverage g ω - 1 =
      (∑ j, (g j ω - 1)) / (M : ℝ) := by
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  simp only [uniformAlternativeAverage, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem expectation_sq_sum_centered {Ω : Type*} {M : ℕ}
    [DecidableEq Ω]
    {P : Finset Ω} {w : Ω → ℝ} {g : Fin M → Ω → ℝ}
    (hmass : ∑ ω ∈ P, w ω = 1)
    (hmean : ∀ j, finiteExpectation P w (g j) = 1)
    (hfactor : PairwiseFactorizesUnder P w g) :
    finiteExpectation P w
        (fun ω => (∑ j, (g j ω - 1)) ^ 2) =
      ∑ j, finiteVariance P w (g j) := by
  classical
  calc
    finiteExpectation P w
        (fun ω => (∑ j, (g j ω - 1)) ^ 2) =
        ∑ j, ∑ k, finiteExpectation P w
          (fun ω => (g j ω - 1) * (g k ω - 1)) := by
      simp only [pow_two, Fintype.sum_mul_sum]
      rw [finiteExpectation_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [finiteExpectation_sum]
    _ = ∑ j, finiteVariance P w (g j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_eq_single j]
      · simp only [finiteVariance, pow_two]
      · intro k _ hkj
        exact centered_cross_expectation_eq_zero hmass hmean hfactor
          (Ne.symm hkj)
      · intro hj
        exact (hj (Finset.mem_univ j)).elim

theorem variance_uniformAlternativeAverage {Ω : Type*} {M : ℕ}
    [DecidableEq Ω]
    {P : Finset Ω} {w : Ω → ℝ} {g : Fin M → Ω → ℝ}
    (hM : 0 < M)
    (hmass : ∑ ω ∈ P, w ω = 1)
    (hmean : ∀ j, finiteExpectation P w (g j) = 1)
    (hfactor : PairwiseFactorizesUnder P w g) :
    finiteVariance P w (uniformAlternativeAverage g) =
      (∑ j, finiteVariance P w (g j)) / (M : ℝ) ^ 2 := by
  rw [finiteVariance, finiteExpectation]
  calc
    ∑ ω ∈ P, w ω * (uniformAlternativeAverage g ω - 1) ^ 2 =
        ∑ ω ∈ P,
          (w ω * (∑ j, (g j ω - 1)) ^ 2) / (M : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [uniformAlternativeAverage_sub_one hM]
      ring
    _ = finiteExpectation P w
          (fun ω => (∑ j, (g j ω - 1)) ^ 2) / (M : ℝ) ^ 2 := by
      rw [finiteExpectation, Finset.sum_div]
    _ = (∑ j, finiteVariance P w (g j)) / (M : ℝ) ^ 2 := by
      rw [expectation_sq_sum_centered hmass hmean hfactor]

/-- The core alternative-band estimate: averaging `M` independent
mean-one component densities divides the square root of the sum of their
variances by `M`. -/
theorem uniformAlternativeAverage_l1_le {Ω : Type*} {M : ℕ}
    [DecidableEq Ω]
    {P : Finset Ω} {w : Ω → ℝ} {g : Fin M → Ω → ℝ}
    (hM : 0 < M)
    (hw : ∀ ω ∈ P, 0 ≤ w ω)
    (hmass : ∑ ω ∈ P, w ω = 1)
    (_hg : ∀ j ω, ω ∈ P → 0 ≤ g j ω)
    (hmean : ∀ j, finiteExpectation P w (g j) = 1)
    (hfactor : PairwiseFactorizesUnder P w g) :
    finiteL1Error P w (uniformAlternativeAverage g) ≤
      Real.sqrt (∑ j, finiteVariance P w (g j)) / (M : ℝ) := by
  have hbase := finiteL1Error_le_sqrt_variance
    (P := P) (w := w) (X := uniformAlternativeAverage g) hw hmass
  rw [variance_uniformAlternativeAverage hM hmass hmean hfactor] at hbase
  have hvar : 0 ≤ ∑ j, finiteVariance P w (g j) :=
    Finset.sum_nonneg fun _ _ => finiteVariance_nonneg hw
  calc
    finiteL1Error P w (uniformAlternativeAverage g) ≤
        Real.sqrt ((∑ j, finiteVariance P w (g j)) /
          (M : ℝ) ^ 2) := hbase
    _ = Real.sqrt (∑ j, finiteVariance P w (g j)) / (M : ℝ) := by
      rw [Real.sqrt_div hvar, Real.sqrt_sq_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < M)]

/-- Individual second-moment bounds may be summed before applying the
alternative-band estimate. -/
theorem uniformAlternativeAverage_l1_le_of_secondMoments
    {Ω : Type*} {M : ℕ} [DecidableEq Ω]
    {P : Finset Ω} {w : Ω → ℝ} {g : Fin M → Ω → ℝ}
    (hM : 0 < M)
    (hw : ∀ ω ∈ P, 0 ≤ w ω)
    (hmass : ∑ ω ∈ P, w ω = 1)
    (hg : ∀ j ω, ω ∈ P → 0 ≤ g j ω)
    (hmean : ∀ j, finiteExpectation P w (g j) = 1)
    (hfactor : PairwiseFactorizesUnder P w g)
    (L : Fin M → ℝ)
    (hL2 : ∀ j, finiteSecondMoment P w (g j) ≤ L j) :
    finiteL1Error P w (uniformAlternativeAverage g) ≤
      Real.sqrt (∑ j, L j) / (M : ℝ) := by
  have hmain := uniformAlternativeAverage_l1_le
    hM hw hmass hg hmean hfactor
  have hvarL : ∑ j, finiteVariance P w (g j) ≤ ∑ j, L j := by
    apply Finset.sum_le_sum
    intro j _
    rw [finiteVariance_eq_secondMoment_sub_one hmass (hmean j)]
    linarith [hL2 j]
  have hsqrt := Real.sqrt_le_sqrt hvarL
  exact hmain.trans (div_le_div_of_nonneg_right hsqrt (by positivity))

/-- A uniform `L²` bound `K` gives the familiar `sqrt (K / M)` error. -/
theorem uniformAlternativeAverage_l1_le_of_uniform_secondMoment
    {Ω : Type*} {M : ℕ} [DecidableEq Ω]
    {P : Finset Ω} {w : Ω → ℝ} {g : Fin M → Ω → ℝ}
    (hM : 0 < M)
    (hw : ∀ ω ∈ P, 0 ≤ w ω)
    (hmass : ∑ ω ∈ P, w ω = 1)
    (hg : ∀ j ω, ω ∈ P → 0 ≤ g j ω)
    (hmean : ∀ j, finiteExpectation P w (g j) = 1)
    (hfactor : PairwiseFactorizesUnder P w g)
    {K : ℝ} (hK : 0 ≤ K)
    (hL2 : ∀ j, finiteSecondMoment P w (g j) ≤ K) :
    finiteL1Error P w (uniformAlternativeAverage g) ≤
      Real.sqrt (K / (M : ℝ)) := by
  have hvar : ∑ j, finiteVariance P w (g j) ≤ (M : ℝ) * K := by
    calc
      ∑ j, finiteVariance P w (g j) ≤ ∑ _j : Fin M, K := by
        apply Finset.sum_le_sum
        intro j _
        rw [finiteVariance_eq_secondMoment_sub_one hmass (hmean j)]
        linarith [hL2 j]
      _ = (M : ℝ) * K := by simp
  have hmain := uniformAlternativeAverage_l1_le
    hM hw hmass hg hmean hfactor
  have hden : (0 : ℝ) < M := by positivity
  calc
    finiteL1Error P w (uniformAlternativeAverage g) ≤
        Real.sqrt (∑ j, finiteVariance P w (g j)) / (M : ℝ) := hmain
    _ ≤ Real.sqrt ((M : ℝ) * K) / (M : ℝ) := by
      exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hvar) hden.le
    _ = Real.sqrt (K / (M : ℝ)) := by
      rw [Real.sqrt_mul hden.le, Real.sqrt_div hK]
      have hsqrtM : Real.sqrt (M : ℝ) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 hden)
      field_simp [hsqrtM]
      rw [Real.sq_sqrt hden.le]
      ring

/-- Product of the first `H` group densities. -/
def groupProductDensity {Ω : Type*}
    (G : ℕ → Ω → ℝ) (H : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ Finset.range H, G i ω

/-- Product of the group densities preceding group `i`. -/
def groupPrefixDensity {Ω : Type*}
    (G : ℕ → Ω → ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  ∏ k ∈ Finset.range i, G k ω

/-- The precise prefix factorization supplied by independence of disjoint
group blocks.  It is stated only for the functions used in the telescoping
argument, which makes it convenient for explicit finite product laws. -/
def HasIndependentPrefixes {Ω : Type*} [DecidableEq Ω]
    (P : Finset Ω) (w : Ω → ℝ) (G : ℕ → Ω → ℝ) (H : ℕ) : Prop :=
  ∀ i < H,
    finiteExpectation P w
        (fun ω => |G i ω - 1| * groupPrefixDensity G i ω) =
      finiteExpectation P w (fun ω => |G i ω - 1|) *
        ∏ k ∈ Finset.range i, finiteExpectation P w (G k)

theorem prod_range_sub_one_eq_sum_prefix (a : ℕ → ℝ) (H : ℕ) :
    (∏ i ∈ Finset.range H, a i) - 1 =
      ∑ i ∈ Finset.range H,
        (a i - 1) * ∏ k ∈ Finset.range i, a k := by
  induction H with
  | zero => simp
  | succ H ih =>
      rw [Finset.prod_range_succ, Finset.sum_range_succ]
      calc
        (∏ x ∈ Finset.range H, a x) * a H - 1 =
            ((∏ x ∈ Finset.range H, a x) - 1) +
              (a H - 1) * ∏ x ∈ Finset.range H, a x := by ring
        _ = ∑ x ∈ Finset.range H,
              (a x - 1) * ∏ k ∈ Finset.range x, a k +
              (a H - 1) * ∏ x ∈ Finset.range H, a x := by rw [ih]

/-- Independent mean-one group densities multiply with at most the sum of
their individual `L¹` errors. -/
theorem groupProductDensity_l1_le_sum {Ω : Type*} [DecidableEq Ω]
    {P : Finset Ω} {w : Ω → ℝ} {G : ℕ → Ω → ℝ} {H : ℕ}
    (hw : ∀ ω ∈ P, 0 ≤ w ω)
    (hG : ∀ i < H, ∀ ω ∈ P, 0 ≤ G i ω)
    (hmean : ∀ i < H, finiteExpectation P w (G i) = 1)
    (hindependent : HasIndependentPrefixes P w G H) :
    finiteL1Error P w (groupProductDensity G H) ≤
      ∑ i ∈ Finset.range H, finiteL1Error P w (G i) := by
  have hpointwise : ∀ ω ∈ P,
      |groupProductDensity G H ω - 1| ≤
        ∑ i ∈ Finset.range H,
          |G i ω - 1| * groupPrefixDensity G i ω := by
    intro ω hω
    rw [groupProductDensity, prod_range_sub_one_eq_sum_prefix]
    calc
      |∑ i ∈ Finset.range H,
          (G i ω - 1) * ∏ k ∈ Finset.range i, G k ω| ≤
          ∑ i ∈ Finset.range H,
            |(G i ω - 1) * ∏ k ∈ Finset.range i, G k ω| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.range H,
          |G i ω - 1| * groupPrefixDensity G i ω := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiH : i < H := Finset.mem_range.mp hi
        have hprefix : 0 ≤ ∏ k ∈ Finset.range i, G k ω := by
          exact Finset.prod_nonneg fun k hk =>
            hG k (lt_trans (Finset.mem_range.mp hk) hiH) ω hω
        rw [abs_mul, abs_of_nonneg hprefix]
        rfl
  calc
    finiteL1Error P w (groupProductDensity G H) ≤
        finiteExpectation P w (fun ω =>
          ∑ i ∈ Finset.range H,
            |G i ω - 1| * groupPrefixDensity G i ω) :=
      finiteExpectation_mono hw hpointwise
    _ = ∑ i ∈ Finset.range H,
          finiteExpectation P w
            (fun ω => |G i ω - 1| * groupPrefixDensity G i ω) := by
      simp only [finiteExpectation, mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range H,
          (finiteExpectation P w (fun ω => |G i ω - 1|) *
            ∏ k ∈ Finset.range i, finiteExpectation P w (G k)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hindependent i (Finset.mem_range.mp hi)
    _ = ∑ i ∈ Finset.range H, finiteL1Error P w (G i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiH : i < H := Finset.mem_range.mp hi
      have hprefixMean :
          ∏ k ∈ Finset.range i, finiteExpectation P w (G k) = 1 := by
        apply Finset.prod_eq_one
        intro k hk
        exact hmean k (lt_trans (Finset.mem_range.mp hk) hiH)
      rw [hprefixMean, mul_one]
      rfl

end Erdos536
