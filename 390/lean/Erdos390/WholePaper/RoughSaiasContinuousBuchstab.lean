import Erdos390.WholePaper.RoughSaiasStieltjesKernel

/-!
# The compact base-free functional behind continuous Buchstab

The de Bruijn approximation has a base-free Stieltjes description against

`d (floor t / t)`.

Since `t \mapsto floor t / t` is not monotone, Mathlib's positive
`StieltjesFunction.measure` is not the right primitive here.  On a finite
interval its signed action is instead represented explicitly as

`sum f(n) / n - integral f(t) floor(t) / t^2 dt`.

This file introduces that atom-minus-density functional, together with the
zero extension of the Dickman function which supplies its exact support.
The cutoff is kept as an explicit natural number: in the continuous
Buchstab identity the outer cutoff can then remain fixed while the first
argument changes from `x` to `x / s`.  The support lemmas below show that
this choice is harmless.

The eventual identification with `roughSaiasLambdaNormalForm` is a separate
finite Abel calculation.  In particular, no equality with the Stieltjes
normalization is built into any definition in this file.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## The supported Dickman profile -/

/-- The Dickman function with the classical zero extension on the negative
half-line.  The finite project function `rho` itself is deliberately equal
to one to the left of its first face, so this separate wrapper is needed in
the Stieltjes representation. -/
noncomputable def roughSaiasZeroExtendedRho (u : ℝ) : ℝ :=
  if u < 0 then 0 else rho u

@[simp]
theorem roughSaiasZeroExtendedRho_of_neg
    {u : ℝ} (hu : u < 0) :
    roughSaiasZeroExtendedRho u = 0 := by
  simp [roughSaiasZeroExtendedRho, hu]

theorem roughSaiasZeroExtendedRho_of_nonneg
    {u : ℝ} (hu : 0 ≤ u) :
    roughSaiasZeroExtendedRho u = rho u := by
  simp [roughSaiasZeroExtendedRho, not_lt.mpr hu]

@[simp]
theorem roughSaiasZeroExtendedRho_zero :
    roughSaiasZeroExtendedRho 0 = 1 := by
  simp [roughSaiasZeroExtendedRho]

theorem measurable_roughSaiasZeroExtendedRho :
    Measurable roughSaiasZeroExtendedRho := by
  unfold roughSaiasZeroExtendedRho
  apply Measurable.ite measurableSet_Iio measurable_const
  exact continuous_rho.measurable

/-- On the five constructed faces, the supported profile remains in the
unit interval. -/
theorem roughSaiasZeroExtendedRho_mem_unitInterval
    {u : ℝ} (hu5 : u ≤ 5) :
    0 ≤ roughSaiasZeroExtendedRho u ∧
      roughSaiasZeroExtendedRho u ≤ 1 := by
  by_cases hu : u < 0
  · simp [roughSaiasZeroExtendedRho_of_neg hu]
  · have hu0 : 0 ≤ u := le_of_not_gt hu
    rw [roughSaiasZeroExtendedRho_of_nonneg hu0]
    exact ⟨(rho_pos_on_zero_five hu0 hu5).le,
      FriableAsymptotic.rho_le_one_of_le_five hu5⟩

theorem roughSaiasZeroExtendedRho_abs_le_one
    {u : ℝ} (hu5 : u ≤ 5) :
    |roughSaiasZeroExtendedRho u| ≤ 1 := by
  have h := roughSaiasZeroExtendedRho_mem_unitInterval hu5
  rw [abs_of_nonneg h.1]
  exact h.2

/-- The base-free Dickman profile on which the compact Stieltjes functional
acts. -/
noncomputable def roughSaiasStieltjesDickmanProfile
    (x y t : ℝ) : ℝ :=
  x * roughSaiasZeroExtendedRho
    (Real.log (x / t) / Real.log y)

theorem measurable_roughSaiasStieltjesDickmanProfile
    (x y : ℝ) :
    Measurable (roughSaiasStieltjesDickmanProfile x y) := by
  have hquot : Measurable (fun t : ℝ => x / t) :=
    measurable_const.div measurable_id
  have hcoordinate : Measurable
      (fun t : ℝ => Real.log (x / t) / Real.log y) :=
    (Real.measurable_log.comp hquot).div measurable_const
  exact measurable_const.mul
    (measurable_roughSaiasZeroExtendedRho.comp hcoordinate)

/-- The supported profile is exactly zero beyond its first argument. -/
theorem roughSaiasStieltjesDickmanProfile_eq_zero_of_lt
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (ht : 0 < t) (hxt : x < t) :
    roughSaiasStieltjesDickmanProfile x y t = 0 := by
  have hratioPos : 0 < x / t := div_pos hx ht
  have hratioLt : x / t < 1 := (div_lt_one ht).2 hxt
  have hlogRatio : Real.log (x / t) < 0 :=
    Real.log_neg hratioPos hratioLt
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hcoordinate : Real.log (x / t) / Real.log y < 0 :=
    div_neg_of_neg_of_pos hlogRatio hlogy
  unfold roughSaiasStieltjesDickmanProfile
  rw [roughSaiasZeroExtendedRho_of_neg hcoordinate, mul_zero]

@[simp]
theorem roughSaiasStieltjesDickmanProfile_self
    {x y : ℝ} (hx : x ≠ 0) :
    roughSaiasStieltjesDickmanProfile x y x = x := by
  unfold roughSaiasStieltjesDickmanProfile
  rw [div_self hx, Real.log_one, zero_div,
    roughSaiasZeroExtendedRho_zero, mul_one]

theorem roughSaiasStieltjesDickmanProfile_one
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 < y) :
    roughSaiasStieltjesDickmanProfile x y 1 =
      x * rho (Real.log x / Real.log y) := by
  have hcoordinate :
      0 ≤ Real.log x / Real.log y :=
    div_nonneg (Real.log_nonneg hx) (Real.log_pos hy).le
  unfold roughSaiasStieltjesDickmanProfile
  rw [div_one, roughSaiasZeroExtendedRho_of_nonneg hcoordinate]

/-- On the supported interval, the logarithmic quotient used in this file
is the real coordinate from `RoughSaiasStieltjesKernel`. -/
theorem roughSaiasStieltjesCoordinate_eq_log_div
    {x y t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    roughSaiasStieltjesCoordinate x y t =
      Real.log (x / t) / Real.log y := by
  unfold roughSaiasStieltjesCoordinate
  rw [Real.log_div hx.ne' ht.ne']

/-- Dividing the supported profile by the Stieltjes variable gives exactly
the corner-safe Abel test from `RoughSaiasStieltjesKernel`. -/
theorem roughSaiasStieltjesDickmanProfile_div_eq_test
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (ht : 0 < t) (htx : t ≤ x) :
    roughSaiasStieltjesDickmanProfile x y t / t =
      roughSaiasStieltjesTest x y t := by
  have hratio : 1 ≤ x / t := by
    exact (le_div_iff₀ ht).2 (by simpa using htx)
  have hcoordinate :
      0 ≤ Real.log (x / t) / Real.log y :=
    div_nonneg (Real.log_nonneg hratio) (Real.log_pos hy).le
  unfold roughSaiasStieltjesDickmanProfile roughSaiasStieltjesTest
    roughSaiasStieltjesCoordinate
  rw [roughSaiasZeroExtendedRho_of_nonneg hcoordinate,
    Real.log_div hx.ne' ht.ne']

/-- Multiplicative form of the preceding test-profile identification. -/
theorem roughSaiasStieltjesDickmanProfile_eq_mul_test
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (ht : 0 < t) (htx : t ≤ x) :
    roughSaiasStieltjesDickmanProfile x y t =
      t * roughSaiasStieltjesTest x y t := by
  have h := roughSaiasStieltjesDickmanProfile_div_eq_test
    hx hy ht htx
  have ht0 : t ≠ 0 := ht.ne'
  calc
    roughSaiasStieltjesDickmanProfile x y t =
        (roughSaiasStieltjesDickmanProfile x y t / t) * t :=
      (div_mul_cancel₀ _ ht0).symm
    _ = t * roughSaiasStieltjesTest x y t := by
      rw [h]
      ring

@[simp]
theorem roughSaiasStieltjesTest_self
    {x y : ℝ} (hx : x ≠ 0) :
    roughSaiasStieltjesTest x y x = 1 := by
  unfold roughSaiasStieltjesTest roughSaiasStieltjesCoordinate
  rw [sub_self, zero_div, rho_zero, mul_one, div_self hx]

/-! ## The finite atom-minus-density functional -/

/-- The absolutely continuous density in
`d (floor t / t)`: its sign is subtracted in the functional below. -/
noncomputable def roughSaiasFloorDensity (t : ℝ) : ℝ :=
  ((⌊t⌋₊ : ℕ) : ℝ) / t ^ (2 : ℕ)

theorem measurable_roughSaiasFloorDensity :
    Measurable roughSaiasFloorDensity := by
  have hfloorNat : Measurable (fun t : ℝ => ⌊t⌋₊) :=
    measurable_id.nat_floor
  have hfloorReal : Measurable (fun t : ℝ => ((⌊t⌋₊ : ℕ) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hfloorNat
  exact hfloorReal.div (measurable_id.pow_const 2)

/-- Atomic part of the compact signed Stieltjes functional. -/
noncomputable def roughSaiasStieltjesAtomPart
    (R : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 R, f (n : ℝ) / (n : ℝ)

/-- Absolutely continuous part of the compact signed Stieltjes functional. -/
noncomputable def roughSaiasStieltjesDensityPart
    (R : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∫ t in Set.Ioc (1 : ℝ) (R : ℝ),
    f t * roughSaiasFloorDensity t

/-- The compact realization of integration against
`d (floor t / t)`. -/
noncomputable def roughSaiasFiniteStieltjesFunctional
    (R : ℕ) (f : ℝ → ℝ) : ℝ :=
  roughSaiasStieltjesAtomPart R f -
    roughSaiasStieltjesDensityPart R f

@[simp]
theorem roughSaiasStieltjesAtomPart_zero (R : ℕ) :
    roughSaiasStieltjesAtomPart R (fun _ => 0) = 0 := by
  simp [roughSaiasStieltjesAtomPart]

@[simp]
theorem roughSaiasStieltjesDensityPart_zero (R : ℕ) :
    roughSaiasStieltjesDensityPart R (fun _ => 0) = 0 := by
  simp [roughSaiasStieltjesDensityPart]

@[simp]
theorem roughSaiasFiniteStieltjesFunctional_zero (R : ℕ) :
    roughSaiasFiniteStieltjesFunctional R (fun _ => 0) = 0 := by
  simp [roughSaiasFiniteStieltjesFunctional]

theorem roughSaiasStieltjesAtomPart_add
    (R : ℕ) (f g : ℝ → ℝ) :
    roughSaiasStieltjesAtomPart R (fun t => f t + g t) =
      roughSaiasStieltjesAtomPart R f +
        roughSaiasStieltjesAtomPart R g := by
  unfold roughSaiasStieltjesAtomPart
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem roughSaiasStieltjesDensityPart_add
    {R : ℕ} {f g : ℝ → ℝ}
    (hf : IntegrableOn
      (fun t => f t * roughSaiasFloorDensity t)
      (Set.Ioc (1 : ℝ) (R : ℝ)))
    (hg : IntegrableOn
      (fun t => g t * roughSaiasFloorDensity t)
      (Set.Ioc (1 : ℝ) (R : ℝ))) :
    roughSaiasStieltjesDensityPart R (fun t => f t + g t) =
      roughSaiasStieltjesDensityPart R f +
        roughSaiasStieltjesDensityPart R g := by
  unfold roughSaiasStieltjesDensityPart
  rw [← MeasureTheory.integral_add hf hg]
  apply integral_congr_ae
  filter_upwards with t
  ring

theorem roughSaiasFiniteStieltjesFunctional_add
    {R : ℕ} {f g : ℝ → ℝ}
    (hf : IntegrableOn
      (fun t => f t * roughSaiasFloorDensity t)
      (Set.Ioc (1 : ℝ) (R : ℝ)))
    (hg : IntegrableOn
      (fun t => g t * roughSaiasFloorDensity t)
      (Set.Ioc (1 : ℝ) (R : ℝ))) :
    roughSaiasFiniteStieltjesFunctional R (fun t => f t + g t) =
      roughSaiasFiniteStieltjesFunctional R f +
        roughSaiasFiniteStieltjesFunctional R g := by
  unfold roughSaiasFiniteStieltjesFunctional
  rw [roughSaiasStieltjesAtomPart_add,
    roughSaiasStieltjesDensityPart_add hf hg]
  ring

/-- Pointwise equality on the atoms and almost-everywhere equality on the
density determine the finite functional. -/
theorem roughSaiasFiniteStieltjesFunctional_congr
    {R : ℕ} {f g : ℝ → ℝ}
    (hatom : ∀ n ∈ Finset.Icc 1 R, f (n : ℝ) = g (n : ℝ))
    (hdensity : f =ᵐ[volume.restrict
      (Set.Ioc (1 : ℝ) (R : ℝ))] g) :
    roughSaiasFiniteStieltjesFunctional R f =
      roughSaiasFiniteStieltjesFunctional R g := by
  have hsum : roughSaiasStieltjesAtomPart R f =
      roughSaiasStieltjesAtomPart R g := by
    unfold roughSaiasStieltjesAtomPart
    apply Finset.sum_congr rfl
    intro n hn
    rw [hatom n hn]
  have hint : roughSaiasStieltjesDensityPart R f =
      roughSaiasStieltjesDensityPart R g := by
    unfold roughSaiasStieltjesDensityPart
    apply integral_congr_ae
    filter_upwards [hdensity] with t ht
    rw [ht]
  unfold roughSaiasFiniteStieltjesFunctional
  rw [hsum, hint]

/-! ## Cutoff independence -/

theorem roughSaiasStieltjesAtomPart_eq_of_cutoff
    {R S : ℕ} {f : ℝ → ℝ} (hRS : R ≤ S)
    (hzero : ∀ n, R < n → n ≤ S → f (n : ℝ) = 0) :
    roughSaiasStieltjesAtomPart R f =
      roughSaiasStieltjesAtomPart S f := by
  unfold roughSaiasStieltjesAtomPart
  apply Finset.sum_subset
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hRS⟩
  · intro n hnS hnR
    have hnData := Finset.mem_Icc.mp hnS
    have hRn : R < n := by
      by_contra hnot
      apply hnR
      exact Finset.mem_Icc.mpr ⟨hnData.1, le_of_not_gt hnot⟩
    rw [hzero n hRn hnData.2, zero_div]

theorem roughSaiasStieltjesDensityPart_eq_of_cutoff
    {R S : ℕ} {f : ℝ → ℝ} (hRS : R ≤ S)
    (hzero : ∀ t, (R : ℝ) < t → t ≤ (S : ℝ) → f t = 0) :
    roughSaiasStieltjesDensityPart R f =
      roughSaiasStieltjesDensityPart S f := by
  have hsubset : Set.Ioc (1 : ℝ) (R : ℝ) ⊆
      Set.Ioc (1 : ℝ) (S : ℝ) := by
    rintro t ⟨ht1, htR⟩
    exact ⟨ht1, htR.trans (by exact_mod_cast hRS)⟩
  unfold roughSaiasStieltjesDensityPart
  symm
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
    measurableSet_Ioc hsubset
  intro t ht
  have htS := ht.1
  have htNotR := ht.2
  have hRt : (R : ℝ) < t := by
    by_contra hnot
    exact htNotR ⟨htS.1, le_of_not_gt hnot⟩
  rw [hzero t hRt htS.2, zero_mul]

theorem roughSaiasFiniteStieltjesFunctional_eq_of_cutoff
    {R S : ℕ} {f : ℝ → ℝ} (hRS : R ≤ S)
    (hzero : ∀ t, (R : ℝ) < t → t ≤ (S : ℝ) → f t = 0) :
    roughSaiasFiniteStieltjesFunctional R f =
      roughSaiasFiniteStieltjesFunctional S f := by
  have hzeroNat : ∀ n, R < n → n ≤ S → f (n : ℝ) = 0 := by
    intro n hRn hnS
    exact hzero (n : ℝ) (by exact_mod_cast hRn) (by exact_mod_cast hnS)
  unfold roughSaiasFiniteStieltjesFunctional
  rw [roughSaiasStieltjesAtomPart_eq_of_cutoff hRS hzeroNat,
    roughSaiasStieltjesDensityPart_eq_of_cutoff hRS hzero]

/-! ## A real-base de Bruijn functional -/

/-- The real-base de Bruijn functional with an explicit compact cap. -/
noncomputable def roughSaiasLambdaStieltjesWithCutoff
    (R : ℕ) (x y : ℝ) : ℝ :=
  roughSaiasFiniteStieltjesFunctional R
    (roughSaiasStieltjesDickmanProfile x y)

/-- Canonical real-base version, using the least natural cap above `x`. -/
noncomputable def roughSaiasLambdaStieltjes
    (x y : ℝ) : ℝ :=
  roughSaiasLambdaStieltjesWithCutoff ⌈x⌉₊ x y

/-- Once the cap lies above `x`, enlarging it changes neither the atoms nor
the density. -/
theorem roughSaiasLambdaStieltjesWithCutoff_eq_of_le
    {R S : ℕ} {x y : ℝ} (hRS : R ≤ S)
    (hx : 0 < x) (hy : 1 < y) (hxR : x ≤ (R : ℝ)) :
    roughSaiasLambdaStieltjesWithCutoff R x y =
      roughSaiasLambdaStieltjesWithCutoff S x y := by
  unfold roughSaiasLambdaStieltjesWithCutoff
  apply roughSaiasFiniteStieltjesFunctional_eq_of_cutoff hRS
  intro t hRt htS
  have hxt : x < t := hxR.trans_lt hRt
  exact roughSaiasStieltjesDickmanProfile_eq_zero_of_lt
    hx hy (hx.trans hxt) hxt

theorem roughSaiasLambdaStieltjesWithCutoff_eq_canonical
    {R : ℕ} {x y : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hxR : x ≤ (R : ℝ)) :
    roughSaiasLambdaStieltjesWithCutoff R x y =
      roughSaiasLambdaStieltjes x y := by
  have hceilR : ⌈x⌉₊ ≤ R := Nat.ceil_le.mpr hxR
  unfold roughSaiasLambdaStieltjes
  symm
  exact roughSaiasLambdaStieltjesWithCutoff_eq_of_le
    hceilR hx hy (Nat.le_ceil x)

/-- At a positive natural outer endpoint, the atom part is literally the
finite sum of the corner-safe Abel test. -/
theorem roughSaiasStieltjesAtomPart_profile_nat
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y) :
    roughSaiasStieltjesAtomPart X
        (roughSaiasStieltjesDickmanProfile (X : ℝ) y) =
      ∑ n ∈ Finset.Icc 1 X,
        roughSaiasStieltjesTest (X : ℝ) y (n : ℝ) := by
  unfold roughSaiasStieltjesAtomPart
  apply Finset.sum_congr rfl
  intro n hn
  have hnData := Finset.mem_Icc.mp hn
  exact roughSaiasStieltjesDickmanProfile_div_eq_test
    (by exact_mod_cast hX) hy (by exact_mod_cast hnData.1)
      (by exact_mod_cast hnData.2)

/-- Right-derivative Abel summation for the exact atom sum.  This is the
corner-safe integration-by-parts step; the remaining cancellation with the
floor density is kept separate. -/
theorem roughSaiasStieltjesTest_sum_eq_endpoint_sub_integral
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    (∑ n ∈ Finset.Icc 1 X,
        roughSaiasStieltjesTest (X : ℝ) y (n : ℝ)) =
      (X : ℝ) -
        ∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
          roughSaiasStieltjesTestRightDerivative (X : ℝ) y t *
            ((⌊t⌋₊ : ℕ) : ℝ) := by
  have hcont : ContinuousOn
      (roughSaiasStieltjesTest (X : ℝ) y)
      (Set.Icc ((1 : ℕ) : ℝ) (X : ℝ)) :=
    continuousOn_roughSaiasStieltjesTest hy (by norm_num)
  have hright : ∀ t ∈ Set.Ioo ((1 : ℕ) : ℝ) (X : ℝ),
      HasDerivWithinAt (roughSaiasStieltjesTest (X : ℝ) y)
        (roughSaiasStieltjesTestRightDerivative (X : ℝ) y t)
        (Set.Ioi t) t := by
    simpa only [Nat.cast_one] using
      (roughSaiasStieltjesTest_hasRightDerivOn
        (x := (X : ℝ)) (y := y) (R := (X : ℝ))
        hy (by exact_mod_cast hX) le_rfl hu5)
  have hint : IntegrableOn
      (roughSaiasStieltjesTestRightDerivative (X : ℝ) y)
      (Set.Icc ((1 : ℕ) : ℝ) (X : ℝ)) := by
    simpa only [Nat.cast_one] using
      (integrableOn_roughSaiasStieltjesTestRightDerivative hX hy hu5)
  have hAbel :=
    RoughSaiasRightAbel.sum_mul_eq_sub_sub_integral_mul_right'
      FriableAsymptotic.positiveIncrement
      (f := roughSaiasStieltjesTest (X : ℝ) y)
      (f' := roughSaiasStieltjesTestRightDerivative (X : ℝ) y)
      (n := 1) (m := X)
      hX hcont hright hint
  have hcum (N : ℕ) :
      (∑ k ∈ Finset.Icc 0 N,
          FriableAsymptotic.positiveIncrement k) = (N : ℝ) := by
    have hfin : Finset.Icc 0 N = Finset.range (N + 1) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_range]
      omega
    rw [hfin]
    exact FriableAsymptotic.sum_range_positiveIncrement N
  have hweighted :
      (∑ k ∈ Finset.Ioc 1 X,
          roughSaiasStieltjesTest (X : ℝ) y (k : ℝ) *
            FriableAsymptotic.positiveIncrement k) =
        ∑ k ∈ Finset.Ioc 1 X,
          roughSaiasStieltjesTest (X : ℝ) y (k : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : k ≠ 0 := by
      rw [Finset.mem_Ioc] at hk
      omega
    simp [FriableAsymptotic.positiveIncrement, hk0]
  rw [hweighted] at hAbel
  simp_rw [hcum] at hAbel
  rw [roughSaiasStieltjesTest_self
      (x := (X : ℝ)) (y := y) (by exact_mod_cast (show X ≠ 0 by omega))]
    at hAbel
  nth_rewrite 1 [Finset.Icc_eq_cons_Ioc hX]
  rw [Finset.sum_cons, hAbel]
  ring

/-- Expansion of the capped real-base functional at a natural outer
endpoint into the Abel test sum and its floor density. -/
theorem roughSaiasLambdaStieltjesWithCutoff_nat_eq_test_sub_density
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y) :
    roughSaiasLambdaStieltjesWithCutoff X (X : ℝ) y =
      (∑ n ∈ Finset.Icc 1 X,
          roughSaiasStieltjesTest (X : ℝ) y (n : ℝ)) -
        roughSaiasStieltjesDensityPart X
          (roughSaiasStieltjesDickmanProfile (X : ℝ) y) := by
  unfold roughSaiasLambdaStieltjesWithCutoff
    roughSaiasFiniteStieltjesFunctional
  rw [roughSaiasStieltjesAtomPart_profile_nat hX hy]

/-- The full capped functional after the corner-safe Abel step, before the
algebraic cancellation between the displayed derivative and the density. -/
theorem roughSaiasLambdaStieltjesWithCutoff_nat_eq_abel_ledger
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    roughSaiasLambdaStieltjesWithCutoff X (X : ℝ) y =
      ((X : ℝ) -
          (∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
            roughSaiasStieltjesTestRightDerivative (X : ℝ) y t *
              ((⌊t⌋₊ : ℕ) : ℝ))) -
        roughSaiasStieltjesDensityPart X
          (roughSaiasStieltjesDickmanProfile (X : ℝ) y) := by
  rw [roughSaiasLambdaStieltjesWithCutoff_nat_eq_test_sub_density
      hX hy,
    roughSaiasStieltjesTest_sum_eq_endpoint_sub_integral hX hy hu5]

@[simp]
theorem roughSaiasLambdaStieltjes_nat
    (X : ℕ) (y : ℝ) :
    roughSaiasLambdaStieltjes (X : ℝ) y =
      roughSaiasLambdaStieltjesWithCutoff X (X : ℝ) y := by
  simp [roughSaiasLambdaStieltjes]

/-- The integrand which appears after applying the continuous Buchstab
identity pointwise under the fixed compact functional. -/
noncomputable def roughSaiasContinuousBuchstabProfile
    (x s t : ℝ) : ℝ :=
  roughSaiasStieltjesDickmanProfile (x / s) s t /
    Real.log s

/-- On a nonnegative Dickman coordinate, the supported profile is a fixed
multiple of the project's ordinary Dickman antiderivative. -/
theorem roughSaiasStieltjesDickmanProfile_eq_mul_antiderivative
    {x y t : ℝ} (ht : 0 < t)
    (hcoordinate : 0 ≤ Real.log (x / t) / Real.log y) :
    roughSaiasStieltjesDickmanProfile x y t =
      t * FriableAsymptotic.dickmanAntiderivative (x / t) y := by
  unfold roughSaiasStieltjesDickmanProfile
    FriableAsymptotic.dickmanAntiderivative
  rw [roughSaiasZeroExtendedRho_of_nonneg hcoordinate]
  field_simp [ht.ne']

/-- In the active region, the pointwise continuous-Buchstab profile is a
fixed multiple of the ordinary Dickman continuous weight. -/
theorem roughSaiasContinuousBuchstabProfile_eq_mul_dickmanWeight
    {x s t : ℝ} (hx : 0 < x) (hs : 1 < s) (ht : 0 < t)
    (hactive : 1 ≤ Real.log (x / t) / Real.log s) :
    roughSaiasContinuousBuchstabProfile x s t =
      t * FriableAsymptotic.dickmanContinuousWeight (x / t) s := by
  have hspos : 0 < s := zero_lt_one.trans hs
  have hqpos : 0 < x / t := div_pos hx ht
  have hlogS : 0 < Real.log s := Real.log_pos hs
  have hquotient : (x / s) / t = (x / t) / s := by
    field_simp [hspos.ne', ht.ne']
  have hcoordinate :
      Real.log ((x / s) / t) / Real.log s =
        Real.log (x / t) / Real.log s - 1 := by
    rw [hquotient, Real.log_div hqpos.ne' hspos.ne']
    field_simp [hlogS.ne']
  have hdelayNonneg :
      0 ≤ Real.log (x / t) / Real.log s - 1 := by
    linarith
  unfold roughSaiasContinuousBuchstabProfile
    roughSaiasStieltjesDickmanProfile
    FriableAsymptotic.dickmanContinuousWeight
  rw [hcoordinate,
    roughSaiasZeroExtendedRho_of_nonneg hdelayNonneg]
  field_simp [hspos.ne', ht.ne', hlogS.ne']

theorem roughSaiasContinuousBuchstabProfile_eq_zero_of_lt
    {x s t : ℝ} (hx : 0 < x) (hs : 1 < s) (ht : 0 < t)
    (hxt : x / s < t) :
    roughSaiasContinuousBuchstabProfile x s t = 0 := by
  unfold roughSaiasContinuousBuchstabProfile
  rw [roughSaiasStieltjesDickmanProfile_eq_zero_of_lt
      (div_pos hx (zero_lt_one.trans hs)) hs ht hxt,
    zero_div]

/-- Below the base, the supported Dickman profile is on its initial face
and is therefore exactly its first argument. -/
theorem roughSaiasStieltjesDickmanProfile_eq_first_of_one_le_ratio
    {x y t : ℝ} (hy : 1 < y)
    (hq1 : 1 ≤ x / t) (hqy : x / t ≤ y) :
    roughSaiasStieltjesDickmanProfile x y t = x := by
  have hqpos : 0 < x / t := zero_lt_one.trans_le hq1
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hlogq : 0 ≤ Real.log (x / t) := Real.log_nonneg hq1
  have hlogqy : Real.log (x / t) ≤ Real.log y :=
    Real.log_le_log hqpos hqy
  have hcoordinateNonneg :
      0 ≤ Real.log (x / t) / Real.log y :=
    div_nonneg hlogq hlogy.le
  have hcoordinateOne :
      Real.log (x / t) / Real.log y ≤ 1 :=
    (div_le_one hlogy).2 hlogqy
  unfold roughSaiasStieltjesDickmanProfile
  rw [roughSaiasZeroExtendedRho_of_nonneg hcoordinateNonneg,
    rho_eq_one_of_le_one hcoordinateOne, mul_one]

/-- The continuous-Buchstab profile is interval integrable up to its birth
face.  At the top endpoint it agrees with the continuous Dickman weight;
this is why the non-strict active-coordinate lemma is used here. -/
theorem intervalIntegrable_roughSaiasContinuousBuchstabProfile_to_birth
    {x t y : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hy : 1 < y) (hyq : y < x / t) :
    IntervalIntegrable (roughSaiasContinuousBuchstabProfile x · t)
      volume y (x / t) := by
  have hcontWeight : ContinuousOn
      (FriableAsymptotic.dickmanContinuousWeight (x / t))
      (Set.Icc y (x / t)) :=
    (FriableAsymptotic.continuousOn_dickmanContinuousWeight
      (x / t)).mono (fun s hs => by
        rw [Set.mem_Ioi]
        exact hy.trans_le hs.1)
  have hcont : ContinuousOn
      (fun s => t *
        FriableAsymptotic.dickmanContinuousWeight (x / t) s)
      (Set.Icc y (x / t)) :=
    continuousOn_const.mul hcontWeight
  have hbase := hcont.intervalIntegrable_of_Icc
    (μ := volume) hyq.le
  apply hbase.congr
  intro s hsU
  have hsI : s ∈ Set.Ioc y (x / t) := by
    simpa only [Set.uIoc_of_le hyq.le] using hsU
  have hsone : 1 < s := hy.trans hsI.1
  have hspos : 0 < s := zero_lt_one.trans hsone
  have hlogSQ : Real.log s ≤ Real.log (x / t) :=
    Real.log_le_log hspos hsI.2
  have hactive : 1 ≤ Real.log (x / t) / Real.log s :=
    (one_le_div (Real.log_pos hsone)).2 hlogSQ
  exact (roughSaiasContinuousBuchstabProfile_eq_mul_dickmanWeight
    hx hsone ht hactive).symm

/-- Past the birth face, the continuous-Buchstab profile is interval
integrable (and vanishes away from the excluded left endpoint). -/
theorem intervalIntegrable_roughSaiasContinuousBuchstabProfile_from_birth
    {x t z : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hq1 : 1 < x / t) (hqz : x / t ≤ z) :
    IntervalIntegrable (roughSaiasContinuousBuchstabProfile x · t)
      volume (x / t) z := by
  have hzero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ))
      volume (x / t) z := continuous_const.intervalIntegrable _ _
  apply hzero.congr
  intro s hsU
  have hsI : s ∈ Set.Ioc (x / t) z := by
    simpa only [Set.uIoc_of_le hqz] using hsU
  have hsone : 1 < s := hq1.trans hsI.1
  have hspos : 0 < s := zero_lt_one.trans hsone
  have hxsMul : x < s * t := (div_lt_iff₀ ht).mp hsI.1
  have hxs : x / s < t := by
    apply (div_lt_iff₀ hspos).2
    simpa only [mul_comm] using hxsMul
  exact (roughSaiasContinuousBuchstabProfile_eq_zero_of_lt
    hx hsone ht hxs).symm

/-- The integral beyond the birth face vanishes.  The value at the left
endpoint itself is immaterial for the interval integral. -/
theorem roughSaiasContinuousBuchstabProfile_integral_from_birth_eq_zero
    {x t z : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hq1 : 1 < x / t) (hqz : x / t ≤ z) :
    (∫ s in (x / t)..z,
      roughSaiasContinuousBuchstabProfile x s t) = 0 := by
  have hcongr :
      (∫ s in (x / t)..z,
        roughSaiasContinuousBuchstabProfile x s t) =
        ∫ _s in (x / t)..z, (0 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s
    intro hsU
    have hsI : s ∈ Set.Ioc (x / t) z := by
      simpa only [Set.uIoc_of_le hqz] using hsU
    have hsone : 1 < s := hq1.trans hsI.1
    have hspos : 0 < s := zero_lt_one.trans hsone
    have hxsMul : x < s * t := (div_lt_iff₀ ht).mp hsI.1
    have hxs : x / s < t := by
      apply (div_lt_iff₀ hspos).2
      simpa only [mul_comm] using hxsMul
    exact roughSaiasContinuousBuchstabProfile_eq_zero_of_lt
      hx hsone ht hxs
  simpa using hcongr

/-- Pointwise continuous Buchstab on an interval where the quotient remains
strictly active.  This is exactly the already-proved Dickman FTC, transported
through the fixed Stieltjes variable `t`. -/
theorem roughSaiasStieltjesDickmanProfile_buchstab_active
    {x t y z : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hy : 1 < y) (hyz : y ≤ z) (hzActive : z < x / t)
    (hu6 : Real.log (x / t) / Real.log y ≤ 6) :
    roughSaiasStieltjesDickmanProfile x y t =
      roughSaiasStieltjesDickmanProfile x z t -
        ∫ s in y..z, roughSaiasContinuousBuchstabProfile x s t := by
  have hypos : 0 < y := zero_lt_one.trans hy
  have hzpos : 0 < z := hypos.trans_le hyz
  have hqpos : 0 < x / t := hzpos.trans hzActive
  have hqone : 1 < x / t := (hy.trans_le hyz).trans hzActive
  have hlogQ : 0 < Real.log (x / t) := Real.log_pos hqone
  have hratio : ∀ s ∈ Set.Icc y z,
      1 < Real.log (x / t) / Real.log s ∧
        Real.log (x / t) / Real.log s ≤ 6 := by
    intro s hsI
    have hspos : 0 < s := hypos.trans_le hsI.1
    have hsone : 1 < s := hy.trans_le hsI.1
    have hlogs : 0 < Real.log s := Real.log_pos hsone
    have hsQ : s < x / t := hsI.2.trans_lt hzActive
    have hlogSQ : Real.log s < Real.log (x / t) :=
      Real.strictMonoOn_log hspos hqpos hsQ
    have hlogYS : Real.log y ≤ Real.log s :=
      Real.log_le_log hypos hsI.1
    constructor
    · exact (one_lt_div hlogs).2 hlogSQ
    · exact (div_le_div_of_nonneg_left hlogQ.le
        (Real.log_pos hy) hlogYS).trans hu6
  have hIntegral := FriableAsymptotic.integral_dickmanContinuousWeight
    (x / t) y z hy hyz hratio
  have hkernel :
      (∫ s in y..z, roughSaiasContinuousBuchstabProfile x s t) =
        t * ∫ s in y..z,
          FriableAsymptotic.dickmanContinuousWeight (x / t) s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hsI
    have hsI' : s ∈ Set.Icc y z := by
      simpa [Set.uIcc_of_le hyz] using hsI
    exact roughSaiasContinuousBuchstabProfile_eq_mul_dickmanWeight
      hx (hy.trans_le hsI'.1) ht (hratio s hsI').1.le
  have hyCoordinate :
      0 ≤ Real.log (x / t) / Real.log y :=
    le_trans (by norm_num) (hratio y ⟨le_rfl, hyz⟩).1.le
  have hzCoordinate :
      0 ≤ Real.log (x / t) / Real.log z :=
    le_trans (by norm_num) (hratio z ⟨hyz, le_rfl⟩).1.le
  rw [roughSaiasStieltjesDickmanProfile_eq_mul_antiderivative
      ht hyCoordinate,
    roughSaiasStieltjesDickmanProfile_eq_mul_antiderivative
      ht hzCoordinate,
    hkernel, hIntegral]
  ring

/-- Pointwise continuous Buchstab when the upper endpoint is exactly the
birth face.  The closed-top Dickman FTC supplies the endpoint case `u = 1`;
no derivative is asserted at that corner. -/
theorem roughSaiasStieltjesDickmanProfile_buchstab_birth
    {x t y : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hy : 1 < y) (hyq : y < x / t)
    (hu6 : Real.log (x / t) / Real.log y ≤ 6) :
    roughSaiasStieltjesDickmanProfile x y t =
      roughSaiasStieltjesDickmanProfile x (x / t) t -
        ∫ s in y..(x / t),
          roughSaiasContinuousBuchstabProfile x s t := by
  have hypos : 0 < y := zero_lt_one.trans hy
  have hqpos : 0 < x / t := hypos.trans hyq
  have hlogQ : 0 < Real.log (x / t) :=
    Real.log_pos (hy.trans hyq)
  have hratio : ∀ s ∈ Set.Icc y (x / t),
      1 ≤ Real.log (x / t) / Real.log s ∧
        Real.log (x / t) / Real.log s ≤ 6 := by
    intro s hsI
    have hspos : 0 < s := hypos.trans_le hsI.1
    have hsone : 1 < s := hy.trans_le hsI.1
    have hlogs : 0 < Real.log s := Real.log_pos hsone
    have hlogSQ : Real.log s ≤ Real.log (x / t) :=
      Real.log_le_log hspos hsI.2
    have hlogYS : Real.log y ≤ Real.log s :=
      Real.log_le_log hypos hsI.1
    constructor
    · exact (one_le_div hlogs).2 hlogSQ
    · exact (div_le_div_of_nonneg_left hlogQ.le
        (Real.log_pos hy) hlogYS).trans hu6
  have hIntegral :=
    FriableAsymptotic.integral_dickmanContinuousWeight_closed_top
      (x / t) y (x / t) hy hyq hratio
  have hkernel :
      (∫ s in y..(x / t),
          roughSaiasContinuousBuchstabProfile x s t) =
        t * ∫ s in y..(x / t),
          FriableAsymptotic.dickmanContinuousWeight (x / t) s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hsI
    have hsI' : s ∈ Set.Icc y (x / t) := by
      simpa [Set.uIcc_of_le hyq.le] using hsI
    exact roughSaiasContinuousBuchstabProfile_eq_mul_dickmanWeight
      hx (hy.trans_le hsI'.1) ht (hratio s hsI').1
  have hyCoordinate :
      0 ≤ Real.log (x / t) / Real.log y :=
    le_trans (by norm_num) (hratio y ⟨le_rfl, hyq.le⟩).1
  have hqCoordinate :
      0 ≤ Real.log (x / t) / Real.log (x / t) :=
    le_trans (by norm_num)
      (hratio (x / t) ⟨hyq.le, le_rfl⟩).1
  rw [roughSaiasStieltjesDickmanProfile_eq_mul_antiderivative
      ht hyCoordinate,
    roughSaiasStieltjesDickmanProfile_eq_mul_antiderivative
      ht hqCoordinate,
    hkernel, hIntegral]
  ring

/-- If the birth face has already been passed at the lower endpoint, both
Dickman profiles agree and the continuous-Buchstab integral is zero. -/
theorem roughSaiasStieltjesDickmanProfile_buchstab_inactive
    {x t y z : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hy : 1 < y) (hyz : y ≤ z) (hqy : x / t ≤ y) :
    roughSaiasStieltjesDickmanProfile x y t =
      roughSaiasStieltjesDickmanProfile x z t -
        ∫ s in y..z, roughSaiasContinuousBuchstabProfile x s t := by
  have hz : 1 < z := hy.trans_le hyz
  have hprofiles :
      roughSaiasStieltjesDickmanProfile x y t =
        roughSaiasStieltjesDickmanProfile x z t := by
    by_cases hq1 : x / t < 1
    · have hxt : x < t := (div_lt_one ht).mp hq1
      rw [roughSaiasStieltjesDickmanProfile_eq_zero_of_lt hx hy ht hxt,
        roughSaiasStieltjesDickmanProfile_eq_zero_of_lt hx hz ht hxt]
    · have hq1' : 1 ≤ x / t := le_of_not_gt hq1
      rw [roughSaiasStieltjesDickmanProfile_eq_first_of_one_le_ratio
          hy hq1' hqy,
        roughSaiasStieltjesDickmanProfile_eq_first_of_one_le_ratio
          hz hq1' (hqy.trans hyz)]
  have hIntegral :
      (∫ s in y..z, roughSaiasContinuousBuchstabProfile x s t) = 0 := by
    have hcongr :
        (∫ s in y..z, roughSaiasContinuousBuchstabProfile x s t) =
          ∫ _s in y..z, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with s
      intro hsU
      have hsI : s ∈ Set.Ioc y z := by
        simpa only [Set.uIoc_of_le hyz] using hsU
      have hsone : 1 < s := hy.trans hsI.1
      have hspos : 0 < s := zero_lt_one.trans hsone
      have hqs : x / t < s := hqy.trans_lt hsI.1
      have hxsMul : x < s * t := (div_lt_iff₀ ht).mp hqs
      have hxs : x / s < t := by
        apply (div_lt_iff₀ hspos).2
        simpa only [mul_comm] using hxsMul
      exact roughSaiasContinuousBuchstabProfile_eq_zero_of_lt
        hx hsone ht hxs
    simpa using hcongr
  rw [hprofiles, hIntegral, sub_zero]

/-- Pointwise continuous Buchstab across the birth face.  The integral is
split at `x / t`; its tail is zero and its first piece is the closed-top
identity above. -/
theorem roughSaiasStieltjesDickmanProfile_buchstab_cross_birth
    {x t y z : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hy : 1 < y) (_hyz : y ≤ z)
    (hyq : y < x / t) (hqz : x / t ≤ z)
    (hu6 : Real.log (x / t) / Real.log y ≤ 6) :
    roughSaiasStieltjesDickmanProfile x y t =
      roughSaiasStieltjesDickmanProfile x z t -
        ∫ s in y..z, roughSaiasContinuousBuchstabProfile x s t := by
  have hq1 : 1 < x / t := hy.trans hyq
  have hbirth := roughSaiasStieltjesDickmanProfile_buchstab_birth
    hx ht hy hyq hu6
  have hprefix :=
    intervalIntegrable_roughSaiasContinuousBuchstabProfile_to_birth
      hx ht hy hyq
  have htail :=
    intervalIntegrable_roughSaiasContinuousBuchstabProfile_from_birth
      hx ht hq1 hqz
  have htailZero :=
    roughSaiasContinuousBuchstabProfile_integral_from_birth_eq_zero
      hx ht hq1 hqz
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hprefix htail
  have hIntegral :
      (∫ s in y..z, roughSaiasContinuousBuchstabProfile x s t) =
        ∫ s in y..(x / t),
          roughSaiasContinuousBuchstabProfile x s t := by
    rw [← hsplit, htailZero, add_zero]
  have hprofile :
      roughSaiasStieltjesDickmanProfile x (x / t) t =
        roughSaiasStieltjesDickmanProfile x z t := by
    rw [roughSaiasStieltjesDickmanProfile_eq_first_of_one_le_ratio
          hq1 hq1.le le_rfl,
      roughSaiasStieltjesDickmanProfile_eq_first_of_one_le_ratio
        (hq1.trans_le hqz) hq1.le hqz]
  rw [hprofile, ← hIntegral] at hbirth
  exact hbirth

/-- The pointwise continuous-Buchstab kernel is interval integrable on the
whole base interval.  This is the regularity input needed before lifting the
pointwise identity through the finite signed functional. -/
theorem intervalIntegrable_roughSaiasContinuousBuchstabProfile
    {x t y z : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hy : 1 < y) (hyz : y ≤ z)
    (_hu6 : Real.log (x / t) / Real.log y ≤ 6) :
    IntervalIntegrable (roughSaiasContinuousBuchstabProfile x · t)
      volume y z := by
  by_cases hqy : x / t ≤ y
  · have hzero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ))
        volume y z := continuous_const.intervalIntegrable _ _
    apply hzero.congr
    intro s hsU
    have hsI : s ∈ Set.Ioc y z := by
      simpa only [Set.uIoc_of_le hyz] using hsU
    have hsone : 1 < s := hy.trans hsI.1
    have hspos : 0 < s := zero_lt_one.trans hsone
    have hqs : x / t < s := hqy.trans_lt hsI.1
    have hxsMul : x < s * t := (div_lt_iff₀ ht).mp hqs
    have hxs : x / s < t := by
      apply (div_lt_iff₀ hspos).2
      simpa only [mul_comm] using hxsMul
    exact (roughSaiasContinuousBuchstabProfile_eq_zero_of_lt
      hx hsone ht hxs).symm
  · have hyq : y < x / t := lt_of_not_ge hqy
    by_cases hzq : z < x / t
    · have hqpos : 0 < x / t :=
          (zero_lt_one.trans hy).trans (hyz.trans_lt hzq)
      have hcontWeight : ContinuousOn
          (FriableAsymptotic.dickmanContinuousWeight (x / t))
          (Set.Icc y z) :=
        (FriableAsymptotic.continuousOn_dickmanContinuousWeight
          (x / t)).mono (fun s hs => by
            rw [Set.mem_Ioi]
            exact hy.trans_le hs.1)
      have hcont : ContinuousOn
          (fun s => t *
            FriableAsymptotic.dickmanContinuousWeight (x / t) s)
          (Set.Icc y z) :=
        continuousOn_const.mul hcontWeight
      have hbase := hcont.intervalIntegrable_of_Icc
        (μ := volume) hyz
      apply hbase.congr
      intro s hsU
      have hsI : s ∈ Set.Ioc y z := by
        simpa only [Set.uIoc_of_le hyz] using hsU
      have hsone : 1 < s := hy.trans hsI.1
      have hspos : 0 < s := zero_lt_one.trans hsone
      have hsQ : s < x / t := hsI.2.trans_lt hzq
      have hlogSQ : Real.log s < Real.log (x / t) :=
        Real.strictMonoOn_log hspos hqpos hsQ
      have hactive : 1 ≤ Real.log (x / t) / Real.log s :=
        ((one_lt_div (Real.log_pos hsone)).2 hlogSQ).le
      exact (roughSaiasContinuousBuchstabProfile_eq_mul_dickmanWeight
        hx hsone ht hactive).symm
    · exact
        (intervalIntegrable_roughSaiasContinuousBuchstabProfile_to_birth
          hx ht hy hyq).trans
          (intervalIntegrable_roughSaiasContinuousBuchstabProfile_from_birth
            hx ht (hy.trans hyq) (le_of_not_gt hzq))

/-- Full pointwise continuous Buchstab identity for the supported Dickman
profile.  The face bound is the only finite method-of-steps restriction. -/
theorem roughSaiasStieltjesDickmanProfile_buchstab
    {x t y z : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hy : 1 < y) (hyz : y ≤ z)
    (hu6 : Real.log (x / t) / Real.log y ≤ 6) :
    roughSaiasStieltjesDickmanProfile x y t =
      roughSaiasStieltjesDickmanProfile x z t -
        ∫ s in y..z, roughSaiasContinuousBuchstabProfile x s t := by
  by_cases hqy : x / t ≤ y
  · exact roughSaiasStieltjesDickmanProfile_buchstab_inactive
      hx ht hy hyz hqy
  · have hyq : y < x / t := lt_of_not_ge hqy
    by_cases hzq : z < x / t
    · exact roughSaiasStieltjesDickmanProfile_buchstab_active
        hx ht hy hyz hzq hu6
    · exact roughSaiasStieltjesDickmanProfile_buchstab_cross_birth
        hx ht hy hyz hyq (le_of_not_gt hzq) hu6

end

end Erdos390.WholePaper
