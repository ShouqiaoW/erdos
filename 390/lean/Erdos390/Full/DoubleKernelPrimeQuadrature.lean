import Erdos390.Full.KernelPrimeQuadrature
import Erdos390.Full.PositiveCellTransfer

/-!
# Double-index prime quadrature for the Poisson--Dickman kernel

This module performs the two prime-index quadratures needed in the
positive-cell part of Lemma 8.4.  The constants are chosen once, before the
kernel coordinate, ambient scale, or moving endpoints.  The moving-low-cell
estimates are kept for the next layer; no lower endpoint tending to zero is
hidden in the positive-cell theorem below.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.DoubleKernelPrimeQuadrature

open MeasureTheory
open ArithmeticModel PrimeSums PrimeBandQuadrature
open DickmanBasic ConditionedPoissonLimit
open KernelPrimeQuadrature
open PoissonDickmanKernelBounds
open PositiveCellTransfer

/-- Actual weighted prime-cell operator on the logarithmic coordinate. -/
def primeCellOperator (z : ℝ) (A Y : ℕ) (f : ℝ → ℝ) : ℝ :=
  fullWeightedReciprocalSum f z Y - fullWeightedReciprocalSum f z A

/-- Continuum cell operator with measure `dt/t`. -/
def continuumCellOperator (z : ℝ) (A Y : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∫ t in realLogCoordinate z (A : ℝ)..realLogCoordinate z (Y : ℝ),
    f t / t

/-- Natural primes in `(A,Y]`. -/
def intervalPrimes (A Y : ℕ) : Finset ℕ :=
  primesUpTo Y \ primesUpTo A

lemma mem_intervalPrimes_iff {A Y p : ℕ} :
    p ∈ intervalPrimes A Y ↔ p.Prime ∧ A < p ∧ p ≤ Y := by
  unfold intervalPrimes
  rw [Finset.mem_sdiff]
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨_hpzero, hpY⟩, hpPrime⟩, hpNotA⟩
    refine ⟨hpPrime, ?_, hpY⟩
    by_contra hnot
    exact hpNotA ⟨⟨Nat.zero_le p, Nat.le_of_not_gt hnot⟩, hpPrime⟩
  · rintro ⟨hpPrime, hpA, hpY⟩
    refine ⟨⟨⟨Nat.zero_le p, hpY⟩, hpPrime⟩, ?_⟩
    rintro ⟨⟨_hpzero, hpA'⟩, _hpPrime⟩
    exact (Nat.not_lt_of_ge hpA') hpA

private lemma primesUpTo_mono {A Y : ℕ} (hAY : A ≤ Y) :
    primesUpTo A ⊆ primesUpTo Y := by
  intro p hp
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans hAY⟩, hp.2⟩

lemma primeCellOperator_eq_sum (z : ℝ) {A Y : ℕ} (hAY : A ≤ Y)
    (f : ℝ → ℝ) :
    primeCellOperator z A Y f =
      ∑ p ∈ intervalPrimes A Y,
        f (realLogCoordinate z (p : ℝ)) / (p : ℝ) := by
  have hsub := primesUpTo_mono hAY
  have hsum := Finset.sum_sdiff hsub
    (f := fun p : ℕ => f (realLogCoordinate z (p : ℝ)) / (p : ℝ))
  unfold primeCellOperator fullWeightedReciprocalSum intervalPrimes
  exact ((eq_sub_iff_add_eq).2 hsum).symm

lemma intervalPrime_pos {A Y p : ℕ} (hp : p ∈ intervalPrimes A Y) :
    0 < p := by
  exact (mem_intervalPrimes_iff.mp hp).1.pos

lemma primeCellOperator_sub (z : ℝ) {A Y : ℕ} (hAY : A ≤ Y)
    (f g : ℝ → ℝ) :
    primeCellOperator z A Y (fun t => f t - g t) =
      primeCellOperator z A Y f - primeCellOperator z A Y g := by
  rw [primeCellOperator_eq_sum z hAY,
    primeCellOperator_eq_sum z hAY,
    primeCellOperator_eq_sum z hAY]
  simp_rw [sub_div]
  simp only [Finset.sum_sub_distrib]

/-- A uniform pointwise bound controls the actual prime-cell operator by
the exact harmonic mass of that cell. -/
lemma abs_primeCellOperator_le (z : ℝ) {A Y : ℕ} (hAY : A ≤ Y)
    (f : ℝ → ℝ) {e : ℝ}
    (hbound : ∀ p ∈ intervalPrimes A Y,
      |f (realLogCoordinate z (p : ℝ))| ≤ e) :
    |primeCellOperator z A Y f| ≤
      e * (fullReciprocalSum Y - fullReciprocalSum A) := by
  rw [primeCellOperator_eq_sum z hAY]
  calc
    |∑ p ∈ intervalPrimes A Y,
        f (realLogCoordinate z (p : ℝ)) / (p : ℝ)| ≤
      ∑ p ∈ intervalPrimes A Y,
        |f (realLogCoordinate z (p : ℝ)) / (p : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ intervalPrimes A Y, e / (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpR : (0 : ℝ) < p := by exact_mod_cast intervalPrime_pos hp
      rw [abs_div, abs_of_pos hpR]
      exact div_le_div_of_nonneg_right (hbound p hp) hpR.le
    _ = e * (fullReciprocalSum Y - fullReciprocalSum A) := by
      have hsub := primesUpTo_mono hAY
      have hsum := Finset.sum_sdiff hsub (f := fun p : ℕ => 1 / (p : ℝ))
      have hcell :
          (∑ p ∈ intervalPrimes A Y, 1 / (p : ℝ)) =
            fullReciprocalSum Y - fullReciprocalSum A := by
        unfold intervalPrimes fullReciprocalSum
        exact (eq_sub_iff_add_eq).2 hsum
      calc
        (∑ p ∈ intervalPrimes A Y, e / (p : ℝ)) =
            e * ∑ p ∈ intervalPrimes A Y, 1 / (p : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          ring
        _ = e * (fullReciprocalSum Y - fullReciprocalSum A) := by
          rw [hcell]

/-- Finite prime summation commutes exactly with a parameter integral. -/
lemma primeCellOperator_intervalIntegral
    (z : ℝ) {A Y : ℕ} (hAY : A ≤ Y)
    {a b : ℝ} (g : ℝ → ℝ → ℝ)
    (hint : ∀ p ∈ intervalPrimes A Y,
      IntervalIntegrable (g (realLogCoordinate z (p : ℝ))) volume a b) :
    primeCellOperator z A Y (fun s => ∫ t in a..b, g s t) =
      ∫ t in a..b, primeCellOperator z A Y (fun s => g s t) := by
  rw [primeCellOperator_eq_sum z hAY]
  calc
    (∑ p ∈ intervalPrimes A Y,
        (∫ t in a..b, g (realLogCoordinate z (p : ℝ)) t) / (p : ℝ)) =
      ∑ p ∈ intervalPrimes A Y,
        ∫ t in a..b, g (realLogCoordinate z (p : ℝ)) t / (p : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [intervalIntegral.integral_div]
    _ = ∫ t in a..b,
        ∑ p ∈ intervalPrimes A Y,
          g (realLogCoordinate z (p : ℝ)) t / (p : ℝ) := by
      symm
      apply intervalIntegral.integral_finset_sum
      intro p hp
      exact (hint p hp).div_const (p : ℝ)
    _ = ∫ t in a..b, primeCellOperator z A Y (fun s => g s t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      change (∑ p ∈ intervalPrimes A Y,
        g (realLogCoordinate z (p : ℝ)) t / (p : ℝ)) =
          primeCellOperator z A Y (fun s => g s t)
      rw [primeCellOperator_eq_sum z hAY]

lemma realLogCoordinate_pos_nat {z : ℝ} {X : ℕ}
    (hz : 1 < z) (hX : 2 ≤ X) :
    0 < realLogCoordinate z (X : ℝ) := by
  simpa only [realLogCoordinate, logCoordinate] using
    (logCoordinate_pos (z := z) (X := X) hz hX)

lemma realLogCoordinate_mono_nat {z : ℝ} {A Y : ℕ}
    (hz : 1 < z) (hA : 2 ≤ A) (hAY : A ≤ Y) :
    realLogCoordinate z (A : ℝ) ≤ realLogCoordinate z (Y : ℝ) := by
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hApos : (0 : ℝ) < A := by positivity
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  unfold realLogCoordinate
  exact div_le_div_of_nonneg_right (Real.log_le_log hApos hAYR) hlogz.le

/-- A pointwise bound on a continuum cell gives the exact harmonic-coordinate
length as its operator norm. -/
lemma abs_continuumCellOperator_le
    (z : ℝ) {A Y : ℕ} (hz : 1 < z) (hA : 2 ≤ A) (hAY : A ≤ Y)
    (f : ℝ → ℝ) {e : ℝ}
    (hint : IntervalIntegrable (fun t => f t / t) volume
      (realLogCoordinate z (A : ℝ)) (realLogCoordinate z (Y : ℝ)))
    (hbound : ∀ t ∈ Icc (realLogCoordinate z (A : ℝ))
      (realLogCoordinate z (Y : ℝ)), |f t| ≤ e) :
    |continuumCellOperator z A Y f| ≤
      e * (Real.log (realLogCoordinate z (Y : ℝ)) -
        Real.log (realLogCoordinate z (A : ℝ))) := by
  let a := realLogCoordinate z (A : ℝ)
  let b := realLogCoordinate z (Y : ℝ)
  have ha : 0 < a := realLogCoordinate_pos_nat hz hA
  have hb : 0 < b := realLogCoordinate_pos_nat hz (hA.trans hAY)
  have hab : a ≤ b := realLogCoordinate_mono_nat hz hA hAY
  have hmajorInt : IntervalIntegrable (fun t : ℝ => e / t) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    exact continuousAt_const.div continuousAt_id
      (ne_of_gt (ha.trans_le ht.1)) |>.continuousWithinAt
  unfold continuumCellOperator
  change |∫ t in a..b, f t / t| ≤
    e * (Real.log b - Real.log a)
  calc
    |∫ t in a..b, f t / t| ≤ ∫ t in a..b, |f t / t| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, e / t := by
      exact intervalIntegral.integral_mono_on hab hint.abs hmajorInt
        (fun t ht => by
          have htpos : 0 < t := ha.trans_le ht.1
          rw [abs_div, abs_of_pos htpos]
          exact div_le_div_of_nonneg_right (hbound t ht) htpos.le)
    _ = e * (Real.log b - Real.log a) := by
      have heq : (fun t : ℝ => e / t) = fun t => e * (1 / t) := by
        funext t
        ring
      rw [heq, intervalIntegral.integral_const_mul,
        integral_one_div_of_pos ha hb, Real.log_div hb.ne' ha.ne']

/-- Exact actual double-prime kernel cell. -/
def doublePrimeKernelCell (z : ℝ) (A₁ Y₁ A₂ Y₂ : ℕ) : ℝ :=
  primeCellOperator z A₁ Y₁ (fun s =>
    primeCellOperator z A₂ Y₂ (covarianceKernel s))

/-- The iterated continuum kernel cell, written in the order convenient for
the second prime quadrature. -/
def doubleContinuumKernelCell (z : ℝ) (A₁ Y₁ A₂ Y₂ : ℕ) : ℝ :=
  continuumCellOperator z A₂ Y₂ (fun t =>
    continuumCellOperator z A₁ Y₁ (covarianceKernel t))

/-- The outer prime-cell operator commutes with the inner continuum kernel
integral.  Kernel symmetry puts the surviving prime sum in the orientation
required by the one-index theorem. -/
lemma primeCellOperator_continuumKernel_commute
    {z : ℝ} (hz : 1 < z)
    {A₁ Y₁ A₂ Y₂ : ℕ}
    (hA₁Y₁ : A₁ ≤ Y₁)
    (hA₂ : 2 ≤ A₂) (hA₂Y₂ : A₂ ≤ Y₂) :
    primeCellOperator z A₁ Y₁ (fun s =>
        continuumCellOperator z A₂ Y₂ (covarianceKernel s)) =
      continuumCellOperator z A₂ Y₂ (fun t =>
        primeCellOperator z A₁ Y₁ (covarianceKernel t)) := by
  let a := realLogCoordinate z (A₂ : ℝ)
  let b := realLogCoordinate z (Y₂ : ℝ)
  have ha : 0 < a := realLogCoordinate_pos_nat hz hA₂
  have hab : a ≤ b := realLogCoordinate_mono_nat hz hA₂ hA₂Y₂
  have hcommute := primeCellOperator_intervalIntegral z hA₁Y₁
    (a := a) (b := b) (fun s t => covarianceKernel s t / t)
    (fun p hp => by
      apply ContinuousOn.intervalIntegrable_of_Icc hab
      intro t ht
      exact (continuous_covarianceKernel_left
        (realLogCoordinate z (p : ℝ))).continuousAt.div continuousAt_id
          (ne_of_gt (ha.trans_le ht.1)) |>.continuousWithinAt)
  unfold continuumCellOperator
  change primeCellOperator z A₁ Y₁
      (fun s => ∫ t in a..b, covarianceKernel s t / t) =
    ∫ t in a..b, primeCellOperator z A₁ Y₁ (covarianceKernel t) / t
  rw [hcommute]
  apply intervalIntegral.integral_congr
  intro t ht
  change primeCellOperator z A₁ Y₁ (fun s => covarianceKernel s t / t) =
    primeCellOperator z A₁ Y₁ (covarianceKernel t) / t
  rw [primeCellOperator_eq_sum z hA₁Y₁,
    primeCellOperator_eq_sum z hA₁Y₁]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  rw [covarianceKernel_comm]
  ring

lemma coordinateCell_mem_unit {z : ℝ} (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y) (hYz : (Y : ℝ) ≤ z)
    {t : ℝ}
    (ht : t ∈ Icc (realLogCoordinate z (A : ℝ))
      (realLogCoordinate z (Y : ℝ))) :
    t ∈ Icc (0 : ℝ) 1 := by
  have hlow := realLogCoordinate_mem_unit hz
    (show (1 : ℝ) ≤ (A : ℝ) by exact_mod_cast (show 1 ≤ A by omega))
    ((show (A : ℝ) ≤ (Y : ℝ) by exact_mod_cast hAY).trans hYz)
  have hupp := realLogCoordinate_mem_unit hz
    (show (1 : ℝ) ≤ (Y : ℝ) by exact_mod_cast (show 1 ≤ Y by omega)) hYz
  exact ⟨hlow.1.trans ht.1, ht.2.trans hupp.2⟩

/-- Regularized continuum kernel cell, using the removable quotient at the
low endpoint. -/
def regularizedContinuumKernelCell (z : ℝ) (A Y : ℕ) (s : ℝ) : ℝ :=
  ∫ t in realLogCoordinate z (A : ℝ)..realLogCoordinate z (Y : ℝ),
    covarianceKernelQuotient s t

lemma continuumCellOperator_kernel_eq_regularized
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y) (hYz : (Y : ℝ) ≤ z) :
    continuumCellOperator z A Y (covarianceKernel s) =
      regularizedContinuumKernelCell z A Y s := by
  unfold continuumCellOperator regularizedContinuumKernelCell
  apply intervalIntegral.integral_congr
  intro t ht
  have htIcc : t ∈ Icc (realLogCoordinate z (A : ℝ))
      (realLogCoordinate z (Y : ℝ)) := by
    simpa [uIcc_of_le (realLogCoordinate_mono_nat hz hA hAY)] using ht
  have htUnit := coordinateCell_mem_unit hz hA hAY hYz htIcc
  have htpos : 0 < t :=
    (realLogCoordinate_pos_nat hz hA).trans_le htIcc.1
  have hmul := mul_covarianceKernelQuotient_eq_kernel hs htUnit
  field_simp [ne_of_gt htpos]
  linarith

lemma continuous_regularizedContinuumKernelCell
    (z : ℝ) (A Y : ℕ) :
    Continuous (regularizedContinuumKernelCell z A Y) := by
  unfold regularizedContinuumKernelCell
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (a₀ := realLogCoordinate z (A : ℝ))
    (b₀ := realLogCoordinate z (Y : ℝ))
  exact continuous_uncurry_covarianceKernelQuotient

lemma continuous_primeCellKernel
    (z : ℝ) {A Y : ℕ} (hAY : A ≤ Y) :
    Continuous (fun s => primeCellOperator z A Y (covarianceKernel s)) := by
  rw [show (fun s => primeCellOperator z A Y (covarianceKernel s)) =
      fun s => ∑ p ∈ intervalPrimes A Y,
        covarianceKernel s (realLogCoordinate z (p : ℝ)) / (p : ℝ) by
    funext s
    rw [primeCellOperator_eq_sum z hAY]]
  apply continuous_finset_sum _
  intro p hp
  exact (continuous_covarianceKernel.comp
    (continuous_id.prodMk continuous_const)).div_const (p : ℝ)

lemma intervalIntegrable_div_of_continuous
    {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    IntervalIntegrable (fun t => f t / t) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro t ht
  exact hf.continuousAt.div continuousAt_id
    (ne_of_gt (ha.trans_le ht.1)) |>.continuousWithinAt

lemma continuumCellOperator_sub
    (z : ℝ) (A Y : ℕ) (f g : ℝ → ℝ)
    (hf : IntervalIntegrable (fun t => f t / t) volume
      (realLogCoordinate z (A : ℝ)) (realLogCoordinate z (Y : ℝ)))
    (hg : IntervalIntegrable (fun t => g t / t) volume
      (realLogCoordinate z (A : ℝ)) (realLogCoordinate z (Y : ℝ))) :
    continuumCellOperator z A Y (fun t => f t - g t) =
      continuumCellOperator z A Y f - continuumCellOperator z A Y g := by
  unfold continuumCellOperator
  simp_rw [sub_div]
  exact intervalIntegral.integral_sub hf hg

/-- Deterministic two-index transfer.  One-index error `e₂` is averaged
over the actual first prime cell, while `e₁` is averaged over the exact
continuum harmonic length of the second cell. -/
theorem doubleKernelCell_error_le_of_oneIndex
    {z : ℝ} (hz : 1 < z)
    {A₁ Y₁ A₂ Y₂ : ℕ}
    (hA₁ : 2 ≤ A₁) (hA₁Y₁ : A₁ ≤ Y₁) (hY₁z : (Y₁ : ℝ) ≤ z)
    (hA₂ : 2 ≤ A₂) (hA₂Y₂ : A₂ ≤ Y₂) (hY₂z : (Y₂ : ℝ) ≤ z)
    {e₁ e₂ : ℝ}
    (hquad₁ : ∀ t ∈ Icc (0 : ℝ) 1,
      |primeCellOperator z A₁ Y₁ (covarianceKernel t) -
        continuumCellOperator z A₁ Y₁ (covarianceKernel t)| ≤ e₁)
    (hquad₂ : ∀ s ∈ Icc (0 : ℝ) 1,
      |primeCellOperator z A₂ Y₂ (covarianceKernel s) -
        continuumCellOperator z A₂ Y₂ (covarianceKernel s)| ≤ e₂) :
    |doublePrimeKernelCell z A₁ Y₁ A₂ Y₂ -
        doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂| ≤
      e₂ * (fullReciprocalSum Y₁ - fullReciprocalSum A₁) +
        e₁ * (Real.log (realLogCoordinate z (Y₂ : ℝ)) -
          Real.log (realLogCoordinate z (A₂ : ℝ))) := by
  let P₁ : (ℝ → ℝ) → ℝ := primeCellOperator z A₁ Y₁
  let C₁ : (ℝ → ℝ) → ℝ := continuumCellOperator z A₁ Y₁
  let P₂ : (ℝ → ℝ) → ℝ := primeCellOperator z A₂ Y₂
  let C₂ : (ℝ → ℝ) → ℝ := continuumCellOperator z A₂ Y₂
  let mixed : ℝ := P₁ (fun s => C₂ (covarianceKernel s))
  have hfirst :
      |doublePrimeKernelCell z A₁ Y₁ A₂ Y₂ - mixed| ≤
        e₂ * (fullReciprocalSum Y₁ - fullReciprocalSum A₁) := by
    have heq :
        doublePrimeKernelCell z A₁ Y₁ A₂ Y₂ - mixed =
          P₁ (fun s => P₂ (covarianceKernel s) - C₂ (covarianceKernel s)) := by
      dsimp only [doublePrimeKernelCell, mixed, P₁, P₂, C₂]
      rw [primeCellOperator_sub z hA₁Y₁]
    rw [heq]
    apply abs_primeCellOperator_le z hA₁Y₁
    intro p hp
    have hpData := mem_intervalPrimes_iff.mp hp
    have hpUnit : realLogCoordinate z (p : ℝ) ∈ Icc (0 : ℝ) 1 := by
      apply realLogCoordinate_mem_unit hz
      · exact_mod_cast (show 1 ≤ p by omega)
      · exact (show (p : ℝ) ≤ (Y₁ : ℝ) by exact_mod_cast hpData.2.2).trans hY₁z
    exact hquad₂ _ hpUnit
  have hmixed : mixed = C₂ (fun t => P₁ (covarianceKernel t)) := by
    dsimp only [mixed, P₁, C₂]
    exact primeCellOperator_continuumKernel_commute hz hA₁Y₁
      hA₂ hA₂Y₂
  let R₁ : ℝ → ℝ := regularizedContinuumKernelCell z A₁ Y₁
  have hC₁eq : C₂ (fun t => C₁ (covarianceKernel t)) = C₂ R₁ := by
    unfold C₂ continuumCellOperator
    apply intervalIntegral.integral_congr
    intro t ht
    have htCell : t ∈ Icc (realLogCoordinate z (A₂ : ℝ))
        (realLogCoordinate z (Y₂ : ℝ)) := by
      simpa [uIcc_of_le (realLogCoordinate_mono_nat hz hA₂ hA₂Y₂)] using ht
    have htUnit := coordinateCell_mem_unit hz hA₂ hA₂Y₂ hY₂z htCell
    change C₁ (covarianceKernel t) / t = R₁ t / t
    congr 1
    dsimp only [C₁, R₁]
    exact continuumCellOperator_kernel_eq_regularized htUnit hz
      hA₁ hA₁Y₁ hY₁z
  have ha₂ : 0 < realLogCoordinate z (A₂ : ℝ) :=
    realLogCoordinate_pos_nat hz hA₂
  have hab₂ : realLogCoordinate z (A₂ : ℝ) ≤
      realLogCoordinate z (Y₂ : ℝ) :=
    realLogCoordinate_mono_nat hz hA₂ hA₂Y₂
  have hPint : IntervalIntegrable
      (fun t => P₁ (covarianceKernel t) / t) volume
      (realLogCoordinate z (A₂ : ℝ)) (realLogCoordinate z (Y₂ : ℝ)) := by
    apply intervalIntegrable_div_of_continuous
      (continuous_primeCellKernel z hA₁Y₁) ha₂ hab₂
  have hRint : IntervalIntegrable (fun t => R₁ t / t) volume
      (realLogCoordinate z (A₂ : ℝ)) (realLogCoordinate z (Y₂ : ℝ)) := by
    apply intervalIntegrable_div_of_continuous
      (continuous_regularizedContinuumKernelCell z A₁ Y₁) ha₂ hab₂
  have hsecond :
      |mixed - doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂| ≤
        e₁ * (Real.log (realLogCoordinate z (Y₂ : ℝ)) -
          Real.log (realLogCoordinate z (A₂ : ℝ))) := by
    have heq : mixed - doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂ =
        C₂ (fun t => P₁ (covarianceKernel t) - R₁ t) := by
      rw [hmixed]
      dsimp only [doubleContinuumKernelCell]
      change C₂ (fun t => P₁ (covarianceKernel t)) -
          C₂ (fun t => C₁ (covarianceKernel t)) = _
      rw [hC₁eq]
      symm
      exact continuumCellOperator_sub z A₂ Y₂ _ _ hPint hRint
    rw [heq]
    apply abs_continuumCellOperator_le z hz hA₂ hA₂Y₂
      (fun t => P₁ (covarianceKernel t) - R₁ t)
    · apply (hPint.sub hRint).congr
      intro t ht
      ring
    · intro t ht
      have htUnit := coordinateCell_mem_unit hz hA₂ hA₂Y₂ hY₂z ht
      have hreg : R₁ t = C₁ (covarianceKernel t) := by
        dsimp only [R₁, C₁]
        exact (continuumCellOperator_kernel_eq_regularized htUnit hz
          hA₁ hA₁Y₁ hY₁z).symm
      rw [hreg]
      exact hquad₁ t htUnit
  calc
    |doublePrimeKernelCell z A₁ Y₁ A₂ Y₂ -
        doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂| ≤
      |doublePrimeKernelCell z A₁ Y₁ A₂ Y₂ - mixed| +
        |mixed - doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂| := by
      have hsplit :
          doublePrimeKernelCell z A₁ Y₁ A₂ Y₂ -
              doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂ =
            (doublePrimeKernelCell z A₁ Y₁ A₂ Y₂ - mixed) +
              (mixed - doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂) := by ring
      rw [hsplit]
      exact abs_add_le _ _
    _ ≤ e₂ * (fullReciprocalSum Y₁ - fullReciprocalSum A₁) +
        e₁ * (Real.log (realLogCoordinate z (Y₂ : ℝ)) -
          Real.log (realLogCoordinate z (A₂ : ℝ))) :=
      add_le_add hfirst hsecond

/-- Unconditional two-index positive-cell quadrature.  The PNT constant and
threshold are selected before the ambient scale and both moving cells.  The
two terms display the input and output quadrature losses separately. -/
theorem exists_uniform_doubleKernelCell_error_bound :
    ∃ D : ℝ, 0 < D ∧ ∃ X₀ : ℕ,
      ∀ z : ℝ, 1 < z →
      ∀ A₁ Y₁ A₂ Y₂ : ℕ,
        X₀ ≤ A₁ → A₁ ≤ Y₁ → (Y₁ : ℝ) ≤ z →
        X₀ ≤ A₂ → A₂ ≤ Y₂ → (Y₂ : ℝ) ≤ z →
        |doublePrimeKernelCell z A₁ Y₁ A₂ Y₂ -
            doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂| ≤
          (D / Real.log (A₂ : ℝ) ^ 3) *
              (fullReciprocalSum Y₁ - fullReciprocalSum A₁) +
            (D / Real.log (A₁ : ℝ) ^ 3) *
              (Real.log (realLogCoordinate z (Y₂ : ℝ)) -
                Real.log (realLogCoordinate z (A₂ : ℝ))) := by
  obtain ⟨D, hD, X₀, hquad⟩ :=
    exists_uniform_kernel_primeCell_error_bound
  refine ⟨D, hD, max X₀ 2, ?_⟩
  intro z hz A₁ Y₁ A₂ Y₂ hA₁ hA₁Y₁ hY₁z
    hA₂ hA₂Y₂ hY₂z
  have hA₁base : X₀ ≤ A₁ := (le_max_left X₀ 2).trans hA₁
  have hA₂base : X₀ ≤ A₂ := (le_max_left X₀ 2).trans hA₂
  have hA₁two : 2 ≤ A₁ := (le_max_right X₀ 2).trans hA₁
  have hA₂two : 2 ≤ A₂ := (le_max_right X₀ 2).trans hA₂
  apply doubleKernelCell_error_le_of_oneIndex hz
    hA₁two hA₁Y₁ hY₁z hA₂two hA₂Y₂ hY₂z
  · intro t ht
    change |fullWeightedReciprocalSum (covarianceKernel t) z Y₁ -
        fullWeightedReciprocalSum (covarianceKernel t) z A₁ -
        (∫ u in realLogCoordinate z (A₁ : ℝ)..
          realLogCoordinate z (Y₁ : ℝ), covarianceKernel t u / u)| ≤
      D / Real.log (A₁ : ℝ) ^ 3
    exact hquad t ht z hz A₁ Y₁ hA₁base hA₁Y₁ hY₁z
  · intro s hs
    change |fullWeightedReciprocalSum (covarianceKernel s) z Y₂ -
        fullWeightedReciprocalSum (covarianceKernel s) z A₂ -
        (∫ u in realLogCoordinate z (A₂ : ℝ)..
          realLogCoordinate z (Y₂ : ℝ), covarianceKernel s u / u)| ≤
      D / Real.log (A₂ : ℝ) ^ 3
    exact hquad s hs z hz A₂ Y₂ hA₂base hA₂Y₂ hY₂z

/-! ## Moving-low input cell -/

lemma intervalLogReciprocalSum_eq_sub {A Y : ℕ} (hAY : A ≤ Y) :
    (∑ p ∈ intervalPrimes A Y, Real.log (p : ℝ) / (p : ℝ)) =
      fullLogReciprocalSum Y - fullLogReciprocalSum A := by
  have hsub := primesUpTo_mono hAY
  have hsum := Finset.sum_sdiff hsub
    (f := fun p : ℕ => Real.log (p : ℝ) / (p : ℝ))
  unfold intervalPrimes fullLogReciprocalSum
  exact (eq_sub_iff_add_eq).2 hsum

/-- Product vanishing of the kernel controls the part of a low prime cell
below an arbitrary split point by its first logarithmic moment. -/
lemma abs_primeCellKernel_le_logMoment
    {C s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {A S : ℕ} (hA : 2 ≤ A) (hAS : A ≤ S) (hSz : (S : ℝ) ≤ z)
    (hK : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel u t| ≤ C * t) :
    |primeCellOperator z A S (covarianceKernel s)| ≤
      (C / Real.log z) *
        (fullLogReciprocalSum S - fullLogReciprocalSum A) := by
  have hlogz : 0 < Real.log z := Real.log_pos hz
  rw [primeCellOperator_eq_sum z hAS]
  calc
    |∑ p ∈ intervalPrimes A S,
        covarianceKernel s (realLogCoordinate z (p : ℝ)) / (p : ℝ)| ≤
      ∑ p ∈ intervalPrimes A S,
        |covarianceKernel s (realLogCoordinate z (p : ℝ)) / (p : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ intervalPrimes A S,
        (C / Real.log z) * (Real.log (p : ℝ) / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpData := mem_intervalPrimes_iff.mp hp
      have hpR : (0 : ℝ) < p := by exact_mod_cast hpData.1.pos
      have hpUnit : realLogCoordinate z (p : ℝ) ∈ Icc (0 : ℝ) 1 := by
        apply realLogCoordinate_mem_unit hz
        · exact_mod_cast (show 1 ≤ p by omega)
        · exact (show (p : ℝ) ≤ (S : ℝ) by exact_mod_cast hpData.2.2).trans hSz
      rw [abs_div, abs_of_pos hpR]
      calc
        |covarianceKernel s (realLogCoordinate z (p : ℝ))| / (p : ℝ) ≤
            (C * realLogCoordinate z (p : ℝ)) / (p : ℝ) :=
          div_le_div_of_nonneg_right (hK s hs _ hpUnit) hpR.le
        _ = (C / Real.log z) * (Real.log (p : ℝ) / (p : ℝ)) := by
          unfold realLogCoordinate
          field_simp [ne_of_gt hlogz, ne_of_gt hpR]
    _ = (C / Real.log z) *
        (fullLogReciprocalSum S - fullLogReciprocalSum A) := by
      calc
        (∑ p ∈ intervalPrimes A S,
            (C / Real.log z) * (Real.log (p : ℝ) / (p : ℝ))) =
          (C / Real.log z) *
            ∑ p ∈ intervalPrimes A S,
              Real.log (p : ℝ) / (p : ℝ) := by
            rw [Finset.mul_sum]
        _ = _ := by rw [intervalLogReciprocalSum_eq_sub hAS]

/-- The corresponding continuum piece is bounded by its ordinary coordinate
length, uniformly in the first kernel coordinate. -/
lemma abs_continuumCellKernel_le_coordinateLength
    {C s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {A S : ℕ} (hA : 2 ≤ A) (hAS : A ≤ S) (hSz : (S : ℝ) ≤ z)
    (hK : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel u t| ≤ C * t) :
    |continuumCellOperator z A S (covarianceKernel s)| ≤
      C * (realLogCoordinate z (S : ℝ) - realLogCoordinate z (A : ℝ)) := by
  let a := realLogCoordinate z (A : ℝ)
  let b := realLogCoordinate z (S : ℝ)
  have ha : 0 < a := realLogCoordinate_pos_nat hz hA
  have hab : a ≤ b := realLogCoordinate_mono_nat hz hA hAS
  unfold continuumCellOperator
  change |∫ t in a..b, covarianceKernel s t / t| ≤ C * (b - a)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := C)
    (f := fun t : ℝ => covarianceKernel s t / t) (fun t ht => by
      have htIcc : t ∈ Icc a b := by
        have ht' : t ∈ uIcc a b := uIoc_subset_uIcc ht
        simpa only [uIcc_of_le hab] using ht'
      have htUnit : t ∈ Icc (0 : ℝ) 1 := by
        exact coordinateCell_mem_unit hz hA hAS hSz htIcc
      have htpos : 0 < t := ha.trans_le htIcc.1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos htpos]
      have hk := hK s hs t htUnit
      exact (div_le_iff₀ htpos).2 (by
        calc
          |covarianceKernel s t| ≤ C * t := hk
          _ = C * t := rfl))
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hnorm
  exact hnorm

lemma primeCellOperator_add_adjacent
    (z : ℝ) {A S Y : ℕ} (f : ℝ → ℝ) :
    primeCellOperator z A Y f =
      primeCellOperator z A S f + primeCellOperator z S Y f := by
  unfold primeCellOperator
  ring

lemma continuumCellOperator_add_adjacent
    (z : ℝ) {A S Y : ℕ} (f : ℝ → ℝ)
    (hleft : IntervalIntegrable (fun t => f t / t) volume
      (realLogCoordinate z (A : ℝ)) (realLogCoordinate z (S : ℝ)))
    (hright : IntervalIntegrable (fun t => f t / t) volume
      (realLogCoordinate z (S : ℝ)) (realLogCoordinate z (Y : ℝ))) :
    continuumCellOperator z A Y f =
      continuumCellOperator z A S f + continuumCellOperator z S Y f := by
  unfold continuumCellOperator
  exact (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm

/-- Explicit moving-low split estimate.  The low piece uses only kernel
product vanishing; PNT quadrature is invoked only above the freely chosen
split `S`. -/
theorem movingLow_kernelCell_error_le_of_tail
    {C e s z : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {A S Y : ℕ} (hA : 2 ≤ A) (hAS : A ≤ S) (hSY : S ≤ Y)
    (hYz : (Y : ℝ) ≤ z)
    (hK : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel u t| ≤ C * t)
    (htail : |primeCellOperator z S Y (covarianceKernel s) -
      continuumCellOperator z S Y (covarianceKernel s)| ≤ e) :
    |primeCellOperator z A Y (covarianceKernel s) -
        continuumCellOperator z A Y (covarianceKernel s)| ≤
      (C / Real.log z) *
          (fullLogReciprocalSum S - fullLogReciprocalSum A) +
        C * (realLogCoordinate z (S : ℝ) -
          realLogCoordinate z (A : ℝ)) + e := by
  have hSz : (S : ℝ) ≤ z :=
    (show (S : ℝ) ≤ (Y : ℝ) by exact_mod_cast hSY).trans hYz
  have hleftInt : IntervalIntegrable (fun t => covarianceKernel s t / t) volume
      (realLogCoordinate z (A : ℝ)) (realLogCoordinate z (S : ℝ)) := by
    exact intervalIntegrable_div_of_continuous
      (continuous_covarianceKernel_left s)
      (realLogCoordinate_pos_nat hz hA)
      (realLogCoordinate_mono_nat hz hA hAS)
  have hrightInt : IntervalIntegrable (fun t => covarianceKernel s t / t) volume
      (realLogCoordinate z (S : ℝ)) (realLogCoordinate z (Y : ℝ)) := by
    exact intervalIntegrable_div_of_continuous
      (continuous_covarianceKernel_left s)
      (realLogCoordinate_pos_nat hz (hA.trans hAS))
      (realLogCoordinate_mono_nat hz (hA.trans hAS) hSY)
  rw [primeCellOperator_add_adjacent z (covarianceKernel s),
    continuumCellOperator_add_adjacent z (covarianceKernel s) hleftInt hrightInt]
  have hlowPrime := abs_primeCellKernel_le_logMoment hs hz hA hAS hSz hK
  have hlowCont := abs_continuumCellKernel_le_coordinateLength
    hs hz hA hAS hSz hK
  calc
    |(primeCellOperator z A S (covarianceKernel s) +
          primeCellOperator z S Y (covarianceKernel s)) -
        (continuumCellOperator z A S (covarianceKernel s) +
          continuumCellOperator z S Y (covarianceKernel s))| ≤
      |primeCellOperator z A S (covarianceKernel s)| +
        |continuumCellOperator z A S (covarianceKernel s)| +
        |primeCellOperator z S Y (covarianceKernel s) -
          continuumCellOperator z S Y (covarianceKernel s)| := by
      have hsplit :
          (primeCellOperator z A S (covarianceKernel s) +
              primeCellOperator z S Y (covarianceKernel s)) -
            (continuumCellOperator z A S (covarianceKernel s) +
              continuumCellOperator z S Y (covarianceKernel s)) =
          primeCellOperator z A S (covarianceKernel s) +
            (-continuumCellOperator z A S (covarianceKernel s)) +
            (primeCellOperator z S Y (covarianceKernel s) -
              continuumCellOperator z S Y (covarianceKernel s)) := by ring
      rw [hsplit]
      calc
        |primeCellOperator z A S (covarianceKernel s) +
            (-continuumCellOperator z A S (covarianceKernel s)) +
            (primeCellOperator z S Y (covarianceKernel s) -
              continuumCellOperator z S Y (covarianceKernel s))| ≤
          |primeCellOperator z A S (covarianceKernel s) +
            (-continuumCellOperator z A S (covarianceKernel s))| +
            |primeCellOperator z S Y (covarianceKernel s) -
              continuumCellOperator z S Y (covarianceKernel s)| := abs_add_le _ _
        _ ≤ |primeCellOperator z A S (covarianceKernel s)| +
            |continuumCellOperator z A S (covarianceKernel s)| +
            |primeCellOperator z S Y (covarianceKernel s) -
              continuumCellOperator z S Y (covarianceKernel s)| := by
          have hpc := abs_add_le (primeCellOperator z A S (covarianceKernel s))
            (-continuumCellOperator z A S (covarianceKernel s))
          rw [abs_neg] at hpc
          linarith
    _ ≤ (C / Real.log z) *
          (fullLogReciprocalSum S - fullLogReciprocalSum A) +
        C * (realLogCoordinate z (S : ℝ) -
          realLogCoordinate z (A : ℝ)) + e := by linarith

/-- Unconditional moving-low input quadrature with an explicit split.  The
lower cutoff `A` is not required to exceed the PNT threshold; only the tail
split `S` is.  This is the quantifier order used when `A=W` is fixed first,
then `S` is placed at a small positive logarithmic coordinate. -/
theorem exists_uniform_movingLow_kernelCell_split_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ D : ℝ, 0 < D ∧ ∃ X₀ : ℕ,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, 1 < z →
      ∀ A S Y : ℕ,
        2 ≤ A → A ≤ S → X₀ ≤ S → S ≤ Y → (Y : ℝ) ≤ z →
        |primeCellOperator z A Y (covarianceKernel s) -
            continuumCellOperator z A Y (covarianceKernel s)| ≤
          (C / Real.log z) *
              (fullLogReciprocalSum S - fullLogReciprocalSum A) +
            C * (realLogCoordinate z (S : ℝ) -
              realLogCoordinate z (A : ℝ)) +
            D / Real.log (S : ℝ) ^ 3 := by
  obtain ⟨C, hC, hK⟩ := exists_covarianceKernel_abs_le_second
  obtain ⟨D, hD, X₀, hquad⟩ :=
    exists_uniform_kernel_primeCell_error_bound
  refine ⟨C, hC, D, hD, X₀, ?_⟩
  intro s hs z hz A S Y hA hAS hX₀S hSY hYz
  apply movingLow_kernelCell_error_le_of_tail hs hz hA hAS hSY hYz hK
  change |fullWeightedReciprocalSum (covarianceKernel s) z Y -
      fullWeightedReciprocalSum (covarianceKernel s) z S -
      (∫ t in realLogCoordinate z (S : ℝ)..
        realLogCoordinate z (Y : ℝ), covarianceKernel s t / t)| ≤
    D / Real.log (S : ℝ) ^ 3
  exact hquad s hs z hz S Y hX₀S hSY hYz

/-- Product-kernel version of the continuum cell estimate, retaining the
first coordinate. -/
lemma abs_continuumCellKernel_le_productLength
    {C s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y) (hYz : (Y : ℝ) ≤ z)
    (hK : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel u t| ≤ C * u * t) :
    |continuumCellOperator z A Y (covarianceKernel s)| ≤
      (C * s) *
        (realLogCoordinate z (Y : ℝ) - realLogCoordinate z (A : ℝ)) := by
  let a := realLogCoordinate z (A : ℝ)
  let b := realLogCoordinate z (Y : ℝ)
  have ha : 0 < a := realLogCoordinate_pos_nat hz hA
  have hab : a ≤ b := realLogCoordinate_mono_nat hz hA hAY
  unfold continuumCellOperator
  change |∫ t in a..b, covarianceKernel s t / t| ≤ (C * s) * (b - a)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := C * s)
    (f := fun t : ℝ => covarianceKernel s t / t) (fun t ht => by
      have ht' : t ∈ uIcc a b := uIoc_subset_uIcc ht
      have htIcc : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht'
      have htUnit := coordinateCell_mem_unit hz hA hAY hYz htIcc
      have htpos : 0 < t := ha.trans_le htIcc.1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos htpos]
      exact (div_le_iff₀ htpos).2 (hK s hs t htUnit))
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hnorm
  exact hnorm

/-- The iterated continuum kernel numerator is bounded by the product of
the two ordinary logarithmic-coordinate lengths. -/
lemma abs_doubleContinuumKernelCell_le_productLengths
    {C z : ℝ} (hz : 1 < z)
    {A₁ Y₁ A₂ Y₂ : ℕ}
    (hA₁ : 2 ≤ A₁) (hA₁Y₁ : A₁ ≤ Y₁) (hY₁z : (Y₁ : ℝ) ≤ z)
    (hA₂ : 2 ≤ A₂) (hA₂Y₂ : A₂ ≤ Y₂) (hY₂z : (Y₂ : ℝ) ≤ z)
    (hK : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel u t| ≤ C * u * t) :
    |doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂| ≤
      C * (realLogCoordinate z (Y₁ : ℝ) -
          realLogCoordinate z (A₁ : ℝ)) *
        (realLogCoordinate z (Y₂ : ℝ) -
          realLogCoordinate z (A₂ : ℝ)) := by
  let a₂ := realLogCoordinate z (A₂ : ℝ)
  let b₂ := realLogCoordinate z (Y₂ : ℝ)
  let ell₁ := realLogCoordinate z (Y₁ : ℝ) -
    realLogCoordinate z (A₁ : ℝ)
  have ha₂ : 0 < a₂ := realLogCoordinate_pos_nat hz hA₂
  have hab₂ : a₂ ≤ b₂ := realLogCoordinate_mono_nat hz hA₂ hA₂Y₂
  unfold doubleContinuumKernelCell continuumCellOperator
  change |∫ t in a₂..b₂,
      continuumCellOperator z A₁ Y₁ (covarianceKernel t) / t| ≤
    C * ell₁ * (b₂ - a₂)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a₂) (b := b₂) (C := C * ell₁)
    (f := fun t : ℝ =>
      continuumCellOperator z A₁ Y₁ (covarianceKernel t) / t)
    (fun t ht => by
      have ht' : t ∈ uIcc a₂ b₂ := uIoc_subset_uIcc ht
      have htIcc : t ∈ Icc a₂ b₂ := by
        simpa only [uIcc_of_le hab₂] using ht'
      have htUnit := coordinateCell_mem_unit hz hA₂ hA₂Y₂ hY₂z htIcc
      have htpos : 0 < t := ha₂.trans_le htIcc.1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos htpos]
      have hinner := abs_continuumCellKernel_le_productLength
        htUnit hz hA₁ hA₁Y₁ hY₁z hK
      exact (div_le_iff₀ htpos).2 (by
        calc
          |continuumCellOperator z A₁ Y₁ (covarianceKernel t)| ≤
              (C * t) * ell₁ := hinner
          _ = (C * ell₁) * t := by ring))
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab₂)] at hnorm
  simpa [ell₁] using hnorm

/-- Exact arithmetic harmonic mass of a prime cell. -/
def actualCellMass (A Y : ℕ) : ℝ :=
  fullReciprocalSum Y - fullReciprocalSum A

/-- Exact continuum harmonic mass of the corresponding logarithmic cell. -/
def continuumCellMass (z : ℝ) (A Y : ℕ) : ℝ :=
  Real.log (realLogCoordinate z (Y : ℝ)) -
    Real.log (realLogCoordinate z (A : ℝ))

/-- Actual output-row normalization of a double kernel cell. -/
def normalizedDoublePrimeKernelCell
    (z : ℝ) (A₁ Y₁ A₂ Y₂ : ℕ) : ℝ :=
  doublePrimeKernelCell z A₁ Y₁ A₂ Y₂ / actualCellMass A₁ Y₁

/-- Continuum output-row normalization of the same cell. -/
def normalizedDoubleContinuumKernelCell
    (z : ℝ) (A₁ Y₁ A₂ Y₂ : ℕ) : ℝ :=
  doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂ /
    continuumCellMass z A₁ Y₁

/-- Exact relative output transfer.  This is the normalization mechanism
which absorbs a bounded fixed-cutoff error on the moving low output row. -/
theorem normalizedDoubleKernelCell_error_le
    {z : ℝ} {A₁ Y₁ A₂ Y₂ : ℕ} {eNumerator eMass : ℝ}
    (hActualMass : 0 < actualCellMass A₁ Y₁)
    (hContinuumMass : continuumCellMass z A₁ Y₁ ≠ 0)
    (hNumerator :
      |doublePrimeKernelCell z A₁ Y₁ A₂ Y₂ -
        doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂| ≤ eNumerator)
    (hMass : |actualCellMass A₁ Y₁ -
      continuumCellMass z A₁ Y₁| ≤ eMass) :
    |normalizedDoublePrimeKernelCell z A₁ Y₁ A₂ Y₂ -
        normalizedDoubleContinuumKernelCell z A₁ Y₁ A₂ Y₂| ≤
      eNumerator / actualCellMass A₁ Y₁ +
        |doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂| * eMass /
          (actualCellMass A₁ Y₁ *
            |continuumCellMass z A₁ Y₁|) := by
  unfold normalizedDoublePrimeKernelCell normalizedDoubleContinuumKernelCell
  exact abs_div_sub_div_le hActualMass hContinuumMass hNumerator hMass

/-- Fully explicit normalized output-row bound obtained by combining double
quadrature, moving-cell mass quadrature, and the product-kernel numerator
bound.  All global constants and thresholds precede the moving cells. -/
theorem exists_uniform_normalizedDoubleKernelCell_error_bound :
    ∃ CKernel : ℝ, 0 < CKernel ∧
    ∃ DKernel : ℝ, 0 < DKernel ∧
    ∃ CMass : ℝ, 0 < CMass ∧
    ∃ X₀ : ℕ,
      ∀ z : ℝ, 1 < z →
      ∀ A₁ Y₁ A₂ Y₂ : ℕ,
        X₀ ≤ A₁ → A₁ ≤ Y₁ → (Y₁ : ℝ) ≤ z →
        X₀ ≤ A₂ → A₂ ≤ Y₂ → (Y₂ : ℝ) ≤ z →
        0 < actualCellMass A₁ Y₁ →
        continuumCellMass z A₁ Y₁ ≠ 0 →
        |normalizedDoublePrimeKernelCell z A₁ Y₁ A₂ Y₂ -
            normalizedDoubleContinuumKernelCell z A₁ Y₁ A₂ Y₂| ≤
          (((DKernel / Real.log (A₂ : ℝ) ^ 3) * actualCellMass A₁ Y₁ +
              (DKernel / Real.log (A₁ : ℝ) ^ 3) *
                continuumCellMass z A₂ Y₂) /
              actualCellMass A₁ Y₁) +
            ((CKernel *
                (realLogCoordinate z (Y₁ : ℝ) - realLogCoordinate z (A₁ : ℝ)) *
                (realLogCoordinate z (Y₂ : ℝ) - realLogCoordinate z (A₂ : ℝ))) *
              (5 * CMass / Real.log (A₁ : ℝ) ^ 3) /
              (actualCellMass A₁ Y₁ *
                |continuumCellMass z A₁ Y₁|)) := by
  obtain ⟨CKernel, hCKernel, hProduct⟩ := kernel_product_bound
  obtain ⟨DKernel, hDKernel, XKernel, hDouble⟩ :=
    exists_uniform_doubleKernelCell_error_bound
  obtain ⟨CMass, hCMass, XMass, hMass⟩ :=
    exists_fullReciprocalSum_interval_error_bound
  refine ⟨CKernel, hCKernel, DKernel, hDKernel, CMass, hCMass,
    max (max XKernel XMass) 2, ?_⟩
  intro z hz A₁ Y₁ A₂ Y₂ hA₁ hA₁Y₁ hY₁z
    hA₂ hA₂Y₂ hY₂z hActualMass hContinuumMass
  have hA₁Kernel : XKernel ≤ A₁ :=
    (le_max_left XKernel XMass).trans
      ((le_max_left (max XKernel XMass) 2).trans hA₁)
  have hA₂Kernel : XKernel ≤ A₂ :=
    (le_max_left XKernel XMass).trans
      ((le_max_left (max XKernel XMass) 2).trans hA₂)
  have hA₁Mass : XMass ≤ A₁ :=
    (le_max_right XKernel XMass).trans
      ((le_max_left (max XKernel XMass) 2).trans hA₁)
  have hA₁two : 2 ≤ A₁ :=
    (le_max_right (max XKernel XMass) 2).trans hA₁
  have hA₂two : 2 ≤ A₂ :=
    (le_max_right (max XKernel XMass) 2).trans hA₂
  have hNum := hDouble z hz A₁ Y₁ A₂ Y₂
    hA₁Kernel hA₁Y₁ hY₁z hA₂Kernel hA₂Y₂ hY₂z
  have hMassRaw := hMass A₁ Y₁ hA₁Mass hA₁Y₁
  have hMassCoord :
      |actualCellMass A₁ Y₁ - continuumCellMass z A₁ Y₁| ≤
        5 * CMass / Real.log (A₁ : ℝ) ^ 3 := by
    unfold actualCellMass continuumCellMass
    rw [show Real.log (realLogCoordinate z (Y₁ : ℝ)) -
        Real.log (realLogCoordinate z (A₁ : ℝ)) =
      Real.log (Real.log (Y₁ : ℝ)) - Real.log (Real.log (A₁ : ℝ)) by
        simpa only [realLogCoordinate, logCoordinate] using
          log_logCoordinate_sub hz hA₁two hA₁Y₁]
    exact hMassRaw
  have hCont := abs_doubleContinuumKernelCell_le_productLengths hz
    hA₁two hA₁Y₁ hY₁z hA₂two hA₂Y₂ hY₂z
    (by
      intro u hu t ht
      simpa only [covarianceKernel] using hProduct u hu t ht)
  have hratio := normalizedDoubleKernelCell_error_le hActualMass hContinuumMass
    hNum hMassCoord
  exact hratio.trans (by
    apply add_le_add
    · exact le_rfl
    · exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCont
          (by positivity : 0 ≤ 5 * CMass / Real.log (A₁ : ℝ) ^ 3))
        (mul_nonneg hActualMass.le (abs_nonneg _)))

end Erdos390.Full.DoubleKernelPrimeQuadrature
