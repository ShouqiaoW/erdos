import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalCoreFirst
import Erdos390.WholePaper.BankPaperFourFiveFixedSimplexKernel

/-!
# Discrete variation of the frozen four/five kernel

The periodic exceptional-core argument needs the prime-power variation of

`b ↦ K(log((2n)/b) / log(yNat n)) / b`.

This file proves that estimate from the already formalized uniform `C¹`
bound for `fourFiveContinuumMixtureKernel`.  The coordinate-range premise is
kept explicit: it is the elementary chamber geometry asserting that all
sampled logarithmic coordinates lie in the padded interval `[4.1,4.7]`.

No rough-number count or exceptional-core asymptotic is used here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! ## The literal frozen kernel -/

/-- The logarithmic coordinate at a frozen smooth core. -/
def roughCanonicalFourFiveFrozenCoordinate (n b : Nat) : Real :=
  Real.log ((2 * (n : Real)) / (b : Real)) /
    Real.log (yNat n : Real)

/-- The literal four/five continuum kernel divided by its smooth core.
The zero value is arbitrary and is never used in a positive core block. -/
def roughCanonicalFourFiveFrozenKernelWeight (n b : Nat) : Real :=
  if b = 0 then 0 else
    fourFiveContinuumMixtureKernel
      (roughCanonicalFourFiveFrozenCoordinate n b) / (b : Real)

/-! ## Compact `C¹` control -/

/-- A common derivative bound on the padded chamber makes the continuum
mixture kernel Lipschitz there. -/
theorem abs_fourFiveContinuumMixtureKernel_sub_le_of_C1_bound
    {C u v : Real}
    (hbound :
      ∀ z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        abs (fourFiveContinuumMixtureKernel z) <= C ∧
        abs (fourFiveContinuumMixtureKernelDerivative z) <= C)
    (hu : u ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (hv : v ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
    abs (fourFiveContinuumMixtureKernel u -
      fourFiveContinuumMixtureKernel v) <= C * abs (u - v) := by
  have hdiff (z : Real)
      (hz : z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
      DifferentiableAt Real fourFiveContinuumMixtureKernel z :=
    (hasDerivAt_fourFiveContinuumMixtureKernel hz).differentiableAt
  have hderiv (z : Real)
      (hz : z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
      ‖deriv fourFiveContinuumMixtureKernel z‖ <= C := by
    rw [(hasDerivAt_fourFiveContinuumMixtureKernel hz).deriv,
      Real.norm_eq_abs]
    exact (hbound z hz).2
  have hmean := Convex.norm_image_sub_le_of_norm_deriv_le
    hdiff hderiv
      (convex_Icc ((41 : Real) / 10) ((47 : Real) / 10)) hv hu
  simpa only [Real.norm_eq_abs] using hmean

/-! ## Coordinate increments -/

/-- Multiplication by a fixed positive integer cancels from the consecutive
logarithmic-coordinate increment. -/
theorem roughCanonicalFourFiveFrozenCoordinate_sub_succ
    {n D m : Nat} (hn : 0 < n) (hD : 0 < D) (hm : 0 < m)
    (hlogY : Real.log (yNat n : Real) ≠ 0) :
    roughCanonicalFourFiveFrozenCoordinate n (D * m) -
        roughCanonicalFourFiveFrozenCoordinate n (D * (m + 1)) =
      Real.log (((m + 1 : Nat) : Real) / (m : Real)) /
        Real.log (yNat n : Real) := by
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have htwoN : (0 : Real) < 2 * (n : Real) := by positivity
  have hDReal : (0 : Real) < (D : Real) := by exact_mod_cast hD
  have hmReal : (0 : Real) < (m : Real) := by exact_mod_cast hm
  have hmOneReal : (0 : Real) < ((m + 1 : Nat) : Real) := by positivity
  have hmSuccReal : (0 : Real) < (m : Real) + 1 := by positivity
  unfold roughCanonicalFourFiveFrozenCoordinate
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [Real.log_div htwoN.ne' (mul_pos hDReal hmReal).ne',
    Real.log_div htwoN.ne' (mul_pos hDReal hmSuccReal).ne',
    Real.log_mul hDReal.ne' hmReal.ne',
    Real.log_mul hDReal.ne' hmSuccReal.ne',
    Real.log_div hmSuccReal.ne' hmReal.ne']
  field_simp [hlogY]
  ring

/-- If `log(yNat n) >= 1`, one consecutive frozen coordinate changes by at
most `1/m`. -/
theorem abs_roughCanonicalFourFiveFrozenCoordinate_sub_succ_le
    {n D m : Nat} (hn : 0 < n) (hD : 0 < D) (hm : 0 < m)
    (hlogY : 1 <= Real.log (yNat n : Real)) :
    abs (roughCanonicalFourFiveFrozenCoordinate n (D * m) -
      roughCanonicalFourFiveFrozenCoordinate n (D * (m + 1))) <=
        1 / (m : Real) := by
  have hmReal : (0 : Real) < (m : Real) := by exact_mod_cast hm
  have hmOneReal : (0 : Real) < ((m + 1 : Nat) : Real) := by positivity
  have hratioPos :
      (0 : Real) < ((m + 1 : Nat) : Real) / (m : Real) :=
    div_pos hmOneReal hmReal
  have hratioOne :
      (1 : Real) <= ((m + 1 : Nat) : Real) / (m : Real) := by
    apply (le_div_iff₀ hmReal).2
    simpa only [one_mul] using
      (show (m : Real) <= ((m + 1 : Nat) : Real) by
        exact_mod_cast Nat.le_succ m)
  have hlogRatioNonneg :
      0 <= Real.log (((m + 1 : Nat) : Real) / (m : Real)) :=
    Real.log_nonneg hratioOne
  have hlogRatio :
      Real.log (((m + 1 : Nat) : Real) / (m : Real)) <=
        1 / (m : Real) := by
    have h := Real.log_le_sub_one_of_pos hratioPos
    calc
      Real.log (((m + 1 : Nat) : Real) / (m : Real)) <=
          ((m + 1 : Nat) : Real) / (m : Real) - 1 := h
      _ = 1 / (m : Real) := by
        field_simp [hmReal.ne']
        push_cast
        ring
  have hlogYPos : 0 < Real.log (yNat n : Real) :=
    zero_lt_one.trans_le hlogY
  rw [roughCanonicalFourFiveFrozenCoordinate_sub_succ
    hn hD hm hlogYPos.ne',
    abs_of_nonneg (div_nonneg hlogRatioNonneg hlogYPos.le)]
  exact (div_le_self hlogRatioNonneg hlogY).trans hlogRatio

/-! ## Finite variation algebra -/

/-- An endpoint bound and a telescoping reciprocal-step bound imply the
required total discrete variation. -/
theorem roughCoreDiscreteVariation_le_two_mul_div_of_reciprocalSteps
    {F : Nat -> Real} {D B : Nat} {C : Real}
    (hD : 0 < D) (hB : 1 <= B) (hC : 0 <= C)
    (hend : abs (F B) <= C / ((D : Real) * (B : Real)))
    (hstep : ∀ m ∈ Finset.Ioc 0 (B - 1),
      abs (F m - F (m + 1)) <=
        (2 * C / (D : Real)) *
          (1 / (m : Real) - 1 / ((m + 1 : Nat) : Real))) :
    roughCoreDiscreteVariation F B <= 2 * C / (D : Real) := by
  have hB0 : B ≠ 0 := by omega
  have hDReal : (0 : Real) < (D : Real) := by exact_mod_cast hD
  have hBReal : (0 : Real) < (B : Real) := by exact_mod_cast hB
  have hinterval :
      Finset.Ioc 0 (B - 1) = Finset.Ico 1 B := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have htelescope :
      (∑ m ∈ Finset.Ioc 0 (B - 1),
        (1 / (m : Real) - 1 / ((m + 1 : Nat) : Real))) =
          1 - 1 / (B : Real) := by
    rw [hinterval]
    simpa only [neg_sub_neg, one_div, Nat.cast_one, inv_one] using
      (Finset.sum_Ico_sub
        (fun m : Nat => -(1 / (m : Real))) hB)
  rw [roughCoreDiscreteVariation, if_neg hB0]
  calc
    abs (F B) +
        ∑ m ∈ Finset.Ioc 0 (B - 1), abs (F m - F (m + 1)) <=
      C / ((D : Real) * (B : Real)) +
        ∑ m ∈ Finset.Ioc 0 (B - 1),
          (2 * C / (D : Real)) *
            (1 / (m : Real) - 1 / ((m + 1 : Nat) : Real)) :=
      add_le_add hend (Finset.sum_le_sum hstep)
    _ = C / ((D : Real) * (B : Real)) +
        (2 * C / (D : Real)) * (1 - 1 / (B : Real)) := by
      rw [← Finset.mul_sum, htelescope]
    _ = 2 * C / (D : Real) -
        C / ((D : Real) * (B : Real)) := by
      field_simp [hDReal.ne', hBReal.ne']
      ring
    _ <= 2 * C / (D : Real) := by
      exact sub_le_self _ (div_nonneg hC
        (mul_nonneg hDReal.le hBReal.le))

/-! ## The literal kernel variation -/

/-- A uniform `C¹` bound and the padded coordinate geometry give the
discrete variation of the literal frozen four/five kernel. -/
theorem roughCoreDiscreteVariation_fourFiveFrozenKernelWeight_le
    {n D B : Nat} {C : Real}
    (hn : 0 < n) (hD : 0 < D) (hlogY : 1 <= Real.log (yNat n : Real))
    (hC : 0 <= C)
    (hbound :
      ∀ z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        abs (fourFiveContinuumMixtureKernel z) <= C ∧
        abs (fourFiveContinuumMixtureKernelDerivative z) <= C)
    (hcoordinate : ∀ m ∈ Finset.Icc 1 B,
      roughCanonicalFourFiveFrozenCoordinate n (D * m) ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
    roughCoreDiscreteVariation
        (fun m => roughCanonicalFourFiveFrozenKernelWeight n (D * m)) B <=
      2 * C / (D : Real) := by
  by_cases hB0 : B = 0
  · subst B
    simp only [roughCoreDiscreteVariation]
    exact div_nonneg (mul_nonneg (by norm_num) hC)
      (Nat.cast_nonneg D)
  have hB : 1 <= B := Nat.one_le_iff_ne_zero.mpr hB0
  apply roughCoreDiscreteVariation_le_two_mul_div_of_reciprocalSteps
    hD hB hC
  · have hDB0 : D * B ≠ 0 :=
      Nat.mul_ne_zero (Nat.ne_of_gt hD) hB0
    have hDBReal : (0 : Real) < ((D * B : Nat) : Real) := by
      exact_mod_cast Nat.mul_pos hD (by omega : 0 < B)
    rw [roughCanonicalFourFiveFrozenKernelWeight, if_neg hDB0,
      abs_div, abs_of_pos hDBReal]
    simpa only [Nat.cast_mul] using
      div_le_div_of_nonneg_right
        (hbound _ (hcoordinate B (Finset.mem_Icc.mpr ⟨hB, le_rfl⟩))).1
        hDBReal.le
  · intro m hm
    have hmData := Finset.mem_Ioc.mp hm
    have hmPos : 0 < m := hmData.1
    have hmOneLeB : m + 1 <= B := by omega
    have hmMem : m ∈ Finset.Icc 1 B :=
      Finset.mem_Icc.mpr ⟨hmPos, by omega⟩
    have hmOneMem : m + 1 ∈ Finset.Icc 1 B :=
      Finset.mem_Icc.mpr ⟨by omega, hmOneLeB⟩
    have hDReal : (0 : Real) < (D : Real) := by exact_mod_cast hD
    have hmReal : (0 : Real) < (m : Real) := by exact_mod_cast hmPos
    have hmOneReal : (0 : Real) < ((m + 1 : Nat) : Real) := by
      positivity
    have hDm0 : D * m ≠ 0 :=
      Nat.mul_ne_zero (Nat.ne_of_gt hD) (Nat.ne_of_gt hmPos)
    have hDmOne0 : D * (m + 1) ≠ 0 :=
      Nat.mul_ne_zero (Nat.ne_of_gt hD) (by omega)
    have hDmOneReal :
        (0 : Real) < ((D * (m + 1) : Nat) : Real) := by
      exact_mod_cast Nat.mul_pos hD (by omega : 0 < m + 1)
    let u := roughCanonicalFourFiveFrozenCoordinate n (D * m)
    let v := roughCanonicalFourFiveFrozenCoordinate n (D * (m + 1))
    have hu : u ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10) :=
      hcoordinate m hmMem
    have hv : v ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10) :=
      hcoordinate (m + 1) hmOneMem
    have hcoordinateStep : abs (u - v) <= 1 / (m : Real) := by
      exact abs_roughCanonicalFourFiveFrozenCoordinate_sub_succ_le
        hn hD hmPos hlogY
    have hkernel :
        abs (fourFiveContinuumMixtureKernel u -
          fourFiveContinuumMixtureKernel v) <=
            C * (1 / (m : Real)) := by
      exact (abs_fourFiveContinuumMixtureKernel_sub_le_of_C1_bound
        hbound hu hv).trans
          (mul_le_mul_of_nonneg_left hcoordinateStep hC)
    have hstepNonneg :
        0 <= 1 / (m : Real) -
          1 / ((m + 1 : Nat) : Real) := by
      exact sub_nonneg.mpr
        (one_div_le_one_div_of_le hmReal
          (by exact_mod_cast (Nat.le_succ m)))
    have hreciprocalD :
        1 / ((D * m : Nat) : Real) -
            1 / ((D * (m + 1) : Nat) : Real) =
          (1 / (D : Real)) *
            (1 / (m : Real) -
              1 / ((m + 1 : Nat) : Real)) := by
      push_cast
      field_simp [hDReal.ne', hmReal.ne', hmOneReal.ne']
    have hreciprocalNonneg :
        0 <= 1 / ((D * m : Nat) : Real) -
          1 / ((D * (m + 1) : Nat) : Real) := by
      rw [hreciprocalD]
      exact mul_nonneg (by positivity) hstepNonneg
    have hfirst :
        abs (fourFiveContinuumMixtureKernel u *
          (1 / ((D * m : Nat) : Real) -
            1 / ((D * (m + 1) : Nat) : Real))) <=
          (C / (D : Real)) *
            (1 / (m : Real) -
              1 / ((m + 1 : Nat) : Real)) := by
      rw [abs_mul, abs_of_nonneg hreciprocalNonneg, hreciprocalD]
      calc
        abs (fourFiveContinuumMixtureKernel u) *
            ((1 / (D : Real)) *
              (1 / (m : Real) -
                1 / ((m + 1 : Nat) : Real))) <=
          C * ((1 / (D : Real)) *
              (1 / (m : Real) -
                1 / ((m + 1 : Nat) : Real))) :=
            mul_le_mul_of_nonneg_right (hbound u hu).1
              (mul_nonneg (by positivity) hstepNonneg)
        _ = (C / (D : Real)) *
            (1 / (m : Real) -
              1 / ((m + 1 : Nat) : Real)) := by ring
    have hsecond :
        abs ((fourFiveContinuumMixtureKernel u -
            fourFiveContinuumMixtureKernel v) /
          ((D * (m + 1) : Nat) : Real)) <=
          (C / (D : Real)) *
            (1 / (m : Real) -
              1 / ((m + 1 : Nat) : Real)) := by
      rw [abs_div, abs_of_pos hDmOneReal]
      calc
        abs (fourFiveContinuumMixtureKernel u -
            fourFiveContinuumMixtureKernel v) /
            ((D * (m + 1) : Nat) : Real) <=
          (C * (1 / (m : Real))) /
            ((D * (m + 1) : Nat) : Real) :=
              div_le_div_of_nonneg_right hkernel hDmOneReal.le
        _ = (C / (D : Real)) *
            (1 / (m : Real) -
              1 / ((m + 1 : Nat) : Real)) := by
          push_cast
          field_simp [hDReal.ne', hmReal.ne', hmOneReal.ne']
          ring
    have hweightM :
        roughCanonicalFourFiveFrozenKernelWeight n (D * m) =
          fourFiveContinuumMixtureKernel u /
            ((D * m : Nat) : Real) := by
      rw [roughCanonicalFourFiveFrozenKernelWeight, if_neg hDm0]
    have hweightMOne :
        roughCanonicalFourFiveFrozenKernelWeight n (D * (m + 1)) =
          fourFiveContinuumMixtureKernel v /
            ((D * (m + 1) : Nat) : Real) := by
      rw [roughCanonicalFourFiveFrozenKernelWeight, if_neg hDmOne0]
    have hdecomposition :
        fourFiveContinuumMixtureKernel u /
              ((D * m : Nat) : Real) -
            fourFiveContinuumMixtureKernel v /
              ((D * (m + 1) : Nat) : Real) =
          fourFiveContinuumMixtureKernel u *
              (1 / ((D * m : Nat) : Real) -
                1 / ((D * (m + 1) : Nat) : Real)) +
            (fourFiveContinuumMixtureKernel u -
              fourFiveContinuumMixtureKernel v) /
                ((D * (m + 1) : Nat) : Real) := by
      ring
    rw [hweightM, hweightMOne, hdecomposition]
    calc
      abs (fourFiveContinuumMixtureKernel u *
            (1 / ((D * m : Nat) : Real) -
              1 / ((D * (m + 1) : Nat) : Real)) +
          (fourFiveContinuumMixtureKernel u -
            fourFiveContinuumMixtureKernel v) /
              ((D * (m + 1) : Nat) : Real)) <=
        abs (fourFiveContinuumMixtureKernel u *
            (1 / ((D * m : Nat) : Real) -
              1 / ((D * (m + 1) : Nat) : Real))) +
          abs ((fourFiveContinuumMixtureKernel u -
            fourFiveContinuumMixtureKernel v) /
              ((D * (m + 1) : Nat) : Real)) :=
        abs_add_le _ _
      _ <= (C / (D : Real)) *
            (1 / (m : Real) -
              1 / ((m + 1 : Nat) : Real)) +
          (C / (D : Real)) *
            (1 / (m : Real) -
              1 / ((m + 1 : Nat) : Real)) :=
        add_le_add hfirst hsecond
      _ = (2 * C / (D : Real)) *
          (1 / (m : Real) -
            1 / ((m + 1 : Nat) : Real)) := by ring

/-- Prime-power form used verbatim by the exceptional-core chamber. -/
theorem roughCoreDiscreteVariation_fourFiveFrozenKernelWeight_primePower_le
    {n p k B : Nat} {C : Real}
    (hn : 0 < n) (hp : p.Prime)
    (hlogY : 1 <= Real.log (yNat n : Real))
    (hC : 0 <= C)
    (hbound :
      ∀ z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        abs (fourFiveContinuumMixtureKernel z) <= C ∧
        abs (fourFiveContinuumMixtureKernelDerivative z) <= C)
    (hcoordinate : ∀ m ∈ Finset.Icc 1 (B / p ^ k),
      roughCanonicalFourFiveFrozenCoordinate n (p ^ k * m) ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
    roughCoreDiscreteVariation
        (fun m => roughCanonicalFourFiveFrozenKernelWeight n (p ^ k * m))
        (B / p ^ k) <=
      2 * C / ((p ^ k : Nat) : Real) := by
  exact roughCoreDiscreteVariation_fourFiveFrozenKernelWeight_le
    hn (pow_pos hp.pos k) hlogY hC hbound hcoordinate

/-- There is one positive constant which supplies the required variation
bound for every positive dilation and every finite frozen core block whose
coordinates stay in the padded chamber. -/
theorem exists_roughCanonicalFourFiveFrozenKernelVariationConstant :
    ∃ Cvariation : Real, 0 < Cvariation ∧
      ∀ n D B : Nat,
        0 < n ->
        0 < D ->
        1 <= Real.log (yNat n : Real) ->
        (∀ m ∈ Finset.Icc 1 B,
          roughCanonicalFourFiveFrozenCoordinate n (D * m) ∈
            Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) ->
        roughCoreDiscreteVariation
            (fun m =>
              roughCanonicalFourFiveFrozenKernelWeight n (D * m)) B <=
          Cvariation / (D : Real) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_fourFiveContinuumMixtureKernel_uniform_C1_bound
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro n D B hn hD hlogY hcoordinate
  exact roughCoreDiscreteVariation_fourFiveFrozenKernelWeight_le
    hn hD hlogY hC.le hbound hcoordinate

/-- Chamber-facing prime-power specialization of the uniform constant.
The only remaining premise is the padded coordinate geometry for the
particular deep-core block. -/
theorem
    exists_roughCanonicalFourFiveFrozenKernelPrimePowerVariationConstant :
    ∃ Cvariation : Real, 0 < Cvariation ∧
      ∀ n p k B : Nat,
        0 < n ->
        p.Prime ->
        1 <= Real.log (yNat n : Real) ->
        (∀ m ∈ Finset.Icc 1 (B / p ^ k),
          roughCanonicalFourFiveFrozenCoordinate n (p ^ k * m) ∈
            Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) ->
        roughCoreDiscreteVariation
            (fun m =>
              roughCanonicalFourFiveFrozenKernelWeight n (p ^ k * m))
            (B / p ^ k) <=
          Cvariation / ((p ^ k : Nat) : Real) := by
  obtain ⟨Cvariation, hCvariation, hvariation⟩ :=
    exists_roughCanonicalFourFiveFrozenKernelVariationConstant
  refine ⟨Cvariation, hCvariation, ?_⟩
  intro n p k B hn hp hlogY hcoordinate
  exact hvariation n (p ^ k) (B / p ^ k)
    hn (pow_pos hp.pos k) hlogY hcoordinate

end BankPaperRealization

end

end Erdos390.WholePaper
