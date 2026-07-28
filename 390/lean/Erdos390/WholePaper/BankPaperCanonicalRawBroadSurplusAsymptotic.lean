import Erdos390.WholePaper.BankPaperCanonicalGuardCapacityReduction
import Erdos390.WholePaper.RoughFixedHeadFriableShift
import Erdos390.WholePaper.UpperScale

/-!
# Eventual raw broad-pool surplus on every active rough row

The tangent clean-list estimate is global in the common multiplier and
therefore cannot by itself give a lower bound in each complete rough row.
The rowwise input needed by the guard-capacity reduction is instead the
`active-clean-pool` estimate from Section 6 of the paper.  This file derives
that estimate from the already proved uniform de Bruijn bound and the
already proved fixed-head endpoint shift.

The proof has three quantitative layers.

* On a fixed-ratio interval `(A,B]`, the Dickman endpoint main term grows by
  a fixed positive multiple of `B-A`.  The uniform friable error is absorbed
  once `log y` is large.
* Exact head Möbius inversion and the fixed-divisor endpoint shift retain a
  fixed multiple of `A` in the head-free smooth interval.
* For an active label, `A = n / label` tends to infinity uniformly, while
  both `label / n` and `upperTailLength c n / n` tend to zero.  Consequently
  the broad pool dominates the literal upper-row quota and the three local
  guards.

The final theorem constructs
`RoughCanonicalActiveRawBroadSurplus ... 3 poolMinimum` for every fixed
`poolMinimum`, without a selector premise or an additional analytic
assumption.  The stronger linear real lower bound used to absorb that
constant is retained separately below.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells
open BankPaperRealization

noncomputable section

/-! ## A positive Dickman floor -/

/-- The fixed Dickman value used as a uniform floor on the full endpoint
range `0 <= u <= 5`. -/
def roughCanonicalPoolDickmanFloor : Real :=
  rho 5

/-- The fixed Dickman floor is strictly positive. -/
theorem roughCanonicalPoolDickmanFloor_pos :
    0 < roughCanonicalPoolDickmanFloor := by
  unfold roughCanonicalPoolDickmanFloor
  exact rho_pos_on_zero_five (by norm_num) le_rfl

/-- The value at the right endpoint `5` is a lower bound throughout the
compact Dickman range used by the rough rows. -/
theorem roughCanonicalPoolDickmanFloor_le_rho
    {u : Real} (_hu0 : 0 <= u) (hu5 : u <= 5) :
    roughCanonicalPoolDickmanFloor <= rho u := by
  unfold roughCanonicalPoolDickmanFloor
  by_cases hu1 : u <= 1
  · rw [rho_eq_one_of_le_one hu1]
    exact Erdos390.Full.FriableAsymptotic.rho_le_one_of_le_five le_rfl
  · have huMem : u ∈ Set.Icc (1 : Real) 5 :=
      ⟨le_of_not_ge hu1, hu5⟩
    have hfive : (5 : Real) ∈ Set.Icc (1 : Real) 5 := by norm_num
    exact antitoneOn_rho_one_five huMem hfive hu5

/-! ## Growth of the unrestricted smooth interval -/

/-- On the full compact de Bruijn range, the Dickman endpoint main term
grows by at least half the fixed Dickman floor once `log y` is large.

This elementary estimate uses the proved one-Lipschitz property of `rho`.
It deliberately keeps the natural endpoints `A,B`; all floor losses have
already occurred before this statement. -/
theorem roughCanonical_dickmanEndpointMain_sub_lower
    {A B y : Nat}
    (hyTwo : 2 <= y) (hA : 0 < A) (hAB : A <= B)
    (hlogB : Real.log (B : Real) <= 5 * Real.log (y : Real))
    (hlogLarge :
      2 / Real.log (y : Real) <= roughCanonicalPoolDickmanFloor) :
    roughCanonicalPoolDickmanFloor / 2 * ((B - A : Nat) : Real) <=
      (B : Real) * rho (FriableAsymptotic.dickmanU B y) -
        (A : Real) * rho (FriableAsymptotic.dickmanU A y) := by
  have hyReal : (1 : Real) < y := by exact_mod_cast (by omega : 1 < y)
  have hlogY : 0 < Real.log (y : Real) := Real.log_pos hyReal
  have hAReal : (0 : Real) < A := by exact_mod_cast hA
  have hBPos : 0 < B := hA.trans_le hAB
  have hBReal : (0 : Real) < B := by exact_mod_cast hBPos
  let uA : Real := Real.log (A : Real) / Real.log (y : Real)
  let uB : Real := Real.log (B : Real) / Real.log (y : Real)
  have hlogAB : Real.log (A : Real) <= Real.log (B : Real) :=
    Real.log_le_log hAReal (by exact_mod_cast hAB)
  have huAB : uA <= uB := by
    dsimp only [uA, uB]
    exact div_le_div_of_nonneg_right hlogAB hlogY.le
  have huA0 : 0 <= uA := by
    dsimp only [uA]
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 <= A by omega))) hlogY.le
  have huB0 : 0 <= uB := huA0.trans huAB
  have huB5 : uB <= 5 := by
    dsimp only [uB]
    exact (div_le_iff₀ hlogY).2 hlogB
  have hrhoFloor : roughCanonicalPoolDickmanFloor <= rho uB :=
    roughCanonicalPoolDickmanFloor_le_rho huB0 huB5
  have hrhoLip : |rho uB - rho uA| <= uB - uA := by
    exact FriableAsymptotic.rho_lipschitz_of_le_five huAB huB5
  have hrhoDiff : -(uB - uA) <= rho uB - rho uA :=
    (abs_le.mp hrhoLip).1
  have hlogGap :
      (A : Real) *
          (Real.log (B : Real) - Real.log (A : Real)) <=
        (B : Real) - (A : Real) := by
    have hratioPos : 0 < (B : Real) / (A : Real) :=
      div_pos hBReal hAReal
    have hlog := Real.log_le_sub_one_of_pos hratioPos
    rw [Real.log_div hBReal.ne' hAReal.ne'] at hlog
    have hscaled := mul_le_mul_of_nonneg_left hlog hAReal.le
    calc
      (A : Real) *
          (Real.log (B : Real) - Real.log (A : Real)) <=
        (A : Real) * ((B : Real) / (A : Real) - 1) := hscaled
      _ = (B : Real) - (A : Real) := by
        field_simp [hAReal.ne']
  have hcoordGap :
      (A : Real) * (uB - uA) <=
        ((B : Real) - (A : Real)) / Real.log (y : Real) := by
    calc
      (A : Real) * (uB - uA) =
          ((A : Real) *
              (Real.log (B : Real) - Real.log (A : Real))) /
            Real.log (y : Real) := by
        dsimp only [uA, uB]
        field_simp [hlogY.ne']
      _ <= ((B : Real) - (A : Real)) /
          Real.log (y : Real) :=
        div_le_div_of_nonneg_right hlogGap hlogY.le
  have hfloorHalf :
      roughCanonicalPoolDickmanFloor / 2 <=
        roughCanonicalPoolDickmanFloor -
          1 / Real.log (y : Real) := by
    have hinv : 2 * (1 / Real.log (y : Real)) <=
        roughCanonicalPoolDickmanFloor := by
      calc
        2 * (1 / Real.log (y : Real)) =
            2 / Real.log (y : Real) := by ring
        _ <= roughCanonicalPoolDickmanFloor := hlogLarge
    linarith
  have hlength : (0 : Real) <= (B : Real) - (A : Real) := by
    exact sub_nonneg.mpr (by exact_mod_cast hAB)
  have hcastSub : (((B - A : Nat) : Real)) =
      (B : Real) - (A : Real) := by
    rw [Nat.cast_sub hAB]
  rw [hcastSub]
  calc
    roughCanonicalPoolDickmanFloor / 2 *
          ((B : Real) - (A : Real)) <=
        (roughCanonicalPoolDickmanFloor -
            1 / Real.log (y : Real)) *
          ((B : Real) - (A : Real)) :=
      mul_le_mul_of_nonneg_right hfloorHalf hlength
    _ = roughCanonicalPoolDickmanFloor *
          ((B : Real) - (A : Real)) -
        ((B : Real) - (A : Real)) / Real.log (y : Real) := by ring
    _ <= ((B : Real) - (A : Real)) * rho uB -
        (A : Real) * (uB - uA) := by
      have hmainScaled :
          roughCanonicalPoolDickmanFloor *
              ((B : Real) - (A : Real)) <=
            ((B : Real) - (A : Real)) * rho uB := by
        calc
          _ = ((B : Real) - (A : Real)) *
              roughCanonicalPoolDickmanFloor := by ring
          _ <= ((B : Real) - (A : Real)) * rho uB :=
            mul_le_mul_of_nonneg_left hrhoFloor hlength
      exact sub_le_sub hmainScaled hcoordGap
    _ <= ((B : Real) - (A : Real)) * rho uB +
        (A : Real) * (rho uB - rho uA) := by
      have hmul := mul_le_mul_of_nonneg_left hrhoDiff hAReal.le
      linarith
    _ = (B : Real) * rho (FriableAsymptotic.dickmanU B y) -
        (A : Real) * rho (FriableAsymptotic.dickmanU A y) := by
      dsimp only [uA, uB, FriableAsymptotic.dickmanU]
      ring

/-- A supplied uniform de Bruijn estimate gives a fixed positive lower
bound for a smooth interval whose length is a fixed fraction of its lower
endpoint. -/
theorem roughCanonical_smoothInterval_card_lower
    {C : Real} {Y0 A B y : Nat}
    (hC : 0 < C)
    (hdeBruijn : forall {X z : Nat},
      Y0 <= z -> 0 < X ->
      Real.log (X : Real) <= 5 * Real.log (z : Real) ->
      |(FriableAsymptotic.friableCount X z : Real) -
          (X : Real) * rho (FriableAsymptotic.dickmanU X z)| <=
        C * (X : Real) / Real.log (z : Real))
    (hY : Y0 <= y) (hyTwo : 2 <= y)
    (hA : 0 < A) (hAB : A <= B) (hBthree : B <= 3 * A)
    (hlength : A <= 2 * (B - A))
    (hlogB : Real.log (B : Real) <= 5 * Real.log (y : Real))
    (hlogMain :
      2 / Real.log (y : Real) <= roughCanonicalPoolDickmanFloor)
    (hlogError :
      8 * C / Real.log (y : Real) <=
        roughCanonicalPoolDickmanFloor / 4) :
    roughCanonicalPoolDickmanFloor / 8 * (A : Real) <=
      ((smoothInterval A B y).card : Real) := by
  have hBPos : 0 < B := hA.trans_le hAB
  have hyReal : (1 : Real) < y := by exact_mod_cast (by omega : 1 < y)
  have hlogY : 0 < Real.log (y : Real) := Real.log_pos hyReal
  have hlogA : Real.log (A : Real) <= 5 * Real.log (y : Real) := by
    have hmono : Real.log (A : Real) <= Real.log (B : Real) := by
      apply Real.log_le_log
      · exact_mod_cast hA
      · exact_mod_cast hAB
    exact hmono.trans hlogB
  have hPsiA := hdeBruijn hY hA hlogA
  have hPsiB := hdeBruijn hY hBPos hlogB
  have hmain := roughCanonical_dickmanEndpointMain_sub_lower
    hyTwo hA hAB hlogB hlogMain
  have hlengthReal :
      (A : Real) <= 2 * ((B : Real) - (A : Real)) := by
    have hlengthCast :
        (A : Real) <= 2 * (((B - A : Nat) : Real)) := by
      exact_mod_cast hlength
    simpa only [Nat.cast_sub hAB] using hlengthCast
  have hsumEndpoints :
      (A : Real) + (B : Real) <=
        8 * ((B : Real) - (A : Real)) := by
    have hBthreeReal : (B : Real) <= 3 * (A : Real) := by
      exact_mod_cast hBthree
    linarith
  have herror :
      C * (B : Real) / Real.log (y : Real) +
          C * (A : Real) / Real.log (y : Real) <=
        roughCanonicalPoolDickmanFloor / 4 *
          ((B : Real) - (A : Real)) := by
    calc
      C * (B : Real) / Real.log (y : Real) +
          C * (A : Real) / Real.log (y : Real) =
        C * ((A : Real) + (B : Real)) /
          Real.log (y : Real) := by ring
      _ <= C * (8 * ((B : Real) - (A : Real))) /
          Real.log (y : Real) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsumEndpoints hC.le) hlogY.le
      _ = (8 * C / Real.log (y : Real)) *
          ((B : Real) - (A : Real)) := by ring
      _ <= roughCanonicalPoolDickmanFloor / 4 *
          ((B : Real) - (A : Real)) := by
        apply mul_le_mul_of_nonneg_right hlogError
        exact sub_nonneg.mpr (by exact_mod_cast hAB)
  have hPsiLower :
      roughCanonicalPoolDickmanFloor / 4 *
          ((B : Real) - (A : Real)) <=
        (FriableAsymptotic.friableCount B y : Real) -
          (FriableAsymptotic.friableCount A y : Real) := by
    have hlowerB := (abs_le.mp hPsiB).1
    have hupperA := (abs_le.mp hPsiA).2
    have hmain' :
        roughCanonicalPoolDickmanFloor / 2 *
            ((B : Real) - (A : Real)) <=
          (B : Real) * rho (FriableAsymptotic.dickmanU B y) -
            (A : Real) * rho (FriableAsymptotic.dickmanU A y) := by
      simpa only [Nat.cast_sub hAB] using hmain
    linarith
  have hmono := FriableAsymptotic.friableCount_mono_left (y := y) hAB
  rw [smoothInterval_card_eq_psi_sub hAB]
  simp_rw [Erdos390.Full.MarkedFriableAsymptotic.psi_eq_friableCount]
  rw [Nat.cast_sub hmono]
  calc
    roughCanonicalPoolDickmanFloor / 8 * (A : Real) <=
        roughCanonicalPoolDickmanFloor / 4 *
          ((B : Real) - (A : Real)) := by
      have hfloorNonneg := roughCanonicalPoolDickmanFloor_pos.le
      have hscaled :=
        mul_le_mul_of_nonneg_left hlengthReal hfloorNonneg
      nlinarith
    _ <= _ := hPsiLower

/-! ## Closing the fixed head -/

/-- Exact real identity for the rough-head Möbius density. -/
theorem roughHead_sum_moebius_div_eq_density (W : Nat) :
    (∑ d ∈ (roughHeadModulus W).divisors,
        (ArithmeticFunction.moebius d : Real) / (d : Real)) =
      roughHeadDensity W := by
  exact roughHead_moebius_inv_sum_eq_density W

/-- One fixed-divisor endpoint shift controls the corresponding smooth
interval after division by that head divisor. -/
theorem roughCanonical_smoothInterval_divisorShift_error
    {W : Nat} {Kshift : Real} {Y0 A B y d : Nat}
    (hshift : forall {X z e : Nat},
      Y0 <= z ->
      e ∈ (roughHeadModulus W).divisors -> e <= X ->
      Real.log (X : Real) <= 5 * Real.log (z : Real) ->
      |(FriableAsymptotic.friableCount (X / e) z : Real) -
          (FriableAsymptotic.friableCount X z : Real) / (e : Real)| <=
        Kshift * (X : Real) /
            ((e : Real) * Real.log (z : Real)) + 3)
    (hY : Y0 <= y) (hd : d ∈ (roughHeadModulus W).divisors)
    (hdA : d <= A) (hAB : A <= B)
    (hlogB : Real.log (B : Real) <= 5 * Real.log (y : Real)) :
    |((smoothInterval (A / d) (B / d) y).card : Real) -
        ((smoothInterval A B y).card : Real) / (d : Real)| <=
      Kshift * ((A : Real) + (B : Real)) /
          ((d : Real) * Real.log (y : Real)) + 6 := by
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
  have hAPos : 0 < A := hdPos.trans_le hdA
  have hBPos : 0 < B := hAPos.trans_le hAB
  have hdB : d <= B := hdA.trans hAB
  have hlogA : Real.log (A : Real) <= 5 * Real.log (y : Real) := by
    have hmono : Real.log (A : Real) <= Real.log (B : Real) := by
      apply Real.log_le_log
      · exact_mod_cast hAPos
      · exact_mod_cast hAB
    exact hmono.trans hlogB
  have hAshift := hshift hY hd hdA hlogA
  have hBshift := hshift hY hd hdB hlogB
  have hmonoA := FriableAsymptotic.friableCount_mono_left (y := y) hAB
  have hdivAB : A / d <= B / d := Nat.div_le_div_right hAB
  have hmonoDiv :=
    FriableAsymptotic.friableCount_mono_left (y := y) hdivAB
  rw [smoothInterval_card_eq_psi_sub hdivAB,
    smoothInterval_card_eq_psi_sub hAB]
  simp_rw [Erdos390.Full.MarkedFriableAsymptotic.psi_eq_friableCount]
  rw [Nat.cast_sub hmonoDiv, Nat.cast_sub hmonoA]
  have hrearrange :
      ((FriableAsymptotic.friableCount (B / d) y : Real) -
          (FriableAsymptotic.friableCount (A / d) y : Real)) -
        ((FriableAsymptotic.friableCount B y : Real) -
          (FriableAsymptotic.friableCount A y : Real)) / (d : Real) =
      ((FriableAsymptotic.friableCount (B / d) y : Real) -
          (FriableAsymptotic.friableCount B y : Real) / (d : Real)) -
        ((FriableAsymptotic.friableCount (A / d) y : Real) -
          (FriableAsymptotic.friableCount A y : Real) / (d : Real)) := by
    ring
  rw [hrearrange]
  calc
    _ <=
        |(FriableAsymptotic.friableCount (B / d) y : Real) -
          (FriableAsymptotic.friableCount B y : Real) / (d : Real)| +
        |(FriableAsymptotic.friableCount (A / d) y : Real) -
          (FriableAsymptotic.friableCount A y : Real) / (d : Real)| :=
      abs_sub _ _
    _ <=
        (Kshift * (B : Real) /
            ((d : Real) * Real.log (y : Real)) + 3) +
        (Kshift * (A : Real) /
            ((d : Real) * Real.log (y : Real)) + 3) :=
      add_le_add hBshift hAshift
    _ = Kshift * ((A : Real) + (B : Real)) /
          ((d : Real) * Real.log (y : Real)) + 6 := by ring

/-- The exact Möbius closure differs from its positive density main term by
at most the sum of the fixed-divisor endpoint errors. -/
theorem roughCanonical_headFreeSmoothInterval_lower_of_shift
    {W : Nat} {Kshift : Real} {Y0 A B y : Nat}
    (hKshift : 0 < Kshift)
    (hshift : forall {X z d : Nat},
      Y0 <= z ->
      d ∈ (roughHeadModulus W).divisors -> d <= X ->
      Real.log (X : Real) <= 5 * Real.log (z : Real) ->
      |(FriableAsymptotic.friableCount (X / d) z : Real) -
          (FriableAsymptotic.friableCount X z : Real) / (d : Real)| <=
        Kshift * (X : Real) /
            ((d : Real) * Real.log (z : Real)) + 3)
    (hY : Y0 <= y) (hWy : W <= y) (hyTwo : 2 <= y)
    (hmodA : roughHeadModulus W <= A) (hAB : A <= B)
    (hlogB : Real.log (B : Real) <= 5 * Real.log (y : Real)) :
    roughHeadDensity W * ((smoothInterval A B y).card : Real) -
        (roughHeadModulus W : Real) *
          (Kshift * ((A : Real) + (B : Real)) /
              Real.log (y : Real) + 6) <=
      ((roughHeadFreeSmoothInterval W A B y).card : Real) := by
  let P := roughHeadModulus W
  let S : Real := ((smoothInterval A B y).card : Real)
  let E : Real :=
    Kshift * ((A : Real) + (B : Real)) / Real.log (y : Real) + 6
  have hPPos : 0 < P := by
    simpa only [P] using roughHeadModulus_pos W
  have hlogY : 0 < Real.log (y : Real) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hterm : ∀ d ∈ P.divisors,
      (ArithmeticFunction.moebius d : Real) * (S / (d : Real)) - E <=
        (ArithmeticFunction.moebius d : Real) *
          ((smoothInterval (A / d) (B / d) y).card : Real) := by
    intro d hd
    have hdP : d ∈ (roughHeadModulus W).divisors := by
      simpa only [P] using hd
    have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdLeP : d <= P := Nat.le_of_dvd hPPos
      (Nat.mem_divisors.mp hd).1
    have hdA : d <= A := hdLeP.trans (by simpa only [P] using hmodA)
    have herr := roughCanonical_smoothInterval_divisorShift_error
      (W := W) (Kshift := Kshift) (Y0 := Y0)
      hshift hY hdP hdA hAB hlogB
    have hdenomOne : (1 : Real) <= d := by exact_mod_cast hdPos
    have herr' :
        |((smoothInterval (A / d) (B / d) y).card : Real) -
            S / (d : Real)| <= E := by
      apply herr.trans
      dsimp only [E]
      have hdenom :
          (d : Real) * Real.log (y : Real) >=
            Real.log (y : Real) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hdenomOne hlogY.le
      have hnumNonneg :
          0 <= Kshift * ((A : Real) + (B : Real)) :=
        mul_nonneg hKshift.le (by positivity)
      simpa only [add_comm] using
        add_le_add_right
          (div_le_div_of_nonneg_left
            hnumNonneg hlogY hdenom) 6
    have hmu : |(ArithmeticFunction.moebius d : Real)| <= 1 := by
      rcases ArithmeticFunction.moebius_eq_or d with hzero | hone | hneg
      · simp [hzero]
      · simp [hone]
      · simp [hneg]
    have hmul :
        |(ArithmeticFunction.moebius d : Real) *
            (((smoothInterval (A / d) (B / d) y).card : Real) -
              S / (d : Real))| <= E := by
      rw [abs_mul]
      exact (mul_le_mul hmu herr' (abs_nonneg _) zero_le_one).trans_eq
        (one_mul E)
    have hlower := (abs_le.mp hmul).1
    linarith
  rw [roughHeadFreeSmoothInterval_card_real_eq_divisorShift hWy]
  have hsum := Finset.sum_le_sum hterm
  have hmain :
      (∑ d ∈ P.divisors,
          ((ArithmeticFunction.moebius d : Real) * (S / (d : Real)) - E)) =
        roughHeadDensity W * S - (P.divisors.card : Real) * E := by
    calc
      _ = (∑ d ∈ P.divisors,
          (ArithmeticFunction.moebius d : Real) / (d : Real)) * S -
            (P.divisors.card : Real) * E := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul]
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro d _hd
        ring
      _ = roughHeadDensity W * S - (P.divisors.card : Real) * E := by
        rw [show (∑ d ∈ P.divisors,
            (ArithmeticFunction.moebius d : Real) / (d : Real)) =
          roughHeadDensity W by
            simpa only [P] using roughHead_sum_moebius_div_eq_density W]
  rw [hmain] at hsum
  have hE : 0 <= E := by
    dsimp only [E]
    positivity
  have hcard : (P.divisors.card : Real) <= (P : Real) := by
    exact_mod_cast Nat.card_divisors_le_self P
  have hreplace :
      roughHeadDensity W * S - (P : Real) * E <=
        roughHeadDensity W * S - (P.divisors.card : Real) * E := by
    exact sub_le_sub_left (mul_le_mul_of_nonneg_right hcard hE) _
  simpa only [P, S, E] using hreplace.trans hsum

/-- Once the logarithmic and fixed endpoint losses are small, the
head-free smooth interval retains a fixed linear fraction of its lower
endpoint. -/
theorem roughCanonical_headFreeSmoothInterval_card_lower
    {W : Nat} {C Kshift : Real} {YdeBruijn Yshift A B y : Nat}
    (hC : 0 < C) (hKshift : 0 < Kshift)
    (hdeBruijn : forall {X z : Nat},
      YdeBruijn <= z -> 0 < X ->
      Real.log (X : Real) <= 5 * Real.log (z : Real) ->
      |(FriableAsymptotic.friableCount X z : Real) -
          (X : Real) * rho (FriableAsymptotic.dickmanU X z)| <=
        C * (X : Real) / Real.log (z : Real))
    (hshift : forall {X z d : Nat},
      Yshift <= z ->
      d ∈ (roughHeadModulus W).divisors -> d <= X ->
      Real.log (X : Real) <= 5 * Real.log (z : Real) ->
      |(FriableAsymptotic.friableCount (X / d) z : Real) -
          (FriableAsymptotic.friableCount X z : Real) / (d : Real)| <=
        Kshift * (X : Real) /
            ((d : Real) * Real.log (z : Real)) + 3)
    (hYdeBruijn : YdeBruijn <= y) (hYshift : Yshift <= y)
    (hWy : W <= y) (hyTwo : 2 <= y)
    (hmodA : roughHeadModulus W <= A)
    (hAB : A <= B) (hBthree : B <= 3 * A)
    (hlength : A <= 2 * (B - A))
    (hlogB : Real.log (B : Real) <= 5 * Real.log (y : Real))
    (hlogMain :
      2 / Real.log (y : Real) <= roughCanonicalPoolDickmanFloor)
    (hlogSmooth :
      8 * C / Real.log (y : Real) <=
        roughCanonicalPoolDickmanFloor / 4)
    (hlogHead :
      4 * (roughHeadModulus W : Real) * Kshift /
          Real.log (y : Real) <=
        roughHeadDensity W * roughCanonicalPoolDickmanFloor / 32)
    (hendpoint :
      6 * (roughHeadModulus W : Real) <=
        roughHeadDensity W * roughCanonicalPoolDickmanFloor / 32 *
          (A : Real)) :
    roughHeadDensity W * roughCanonicalPoolDickmanFloor / 16 *
        (A : Real) <=
      ((roughHeadFreeSmoothInterval W A B y).card : Real) := by
  have hA : 0 < A :=
    (roughHeadModulus_pos W).trans_le hmodA
  have hsmooth := roughCanonical_smoothInterval_card_lower
    hC hdeBruijn hYdeBruijn hyTwo hA hAB hBthree hlength hlogB
      hlogMain hlogSmooth
  have hhead := roughCanonical_headFreeSmoothInterval_lower_of_shift
    hKshift hshift hYshift hWy hyTwo hmodA hAB hlogB
  have hAplusB : (A : Real) + (B : Real) <= 4 * (A : Real) := by
    have hBthreeReal : (B : Real) <= 3 * (A : Real) := by
      exact_mod_cast hBthree
    linarith
  have hlogY : 0 < Real.log (y : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hshiftError :
      (roughHeadModulus W : Real) *
          (Kshift * ((A : Real) + (B : Real)) /
              Real.log (y : Real) + 6) <=
        roughHeadDensity W * roughCanonicalPoolDickmanFloor / 16 *
          (A : Real) := by
    calc
      _ = (roughHeadModulus W : Real) * Kshift *
            ((A : Real) + (B : Real)) /
              Real.log (y : Real) +
          6 * (roughHeadModulus W : Real) := by ring
      _ <= (roughHeadModulus W : Real) * Kshift *
            (4 * (A : Real)) / Real.log (y : Real) +
          6 * (roughHeadModulus W : Real) := by
        gcongr
      _ = (4 * (roughHeadModulus W : Real) * Kshift /
            Real.log (y : Real)) * (A : Real) +
          6 * (roughHeadModulus W : Real) := by ring
      _ <= (roughHeadDensity W * roughCanonicalPoolDickmanFloor / 32) *
            (A : Real) +
          (roughHeadDensity W * roughCanonicalPoolDickmanFloor / 32) *
            (A : Real) :=
        add_le_add
          (mul_le_mul_of_nonneg_right hlogHead (Nat.cast_nonneg A))
          hendpoint
      _ = roughHeadDensity W * roughCanonicalPoolDickmanFloor / 16 *
          (A : Real) := by ring
  have hmain :
      roughHeadDensity W * roughCanonicalPoolDickmanFloor / 8 *
          (A : Real) <=
        roughHeadDensity W * ((smoothInterval A B y).card : Real) := by
    calc
      _ = roughHeadDensity W *
          (roughCanonicalPoolDickmanFloor / 8 * (A : Real)) := by ring
      _ <= roughHeadDensity W *
          ((smoothInterval A B y).card : Real) :=
        mul_le_mul_of_nonneg_left hsmooth (roughHeadDensity_pos W).le
  linarith

/-! ## Literal rough-row adapters -/

/-- The real linear density retained in the raw broad pool. -/
def roughCanonicalRawBroadPoolDensity (W : Nat) : Real :=
  roughHeadDensity W * roughCanonicalPoolDickmanFloor / 16

/-- The retained raw broad-pool density is strictly positive. -/
theorem roughCanonicalRawBroadPoolDensity_pos (W : Nat) :
    0 < roughCanonicalRawBroadPoolDensity W := by
  unfold roughCanonicalRawBroadPoolDensity
  exact div_pos
    (mul_pos (roughHeadDensity_pos W)
      roughCanonicalPoolDickmanFloor_pos) (by norm_num)

/-- Reindexing identifies the literal raw broad correction pool with the
head-free smooth quotient interval. -/
theorem roughCanonicalBroadCorrectionPool_card_eq_headFreeSmoothInterval
    {W n h K y : Nat}
    (row : CanonicalCompleteRoughRow y (roughRawCandidateSet n h K))
    (hWy : W <= y) :
    (roughCanonicalBroadCorrectionPool W n h K y row.1).card =
      (roughHeadFreeSmoothInterval W (n / row.1)
        ((2 * n - K * h) / row.1) y).card := by
  have hlabel := isCompleteRoughLabel_of_canonicalCompleteRoughRow row
  have hcop := isCompleteRoughLabel_coprime_roughHeadModulus hWy hlabel
  unfold roughCanonicalBroadCorrectionPool roughBroadLowerBlock
  exact completeRoughRowFiber_headFreeIoc_card_eq_headFreeSmoothInterval
    hlabel hcop

/-- The same reindexing only needs the intrinsic complete-rough-label
geometry.  In particular, it does not require the label to have already
been observed among the guarded candidates. -/
theorem roughCanonicalBroadCorrectionPool_card_eq_headFreeSmoothInterval_of_isCompleteRoughLabel
    {W n h K y label : Nat}
    (hlabel : IsCompleteRoughLabel y label)
    (hWy : W <= y) :
    (roughCanonicalBroadCorrectionPool W n h K y label).card =
      (roughHeadFreeSmoothInterval W (n / label)
        ((2 * n - K * h) / label) y).card := by
  have hcop := isCompleteRoughLabel_coprime_roughHeadModulus hWy hlabel
  unfold roughCanonicalBroadCorrectionPool roughBroadLowerBlock
  exact completeRoughRowFiber_headFreeIoc_card_eq_headFreeSmoothInterval
    hlabel hcop

/-- The literal upper-row target is bounded by its quotient interval
length, hence by `h / label + 1`. -/
theorem roughUpperCompleteRoughRowTarget_le_div_add_one
    {n h y label : Nat} (hlabel : IsCompleteRoughLabel y label) :
    roughUpperCompleteRoughRowTarget n h y label <= h / label + 1 := by
  have hlabelPos := hlabel.1
  have hsubset :
      smoothInterval ((2 * n) / label) ((2 * n + h) / label) y ⊆
        Finset.Ioc ((2 * n) / label) ((2 * n + h) / label) := by
    intro a ha
    exact Finset.mem_Ioc.mpr
      ⟨(mem_smoothInterval.mp ha).1, (mem_smoothInterval.mp ha).2.1⟩
  unfold roughUpperCompleteRoughRowTarget roughUpperBlock
  rw [completeRoughRowFiber_Ioc_card_eq_smoothInterval hlabel]
  have hcard := Finset.card_le_card hsubset
  have hquotient :
      (2 * n + h) / label <=
        (2 * n) / label + h / label + 1 := by
    rw [Nat.add_div hlabelPos]
    split_ifs <;> omega
  have hlength :
      (2 * n + h) / label - (2 * n) / label <= h / label + 1 := by
    apply Nat.sub_le_iff_le_add'.mpr
    simpa only [Nat.add_assoc] using hquotient
  have hcard' :
      (smoothInterval ((2 * n) / label) ((2 * n + h) / label) y).card <=
        (2 * n + h) / label - (2 * n) / label := by
    simpa only [Nat.card_Ioc] using hcard
  exact hcard'.trans hlength

/-- Any guarded label is also represented by a canonical row of the raw
candidate set. -/
def BankPaperRealization.rawCanonicalRowOfGuardedLabel
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K label : Nat)
    (hlabel : label ∈ completeRoughLabelSet (yNat n)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)) :
    CanonicalCompleteRoughRow (yNat n) (roughRawCandidateSet n h K) := by
  refine ⟨label, ?_⟩
  obtain ⟨a, ha, hlabelA⟩ := mem_completeRoughLabelSet.mp hlabel
  exact mem_completeRoughLabelSet.mpr
    ⟨a, R.roughCanonicalGuardedCandidateSet_subset_rawCandidateSet
      certificate deltaStar K ha, hlabelA⟩

/-! ## Uniform paper-scale choices -/

private theorem roughCanonical_yNat_tendsto_atTop : Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : Nat => y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : Real) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_nat_floor_atTop.comp hy

private theorem roughCanonical_log_yNat_tendsto_atTop :
    Tendsto (fun n : Nat => Real.log (yNat n : Real)) atTop atTop := by
  have hyReal : Tendsto (fun n : Nat => (yNat n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp roughCanonical_yNat_tendsto_atTop
  exact Real.tendsto_log_atTop.comp hyReal

private theorem roughCanonical_rpow_tendsto_atTop
    {deltaStar : Real} (hdelta : 0 < deltaStar) :
    Tendsto (fun n : Nat => (n : Real) ^ deltaStar) atTop atTop := by
  exact (tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop

/-- Active labels have uniformly large natural quotient scale once the
real exceptional cutoff is large. -/
theorem roughCanonical_activeLabel_div_scale_lower
    {n label A0 : Nat} {deltaStar : Real}
    (_hn : 0 < n) (hlabel : 0 < label)
    (hactive : (n : Real) ^ deltaStar <=
      2 * (n : Real) / (label : Real))
    (hpower : (2 * (A0 + 1) : Real) <= (n : Real) ^ deltaStar) :
    A0 <= n / label := by
  have hlabelReal : (0 : Real) < label := by exact_mod_cast hlabel
  have hquotient : (n : Real) ^ deltaStar / 2 <=
      (n : Real) / (label : Real) := by
    apply (div_le_iff₀ (by norm_num : (0 : Real) < 2)).2
    calc
      (n : Real) ^ deltaStar <=
          2 * (n : Real) / (label : Real) := hactive
      _ = (n : Real) / (label : Real) * 2 := by ring
  have hnatUpper :
      (n : Real) / (label : Real) < ((n / label : Nat) : Real) + 1 := by
    apply (div_lt_iff₀ hlabelReal).2
    have hnat := (Nat.div_lt_iff_lt_mul hlabel).mp
      (Nat.lt_succ_self (n / label))
    exact_mod_cast hnat
  have hA0 : (A0 : Real) + 1 <= (n : Real) ^ deltaStar / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : Real) < 2)).2
    calc
      ((A0 : Real) + 1) * 2 =
          2 * ((A0 : Real) + 1) := by ring
      _ <= (n : Real) ^ deltaStar := hpower
  have hreal :
      (A0 : Real) + 1 < ((n / label : Nat) : Real) + 1 :=
    lt_of_le_of_lt hA0 (hquotient.trans_lt hnatUpper)
  have hnat : A0 + 1 < n / label + 1 := by exact_mod_cast hreal
  omega

/-- The active real scale also makes the label itself uniformly negligible
relative to `n`. -/
theorem roughCanonical_activeLabel_three_mul_le_half
    {n label : Nat} {deltaStar : Real}
    (hn : 0 < n) (hlabel : 0 < label)
    (hactive : (n : Real) ^ deltaStar <=
      2 * (n : Real) / (label : Real))
    (hpower : (12 : Real) <= (n : Real) ^ deltaStar) :
    6 * label <= n := by
  have hnReal : (0 : Real) < n := by exact_mod_cast hn
  have hlabelReal : (0 : Real) < label := by exact_mod_cast hlabel
  have hmul := mul_le_mul_of_nonneg_left hactive hlabelReal.le
  have hcancel :
      (label : Real) * (2 * (n : Real) / (label : Real)) =
        2 * (n : Real) := by field_simp [hlabelReal.ne']
  rw [hcancel] at hmul
  have hpowerMul : (12 : Real) * (label : Real) <=
      (label : Real) * (n : Real) ^ deltaStar := by
    calc
      (12 : Real) * (label : Real) = (label : Real) * 12 := by ring
      _ <= (label : Real) * (n : Real) ^ deltaStar :=
        mul_le_mul_of_nonneg_left hpower hlabelReal.le
  have hbound : (12 : Real) * (label : Real) <= 2 * (n : Real) :=
    hpowerMul.trans hmul
  have hbound' : (6 * label : Real) <= (n : Real) := by
    linarith
  exact_mod_cast hbound'

/-- Uniform linear raw broad-pool lower bound on every intrinsic active
complete-rough label.  No prior occurrence among the guarded candidates is
needed.  All analytic constants are chosen before `n` and the label. -/
theorem eventually_roughCanonical_activeRawBroadPool_linear_lower
    (W K : Nat) {c deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop,
      forall label,
        IsCompleteRoughLabel (yNat n) label ->
        RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        roughCanonicalRawBroadPoolDensity W *
            ((n / label : Nat) : Real) <=
          (roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
            (yNat n) label).card := by
  obtain ⟨C, hC, YdeBruijn, hdeBruijn⟩ :=
    FriableAsymptotic.exists_uniform_friableCount_dickman_bound_all_faces
  obtain ⟨Kshift, hKshift, Yshift, hshift⟩ :=
    exists_uniform_roughFixedHead_friableCount_shift_bound W
  let P : Real := roughHeadModulus W
  let r : Real := roughCanonicalPoolDickmanFloor
  have hr : 0 < r := by
    dsimp only [r]
    exact roughCanonicalPoolDickmanFloor_pos
  let A0 : Nat :=
    max (roughHeadModulus W)
      (max 2 ⌈192 * P / (roughHeadDensity W * r)⌉₊)
  let logThreshold : Real :=
    max (2 / r)
      (max (32 * C / r)
        (128 * P * Kshift / (roughHeadDensity W * r)))
  have hlogEvent : ∀ᶠ n : Nat in atTop,
      logThreshold <= Real.log (yNat n : Real) :=
    roughCanonical_log_yNat_tendsto_atTop.eventually
      (eventually_ge_atTop logThreshold)
  have hyEvent : ∀ᶠ n : Nat in atTop,
      max W (max YdeBruijn (max Yshift 2)) <= yNat n :=
    roughCanonical_yNat_tendsto_atTop.eventually
      (eventually_ge_atTop (max W (max YdeBruijn (max Yshift 2))))
  have hpowerEvent : ∀ᶠ n : Nat in atTop,
      max 12 (2 * (A0 + 1) : Real) <= (n : Real) ^ deltaStar :=
    (roughCanonical_rpow_tendsto_atTop hdelta).eventually
      (eventually_ge_atTop (max 12 (2 * (A0 + 1) : Real)))
  have htailEvent : ∀ᶠ n : Nat in atTop,
      ((2 * K * upperTailLength c n : Nat) : Real) / (n : Real) <=
        1 / 2 := by
    have hT : Tendsto
        (fun n : Nat => (2 * (K : Real)) *
          ((upperTailLength c n : Real) / (n : Real)))
        atTop (nhds 0) := by
      simpa only [mul_zero] using
        (upperTailLength_ratio_tendsto_zero hc).const_mul
          (2 * (K : Real))
    have hsmall := hT.eventually
      (eventually_lt_nhds (by norm_num : (0 : Real) < 1 / 2))
    filter_upwards [hsmall] with n hn
    have hn' :
        (2 * (K : Real)) *
            ((upperTailLength c n : Real) / (n : Real)) < 1 / 2 := hn
    calc
      ((2 * K * upperTailLength c n : Nat) : Real) / (n : Real) =
          (2 * (K : Real)) *
            ((upperTailLength c n : Real) / (n : Real)) := by
        push_cast
        ring
      _ <= 1 / 2 := hn'.le
  have hlogFace := FriableAsymptotic.eventually_one_fifth_L_le_log_yNat
  filter_upwards [eventually_gt_atTop 0, hlogEvent, hyEvent, hpowerEvent,
    htailEvent, hlogFace] with n hn hlog hy hpower htail hface
  intro label hlabelData hactive
  have hlabelPos : 0 < label := hlabelData.1
  have hlabelNeOne : label ≠ 1 := hactive.1
  have hlabelTwo : 2 <= label := by omega
  have hA0 : A0 <= n / label :=
    roughCanonical_activeLabel_div_scale_lower hn hlabelPos hactive.2
      (le_trans (le_max_right 12 _) hpower)
  have hlabelSmall : 6 * label <= n :=
    roughCanonical_activeLabel_three_mul_le_half hn hlabelPos hactive.2
      (le_trans (le_max_left 12 _) hpower)
  have htailNat : 4 * K * upperTailLength c n <= n := by
    have hnReal : (0 : Real) < n := by exact_mod_cast hn
    have hcross := (div_le_iff₀ hnReal).mp htail
    have hcast :
        ((2 * K * upperTailLength c n : Nat) : Real) <=
          (n : Real) / 2 := by
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using hcross
    have hcast' :
        ((4 * K * upperTailLength c n : Nat) : Real) <= (n : Real) := by
      push_cast at hcast ⊢
      linarith
    exact_mod_cast hcast'
  let A := n / label
  let B := (2 * n - K * upperTailLength c n) / label
  have htailNat' :
      4 * (K * upperTailLength c n) <= n := by
    simpa only [mul_assoc] using htailNat
  have hgeometry :
      2 * (K * upperTailLength c n) + 3 * label <= n := by
    omega
  have hKh : K * upperTailLength c n <= n := by omega
  have hAB : A <= B := by
    dsimp only [A, B]
    apply Nat.div_le_div_right
    omega
  have hBthree : B <= 3 * A := by
    have hBLe : B <= (2 * n) / label :=
      Nat.div_le_div_right (Nat.sub_le _ _)
    have htwoDiv : (2 * n) / label <= 2 * A + 1 := by
      dsimp only [A]
      rw [two_mul]
      rw [Nat.add_div hlabelPos]
      split_ifs <;> omega
    have hATwo : 2 <= A :=
      (le_max_left 2 _).trans ((le_max_right (roughHeadModulus W) _).trans hA0)
    omega
  have hlength : A <= 2 * (B - A) := by
    have hlohi : n <= 2 * n - K * upperTailLength c n := by omega
    have hfloor :
        |(((B - A : Nat) : Real)) -
            (((2 * n - K * upperTailLength c n - n : Nat) : Real)) /
              (label : Real)| < 1 := by
      simpa only [A, B] using
        (quotientIocLength_sub_realLengthDiv_abs_lt_one
          (D := label) (lo := n)
          (hi := 2 * n - K * upperTailLength c n) hlabelPos hlohi)
    have hsub :
        2 * n - K * upperTailLength c n - n =
          n - K * upperTailLength c n := by omega
    rw [hsub, Nat.cast_sub hKh] at hfloor
    have hAmulNat : A * label <= n := by
      simpa only [A] using Nat.div_mul_le_self n label
    have hAmulReal : (A : Real) * (label : Real) <= (n : Real) := by
      exact_mod_cast hAmulNat
    have hgeometryReal :
        2 * ((K * upperTailLength c n : Nat) : Real) +
            3 * (label : Real) <= (n : Real) := by
      exact_mod_cast hgeometry
    have hlabelReal : (0 : Real) < label := by exact_mod_cast hlabelPos
    have hgap :
        (A : Real) / 2 + 1 <=
          ((n : Real) - (K * upperTailLength c n : Nat)) /
            (label : Real) := by
      apply (le_div_iff₀ hlabelReal).2
      nlinarith [hAmulReal, hgeometryReal]
    have hlower := (abs_lt.mp hfloor).1
    have htwice :
        (A : Real) < 2 * ((B - A : Nat) : Real) := by
      nlinarith [hgap, hlower]
    have : A < 2 * (B - A) := by exact_mod_cast htwice
    omega
  have hmodA : roughHeadModulus W <= A := by
    exact (le_max_left _ _).trans hA0
  have hlogB : Real.log (B : Real) <=
      5 * Real.log (yNat n : Real) := by
    have hBLeN : B <= n := by
      calc
        B <= (2 * n) / label :=
          Nat.div_le_div_right (Nat.sub_le _ _)
        _ <= (2 * n) / 2 :=
          Nat.div_le_div_left (a := 2 * n) hlabelTwo (by norm_num)
        _ = n := by omega
    have hBPos : 0 < B := (by
      have : 0 < A := (roughHeadModulus_pos W).trans_le hmodA
      exact this.trans_le hAB)
    have hlogLe : Real.log (B : Real) <= L n := by
      unfold L
      exact Real.log_le_log (by exact_mod_cast hBPos)
        (by exact_mod_cast hBLeN)
    exact hlogLe.trans (by nlinarith [hface])
  have hlogY : 0 < Real.log (yNat n : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < yNat n by omega))
  have hlogMain :
      2 / Real.log (yNat n : Real) <= r := by
    have hthreshold : 2 / r <= Real.log (yNat n : Real) :=
      (le_max_left _ _).trans hlog
    exact (div_le_iff₀ hlogY).2 <| by
      simpa only [mul_comm] using (div_le_iff₀ hr).1 hthreshold
  have hlogSmooth :
      8 * C / Real.log (yNat n : Real) <= r / 4 := by
    have hthreshold : 32 * C / r <= Real.log (yNat n : Real) :=
      (le_max_left (32 * C / r)
        (128 * P * Kshift / (roughHeadDensity W * r))).trans
          ((le_max_right (2 / r) _).trans hlog)
    have hcross : 32 * C <=
        r * Real.log (yNat n : Real) := by
      simpa only [mul_comm] using (div_le_iff₀ hr).1 hthreshold
    have hleft : 32 * C / Real.log (yNat n : Real) <= r :=
      (div_le_iff₀ hlogY).2 hcross
    calc
      8 * C / Real.log (yNat n : Real) =
          (32 * C / Real.log (yNat n : Real)) / 4 := by ring
      _ <= r / 4 :=
        div_le_div_of_nonneg_right hleft (by norm_num)
  have hlogHead :
      4 * P * Kshift / Real.log (yNat n : Real) <=
        roughHeadDensity W * r / 32 := by
    have hthreshold :
        128 * P * Kshift / (roughHeadDensity W * r) <=
          Real.log (yNat n : Real) :=
      (le_max_right (32 * C / r) _).trans
        ((le_max_right (2 / r) _).trans hlog)
    have hdenom : 0 < roughHeadDensity W * r :=
      mul_pos (roughHeadDensity_pos W) hr
    have hnumerator : 128 * P * Kshift <=
        (roughHeadDensity W * r) * Real.log (yNat n : Real) := by
      simpa only [mul_comm] using (div_le_iff₀ hdenom).1 hthreshold
    have hcross :
        128 * P * Kshift / Real.log (yNat n : Real) <=
          roughHeadDensity W * r :=
      (div_le_iff₀ hlogY).2 hnumerator
    calc
      4 * P * Kshift / Real.log (yNat n : Real) =
          (128 * P * Kshift / Real.log (yNat n : Real)) / 32 := by ring
      _ <= (roughHeadDensity W * r) / 32 :=
        div_le_div_of_nonneg_right hcross (by norm_num)
  have hendpoint :
      6 * P <= roughHeadDensity W * r / 32 * (A : Real) := by
    have hceil :
        192 * P / (roughHeadDensity W * r) <=
          (⌈192 * P / (roughHeadDensity W * r)⌉₊ : Real) :=
      Nat.le_ceil _
    have hceilA :
        (⌈192 * P / (roughHeadDensity W * r)⌉₊ : Nat) <= A :=
      (le_max_right 2 _).trans ((le_max_right (roughHeadModulus W) _).trans hA0)
    have hcastA :
        192 * P / (roughHeadDensity W * r) <= (A : Real) :=
      hceil.trans (by exact_mod_cast hceilA)
    have hdenom : 0 < roughHeadDensity W * r :=
      mul_pos (roughHeadDensity_pos W) hr
    have hcross :
        192 * P <= (A : Real) * (roughHeadDensity W * r) :=
      (div_le_iff₀ hdenom).1 hcastA
    calc
      6 * P = (192 * P) / 32 := by ring
      _ <= ((A : Real) * (roughHeadDensity W * r)) / 32 :=
        div_le_div_of_nonneg_right hcross (by norm_num)
      _ = roughHeadDensity W * r / 32 * (A : Real) := by ring
  have hlower := roughCanonical_headFreeSmoothInterval_card_lower
    hC hKshift hdeBruijn hshift
    ((le_max_left YdeBruijn (max Yshift 2)).trans
      ((le_max_right W _).trans hy))
    ((le_max_left Yshift 2).trans
      ((le_max_right YdeBruijn _).trans ((le_max_right W _).trans hy)))
    ((le_max_left W _).trans hy)
    ((le_max_right Yshift 2).trans
      ((le_max_right YdeBruijn _).trans ((le_max_right W _).trans hy)))
    hmodA hAB hBthree hlength hlogB
    (by simpa only [r] using hlogMain)
    (by simpa only [r] using hlogSmooth)
    (by simpa only [P, r] using hlogHead)
    (by simpa only [P, r] using hendpoint)
  rw [roughCanonicalBroadCorrectionPool_card_eq_headFreeSmoothInterval_of_isCompleteRoughLabel
      hlabelData ((le_max_left W _).trans hy)]
  simpa only [roughCanonicalRawBroadPoolDensity, A, B]
    using hlower

/-- Intrinsic version of the raw broad surplus.  It is stated for every
complete-rough label, before asking whether that label is already attained
by any lower candidate set. -/
def RoughCanonicalActiveIntrinsicRawBroadSurplus
    (W n h K budget poolMinimum : Nat) (deltaStar : Real) : Prop :=
  forall label, IsCompleteRoughLabel (yNat n) label ->
    RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
      max poolMinimum
          (roughUpperCompleteRoughRowTarget n h (yNat n) label) + budget <=
        (roughCanonicalBroadCorrectionPool W n h K (yNat n) label).card

/-- Eventually, every intrinsic active row has enough raw broad coordinates
for its full upper-row target, any prescribed fixed correction-pool
minimum, and the literal three-coordinate guard budget. -/
theorem eventually_roughCanonicalActiveIntrinsicRawBroadSurplus
    (W K poolMinimum : Nat) {c deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop,
      RoughCanonicalActiveIntrinsicRawBroadSurplus W n
        (upperTailLength c n) K 3 poolMinimum deltaStar := by
  have hlinear :=
    eventually_roughCanonical_activeRawBroadPool_linear_lower
      W K hc hdelta
  let density := roughCanonicalRawBroadPoolDensity W
  have hdensity : 0 < density := by
    dsimp only [density]
    exact roughCanonicalRawBroadPoolDensity_pos W
  have htailSmall : ∀ᶠ n : Nat in atTop,
      (upperTailLength c n : Real) / (n : Real) <= density / 4 := by
    have hT := upperTailLength_ratio_tendsto_zero hc
    have hsmall := hT.eventually
      (eventually_lt_nhds (div_pos hdensity (by norm_num : (0 : Real) < 4)))
    filter_upwards [hsmall] with n hn
    exact hn.le
  let constantTarget : Nat := max 4 (poolMinimum + 3)
  let A0 : Nat := max 1 ⌈(2 * (constantTarget : Real)) / density⌉₊
  have hpowerEvent : ∀ᶠ n : Nat in atTop,
      (2 * (A0 + 1) : Real) <= (n : Real) ^ deltaStar :=
    (roughCanonical_rpow_tendsto_atTop hdelta).eventually
      (eventually_ge_atTop (2 * (A0 + 1) : Real))
  filter_upwards [eventually_gt_atTop 0, hlinear, htailSmall, hpowerEvent]
    with n hn hlinearN htail hpower
  unfold RoughCanonicalActiveIntrinsicRawBroadSurplus
  intro label hlabelData hactive
  have hlabelPos : 0 < label := hlabelData.1
  let A := n / label
  have hA0 : A0 <= A :=
    roughCanonical_activeLabel_div_scale_lower hn hlabelPos hactive.2 hpower
  have hAOne : 1 <= A := (le_max_left 1 _).trans hA0
  have hlinearRow : density * (A : Real) <=
      (roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
        (yNat n) label).card := by
    simpa only [density, A] using
      hlinearN label hlabelData hactive
  have htarget :
      roughUpperCompleteRoughRowTarget n (upperTailLength c n)
          (yNat n) label <= upperTailLength c n / label + 1 := by
    exact roughUpperCompleteRoughRowTarget_le_div_add_one
      hlabelData
  have hnReal : (0 : Real) < n := by exact_mod_cast hn
  have hlabelReal : (0 : Real) < label := by exact_mod_cast hlabelPos
  have hARealUpper : (n : Real) / (label : Real) < (A : Real) + 1 := by
    apply (div_lt_iff₀ hlabelReal).2
    have hnat := (Nat.div_lt_iff_lt_mul hlabelPos).mp
      (Nat.lt_succ_self A)
    exact_mod_cast hnat
  have htailDiv :
      (upperTailLength c n : Real) / (label : Real) <=
        density / 4 * ((A : Real) + 1) := by
    calc
      (upperTailLength c n : Real) / (label : Real) =
          ((upperTailLength c n : Real) / (n : Real)) *
            ((n : Real) / (label : Real)) := by
        field_simp [hnReal.ne', hlabelReal.ne']
      _ <= density / 4 * ((n : Real) / (label : Real)) := by
        exact mul_le_mul_of_nonneg_right htail
          (div_nonneg hnReal.le hlabelReal.le)
      _ <= density / 4 * ((A : Real) + 1) := by
        exact mul_le_mul_of_nonneg_left hARealUpper.le
          (div_nonneg hdensity.le (by norm_num))
  have htailDiv' :
      ((upperTailLength c n / label : Nat) : Real) <=
        density / 2 * (A : Real) := by
    have hcastDiv :
        ((upperTailLength c n / label : Nat) : Real) <=
          (upperTailLength c n : Real) / (label : Real) := Nat.cast_div_le
    have hAOneReal : (1 : Real) <= A := by exact_mod_cast hAOne
    calc
      ((upperTailLength c n / label : Nat) : Real) <=
          (upperTailLength c n : Real) / (label : Real) := hcastDiv
      _ <= density / 4 * ((A : Real) + 1) := htailDiv
      _ <= density / 4 * (2 * (A : Real)) := by
        apply mul_le_mul_of_nonneg_left (by linarith)
        exact div_nonneg hdensity.le (by norm_num)
      _ = density / 2 * (A : Real) := by ring
  have hconstant : (constantTarget : Real) <=
      density / 2 * (A : Real) := by
    have hceil : (2 * (constantTarget : Real)) / density <=
        (⌈(2 * (constantTarget : Real)) / density⌉₊ : Real) :=
      Nat.le_ceil _
    have hceilA :
        (⌈(2 * (constantTarget : Real)) / density⌉₊ : Nat) <= A :=
      (le_max_right 1 _).trans hA0
    have hA : (2 * (constantTarget : Real)) / density <= (A : Real) :=
      hceil.trans (by exact_mod_cast hceilA)
    have := (div_le_iff₀ hdensity).1 hA
    nlinarith
  have hfourTargetNat : 4 <= constantTarget := by
    exact le_max_left 4 (poolMinimum + 3)
  have hminimumTargetNat : poolMinimum + 3 <= constantTarget := by
    exact le_max_right 4 (poolMinimum + 3)
  have hfourTargetCast : (4 : Real) <= (constantTarget : Real) := by
    exact_mod_cast hfourTargetNat
  have hminimumTargetCast : ((poolMinimum + 3 : Nat) : Real) <=
      (constantTarget : Real) := by
    exact_mod_cast hminimumTargetNat
  have hfour : (4 : Real) <= density / 2 * (A : Real) :=
    hfourTargetCast.trans hconstant
  have hminimumConstant : ((poolMinimum + 3 : Nat) : Real) <=
      density / 2 * (A : Real) :=
    hminimumTargetCast.trans hconstant
  have htargetPool :
      roughUpperCompleteRoughRowTarget n (upperTailLength c n)
          (yNat n) label + 3 <=
        (roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
          (yNat n) label).card := by
    have htargetReal :
        (roughUpperCompleteRoughRowTarget n (upperTailLength c n)
            (yNat n) label + 3 : Nat) <=
          density * (A : Real) := by
      push_cast
      have htargetCast :
          (roughUpperCompleteRoughRowTarget n (upperTailLength c n)
              (yNat n) label : Real) <=
            ((upperTailLength c n / label : Nat) : Real) + 1 := by
        exact_mod_cast htarget
      linarith [hfour]
    exact_mod_cast htargetReal.trans hlinearRow
  have hminimumPool : poolMinimum + 3 <=
      (roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
        (yNat n) label).card := by
    have hreal : ((poolMinimum + 3 : Nat) : Real) <=
        (roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
          (yNat n) label).card := by
      have hhalf : density / 2 * (A : Real) <= density * (A : Real) := by
        have hAReal : (0 : Real) <= A := Nat.cast_nonneg A
        exact mul_le_mul_of_nonneg_right (by linarith) hAReal
      exact hminimumConstant.trans (hhalf.trans hlinearRow)
    exact_mod_cast hreal
  by_cases hminimumLeTarget : poolMinimum <=
      roughUpperCompleteRoughRowTarget n (upperTailLength c n)
        (yNat n) label
  · rw [max_eq_right hminimumLeTarget]
    exact htargetPool
  · rw [max_eq_left (le_of_not_ge hminimumLeTarget)]
    exact hminimumPool

/-- The original guarded-candidate surplus is an immediate projection of
the intrinsic theorem. -/
theorem BankPaperRealization.eventually_roughCanonicalActiveRawBroadSurplus
    (W K poolMinimum : Nat) {c deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop,
      forall (depth : Nat) (left right : Nat -> Nat)
        (changed : Finset Nat),
      forall (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          left right changed),
        RoughCanonicalActiveRawBroadSurplus R certificate deltaStar
          W K 3 poolMinimum := by
  filter_upwards [eventually_roughCanonicalActiveIntrinsicRawBroadSurplus
    W K poolMinimum hc hdelta] with n hsurplus
  intro depth left right changed R certificate
  unfold RoughCanonicalActiveRawBroadSurplus
  intro label hlabelMem hactive
  have hlabelData : IsCompleteRoughLabel (yNat n) label :=
    isCompleteRoughLabel_of_canonicalCompleteRoughRow
      (⟨label, hlabelMem⟩ :
        CanonicalCompleteRoughRow (yNat n)
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K))
  exact hsurplus label hlabelData hactive

/-- The intrinsic surplus and the literal three-coordinate guard census give
guarded-row capacity before candidate-label attainment is known.  This is
the noncircular coverage input needed when all upper rows are summed. -/
theorem BankPaperRealization.eventually_roughCanonical_active_intrinsic_guard_capacity_inputs
    (W K poolMinimum : Nat) {c deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop,
      forall (depth : Nat) (left right : Nat -> Nat)
        (changed : Finset Nat),
      forall (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          left right changed),
      centralAnchorCutoffThreshold depth <= n ->
      yNat n < centralAnchorCutoff depth n ->
      forall label, IsCompleteRoughLabel (yNat n) label ->
        RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
          RoughCanonicalGuardLocalCensusBound R certificate deltaStar K
              label 3 ∧
            RoughCanonicalGuardedBroadPoolCapacity R certificate deltaStar
              W K label poolMinimum ∧
            RoughCanonicalPostchargeRowCapacity R certificate deltaStar K
              label := by
  filter_upwards [eventually_roughCanonicalActiveIntrinsicRawBroadSurplus
    W K poolMinimum hc hdelta] with n hsurplus
  intro depth left right changed R certificate hnCutoff hyCutoff
    label hlabel hactive
  have hcensus : RoughCanonicalGuardLocalCensusBound R certificate
      deltaStar K label 3 :=
    R.roughCanonicalGuardLocalCensusBound_three_of_active certificate
      deltaStar K label hnCutoff hyCutoff hactive
  have hbroad : RoughCanonicalGuardedBroadPoolCapacity R certificate
      deltaStar W K label poolMinimum := by
    apply R.roughCanonicalGuardedBroadPoolCapacity_of_raw_surplus certificate
      deltaStar W K label poolMinimum 3 hcensus
    exact le_trans
      (Nat.add_le_add_right (Nat.le_max_left _ _) 3)
      (hsurplus label hlabel hactive)
  have hpostcharge : RoughCanonicalPostchargeRowCapacity R certificate
      deltaStar K label := by
    let minimum := max poolMinimum
      (roughUpperCompleteRoughRowTarget n (upperTailLength c n)
        (yNat n) label)
    have hcapacity : RoughCanonicalGuardedBroadPoolCapacity R certificate
        deltaStar W K label minimum := by
      apply R.roughCanonicalGuardedBroadPoolCapacity_of_raw_surplus
        certificate deltaStar W K label minimum 3 hcensus
      exact hsurplus label hlabel hactive
    apply R.roughCanonicalPostchargeRowCapacity_of_guardedBroadPoolCapacity
      certificate deltaStar W K label minimum
    · exact Nat.le_max_right _ _
    · exact hcapacity
  exact ⟨hcensus, hbroad, hpostcharge⟩

/-- Combining the assumption-free raw surplus with the finite guard census
closes all three active-row capacity inputs with budget `3` and any fixed
pool minimum. -/
theorem BankPaperRealization.eventually_roughCanonical_active_guard_capacity_inputs
    (W K poolMinimum : Nat) {c deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop,
      forall (depth : Nat) (left right : Nat -> Nat)
        (changed : Finset Nat),
      forall (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          left right changed),
      centralAnchorCutoffThreshold depth <= n ->
      yNat n < centralAnchorCutoff depth n ->
      (∀ label ∈ completeRoughLabelSet (yNat n)
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
        RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
          RoughCanonicalGuardLocalCensusBound R certificate deltaStar K
            label 3) ∧
      (∀ label ∈ completeRoughLabelSet (yNat n)
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
        RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
          RoughCanonicalGuardedBroadPoolCapacity R certificate deltaStar
            W K label poolMinimum) ∧
      (∀ label ∈ completeRoughLabelSet (yNat n)
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
        RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
          RoughCanonicalPostchargeRowCapacity R certificate deltaStar K
            label) := by
  filter_upwards [BankPaperRealization.eventually_roughCanonicalActiveRawBroadSurplus
    W K poolMinimum hc hdelta] with n hsurplus
  intro depth left right changed R certificate hnCutoff hyCutoff
  exact R.roughCanonical_active_guard_capacity_inputs_of_rawBroadSurplus
    certificate deltaStar W K poolMinimum hnCutoff hyCutoff
      (hsurplus depth left right changed R certificate)

end

end Erdos390.WholePaper
