import Erdos390.WholePaper.RoughSaiasSharpCorrectionTarget
import Erdos390.WholePaper.RoughSaiasCanonicalRowBridge

/-!
# Sharp fixed-head interval shifts

The endpointwise fixed-head estimate loses one logarithm because it takes
absolute values before subtracting the two endpoints of an interval.  This
file retains that subtraction.  The Dickman main terms are first compared
at the interval level; the two residual increments are then bounded by the
already-proved sharp Saias endpoint approximation.

No new analytic predicate is introduced.  In particular, the only
approximation used below is
`roughSaiasSharpEndpointApproximationUpToFive`.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## The interval-level Dickman cancellation -/

/-- The continuous translation defect before the natural quotient is
floored.  At a single endpoint it has size `X log(d)/(d log(y))`; its
difference on an interval has size proportional only to the interval
length. -/
noncomputable def roughFriableContinuousFixedDivisorDefect
    (X y d : ℕ) : ℝ :=
  (X : ℝ) / (d : ℝ) *
    (rho (FriableAsymptotic.dickmanU X y -
        Real.log (d : ℝ) / Real.log (y : ℝ)) -
      rho (FriableAsymptotic.dickmanU X y))

/-- Flooring `X/d` costs at most three in the translated continuous
Dickman main term.  This is the floor part of
`roughFriableMain_fixedDivisorShift`, recorded separately so that the
translation defects at two endpoints can be subtracted before taking
absolute values. -/
theorem roughFriableMain_quotientFloor_stability
    {X y d : ℕ}
    (hy : 2 ≤ y) (hd : 0 < d) (hdX : d ≤ X)
    (hlogX : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |roughFriableDickmanMain (X / d) y -
        (X : ℝ) / (d : ℝ) *
          rho (FriableAsymptotic.dickmanU X y -
            Real.log (d : ℝ) / Real.log (y : ℝ))| ≤ 3 := by
  have hX : 0 < X := hd.trans_le hdX
  have hA : 1 ≤ X / d := by
    apply (Nat.le_div_iff_mul_le hd).2
    simpa using hdX
  have hdReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hXReal : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hyReal : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  let r : ℝ := (X : ℝ) / (d : ℝ)
  have hAr : ((X / d : ℕ) : ℝ) ≤ r := by
    dsimp [r]
    exact Nat.cast_div_le
  have hupperNat : X < (X / d + 1) * d :=
    (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (X / d))
  have hrA : r < ((X / d : ℕ) : ℝ) + 1 := by
    dsimp [r]
    apply (div_lt_iff₀ hdReal).2
    exact_mod_cast hupperNat
  have hlogr :
      Real.log r = Real.log (X : ℝ) - Real.log (d : ℝ) := by
    dsimp [r]
    rw [Real.log_div hXReal.ne' hdReal.ne']
  have hlogd : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ d by omega))
  have hlogrLe : Real.log r ≤ Real.log (X : ℝ) := by
    rw [hlogr]
    linarith
  have hr5 : Real.log r / Real.log (y : ℝ) ≤ 5 := by
    apply (div_le_iff₀ hlogY).2
    exact hlogrLe.trans hlogX
  have hfloor := roughRhoFloorKernel_stability (X / d)
    hA hAr hrA hyReal hr5
  have hcoordinate :
      Real.log r / Real.log (y : ℝ) =
        FriableAsymptotic.dickmanU X y -
          Real.log (d : ℝ) / Real.log (y : ℝ) := by
    rw [hlogr]
    simp only [FriableAsymptotic.dickmanU]
    ring
  simpa only [roughFriableDickmanMain,
    FriableAsymptotic.dickmanU, hcoordinate, r] using hfloor

/-- The continuous fixed-divisor translation defects cancel on an
interval.  The term `log d` is the genuine fixed translation; the extra
`2` comes from comparing the two Dickman increments. -/
theorem roughFriableContinuousFixedDivisorDefect_sub_abs_le
    {A B y d : ℕ}
    (hy : 2 ≤ y) (hd : 0 < d) (hdA : d ≤ A) (hAB : A ≤ B)
    (hlogB : Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |roughFriableContinuousFixedDivisorDefect B y d -
        roughFriableContinuousFixedDivisorDefect A y d| ≤
      ((B - A : ℕ) : ℝ) *
        (Real.log (d : ℝ) + 2) /
          ((d : ℝ) * Real.log (y : ℝ)) := by
  have hA : 0 < A := hd.trans_le hdA
  have hB : 0 < B := hA.trans_le hAB
  have hAReal : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hBReal : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hdReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogd : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ d by omega))
  let uA : ℝ := FriableAsymptotic.dickmanU A y
  let uB : ℝ := FriableAsymptotic.dickmanU B y
  let t : ℝ := Real.log (d : ℝ) / Real.log (y : ℝ)
  have ht : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg hlogd hlogY.le
  have hlogAB : Real.log (A : ℝ) ≤ Real.log (B : ℝ) :=
    Real.log_le_log hAReal (by exact_mod_cast hAB)
  have huAB : uA ≤ uB := by
    dsimp [uA, uB, FriableAsymptotic.dickmanU]
    exact div_le_div_of_nonneg_right hlogAB hlogY.le
  have huB5 : uB ≤ 5 := by
    dsimp [uB, FriableAsymptotic.dickmanU]
    exact (div_le_iff₀ hlogY).2 hlogB
  have hshiftAB : uA - t ≤ uB - t := sub_le_sub_right huAB t
  have hshiftB5 : uB - t ≤ 5 :=
    (sub_le_self uB ht).trans huB5
  have hgB :
      |rho (uB - t) - rho uB| ≤ t := by
    rw [abs_sub_comm]
    calc
      |rho uB - rho (uB - t)| ≤ uB - (uB - t) :=
        FriableAsymptotic.rho_lipschitz_of_le_five
          (sub_le_self uB ht) huB5
      _ = t := by ring
  have hshiftRho :
      |rho (uB - t) - rho (uA - t)| ≤ uB - uA := by
    calc
      |rho (uB - t) - rho (uA - t)| ≤
          (uB - t) - (uA - t) :=
        FriableAsymptotic.rho_lipschitz_of_le_five
          hshiftAB hshiftB5
      _ = uB - uA := by ring
  have hunshiftRho :
      |rho uB - rho uA| ≤ uB - uA :=
    FriableAsymptotic.rho_lipschitz_of_le_five huAB huB5
  have hgDiff :
      |(rho (uB - t) - rho uB) -
          (rho (uA - t) - rho uA)| ≤
        2 * (uB - uA) := by
    calc
      |(rho (uB - t) - rho uB) -
          (rho (uA - t) - rho uA)| =
        |(rho (uB - t) - rho (uA - t)) -
          (rho uB - rho uA)| := by
            congr 1
            ring
      _ ≤ |rho (uB - t) - rho (uA - t)| +
          |rho uB - rho uA| := abs_sub _ _
      _ ≤ (uB - uA) + (uB - uA) :=
        add_le_add hshiftRho hunshiftRho
      _ = 2 * (uB - uA) := by ring
  have hlogQuotient :
      Real.log (B : ℝ) - Real.log (A : ℝ) ≤
        (B : ℝ) / (A : ℝ) - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hBReal hAReal)
    rw [Real.log_div hBReal.ne' hAReal.ne'] at h
    exact h
  have hscaledLog :
      (A : ℝ) *
          (Real.log (B : ℝ) - Real.log (A : ℝ)) ≤
        (B : ℝ) - (A : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlogQuotient hAReal.le
    calc
      (A : ℝ) *
          (Real.log (B : ℝ) - Real.log (A : ℝ)) ≤
        (A : ℝ) * ((B : ℝ) / (A : ℝ) - 1) := h
      _ = (B : ℝ) - (A : ℝ) := by field_simp
  have hAuDiff :
      (A : ℝ) * (uB - uA) ≤
        ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) := by
    calc
      (A : ℝ) * (uB - uA) =
          (A : ℝ) *
            (Real.log (B : ℝ) - Real.log (A : ℝ)) /
              Real.log (y : ℝ) := by
                dsimp [uA, uB, FriableAsymptotic.dickmanU]
                ring
      _ ≤ ((B : ℝ) - (A : ℝ)) / Real.log (y : ℝ) :=
        div_le_div_of_nonneg_right hscaledLog hlogY.le
      _ = ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) := by
        rw [Nat.cast_sub hAB]
  have hgapNonneg : 0 ≤ ((B - A : ℕ) : ℝ) / (d : ℝ) := by
    positivity
  have hfirst :
      |(((B - A : ℕ) : ℝ) / (d : ℝ)) *
          (rho (uB - t) - rho uB)| ≤
        (((B - A : ℕ) : ℝ) / (d : ℝ)) * t := by
    rw [abs_mul, abs_of_nonneg hgapNonneg]
    exact mul_le_mul_of_nonneg_left hgB hgapNonneg
  have hsecond :
      |((A : ℝ) / (d : ℝ)) *
          ((rho (uB - t) - rho uB) -
            (rho (uA - t) - rho uA))| ≤
        2 * ((B - A : ℕ) : ℝ) /
          ((d : ℝ) * Real.log (y : ℝ)) := by
    rw [abs_mul, abs_of_pos (div_pos hAReal hdReal)]
    calc
      (A : ℝ) / (d : ℝ) *
          |(rho (uB - t) - rho uB) -
            (rho (uA - t) - rho uA)| ≤
        (A : ℝ) / (d : ℝ) * (2 * (uB - uA)) :=
          mul_le_mul_of_nonneg_left hgDiff
            (div_nonneg hAReal.le hdReal.le)
      _ = (2 / (d : ℝ)) * ((A : ℝ) * (uB - uA)) := by ring
      _ ≤ (2 / (d : ℝ)) *
          (((B - A : ℕ) : ℝ) / Real.log (y : ℝ)) :=
        mul_le_mul_of_nonneg_left hAuDiff (by positivity)
      _ = 2 * ((B - A : ℕ) : ℝ) /
          ((d : ℝ) * Real.log (y : ℝ)) := by ring
  change
    |(B : ℝ) / (d : ℝ) * (rho (uB - t) - rho uB) -
        (A : ℝ) / (d : ℝ) * (rho (uA - t) - rho uA)| ≤ _
  calc
    |(B : ℝ) / (d : ℝ) * (rho (uB - t) - rho uB) -
        (A : ℝ) / (d : ℝ) * (rho (uA - t) - rho uA)| =
      |(((B - A : ℕ) : ℝ) / (d : ℝ)) *
          (rho (uB - t) - rho uB) +
        ((A : ℝ) / (d : ℝ)) *
          ((rho (uB - t) - rho uB) -
            (rho (uA - t) - rho uA))| := by
              rw [Nat.cast_sub hAB]
              congr 1
              ring
    _ ≤
        |(((B - A : ℕ) : ℝ) / (d : ℝ)) *
          (rho (uB - t) - rho uB)| +
        |((A : ℝ) / (d : ℝ)) *
          ((rho (uB - t) - rho uB) -
            (rho (uA - t) - rho uA))| := abs_add_le _ _
    _ ≤ (((B - A : ℕ) : ℝ) / (d : ℝ)) * t +
        2 * ((B - A : ℕ) : ℝ) /
          ((d : ℝ) * Real.log (y : ℝ)) :=
      add_le_add hfirst hsecond
    _ = ((B - A : ℕ) : ℝ) *
        (Real.log (d : ℝ) + 2) /
          ((d : ℝ) * Real.log (y : ℝ)) := by
      dsimp [t]
      ring

/-- After the two quotient floors are restored, the interval Dickman shift
has the desired length-over-log scale, plus the two absolute floor
constants. -/
theorem roughFriableDickmanMain_interval_fixedDivisorShift_abs_le
    {A B y d : ℕ}
    (hy : 2 ≤ y) (hd : 0 < d) (hdA : d ≤ A) (hAB : A ≤ B)
    (hlogB : Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |(roughFriableDickmanMain (B / d) y -
          roughFriableDickmanMain (A / d) y) -
        (roughFriableDickmanMain B y -
          roughFriableDickmanMain A y) / (d : ℝ)| ≤
      6 + ((B - A : ℕ) : ℝ) *
        (Real.log (d : ℝ) + 2) /
          ((d : ℝ) * Real.log (y : ℝ)) := by
  have hdB : d ≤ B := hdA.trans hAB
  let floorError : ℕ → ℝ := fun X ↦
    roughFriableDickmanMain (X / d) y -
      (X : ℝ) / (d : ℝ) *
        rho (FriableAsymptotic.dickmanU X y -
          Real.log (d : ℝ) / Real.log (y : ℝ))
  have hfloorA : |floorError A| ≤ 3 := by
    simpa only [floorError] using
      roughFriableMain_quotientFloor_stability hy hd hdA
        (by
          have hA : 0 < A := hd.trans_le hdA
          have hlogAB : Real.log (A : ℝ) ≤ Real.log (B : ℝ) :=
            Real.log_le_log (by exact_mod_cast hA)
              (by exact_mod_cast hAB)
          exact hlogAB.trans hlogB)
  have hfloorB : |floorError B| ≤ 3 := by
    simpa only [floorError] using
      roughFriableMain_quotientFloor_stability hy hd hdB hlogB
  have hcontinuous :=
    roughFriableContinuousFixedDivisorDefect_sub_abs_le
      hy hd hdA hAB hlogB
  have hrearrange :
      (roughFriableDickmanMain (B / d) y -
          roughFriableDickmanMain (A / d) y) -
        (roughFriableDickmanMain B y -
          roughFriableDickmanMain A y) / (d : ℝ) =
      (floorError B - floorError A) +
        (roughFriableContinuousFixedDivisorDefect B y d -
          roughFriableContinuousFixedDivisorDefect A y d) := by
    dsimp [floorError, roughFriableContinuousFixedDivisorDefect,
      roughFriableDickmanMain]
    ring
  rw [hrearrange]
  calc
    |(floorError B - floorError A) +
        (roughFriableContinuousFixedDivisorDefect B y d -
          roughFriableContinuousFixedDivisorDefect A y d)| ≤
      (|floorError B| + |floorError A|) +
        |roughFriableContinuousFixedDivisorDefect B y d -
          roughFriableContinuousFixedDivisorDefect A y d| := by
            calc
              _ ≤ |floorError B - floorError A| +
                  |roughFriableContinuousFixedDivisorDefect B y d -
                    roughFriableContinuousFixedDivisorDefect A y d| :=
                abs_add_le _ _
              _ ≤ (|floorError B| + |floorError A|) +
                  |roughFriableContinuousFixedDivisorDefect B y d -
                    roughFriableContinuousFixedDivisorDefect A y d| :=
                add_le_add (abs_sub _ _) le_rfl
    _ ≤ (3 + 3) +
        ((B - A : ℕ) : ℝ) *
          (Real.log (d : ℝ) + 2) /
            ((d : ℝ) * Real.log (y : ℝ)) :=
      add_le_add (add_le_add hfloorB hfloorA) hcontinuous
    _ = 6 + ((B - A : ℕ) : ℝ) *
        (Real.log (d : ℝ) + 2) /
          ((d : ℝ) * Real.log (y : ℝ)) := by ring

/-! ## Adding the two residual increments -/

/-- Exact budget for an interval fixed-divisor shift.  The first term is
the interval Dickman cancellation above.  The second is the residual
increment on the divided interval, and the third is `1/d` times the
residual increment on the original interval. -/
noncomputable def roughSaiasIntervalFixedDivisorShiftBudget
    (eta : ℕ → ℝ) (A B y d : ℕ) : ℝ :=
  6 + ((B - A : ℕ) : ℝ) *
      (Real.log (d : ℝ) + 2) /
        ((d : ℝ) * Real.log (y : ℝ)) +
    roughSaiasPairTransitionBudget eta (A / d) (B / d) y +
    roughSaiasPairTransitionBudget eta A B y / (d : ℝ)

/-- A Saias endpoint approximation controls the genuine friable interval
shift at the cancellation-preserving scale.  This theorem does not take
absolute values of four endpoint shifts: it takes absolute values only
after forming the divided and undivided residual increments. -/
theorem roughFriableInterval_fixedDivisorShift_abs_le_of_saiasEndpointApproximation
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ A B y d : ℕ}
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy : 2 ≤ y)
    (hd : 0 < d) (hdA : d ≤ A) (hAB : A ≤ B)
    (hlogB : Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |((FriableAsymptotic.friableCount (B / d) y : ℝ) -
          (FriableAsymptotic.friableCount (A / d) y : ℝ)) -
        ((FriableAsymptotic.friableCount B y : ℝ) -
          (FriableAsymptotic.friableCount A y : ℝ)) / (d : ℝ)| ≤
      roughSaiasIntervalFixedDivisorShiftBudget eta A B y d := by
  have hA : 0 < A := hd.trans_le hdA
  have hB : 0 < B := hA.trans_le hAB
  have hdB : d ≤ B := hdA.trans hAB
  have hqA : 0 < A / d := Nat.div_pos hdA hd
  have hqB : 0 < B / d := Nat.div_pos hdB hd
  have hqAB : A / d ≤ B / d := Nat.div_le_div_right hAB
  have hqBlog :
      Real.log ((B / d : ℕ) : ℝ) ≤
        5 * Real.log (y : ℝ) := by
    have hmono :
        Real.log ((B / d : ℕ) : ℝ) ≤ Real.log (B : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast hqB
      · exact_mod_cast Nat.div_le_self B d
    exact hmono.trans hlogB
  have hmain :=
    roughFriableDickmanMain_interval_fixedDivisorShift_abs_le
      hy hd hdA hAB hlogB
  have hsmall :=
    roughFriableResidual_difference_abs_le_of_saiasEndpointApproximation
      hBV happrox hY hy hqA hqAB hqBlog
  have hlarge :=
    roughFriableResidual_difference_abs_le_of_saiasEndpointApproximation
      hBV happrox hY hy hA hAB hlogB
  have hdReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlarge' :
      |(roughFriableResidual B y - roughFriableResidual A y) /
          (d : ℝ)| ≤
        roughSaiasPairTransitionBudget eta A B y / (d : ℝ) := by
    rw [abs_div, abs_of_pos hdReal]
    exact (div_le_div_iff_of_pos_right hdReal).2 hlarge
  have hrearrange :
      ((FriableAsymptotic.friableCount (B / d) y : ℝ) -
          (FriableAsymptotic.friableCount (A / d) y : ℝ)) -
        ((FriableAsymptotic.friableCount B y : ℝ) -
          (FriableAsymptotic.friableCount A y : ℝ)) / (d : ℝ) =
      ((roughFriableDickmanMain (B / d) y -
          roughFriableDickmanMain (A / d) y) -
        (roughFriableDickmanMain B y -
          roughFriableDickmanMain A y) / (d : ℝ)) +
      (roughFriableResidual (B / d) y -
        roughFriableResidual (A / d) y) -
      (roughFriableResidual B y -
        roughFriableResidual A y) / (d : ℝ) := by
    rw [roughFriableCount_eq_main_add_residual (B / d) y,
      roughFriableCount_eq_main_add_residual (A / d) y,
      roughFriableCount_eq_main_add_residual B y,
      roughFriableCount_eq_main_add_residual A y]
    ring
  rw [hrearrange]
  calc
    |((roughFriableDickmanMain (B / d) y -
          roughFriableDickmanMain (A / d) y) -
        (roughFriableDickmanMain B y -
          roughFriableDickmanMain A y) / (d : ℝ)) +
      (roughFriableResidual (B / d) y -
        roughFriableResidual (A / d) y) -
      (roughFriableResidual B y -
        roughFriableResidual A y) / (d : ℝ)| ≤
      |(roughFriableDickmanMain (B / d) y -
          roughFriableDickmanMain (A / d) y) -
        (roughFriableDickmanMain B y -
          roughFriableDickmanMain A y) / (d : ℝ)| +
      |roughFriableResidual (B / d) y -
        roughFriableResidual (A / d) y| +
      |(roughFriableResidual B y -
        roughFriableResidual A y) / (d : ℝ)| := by
          calc
            _ ≤
              |((roughFriableDickmanMain (B / d) y -
                    roughFriableDickmanMain (A / d) y) -
                  (roughFriableDickmanMain B y -
                    roughFriableDickmanMain A y) / (d : ℝ)) +
                (roughFriableResidual (B / d) y -
                  roughFriableResidual (A / d) y)| +
              |(roughFriableResidual B y -
                roughFriableResidual A y) / (d : ℝ)| :=
              abs_sub _ _
            _ ≤
              (|(roughFriableDickmanMain (B / d) y -
                    roughFriableDickmanMain (A / d) y) -
                  (roughFriableDickmanMain B y -
                    roughFriableDickmanMain A y) / (d : ℝ)| +
                |roughFriableResidual (B / d) y -
                  roughFriableResidual (A / d) y|) +
              |(roughFriableResidual B y -
                roughFriableResidual A y) / (d : ℝ)| :=
              add_le_add (abs_add_le _ _) le_rfl
            _ = _ := by ring
    _ ≤
      (6 + ((B - A : ℕ) : ℝ) *
          (Real.log (d : ℝ) + 2) /
            ((d : ℝ) * Real.log (y : ℝ))) +
      roughSaiasPairTransitionBudget eta (A / d) (B / d) y +
      roughSaiasPairTransitionBudget eta A B y / (d : ℝ) :=
        add_le_add (add_le_add hmain hsmall) hlarge'
    _ = roughSaiasIntervalFixedDivisorShiftBudget eta A B y d := by
      rfl

/-! ## The closed inverse-log-square specialization -/

/-- A convenient explicit upper budget after substituting the closed sharp
endpoint rate.  Its four summands are respectively the quotient-floor
constant, the quotient-length floor constant, the main interval
translation, and the two sharp endpoint envelopes. -/
noncomputable def roughSaiasSharpIntervalFixedDivisorBudget
    (A B y d : ℕ) : ℝ :=
  6 + 5 / Real.log (y : ℝ) +
    ((B - A : ℕ) : ℝ) *
      (Real.log (d : ℝ) + 12) /
        ((d : ℝ) * Real.log (y : ℝ)) +
    20 * roughSaiasSharpDefectConstant *
      ((A : ℝ) + (B : ℝ)) /
        ((d : ℝ) * Real.log (y : ℝ) ^ 2)

/-- The abstract interval budget with the concrete sharp endpoint rate is
bounded by the explicit inverse-log-square budget above. -/
theorem roughSaiasIntervalFixedDivisorShiftBudget_sharp_le
    {A B y d : ℕ}
    (hy : 2 ≤ y) (hd : 0 < d) (hAB : A ≤ B) :
    roughSaiasIntervalFixedDivisorShiftBudget
        (roughSaiasInvLogSqEndpointRate
          roughSaiasSharpDefectConstant) A B y d ≤
      roughSaiasSharpIntervalFixedDivisorBudget A B y d := by
  have hdReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hC : 0 ≤ roughSaiasSharpDefectConstant := by
    unfold roughSaiasSharpDefectConstant
    have htheta : 0 ≤ roughSaiasThetaFourthPowerConstant :=
      roughSaiasThetaFourthPowerConstant_pos.le
    positivity
  have heta :
      0 ≤ roughSaiasInvLogSqEndpointRate
        roughSaiasSharpDefectConstant y := by
    unfold roughSaiasInvLogSqEndpointRate
    positivity
  have hqA :
      (((A / d : ℕ) : ℝ)) ≤ (A : ℝ) / (d : ℝ) :=
    Nat.cast_div_le
  have hqB :
      (((B / d : ℕ) : ℝ)) ≤ (B : ℝ) / (d : ℝ) :=
    Nat.cast_div_le
  have hqsum :
      (((A / d : ℕ) : ℝ) + ((B / d : ℕ) : ℝ)) ≤
        ((A : ℝ) + (B : ℝ)) / (d : ℝ) := by
    calc
      (((A / d : ℕ) : ℝ) + ((B / d : ℕ) : ℝ)) ≤
          (A : ℝ) / (d : ℝ) + (B : ℝ) / (d : ℝ) :=
        add_le_add hqA hqB
      _ = ((A : ℝ) + (B : ℝ)) / (d : ℝ) := by ring
  have hfloor :=
    quotientIocLength_sub_realLengthDiv_abs_lt_one hd hAB
  have hqgap :
      (((B / d - A / d : ℕ) : ℝ)) ≤
        ((B - A : ℕ) : ℝ) / (d : ℝ) + 1 := by
    rw [abs_lt] at hfloor
    linarith
  have hqendpoint :
      roughSaiasInvLogSqEndpointRate
          roughSaiasSharpDefectConstant y *
            (((A / d : ℕ) : ℝ) + ((B / d : ℕ) : ℝ)) ≤
        roughSaiasInvLogSqEndpointRate
          roughSaiasSharpDefectConstant y *
            (((A : ℝ) + (B : ℝ)) / (d : ℝ)) :=
    mul_le_mul_of_nonneg_left hqsum heta
  have hqlength :
      5 * ((B / d - A / d : ℕ) : ℝ) /
          Real.log (y : ℝ) ≤
        5 * (((B - A : ℕ) : ℝ) / (d : ℝ) + 1) /
          Real.log (y : ℝ) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hqgap (by norm_num)) hlogY.le
  have hsmallBudget :
      roughSaiasInvLogSqEndpointRate
          roughSaiasSharpDefectConstant y *
            (((A / d : ℕ) : ℝ) + ((B / d : ℕ) : ℝ)) +
        5 * ((B / d - A / d : ℕ) : ℝ) /
          Real.log (y : ℝ) ≤
      roughSaiasInvLogSqEndpointRate
          roughSaiasSharpDefectConstant y *
            (((A : ℝ) + (B : ℝ)) / (d : ℝ)) +
        5 * (((B - A : ℕ) : ℝ) / (d : ℝ) + 1) /
          Real.log (y : ℝ) :=
    add_le_add hqendpoint hqlength
  unfold roughSaiasIntervalFixedDivisorShiftBudget
    roughSaiasPairTransitionBudget
    roughSaiasSharpIntervalFixedDivisorBudget
  calc
    6 + ((B - A : ℕ) : ℝ) *
          (Real.log (d : ℝ) + 2) /
            ((d : ℝ) * Real.log (y : ℝ)) +
        (roughSaiasInvLogSqEndpointRate
            roughSaiasSharpDefectConstant y *
              (((A / d : ℕ) : ℝ) + ((B / d : ℕ) : ℝ)) +
          5 * ((B / d - A / d : ℕ) : ℝ) /
            Real.log (y : ℝ)) +
        (roughSaiasInvLogSqEndpointRate
            roughSaiasSharpDefectConstant y *
              ((A : ℝ) + (B : ℝ)) +
          5 * ((B - A : ℕ) : ℝ) /
            Real.log (y : ℝ)) / (d : ℝ) ≤
      6 + ((B - A : ℕ) : ℝ) *
          (Real.log (d : ℝ) + 2) /
            ((d : ℝ) * Real.log (y : ℝ)) +
        (roughSaiasInvLogSqEndpointRate
            roughSaiasSharpDefectConstant y *
              (((A : ℝ) + (B : ℝ)) / (d : ℝ)) +
          5 * (((B - A : ℕ) : ℝ) / (d : ℝ) + 1) /
            Real.log (y : ℝ)) +
        (roughSaiasInvLogSqEndpointRate
            roughSaiasSharpDefectConstant y *
              ((A : ℝ) + (B : ℝ)) +
          5 * ((B - A : ℕ) : ℝ) /
            Real.log (y : ℝ)) / (d : ℝ) := by
      exact add_le_add
        (add_le_add le_rfl hsmallBudget) le_rfl
    _ = 6 + 5 / Real.log (y : ℝ) +
        ((B - A : ℕ) : ℝ) *
          (Real.log (d : ℝ) + 12) /
            ((d : ℝ) * Real.log (y : ℝ)) +
        20 * roughSaiasSharpDefectConstant *
          ((A : ℝ) + (B : ℝ)) /
            ((d : ℝ) * Real.log (y : ℝ) ^ 2) := by
      unfold roughSaiasInvLogSqEndpointRate
      ring

/-- Fully closed sharp fixed-divisor interval shift. -/
theorem roughFriableInterval_fixedDivisorShift_abs_le_sharp
    {A B y d : ℕ}
    (hY :
      roughSaiasInvLogSqEndpointCutoff roughSaiasSharpDefectCutoff ≤ y)
    (hy : 2 ≤ y) (hd : 0 < d) (hdA : d ≤ A) (hAB : A ≤ B)
    (hlogB : Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |((FriableAsymptotic.friableCount (B / d) y : ℝ) -
          (FriableAsymptotic.friableCount (A / d) y : ℝ)) -
        ((FriableAsymptotic.friableCount B y : ℝ) -
          (FriableAsymptotic.friableCount A y : ℝ)) / (d : ℝ)| ≤
      roughSaiasSharpIntervalFixedDivisorBudget A B y d := by
  exact
    (roughFriableInterval_fixedDivisorShift_abs_le_of_saiasEndpointApproximation
      roughCompactBVTranslationPrinciple
      roughSaiasSharpEndpointApproximationUpToFive
      hY hy hd hdA hAB hlogB).trans
      (roughSaiasIntervalFixedDivisorShiftBudget_sharp_le hy hd hAB)

/-! ## Physical blocks and the finite head -/

/-- The literal two-piece physical block inherits the two
cancellation-preserving interval budgets. -/
theorem roughSmoothPhysicalBlock_fixedDivisorShift_abs_le_sharp
    {lo split hi y d : ℕ} {alpha broad : ℝ}
    (hY :
      roughSaiasInvLogSqEndpointCutoff roughSaiasSharpDefectCutoff ≤ y)
    (hy : 2 ≤ y) (hd : 0 < d) (hdLo : d ≤ lo)
    (hloSplit : lo ≤ split) (hSplitHi : split ≤ hi)
    (hlogHi : Real.log (hi : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
          alpha broad -
        roughSmoothPhysicalBlock lo split hi y alpha broad / (d : ℝ)| ≤
      |alpha| *
          roughSaiasSharpIntervalFixedDivisorBudget split hi y d +
        |broad| *
          roughSaiasSharpIntervalFixedDivisorBudget lo split y d := by
  have hlo : 0 < lo := hd.trans_le hdLo
  have hsplit : 0 < split := hlo.trans_le hloSplit
  have hdSplit : d ≤ split := hdLo.trans hloSplit
  have hlogSplit :
      Real.log (split : ℝ) ≤ 5 * Real.log (y : ℝ) := by
    have hmono : Real.log (split : ℝ) ≤ Real.log (hi : ℝ) :=
      Real.log_le_log (by exact_mod_cast hsplit)
        (by exact_mod_cast hSplitHi)
    exact hmono.trans hlogHi
  have hhigh :=
    roughFriableInterval_fixedDivisorShift_abs_le_sharp
      hY hy hd hdSplit hSplitHi hlogHi
  have hbroad :=
    roughFriableInterval_fixedDivisorShift_abs_le_sharp
      hY hy hd hdLo hloSplit hlogSplit
  let intervalError : ℕ → ℕ → ℝ := fun A B ↦
    ((FriableAsymptotic.friableCount (B / d) y : ℝ) -
        (FriableAsymptotic.friableCount (A / d) y : ℝ)) -
      ((FriableAsymptotic.friableCount B y : ℝ) -
        (FriableAsymptotic.friableCount A y : ℝ)) / (d : ℝ)
  have hblock :
      roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
            alpha broad -
          roughSmoothPhysicalBlock lo split hi y alpha broad / (d : ℝ) =
        alpha * intervalError split hi +
          broad * intervalError lo split := by
    rw [roughSmoothPhysicalBlock_eq_friableEndpoints
        (Nat.div_le_div_right hloSplit)
        (Nat.div_le_div_right hSplitHi),
      roughSmoothPhysicalBlock_eq_friableEndpoints hloSplit hSplitHi]
    dsimp [intervalError]
    ring
  have hhigh' :
      |intervalError split hi| ≤
        roughSaiasSharpIntervalFixedDivisorBudget split hi y d := by
    simpa only [intervalError] using hhigh
  have hbroad' :
      |intervalError lo split| ≤
        roughSaiasSharpIntervalFixedDivisorBudget lo split y d := by
    simpa only [intervalError] using hbroad
  rw [hblock]
  calc
    |alpha * intervalError split hi +
        broad * intervalError lo split| ≤
      |alpha| * |intervalError split hi| +
        |broad| * |intervalError lo split| := by
          rw [← abs_mul, ← abs_mul]
          exact abs_add_le _ _
    _ ≤ |alpha| *
          roughSaiasSharpIntervalFixedDivisorBudget split hi y d +
        |broad| *
          roughSaiasSharpIntervalFixedDivisorBudget lo split y d :=
      add_le_add
        (mul_le_mul_of_nonneg_left hhigh' (abs_nonneg alpha))
        (mul_le_mul_of_nonneg_left hbroad' (abs_nonneg broad))

/-- A smooth physical block is bounded by its right endpoint times the
sum of the two absolute weights. -/
theorem roughSmoothPhysicalBlock_abs_le_rightEndpoint
    {lo split hi y : ℕ} {alpha broad : ℝ}
    (hSplitHi : split ≤ hi) :
    |roughSmoothPhysicalBlock lo split hi y alpha broad| ≤
      (|alpha| + |broad|) * (hi : ℝ) := by
  have hsmoothCard :
      ∀ A B : ℕ,
        ((Erdos390.Full.StructuredCells.smoothInterval A B y).card : ℝ) ≤
          (B : ℝ) := by
    intro A B
    have hsubset :
        Erdos390.Full.StructuredCells.smoothInterval A B y ⊆
          Finset.Ioc A B := by
      intro a ha
      have haData :=
        Erdos390.Full.StructuredCells.mem_smoothInterval.mp ha
      exact Finset.mem_Ioc.mpr ⟨haData.1, haData.2.1⟩
    have hcard :
        (Erdos390.Full.StructuredCells.smoothInterval A B y).card ≤
          (Finset.Ioc A B).card :=
      Finset.card_le_card hsubset
    calc
      ((Erdos390.Full.StructuredCells.smoothInterval A B y).card : ℝ) ≤
          ((Finset.Ioc A B).card : ℝ) := by exact_mod_cast hcard
      _ = ((B - A : ℕ) : ℝ) := by rw [Nat.card_Ioc]
      _ ≤ (B : ℝ) := by exact_mod_cast Nat.sub_le B A
  have hhighCard :
      ((Erdos390.Full.StructuredCells.smoothInterval split hi y).card : ℝ) ≤
        (hi : ℝ) :=
    hsmoothCard split hi
  have hbroadCard :
      ((Erdos390.Full.StructuredCells.smoothInterval lo split y).card : ℝ) ≤
        (hi : ℝ) :=
    (hsmoothCard lo split).trans (by exact_mod_cast hSplitHi)
  unfold roughSmoothPhysicalBlock
  calc
    |alpha *
          ((Erdos390.Full.StructuredCells.smoothInterval split hi y).card : ℝ) +
        broad *
          ((Erdos390.Full.StructuredCells.smoothInterval lo split y).card : ℝ)| ≤
      |alpha *
          ((Erdos390.Full.StructuredCells.smoothInterval split hi y).card : ℝ)| +
        |broad *
          ((Erdos390.Full.StructuredCells.smoothInterval lo split y).card : ℝ)| :=
      abs_add_le _ _
    _ =
      |alpha| *
          ((Erdos390.Full.StructuredCells.smoothInterval split hi y).card : ℝ) +
      |broad| *
          ((Erdos390.Full.StructuredCells.smoothInterval lo split y).card : ℝ) := by
      rw [abs_mul, abs_mul,
        abs_of_nonneg (show 0 ≤
          ((Erdos390.Full.StructuredCells.smoothInterval split hi y).card : ℝ) by
            exact_mod_cast Nat.zero_le
              (Erdos390.Full.StructuredCells.smoothInterval split hi y).card
        ),
        abs_of_nonneg (show 0 ≤
          ((Erdos390.Full.StructuredCells.smoothInterval lo split y).card : ℝ) by
            exact_mod_cast Nat.zero_le
              (Erdos390.Full.StructuredCells.smoothInterval lo split y).card
        )]
    _ ≤ |alpha| * (hi : ℝ) + |broad| * (hi : ℝ) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hhighCard (abs_nonneg alpha))
        (mul_le_mul_of_nonneg_left hbroadCard (abs_nonneg broad))
    _ = (|alpha| + |broad|) * (hi : ℝ) := by ring

/-- If the entire physical row lies below `2d`, both the divided and
undivided blocks have uniformly bounded fixed-divisor shift.  This is the
small-row branch needed when the fixed head modulus does not fit below the
lower endpoint. -/
theorem roughSmoothPhysicalBlock_fixedDivisorShift_abs_le_small
    {lo split hi y d : ℕ} {alpha broad : ℝ}
    (hd : 0 < d) (_hloSplit : lo ≤ split) (hSplitHi : split ≤ hi)
    (hhi : hi ≤ 2 * d) :
    |roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
          alpha broad -
        roughSmoothPhysicalBlock lo split hi y alpha broad / (d : ℝ)| ≤
      4 * (|alpha| + |broad|) := by
  have hdReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hweight : 0 ≤ |alpha| + |broad| :=
    add_nonneg (abs_nonneg alpha) (abs_nonneg broad)
  have hquotientHi :
      (((hi / d : ℕ) : ℝ)) ≤ 2 := by
    calc
      (((hi / d : ℕ) : ℝ)) ≤ (hi : ℝ) / (d : ℝ) :=
        Nat.cast_div_le
      _ ≤ 2 := by
        apply (div_le_iff₀ hdReal).2
        exact_mod_cast hhi
  have hsmall :
      |roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
          alpha broad| ≤
        (|alpha| + |broad|) * ((hi / d : ℕ) : ℝ) :=
    roughSmoothPhysicalBlock_abs_le_rightEndpoint
      (lo := lo / d) (split := split / d) (hi := hi / d) (y := y)
      (alpha := alpha) (broad := broad)
      (Nat.div_le_div_right (c := d) hSplitHi)
  have hlarge :
      |roughSmoothPhysicalBlock lo split hi y alpha broad| ≤
        (|alpha| + |broad|) * (hi : ℝ) :=
    roughSmoothPhysicalBlock_abs_le_rightEndpoint
      (lo := lo) (split := split) (hi := hi) (y := y)
      (alpha := alpha) (broad := broad) hSplitHi
  have hsmall' :
      |roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
          alpha broad| ≤
        2 * (|alpha| + |broad|) := by
    calc
      _ ≤ (|alpha| + |broad|) * ((hi / d : ℕ) : ℝ) := hsmall
      _ ≤ (|alpha| + |broad|) * 2 :=
        mul_le_mul_of_nonneg_left hquotientHi hweight
      _ = 2 * (|alpha| + |broad|) := by ring
  have hlarge' :
      |roughSmoothPhysicalBlock lo split hi y alpha broad / (d : ℝ)| ≤
        2 * (|alpha| + |broad|) := by
    rw [abs_div, abs_of_pos hdReal]
    calc
      |roughSmoothPhysicalBlock lo split hi y alpha broad| / (d : ℝ) ≤
          ((|alpha| + |broad|) * (hi : ℝ)) / (d : ℝ) := by
        exact (div_le_div_iff_of_pos_right hdReal).2 hlarge
      _ = (|alpha| + |broad|) * ((hi : ℝ) / (d : ℝ)) := by ring
      _ ≤ (|alpha| + |broad|) * 2 := by
        apply mul_le_mul_of_nonneg_left _ hweight
        exact (div_le_iff₀ hdReal).2 (by exact_mod_cast hhi)
      _ = 2 * (|alpha| + |broad|) := by ring
  calc
    |roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
          alpha broad -
        roughSmoothPhysicalBlock lo split hi y alpha broad / (d : ℝ)| ≤
      |roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
          alpha broad| +
        |roughSmoothPhysicalBlock lo split hi y alpha broad / (d : ℝ)| :=
      abs_sub _ _
    _ ≤ 2 * (|alpha| + |broad|) +
        2 * (|alpha| + |broad|) :=
      add_le_add hsmall' hlarge'
    _ = 4 * (|alpha| + |broad|) := by ring

/-- Explicit sharp finite-divisor allowance for one canonical fixed-head
row. -/
noncomputable def roughCanonicalSharpFixedHeadShiftBudget
    (W n h K y : ℕ) (alpha beta L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) : ℝ :=
  ∑ d ∈ (roughHeadModulus W).divisors,
    |(ArithmeticFunction.moebius d : ℝ)| *
      (|alpha| *
          roughSaiasSharpIntervalFixedDivisorBudget
            ((2 * n - K * h) / row.1) ((2 * n) / row.1) y d +
        |beta / L| *
          roughSaiasSharpIntervalFixedDivisorBudget
            (n / row.1) ((2 * n - K * h) / row.1) y d)

/-- The canonical fixed-head ledger is bounded by the explicit sharp
finite-divisor allowance whenever the fixed modulus fits below the lower
row endpoint.  No endpointwise de Bruijn estimate appears in the proof. -/
theorem roughCanonicalFixedHeadShiftLedger_le_sharpIntervalBudget
    {W n h K y : ℕ} {alpha beta L : ℝ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hY :
      roughSaiasInvLogSqEndpointCutoff roughSaiasSharpDefectCutoff ≤ y)
    (hy : 2 ≤ y) (hKh : K * h ≤ n)
    (hheadLo : roughHeadModulus W ≤ n / row.1)
    (hlogHi :
      Real.log (((2 * n) / row.1 : ℕ) : ℝ) ≤
        5 * Real.log (y : ℝ)) :
    roughCanonicalFixedHeadShiftLedger
        W n h K y alpha beta L row ≤
      roughCanonicalSharpFixedHeadShiftBudget
        W n h K y alpha beta L row := by
  have hloSplit :
      n / row.1 ≤ (2 * n - K * h) / row.1 := by
    apply Nat.div_le_div_right
    omega
  have hSplitHi :
      (2 * n - K * h) / row.1 ≤ (2 * n) / row.1 :=
    Nat.div_le_div_right (Nat.sub_le _ _)
  unfold roughCanonicalFixedHeadShiftLedger
    roughCanonicalSharpFixedHeadShiftBudget
  apply Finset.sum_le_sum
  intro d hdMem
  have hd : 0 < d := Nat.pos_of_mem_divisors hdMem
  have hdDvd : d ∣ roughHeadModulus W :=
    (Nat.mem_divisors.mp hdMem).1
  have hdHead : d ≤ roughHeadModulus W :=
    Nat.le_of_dvd (roughHeadModulus_pos W) hdDvd
  have hdLo : d ≤ n / row.1 := hdHead.trans hheadLo
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact roughSmoothPhysicalBlock_fixedDivisorShift_abs_le_sharp
    hY hy hd hdLo hloSplit hSplitHi hlogHi

/-- All-row sharp fixed-head allowance.  Large rows use the interval
cancellation budget; when `d` exceeds the lower endpoint, the whole row is
below `2d` and the fixed constant branch applies. -/
noncomputable def roughCanonicalSharpFixedHeadShiftBudgetAllRows
    (W n h K y : ℕ) (alpha beta L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) : ℝ :=
  ∑ d ∈ (roughHeadModulus W).divisors,
    |(ArithmeticFunction.moebius d : ℝ)| *
      if d ≤ n / row.1 then
        (|alpha| *
            roughSaiasSharpIntervalFixedDivisorBudget
              ((2 * n - K * h) / row.1) ((2 * n) / row.1) y d +
          |beta / L| *
            roughSaiasSharpIntervalFixedDivisorBudget
              (n / row.1) ((2 * n - K * h) / row.1) y d)
      else
        4 * (|alpha| + |beta / L|)

/-- The literal canonical fixed-head ledger is controlled on every active
row, without assuming that the fixed modulus lies below the row endpoint.
The small-row branch is purely finite and contributes only a
head-dependent constant after the divisor sum. -/
theorem roughCanonicalFixedHeadShiftLedger_le_sharpIntervalBudget_allRows
    {W n h K y : ℕ} {alpha beta L : ℝ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hY :
      roughSaiasInvLogSqEndpointCutoff roughSaiasSharpDefectCutoff ≤ y)
    (hy : 2 ≤ y) (hKh : K * h ≤ n)
    (hlogHi :
      Real.log (((2 * n) / row.1 : ℕ) : ℝ) ≤
        5 * Real.log (y : ℝ)) :
    roughCanonicalFixedHeadShiftLedger
        W n h K y alpha beta L row ≤
      roughCanonicalSharpFixedHeadShiftBudgetAllRows
        W n h K y alpha beta L row := by
  have hlabel : 0 < row.1 :=
    canonicalCompleteRoughRow_label_pos y
      (roughRawCandidateSet n h K) row
  have hloSplit :
      n / row.1 ≤ (2 * n - K * h) / row.1 := by
    apply Nat.div_le_div_right
    omega
  have hSplitHi :
      (2 * n - K * h) / row.1 ≤ (2 * n) / row.1 :=
    Nat.div_le_div_right (Nat.sub_le _ _)
  unfold roughCanonicalFixedHeadShiftLedger
    roughCanonicalSharpFixedHeadShiftBudgetAllRows
  apply Finset.sum_le_sum
  intro d hdMem
  have hd : 0 < d := Nat.pos_of_mem_divisors hdMem
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  by_cases hdLo : d ≤ n / row.1
  · rw [if_pos hdLo]
    exact roughSmoothPhysicalBlock_fixedDivisorShift_abs_le_sharp
      hY hy hd hdLo hloSplit hSplitHi hlogHi
  · rw [if_neg hdLo]
    have hloD : n / row.1 < d := Nat.lt_of_not_ge hdLo
    have hnD : n < d * row.1 :=
      (Nat.div_lt_iff_lt_mul hlabel).mp hloD
    have htwo :
        2 * n < (2 * d) * row.1 := by
      have hmul :=
        (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hnD
      simpa only [Nat.mul_assoc] using hmul
    have hhiLt : (2 * n) / row.1 < 2 * d :=
      (Nat.div_lt_iff_lt_mul hlabel).mpr htwo
    exact roughSmoothPhysicalBlock_fixedDivisorShift_abs_le_small
      hd hloSplit hSplitHi hhiLt.le

/-- Raw-row quota closure with the analytic endpoint input and the entire
fixed-head shift discharged by the closed sharp theorems in this file.
Only the three explicit finite ledgers remain to be absorbed into the
chosen paper allowance. -/
theorem roughCanonicalRawRowQuotaError_abs_le_three_mul_sharpAllowance
    {W n h K y : ℕ} {alpha beta L E : ℝ}
    (hWy : W ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hrowN : row.1 ≤ n) (hKh : K * h ≤ n)
    (hY :
      roughSaiasInvLogSqEndpointCutoff roughSaiasSharpDefectCutoff ≤ y)
    (hy : 2 ≤ y)
    (hlogs : ∀ i : Fin 4,
      Real.log (roughPhysicalNatEndpoint
          ((2 * n + h) / row.1) ((2 * n) / row.1)
          ((2 * n - K * h) / row.1) (n / row.1) i : ℝ) ≤
        5 * Real.log (y : ℝ))
    (hmain : roughPhysicalDickmanTransitionLedger
        (roughHeadDensity W) alpha beta L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤ E)
    (htransition : roughPhysicalSaiasTransitionBudget
        (roughSaiasInvLogSqEndpointRate roughSaiasSharpDefectConstant)
        (roughHeadDensity W) alpha beta L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤ E)
    (hhead :
      roughCanonicalSharpFixedHeadShiftBudgetAllRows
        W n h K y alpha beta L row ≤ E) :
    |roughCanonicalRawRowQuotaError
        W n h K y alpha beta L row| ≤ 3 * E := by
  have hheadLedger :
      roughCanonicalFixedHeadShiftLedger
          W n h K y alpha beta L row ≤ E :=
    (roughCanonicalFixedHeadShiftLedger_le_sharpIntervalBudget_allRows
      row hY hy hKh (hlogs (1 : Fin 4))).trans hhead
  exact roughCanonicalRawRowQuotaError_abs_le_three_mul_paperAllowance
    roughCompactBVTranslationPrinciple hWy row hrowN hKh
      roughSaiasSharpEndpointApproximationUpToFive hY hy hlogs
      hmain htransition hheadLedger

end

end Erdos390.WholePaper
