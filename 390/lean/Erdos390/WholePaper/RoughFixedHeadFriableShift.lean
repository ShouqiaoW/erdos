import Erdos390.WholePaper.FixedModulusReducedResidueCount
import Erdos390.Full.MarkedFriableAsymptotic
import Erdos390.Full.PaperScaleMarkedCell

/-!
# The strongest available unconditional fixed-head friable shift

The paper uses the Hildebrand--Tenenbaum--Saias transition estimate to
obtain an `O_W(x / log(y)^2 + 1)` shift for a balanced physical block.
That transition estimate is not present in Mathlib, PrimeNumberTheoremAnd,
or the current project.  What *is* present is the closed uniform de Bruijn
estimate

`|Psi(X,y) - X * rho(log X / log y)| <= K * X / log y`

from `Full.FriableAsymptotic`.  This file records the strongest genuine
fixed-head consequence of that theorem.  It proves, without an analytic
hypothesis, an `O_W(X / log y + 1)` shift for the endpoint count, the
literal two-piece physical block, and its complete head Mobius closure.

The first lemma extends the already-proved floor-stability argument from
the recursive four-mark range `u <= 4` to the full endpoint range `u <= 5`.
It uses only the project's proved one-Lipschitz estimate for `rho`.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Full-range floor stability of the Dickman main term -/

/-- Replacing a positive real quotient by its natural-number floor changes
the Dickman endpoint main term by at most three throughout `u <= 5`.

`Full.FriableAsymptotic.rho_floor_kernel_stability` proves the same
estimate with the stronger input `u <= 4`, which is exactly what its prime
recurrence needs.  The proof below is its deterministic endpoint argument
with the already available full compact range retained. -/
theorem roughRhoFloorKernel_stability
    (A : ℕ) {r p : ℝ}
    (hA : 1 ≤ A) (hAr : (A : ℝ) ≤ r) (hrA : r < (A : ℝ) + 1)
    (hp : (2 : ℝ) ≤ p)
    (hb5 : Real.log r / Real.log p ≤ 5) :
    |(A : ℝ) * rho (Real.log (A : ℝ) / Real.log p) -
        r * rho (Real.log r / Real.log p)| ≤ 3 := by
  let a : ℝ := Real.log (A : ℝ) / Real.log p
  let b : ℝ := Real.log r / Real.log p
  have hApos : (0 : ℝ) < (A : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
  have hrpos : 0 < r := hApos.trans_le hAr
  have hlogppos : 0 < Real.log p := Real.log_pos (by linarith)
  have hlogpHalf : (1 / 2 : ℝ) ≤ Real.log p := by
    have hmono : Real.log 2 ≤ Real.log p :=
      Real.log_le_log (by norm_num) hp
    nlinarith [Real.log_two_gt_d9]
  have hlogAr : Real.log (A : ℝ) ≤ Real.log r :=
    Real.log_le_log hApos hAr
  have hab : a ≤ b := by
    dsimp [a, b]
    exact div_le_div_of_nonneg_right hlogAr hlogppos.le
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast hA)) hlogppos.le
  have hb0 : 0 ≤ b := ha0.trans hab
  have hb5' : b ≤ 5 := by
    simpa only [b] using hb5
  have hrhoa0 : 0 ≤ rho a :=
    (rho_pos_on_zero_five ha0 (hab.trans hb5')).le
  have hrhob0 : 0 ≤ rho b :=
    (rho_pos_on_zero_five hb0 hb5').le
  have hrhob1 : rho b ≤ 1 :=
    FriableAsymptotic.rho_le_one_of_le_five hb5'
  have hrho : |rho a - rho b| ≤ b - a := by
    rw [abs_sub_comm]
    exact FriableAsymptotic.rho_lipschitz_of_le_five hab hb5'
  have hlogQuotient :
      Real.log r - Real.log (A : ℝ) ≤ r / (A : ℝ) - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hrpos hApos)
    rw [Real.log_div hrpos.ne' hApos.ne'] at h
    exact h
  have hscaled :
      (A : ℝ) * (Real.log r - Real.log (A : ℝ)) ≤
        r - (A : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlogQuotient hApos.le
    calc
      (A : ℝ) * (Real.log r - Real.log (A : ℝ)) ≤
          (A : ℝ) * (r / (A : ℝ) - 1) := h
      _ = r - (A : ℝ) := by field_simp
  have hAdiff : (A : ℝ) * (b - a) ≤ 2 := by
    have hdiv := div_le_div_of_nonneg_right hscaled hlogppos.le
    have hfirst : (A : ℝ) * (b - a) ≤
        (r - (A : ℝ)) / Real.log p := by
      dsimp [a, b]
      convert hdiv using 1
      ring
    have hsecond : (r - (A : ℝ)) / Real.log p ≤ 2 := by
      apply (div_le_iff₀ hlogppos).2
      nlinarith
    exact hfirst.trans hsecond
  have hgap0 : 0 ≤ r - (A : ℝ) := sub_nonneg.mpr hAr
  have hgap1 : r - (A : ℝ) ≤ 1 := by linarith
  calc
    |(A : ℝ) * rho (Real.log (A : ℝ) / Real.log p) -
        r * rho (Real.log r / Real.log p)| =
      |(A : ℝ) * (rho a - rho b) +
          ((A : ℝ) - r) * rho b| := by
        dsimp [a, b]
        congr 1
        ring
    _ ≤ |(A : ℝ) * (rho a - rho b)| +
          |((A : ℝ) - r) * rho b| := abs_add_le _ _
    _ = (A : ℝ) * |rho a - rho b| +
          (r - (A : ℝ)) * rho b := by
      rw [abs_mul, abs_mul, abs_of_nonneg hApos.le,
        abs_of_nonpos (sub_nonpos.mpr hAr), abs_of_nonneg hrhob0]
      ring
    _ ≤ (A : ℝ) * (b - a) +
          (r - (A : ℝ)) * 1 := by gcongr
    _ ≤ 2 + 1 := add_le_add hAdiff (by simpa using hgap1)
    _ = 3 := by norm_num

/-! ## A fixed-divisor shift for the Dickman main term -/

/-- The Dickman endpoint model at `floor(X/d)` differs from `1/d` times
the model at `X` by the floor constant three plus the exact logarithmic
translation cost. -/
theorem roughFriableMain_fixedDivisorShift
    {X y d : ℕ}
    (hy : 2 ≤ y) (hd : 0 < d) (hdX : d ≤ X)
    (hlogX : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |((X / d : ℕ) : ℝ) *
          rho (FriableAsymptotic.dickmanU (X / d) y) -
        ((X : ℝ) * rho (FriableAsymptotic.dickmanU X y)) / (d : ℝ)| ≤
      3 + (X : ℝ) * Real.log (d : ℝ) /
        ((d : ℝ) * Real.log (y : ℝ)) := by
  have hX : 0 < X := hd.trans_le hdX
  have hA : 1 ≤ X / d := by
    apply (Nat.le_div_iff_mul_le hd).2
    simpa using hdX
  have hApos : 0 < X / d := Nat.zero_lt_of_lt hA
  have hdReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hXReal : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hyReal : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  let r : ℝ := (X : ℝ) / (d : ℝ)
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
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
  have htranslateNonneg :
      0 ≤ Real.log (d : ℝ) / Real.log (y : ℝ) :=
    div_nonneg hlogd hlogY.le
  have hcoordinateLe :
      Real.log r / Real.log (y : ℝ) ≤
        FriableAsymptotic.dickmanU X y := by
    rw [hcoordinate]
    linarith
  have hu5 : FriableAsymptotic.dickmanU X y ≤ 5 := by
    simp only [FriableAsymptotic.dickmanU]
    exact (div_le_iff₀ hlogY).2 hlogX
  have hrho :
      |rho (Real.log r / Real.log (y : ℝ)) -
          rho (FriableAsymptotic.dickmanU X y)| ≤
        Real.log (d : ℝ) / Real.log (y : ℝ) := by
    rw [abs_sub_comm]
    calc
      |rho (FriableAsymptotic.dickmanU X y) -
          rho (Real.log r / Real.log (y : ℝ))| ≤
        FriableAsymptotic.dickmanU X y -
          Real.log r / Real.log (y : ℝ) :=
        FriableAsymptotic.rho_lipschitz_of_le_five hcoordinateLe hu5
      _ = Real.log (d : ℝ) / Real.log (y : ℝ) := by
        rw [hcoordinate]
        ring
  calc
    |((X / d : ℕ) : ℝ) *
          rho (FriableAsymptotic.dickmanU (X / d) y) -
        ((X : ℝ) * rho (FriableAsymptotic.dickmanU X y)) / (d : ℝ)| =
      |(((X / d : ℕ) : ℝ) *
            rho (FriableAsymptotic.dickmanU (X / d) y) -
          r * rho (Real.log r / Real.log (y : ℝ))) +
        r * (rho (Real.log r / Real.log (y : ℝ)) -
          rho (FriableAsymptotic.dickmanU X y))| := by
        simp only [FriableAsymptotic.dickmanU]
        congr 1
        dsimp [r]
        ring
    _ ≤ |((X / d : ℕ) : ℝ) *
            rho (FriableAsymptotic.dickmanU (X / d) y) -
          r * rho (Real.log r / Real.log (y : ℝ))| +
        |r * (rho (Real.log r / Real.log (y : ℝ)) -
          rho (FriableAsymptotic.dickmanU X y))| := abs_add_le _ _
    _ ≤ 3 + r *
          (Real.log (d : ℝ) / Real.log (y : ℝ)) := by
      apply add_le_add
      · simpa only [FriableAsymptotic.dickmanU] using hfloor
      · rw [abs_mul, abs_of_pos hrpos]
        exact mul_le_mul_of_nonneg_left hrho hrpos.le
    _ = 3 + (X : ℝ) * Real.log (d : ℝ) /
          ((d : ℝ) * Real.log (y : ℝ)) := by
      dsimp [r]
      ring

/-! ## The closed fixed-head endpoint theorem -/

/-- Uniformly over every divisor of the fixed head modulus, the genuine
friable endpoint count at `floor(X/d)` is `1/d` times the count at `X`,
up to `O_W(X / log y + 1)`.  The constants and threshold are chosen before
`X`, `y`, and the head divisor. -/
theorem exists_uniform_roughFixedHead_friableCount_shift_bound
    (W : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {X y d : ℕ},
      Y₀ ≤ y →
      d ∈ (roughHeadModulus W).divisors →
      d ≤ X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |(FriableAsymptotic.friableCount (X / d) y : ℝ) -
          (FriableAsymptotic.friableCount X y : ℝ) / (d : ℝ)| ≤
        K * (X : ℝ) / ((d : ℝ) * Real.log (y : ℝ)) + 3 := by
  obtain ⟨K₀, hK₀, Y₁, hdeBruijn⟩ :=
    FriableAsymptotic.exists_uniform_friableCount_dickman_bound_all_faces
  let P : ℕ := roughHeadModulus W
  let K : ℝ := 2 * K₀ + Real.log (P : ℝ)
  let Y₀ : ℕ := max 2 Y₁
  have hP : 0 < P := by
    simpa only [P] using roughHeadModulus_pos W
  have hlogP : 0 ≤ Real.log (P : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ P by omega))
  have hK : 0 < K := by
    dsimp [K]
    linarith
  refine ⟨K, hK, Y₀, ?_⟩
  intro X y d hY hdMem hdX hlogX
  have hy2 : 2 ≤ y :=
    (le_max_left 2 Y₁).trans (by simpa only [Y₀] using hY)
  have hY₁ : Y₁ ≤ y :=
    (le_max_right 2 Y₁).trans (by simpa only [Y₀] using hY)
  have hdPos : 0 < d := by
    exact Nat.pos_of_mem_divisors (by simpa only [P] using hdMem)
  have hdDvd : d ∣ P := by
    exact (Nat.mem_divisors.mp (by simpa only [P] using hdMem)).1
  have hdP : d ≤ P := Nat.le_of_dvd hP hdDvd
  have hXPos : 0 < X := hdPos.trans_le hdX
  have hAPos : 0 < X / d := by
    apply Nat.div_pos
    exact hdX
    exact hdPos
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hAleX : X / d ≤ X := Nat.div_le_self X d
  have hlogA :
      Real.log ((X / d : ℕ) : ℝ) ≤ 5 * Real.log (y : ℝ) := by
    have hmono :
        Real.log ((X / d : ℕ) : ℝ) ≤ Real.log (X : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast hAPos
      · exact_mod_cast hAleX
    exact hmono.trans hlogX
  have hsmall := hdeBruijn hY₁ hAPos hlogA
  have hlarge := hdeBruijn hY₁ hXPos hlogX
  have hsmall' :
      |(FriableAsymptotic.friableCount (X / d) y : ℝ) -
          ((X / d : ℕ) : ℝ) *
            rho (FriableAsymptotic.dickmanU (X / d) y)| ≤
        K₀ * (X : ℝ) / ((d : ℝ) * Real.log (y : ℝ)) := by
    calc
      _ ≤ K₀ * ((X / d : ℕ) : ℝ) / Real.log (y : ℝ) := hsmall
      _ ≤ K₀ * ((X : ℝ) / (d : ℝ)) / Real.log (y : ℝ) := by
        gcongr
        exact Nat.cast_div_le
      _ = K₀ * (X : ℝ) /
          ((d : ℝ) * Real.log (y : ℝ)) := by ring
  have hlarge' :
      |(((X : ℝ) * rho (FriableAsymptotic.dickmanU X y)) -
          (FriableAsymptotic.friableCount X y : ℝ)) / (d : ℝ)| ≤
        K₀ * (X : ℝ) / ((d : ℝ) * Real.log (y : ℝ)) := by
    rw [abs_div, abs_of_pos (by exact_mod_cast hdPos : (0 : ℝ) < d),
      abs_sub_comm]
    calc
      |(FriableAsymptotic.friableCount X y : ℝ) -
          (X : ℝ) * rho (FriableAsymptotic.dickmanU X y)| / (d : ℝ) ≤
        (K₀ * (X : ℝ) / Real.log (y : ℝ)) / (d : ℝ) := by
          exact (div_le_div_iff_of_pos_right
            (by exact_mod_cast hdPos : (0 : ℝ) < d)).2 hlarge
      _ = K₀ * (X : ℝ) /
          ((d : ℝ) * Real.log (y : ℝ)) := by ring
  have hmodel := roughFriableMain_fixedDivisorShift
    hy2 hdPos hdX hlogX
  let smallError : ℝ :=
    (FriableAsymptotic.friableCount (X / d) y : ℝ) -
      ((X / d : ℕ) : ℝ) *
        rho (FriableAsymptotic.dickmanU (X / d) y)
  let modelError : ℝ :=
    ((X / d : ℕ) : ℝ) *
        rho (FriableAsymptotic.dickmanU (X / d) y) -
      ((X : ℝ) * rho (FriableAsymptotic.dickmanU X y)) / (d : ℝ)
  let largeError : ℝ :=
    (((X : ℝ) * rho (FriableAsymptotic.dickmanU X y)) -
      (FriableAsymptotic.friableCount X y : ℝ)) / (d : ℝ)
  have hrearrange :
      (FriableAsymptotic.friableCount (X / d) y : ℝ) -
          (FriableAsymptotic.friableCount X y : ℝ) / (d : ℝ) =
        smallError + (modelError + largeError) := by
    dsimp [smallError, modelError, largeError]
    ring
  rw [hrearrange]
  have hlogdP : Real.log (d : ℝ) ≤ Real.log (P : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hdPos
    · exact_mod_cast hdP
  have hscale :
      0 ≤ (X : ℝ) / ((d : ℝ) * Real.log (y : ℝ)) := by positivity
  calc
    |smallError + (modelError + largeError)| ≤
        |smallError| + (|modelError| + |largeError|) := by
      exact (abs_add_le _ _).trans
        (add_le_add le_rfl (abs_add_le _ _))
    _ ≤ K₀ * (X : ℝ) / ((d : ℝ) * Real.log (y : ℝ)) +
        ((3 + (X : ℝ) * Real.log (d : ℝ) /
          ((d : ℝ) * Real.log (y : ℝ))) +
        K₀ * (X : ℝ) / ((d : ℝ) * Real.log (y : ℝ))) := by
      exact add_le_add hsmall' (add_le_add hmodel hlarge')
    _ = (2 * K₀ + Real.log (d : ℝ)) * (X : ℝ) /
          ((d : ℝ) * Real.log (y : ℝ)) + 3 := by ring
    _ ≤ (2 * K₀ + Real.log (P : ℝ)) * (X : ℝ) /
          ((d : ℝ) * Real.log (y : ℝ)) + 3 := by
      gcongr
    _ = K * (X : ℝ) /
          ((d : ℝ) * Real.log (y : ℝ)) + 3 := by rfl

/-! ## Literal two-piece physical blocks -/

/-- Rewrite the literal smooth physical block as a three-endpoint
combination of the genuine friable counting function. -/
theorem roughSmoothPhysicalBlock_eq_friableEndpoints
    {lo split hi y : ℕ} {alpha broad : ℝ}
    (hloSplit : lo ≤ split) (hSplitHi : split ≤ hi) :
    roughSmoothPhysicalBlock lo split hi y alpha broad =
      alpha *
          ((FriableAsymptotic.friableCount hi y : ℝ) -
            (FriableAsymptotic.friableCount split y : ℝ)) +
        broad *
          ((FriableAsymptotic.friableCount split y : ℝ) -
            (FriableAsymptotic.friableCount lo y : ℝ)) := by
  have hPsiLoSplit : psi lo y ≤ psi split y :=
    FriableAsymptotic.friableCount_mono_left hloSplit
  have hPsiSplitHi : psi split y ≤ psi hi y :=
    FriableAsymptotic.friableCount_mono_left hSplitHi
  rw [roughSmoothPhysicalBlock,
    smoothInterval_card_eq_psi_sub hSplitHi,
    smoothInterval_card_eq_psi_sub hloSplit,
    Nat.cast_sub hPsiSplitHi, Nat.cast_sub hPsiLoSplit]
  rfl

/-- The literal two-piece physical block has a uniform fixed-head shift
with the strongest currently formalized unconditional scale.  The first
term is `O_W(size / log y)` and the second retains every integer endpoint
constant. -/
theorem exists_uniform_roughFixedHead_smoothPhysicalBlock_shift_bound
    (W : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ,
      ∀ {lo split hi y d : ℕ} {alpha broad : ℝ},
      Y₀ ≤ y →
      d ∈ (roughHeadModulus W).divisors →
      d ≤ lo → lo ≤ split → split ≤ hi →
      Real.log (hi : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
          alpha broad -
        roughSmoothPhysicalBlock lo split hi y alpha broad / (d : ℝ)| ≤
      K *
          (|alpha| * ((hi : ℝ) + (split : ℝ)) +
            |broad| * ((split : ℝ) + (lo : ℝ))) /
        ((d : ℝ) * Real.log (y : ℝ)) +
      6 * (|alpha| + |broad|) := by
  obtain ⟨K, hK, Y₀, hshift⟩ :=
    exists_uniform_roughFixedHead_friableCount_shift_bound W
  refine ⟨K, hK, Y₀, ?_⟩
  intro lo split hi y d alpha broad hY hdMem hdLo
    hloSplit hSplitHi hlogHi
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hdMem
  have hloPos : 0 < lo := hdPos.trans_le hdLo
  have hsplitPos : 0 < split := hloPos.trans_le hloSplit
  have hhiPos : 0 < hi := hsplitPos.trans_le hSplitHi
  have hlogSplit :
      Real.log (split : ℝ) ≤ 5 * Real.log (y : ℝ) := by
    have hmono : Real.log (split : ℝ) ≤ Real.log (hi : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast hsplitPos
      · exact_mod_cast hSplitHi
    exact hmono.trans hlogHi
  have hlogLo :
      Real.log (lo : ℝ) ≤ 5 * Real.log (y : ℝ) := by
    have hmono : Real.log (lo : ℝ) ≤ Real.log (split : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast hloPos
      · exact_mod_cast hloSplit
    exact hmono.trans hlogSplit
  have hdSplit : d ≤ split := hdLo.trans hloSplit
  have hdHi : d ≤ hi := hdSplit.trans hSplitHi
  have hHi := hshift hY hdMem hdHi hlogHi
  have hSplit := hshift hY hdMem hdSplit hlogSplit
  have hLo := hshift hY hdMem hdLo hlogLo
  let endpointError : ℕ → ℝ := fun X ↦
    (FriableAsymptotic.friableCount (X / d) y : ℝ) -
      (FriableAsymptotic.friableCount X y : ℝ) / (d : ℝ)
  have hblock :
      roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
            alpha broad -
          roughSmoothPhysicalBlock lo split hi y alpha broad / (d : ℝ) =
        alpha * (endpointError hi - endpointError split) +
          broad * (endpointError split - endpointError lo) := by
    rw [roughSmoothPhysicalBlock_eq_friableEndpoints
        (Nat.div_le_div_right hloSplit) (Nat.div_le_div_right hSplitHi),
      roughSmoothPhysicalBlock_eq_friableEndpoints hloSplit hSplitHi]
    dsimp [endpointError]
    ring
  rw [hblock]
  have hHi' : |endpointError hi| ≤
      K * (hi : ℝ) / ((d : ℝ) * Real.log (y : ℝ)) + 3 := by
    simpa only [endpointError] using hHi
  have hSplit' : |endpointError split| ≤
      K * (split : ℝ) / ((d : ℝ) * Real.log (y : ℝ)) + 3 := by
    simpa only [endpointError] using hSplit
  have hLo' : |endpointError lo| ≤
      K * (lo : ℝ) / ((d : ℝ) * Real.log (y : ℝ)) + 3 := by
    simpa only [endpointError] using hLo
  calc
    |alpha * (endpointError hi - endpointError split) +
        broad * (endpointError split - endpointError lo)| ≤
      |alpha| * (|endpointError hi| + |endpointError split|) +
        |broad| * (|endpointError split| + |endpointError lo|) := by
      calc
        _ ≤ |alpha * (endpointError hi - endpointError split)| +
            |broad * (endpointError split - endpointError lo)| :=
          abs_add_le _ _
        _ = |alpha| * |endpointError hi - endpointError split| +
            |broad| * |endpointError split - endpointError lo| := by
          rw [abs_mul, abs_mul]
        _ ≤ |alpha| * (|endpointError hi| + |endpointError split|) +
            |broad| * (|endpointError split| + |endpointError lo|) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg alpha))
            (mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg broad))
    _ ≤ |alpha| *
          ((K * (hi : ℝ) / ((d : ℝ) * Real.log (y : ℝ)) + 3) +
            (K * (split : ℝ) /
              ((d : ℝ) * Real.log (y : ℝ)) + 3)) +
        |broad| *
          ((K * (split : ℝ) /
              ((d : ℝ) * Real.log (y : ℝ)) + 3) +
            (K * (lo : ℝ) /
              ((d : ℝ) * Real.log (y : ℝ)) + 3)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add hHi' hSplit')
          (abs_nonneg alpha))
        (mul_le_mul_of_nonneg_left (add_le_add hSplit' hLo')
          (abs_nonneg broad))
    _ = K *
          (|alpha| * ((hi : ℝ) + (split : ℝ)) +
            |broad| * ((split : ℝ) + (lo : ℝ))) /
        ((d : ℝ) * Real.log (y : ℝ)) +
      6 * (|alpha| + |broad|) := by ring

/-! ## Complete head Mobius closure at the available scale -/

/-- The inverse-divisor Mobius mass of the literal zero head is exactly its
reduced-residue density. -/
theorem roughHead_moebius_inv_sum_eq_density (W : ℕ) :
    (∑ d ∈ (roughHeadModulus W).divisors,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) =
      roughHeadDensity W := by
  simpa only [roughHeadZeroPattern_modulus, roughHeadDensity] using
    Erdos390.Full.PaperScaleMarkedCell.sum_moebius_div_inv_eq_totient_ratio
      (roughHeadZeroPattern W)

/-- Combining the exact finite head inclusion--exclusion with the proved
fixed-head shift gives the unconditional density closure.  The displayed
finite sum is an explicit `O_W(size / log y + 1)` constant ledger. -/
theorem exists_uniform_roughHeadFree_smoothPhysicalBlock_density_bound
    (W : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ,
      ∀ {lo split hi y : ℕ} {alpha broad : ℝ},
      Y₀ ≤ y → W ≤ y → roughHeadModulus W ≤ lo →
      lo ≤ split → split ≤ hi →
      Real.log (hi : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |roughHeadFreeSmoothPhysicalBlock W lo split hi y alpha broad -
          roughHeadDensity W *
            roughSmoothPhysicalBlock lo split hi y alpha broad| ≤
        ∑ d ∈ (roughHeadModulus W).divisors,
          |(ArithmeticFunction.moebius d : ℝ)| *
            (K *
                (|alpha| * ((hi : ℝ) + (split : ℝ)) +
                  |broad| * ((split : ℝ) + (lo : ℝ))) /
              ((d : ℝ) * Real.log (y : ℝ)) +
            6 * (|alpha| + |broad|)) := by
  obtain ⟨K, hK, Y₀, hshift⟩ :=
    exists_uniform_roughFixedHead_smoothPhysicalBlock_shift_bound W
  refine ⟨K, hK, Y₀, ?_⟩
  intro lo split hi y alpha broad hY hWy hPlo
    hloSplit hSplitHi hlogHi
  let P : ℕ := roughHeadModulus W
  let B : ℝ := roughSmoothPhysicalBlock lo split hi y alpha broad
  have hexact := roughHeadFreeSmoothPhysicalBlock_eq_divisorShift
    (W := W) (lo := lo) (split := split) (hi := hi) (y := y)
      (α := alpha) (broad := broad) hWy
  have hsum :
      (∑ d ∈ P.divisors,
          (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) =
        roughHeadDensity W := by
    simpa only [P] using roughHead_moebius_inv_sum_eq_density W
  rw [hexact]
  change
    |(∑ d ∈ P.divisors,
        (ArithmeticFunction.moebius d : ℝ) *
          roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
            alpha broad) - roughHeadDensity W * B| ≤ _
  rw [← hsum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  have hterm : ∀ d ∈ P.divisors,
      |roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
          alpha broad - B / (d : ℝ)| ≤
        K *
            (|alpha| * ((hi : ℝ) + (split : ℝ)) +
              |broad| * ((split : ℝ) + (lo : ℝ))) /
          ((d : ℝ) * Real.log (y : ℝ)) +
        6 * (|alpha| + |broad|) := by
    intro d hdMem
    have hdDvd : d ∣ P := (Nat.mem_divisors.mp hdMem).1
    have hP : 0 < P := by
      simpa only [P] using roughHeadModulus_pos W
    have hdP : d ≤ P := Nat.le_of_dvd hP hdDvd
    have hdLo : d ≤ lo := hdP.trans (by simpa only [P] using hPlo)
    simpa only [P, B] using
      hshift hY (by simpa only [P] using hdMem) hdLo
        hloSplit hSplitHi hlogHi
  calc
    |∑ d ∈ P.divisors,
        ((ArithmeticFunction.moebius d : ℝ) *
            roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
              alpha broad -
          ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) * B)| =
      |∑ d ∈ P.divisors,
        (ArithmeticFunction.moebius d : ℝ) *
          (roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
            alpha broad - B / (d : ℝ))| := by
        congr 1
        apply Finset.sum_congr rfl
        intro d _hd
        ring
    _ ≤ ∑ d ∈ P.divisors,
        |(ArithmeticFunction.moebius d : ℝ) *
          (roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
            alpha broad - B / (d : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ P.divisors,
        |(ArithmeticFunction.moebius d : ℝ)| *
          |roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
            alpha broad - B / (d : ℝ)| := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [abs_mul]
    _ ≤ ∑ d ∈ P.divisors,
        |(ArithmeticFunction.moebius d : ℝ)| *
          (K *
              (|alpha| * ((hi : ℝ) + (split : ℝ)) +
                |broad| * ((split : ℝ) + (lo : ℝ))) /
            ((d : ℝ) * Real.log (y : ℝ)) +
          6 * (|alpha| + |broad|)) := by
      apply Finset.sum_le_sum
      intro d hdMem
      exact mul_le_mul_of_nonneg_left (hterm d hdMem) (abs_nonneg _)
    _ = ∑ d ∈ (roughHeadModulus W).divisors,
        |(ArithmeticFunction.moebius d : ℝ)| *
          (K *
              (|alpha| * ((hi : ℝ) + (split : ℝ)) +
                |broad| * ((split : ℝ) + (lo : ℝ))) /
            ((d : ℝ) * Real.log (y : ℝ)) +
          6 * (|alpha| + |broad|)) := by rfl

end

end Erdos390.WholePaper
