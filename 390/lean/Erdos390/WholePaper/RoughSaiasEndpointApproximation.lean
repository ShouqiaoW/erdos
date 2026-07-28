import Erdos390.WholePaper.RoughSaiasNormalization

/-!
# A closed inverse-log endpoint approximation for the Saias normal form

The repository already proves a uniform compact estimate for
`Psi(X,y) - X*rho(log X/log y)` and proves separately that
`|G_y-rho| <= 1/log y`.  Combining those two closed estimates gives a
concrete witness for `RoughSaiasEndpointApproximationUpToFive` with rate
`(K+1)/log y`.

This is an unconditional endpoint theorem about the already formalized
normal form.  It is deliberately not described as the sharper cited
Hildebrand--Tenenbaum--Saias estimate: its inverse-log rate is too large for
the final paper-scale absorption.  The exact reverse recurrence at the end
of this file isolates the normal-form prime-sum defect whose sharper control
would supply that missing gain.  The final section makes that claim precise:
an inverse-log-square bound for this explicit defect, together with the
already proved prime contraction, conditionally gives the paper-absorbable
endpoint rate `10*C/log(y)^2`.  Thus the coarse closed witness and the sole
sharp analytic input have different names and cannot be confused downstream.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## Named witnesses from the closed Dickman endpoint theorem -/

/-- A fixed constant in the existing compact uniform Dickman estimate. -/
noncomputable def roughSaiasDickmanEndpointConstant : ℝ :=
  Classical.choose
    FriableAsymptotic.exists_uniform_friableCount_dickman_bound_all_faces

theorem roughSaiasDickmanEndpointConstant_pos :
    0 < roughSaiasDickmanEndpointConstant :=
  (Classical.choose_spec
    FriableAsymptotic.exists_uniform_friableCount_dickman_bound_all_faces).1

/-- The corresponding fixed smoothness cutoff. -/
noncomputable def roughSaiasDickmanEndpointCutoff : ℕ :=
  Classical.choose
    (Classical.choose_spec
      FriableAsymptotic.exists_uniform_friableCount_dickman_bound_all_faces).2

theorem roughSaiasDickmanEndpoint_bound
    {X y : ℕ} (hY : roughSaiasDickmanEndpointCutoff ≤ y)
    (hX : 0 < X)
    (hlog : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |(FriableAsymptotic.friableCount X y : ℝ) -
        (X : ℝ) * rho (FriableAsymptotic.dickmanU X y)| ≤
      roughSaiasDickmanEndpointConstant * (X : ℝ) /
        Real.log (y : ℝ) :=
  (Classical.choose_spec
    (Classical.choose_spec
      FriableAsymptotic.exists_uniform_friableCount_dickman_bound_all_faces).2)
    hY hX hlog

/-- The explicit closed endpoint rate currently derivable in the project. -/
noncomputable def roughSaiasInvLogEndpointRate (y : ℕ) : ℝ :=
  (roughSaiasDickmanEndpointConstant + 1) / Real.log (y : ℝ)

/-! ## Identification with the formal normal form -/

/-- The genuine endpoint error is literally `Psi` minus the formal
`Lambda` normal form at a natural endpoint. -/
theorem roughSaiasEndpointError_eq_friableCount_sub_lambdaNormalForm
    (X y : ℕ) :
    roughSaiasEndpointError X y =
      (FriableAsymptotic.friableCount X y : ℝ) -
        roughSaiasLambdaNormalForm (X : ℝ) y := by
  unfold roughSaiasEndpointError
  rw [roughSaiasNaturalMain_eq_lambdaNormalForm]

/-! ## Closed endpoint envelope -/

/-- The isolated endpoint proposition has an unconditional inverse-log
witness.  This uses no endpoint approximation hypothesis. -/
theorem roughSaiasInvLogEndpointApproximationUpToFive :
    RoughSaiasEndpointApproximationUpToFive
      roughSaiasInvLogEndpointRate roughSaiasDickmanEndpointCutoff := by
  intro X y hY hy2 hX hlog
  let u : ℝ := FriableAsymptotic.dickmanU X y
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hu5 : u ≤ 5 := by
    dsimp only [u, FriableAsymptotic.dickmanU]
    exact (div_le_iff₀ hlogy).2 hlog
  have hmodel :
      |(FriableAsymptotic.friableCount X y : ℝ) -
          (X : ℝ) * rho u| ≤
        roughSaiasDickmanEndpointConstant * (X : ℝ) /
          Real.log (y : ℝ) := by
    simpa only [u] using roughSaiasDickmanEndpoint_bound hY hX hlog
  have hnormal :
      |roughSaiasG y u - rho u| ≤ 1 / Real.log (y : ℝ) :=
    roughSaiasG_sub_rho_abs_le_inv_log hy2 hu5
  have hcorrection :
      |(X : ℝ) * rho u - (X : ℝ) * roughSaiasG y u| ≤
        (X : ℝ) / Real.log (y : ℝ) := by
    calc
      |(X : ℝ) * rho u - (X : ℝ) * roughSaiasG y u| =
          (X : ℝ) * |roughSaiasG y u - rho u| := by
        rw [← mul_sub, abs_mul,
          abs_of_nonneg (Nat.cast_nonneg X), abs_sub_comm]
      _ ≤ (X : ℝ) * (1 / Real.log (y : ℝ)) :=
        mul_le_mul_of_nonneg_left hnormal (Nat.cast_nonneg X)
      _ = (X : ℝ) / Real.log (y : ℝ) := by ring
  unfold roughSaiasEndpointError roughSaiasNaturalMain
  change
    |(FriableAsymptotic.friableCount X y : ℝ) -
        (X : ℝ) * roughSaiasG y u| ≤
      roughSaiasInvLogEndpointRate y * (X : ℝ)
  calc
    |(FriableAsymptotic.friableCount X y : ℝ) -
        (X : ℝ) * roughSaiasG y u| ≤
      |(FriableAsymptotic.friableCount X y : ℝ) -
          (X : ℝ) * rho u| +
        |(X : ℝ) * rho u - (X : ℝ) * roughSaiasG y u| :=
      abs_sub_le _ _ _
    _ ≤ roughSaiasDickmanEndpointConstant * (X : ℝ) /
          Real.log (y : ℝ) +
        (X : ℝ) / Real.log (y : ℝ) :=
      add_le_add hmodel hcorrection
    _ = roughSaiasInvLogEndpointRate y * (X : ℝ) := by
      unfold roughSaiasInvLogEndpointRate
      ring

/-- The same closed estimate displayed directly against the formal
natural-endpoint `Lambda` normal form. -/
theorem roughSaiasLambdaNormalForm_endpoint_invLog_bound
    {X y : ℕ} (hY : roughSaiasDickmanEndpointCutoff ≤ y)
    (hy2 : 2 ≤ y) (hX : 0 < X)
    (hlog : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |(FriableAsymptotic.friableCount X y : ℝ) -
        roughSaiasLambdaNormalForm (X : ℝ) y| ≤
      roughSaiasInvLogEndpointRate y * (X : ℝ) := by
  rw [← roughSaiasEndpointError_eq_friableCount_sub_lambdaNormalForm]
  exact roughSaiasInvLogEndpointApproximationUpToFive
    hY hy2 hX hlog

/-! ## Exact reverse recurrence for the normal-form error -/

/-- Failure of the formal normal form to obey the reverse largest-prime
recurrence exactly.  Unlike the endpoint error itself, this is a completely
explicit prime-sum consistency defect. -/
noncomputable def roughSaiasReverseNormalFormDefect
    (X y Z : ℕ) : ℝ :=
  roughSaiasNaturalMain X Z - roughSaiasNaturalMain X y -
    ∑ p ∈ roughReversePrimeInterval y Z,
      roughSaiasNaturalMain (X / p) p

/-- Exact reverse recurrence: every counting term has disappeared except
for strictly smaller quotient endpoint errors.  Thus a sharp bound for the
explicit normal-form defect is the non-circular analytic input needed for a
stronger endpoint rate. -/
theorem roughSaiasEndpointError_reverseRecurrence
    {X y Z : ℕ} (hX : 0 < X) (hyZ : y ≤ Z) :
    roughSaiasEndpointError X y =
      roughSaiasEndpointError X Z -
        ∑ p ∈ roughReversePrimeInterval y Z,
          roughSaiasEndpointError (X / p) p +
        roughSaiasReverseNormalFormDefect X y Z := by
  have hrec := FriableAsymptotic.friableCount_prime_interval X hX hyZ
  have hrecReal := congrArg (fun n : ℕ => (n : ℝ)) hrec
  simp only [Nat.cast_add, Nat.cast_sum] at hrecReal
  unfold roughSaiasEndpointError roughSaiasReverseNormalFormDefect
  rw [Finset.sum_sub_distrib]
  dsimp only [roughReversePrimeInterval] at hrecReal ⊢
  linarith

/-- With the reverse cap at the endpoint, the top error is exactly zero. -/
theorem roughSaiasEndpointError_reverseRecurrence_top
    {X y : ℕ} (hX2 : 2 ≤ X) (hyX : y ≤ X) :
    roughSaiasEndpointError X y =
      roughSaiasReverseNormalFormDefect X y X -
        ∑ p ∈ roughReversePrimeInterval y X,
          roughSaiasEndpointError (X / p) p := by
  have hrec := roughSaiasEndpointError_reverseRecurrence
    (X := X) (y := y) (Z := X) (by omega) hyX
  have htop : roughSaiasEndpointError X X = 0 :=
    roughSaiasEndpointError_initial (by omega) (by omega) le_rfl
  rw [hrec, htop]
  ring

/-! ## The sole sharp analytic input and its endpoint consequence -/

/-- The inverse-log-square defect estimate needed for the paper-strength
endpoint envelope.  This proposition contains only the explicit normal form
`M(X,y)=X*G_y(log X/log y)` and a finite prime sum; in particular it contains
no friable count and no endpoint error. -/
def RoughSaiasReverseNormalFormDefectInvLogSqBound
    (C : ℝ) (Y₀ : ℕ) : Prop :=
  ∀ {X y : ℕ}, Y₀ ≤ y → 2 ≤ y → y < X →
    Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
    |roughSaiasReverseNormalFormDefect X y X| ≤
      C * (X : ℝ) / Real.log (y : ℝ) ^ 2

/-- A fixed threshold for the already proved reciprocal-log prime
contraction. -/
noncomputable def roughSaiasPrimeInvLogContractionCutoff : ℕ :=
  Classical.choose
    FriableAsymptotic.exists_primeInvLogSum_contraction_threshold

theorem roughSaiasPrimeInvLogContraction_bound
    {y X : ℕ} (hY : roughSaiasPrimeInvLogContractionCutoff ≤ y)
    (hyX : y < X)
    (hlog : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    FriableAsymptotic.primeInvLogSum y X ≤
      9 / (10 * Real.log (y : ℝ)) :=
  (Classical.choose_spec
    FriableAsymptotic.exists_primeInvLogSum_contraction_threshold)
    hY hyX hlog

/-- The extra reciprocal logarithm that appears in an inverse-log-square
endpoint induction. -/
noncomputable def roughSaiasPrimeInvLogSqSum (y X : ℕ) : ℝ :=
  ∑ p ∈ roughReversePrimeInterval y X,
    1 / ((p : ℝ) * Real.log (p : ℝ) ^ 2)

/-- The existing reciprocal-log contraction automatically contracts the
squared reciprocal-log kernel: on the prime interval `p>y`, the additional
factor `1/log p` is at most `1/log y`. -/
theorem roughSaiasPrimeInvLogSqSum_contraction
    {y X : ℕ} (hY : roughSaiasPrimeInvLogContractionCutoff ≤ y)
    (hy2 : 2 ≤ y) (hyX : y < X)
    (hlog : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    roughSaiasPrimeInvLogSqSum y X ≤
      9 / (10 * Real.log (y : ℝ) ^ 2) := by
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hcontract := roughSaiasPrimeInvLogContraction_bound hY hyX hlog
  have hcompare : roughSaiasPrimeInvLogSqSum y X ≤
      (1 / Real.log (y : ℝ)) *
        FriableAsymptotic.primeInvLogSum y X := by
    unfold roughSaiasPrimeInvLogSqSum
      FriableAsymptotic.primeInvLogSum
    dsimp only [roughReversePrimeInterval]
    calc
      (∑ p ∈ (X + 1).primesBelow \ (y + 1).primesBelow,
          1 / ((p : ℝ) * Real.log (p : ℝ) ^ 2)) ≤
        ∑ p ∈ (X + 1).primesBelow \ (y + 1).primesBelow,
          (1 / Real.log (y : ℝ)) *
            (1 / ((p : ℝ) * Real.log (p : ℝ))) := by
          apply Finset.sum_le_sum
          intro p hp
          have hpprime : p.Prime :=
            Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
          have hyp : y < p := by
            have hpout := (Finset.mem_sdiff.mp hp).2
            by_contra hnot
            apply hpout
            rw [Nat.mem_primesBelow]
            exact ⟨by omega, hpprime⟩
          have hlogp : 0 < Real.log (p : ℝ) :=
            Real.log_pos (by exact_mod_cast hpprime.one_lt)
          have hlogyp : Real.log (y : ℝ) ≤ Real.log (p : ℝ) :=
            Real.log_le_log (by positivity) (by exact_mod_cast hyp.le)
          have hinv : 1 / Real.log (p : ℝ) ≤
              1 / Real.log (y : ℝ) :=
            one_div_le_one_div_of_le hlogy hlogyp
          calc
            1 / ((p : ℝ) * Real.log (p : ℝ) ^ 2) =
                (1 / Real.log (p : ℝ)) *
                  (1 / ((p : ℝ) * Real.log (p : ℝ))) := by
              field_simp
            _ ≤ (1 / Real.log (y : ℝ)) *
                  (1 / ((p : ℝ) * Real.log (p : ℝ))) :=
              mul_le_mul_of_nonneg_right hinv (by positivity)
      _ = (1 / Real.log (y : ℝ)) *
          ∑ p ∈ (X + 1).primesBelow \ (y + 1).primesBelow,
            1 / ((p : ℝ) * Real.log (p : ℝ)) := by
        rw [Finset.mul_sum]
  calc
    roughSaiasPrimeInvLogSqSum y X ≤
        (1 / Real.log (y : ℝ)) *
          FriableAsymptotic.primeInvLogSum y X := hcompare
    _ ≤ (1 / Real.log (y : ℝ)) *
          (9 / (10 * Real.log (y : ℝ))) :=
      mul_le_mul_of_nonneg_left hcontract (by positivity)
    _ = 9 / (10 * Real.log (y : ℝ) ^ 2) := by
      field_simp

/-- The explicit inverse-log-square endpoint rate obtained from the sharp
normal-form defect. -/
noncomputable def roughSaiasInvLogSqEndpointRate
    (C : ℝ) (y : ℕ) : ℝ :=
  10 * C / Real.log (y : ℝ) ^ 2

/-- The original defect threshold enlarged only by the already closed prime
contraction threshold. -/
noncomputable def roughSaiasInvLogSqEndpointCutoff (Y₀ : ℕ) : ℕ :=
  max Y₀ roughSaiasPrimeInvLogContractionCutoff

/-- A sharp bound for the explicit normal-form prime defect is sufficient
for the paper-absorbable endpoint envelope.  The proof is a genuine strong
induction on `X`: the reverse recurrence reduces every error to `X/p<X`, and
the reciprocal-log-square prime sum contracts by `9/10`.

This is conditional only on
`RoughSaiasReverseNormalFormDefectInvLogSqBound`; it does not use the coarse
inverse-log endpoint theorem above as a sharp input. -/
theorem roughSaiasInvLogSqEndpointApproximationUpToFive_of_defect
    {C : ℝ} {Y₀ : ℕ} (hC : 0 ≤ C)
    (hdefect : RoughSaiasReverseNormalFormDefectInvLogSqBound C Y₀) :
    RoughSaiasEndpointApproximationUpToFive
      (roughSaiasInvLogSqEndpointRate C)
      (roughSaiasInvLogSqEndpointCutoff Y₀) := by
  intro X
  induction X using Nat.strong_induction_on with
  | h X ih =>
      intro y hY hy2 hX hlog
      have hmax : max Y₀ roughSaiasPrimeInvLogContractionCutoff ≤ y := by
        simpa only [roughSaiasInvLogSqEndpointCutoff] using hY
      have hY₀y : Y₀ ≤ y := (le_max_left _ _).trans hmax
      have hZcy : roughSaiasPrimeInvLogContractionCutoff ≤ y :=
        (le_max_right _ _).trans hmax
      have hlogy : 0 < Real.log (y : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < y by omega))
      by_cases hXy : X ≤ y
      · rw [roughSaiasEndpointError_initial hX (by omega) hXy, abs_zero]
        unfold roughSaiasInvLogSqEndpointRate
        positivity
      · have hyX : y < X := lt_of_not_ge hXy
        have hX2 : 2 ≤ X := hy2.trans hyX.le
        let K : ℝ := 10 * C
        have hK : 0 ≤ K := by
          dsimp only [K]
          positivity
        have hquotient : ∀ p ∈ roughReversePrimeInterval y X,
            |roughSaiasEndpointError (X / p) p| ≤
              K * ((X / p : ℕ) : ℝ) / Real.log (p : ℝ) ^ 2 := by
          intro p hp
          have hpprime : p.Prime := roughReversePrimeInterval_prime hp
          have hyp : y < p := roughReversePrimeInterval_gt_left hp
          have hpX : p ≤ X := roughReversePrimeInterval_le_right hp
          have hquotPos : 1 ≤ X / p :=
            (Nat.le_div_iff_mul_le hpprime.pos).2 (by simpa using hpX)
          have hquotLt : X / p < X :=
            Nat.div_lt_self hX hpprime.one_lt
          have hlogQuotX : Real.log ((X / p : ℕ) : ℝ) ≤
              Real.log (X : ℝ) := by
            apply Real.log_le_log (by exact_mod_cast hquotPos)
            exact_mod_cast Nat.div_le_self X p
          have hlogyp : Real.log (y : ℝ) ≤ Real.log (p : ℝ) :=
            Real.log_le_log (by positivity) (by exact_mod_cast hyp.le)
          have hlogQuot5 : Real.log ((X / p : ℕ) : ℝ) ≤
              5 * Real.log (p : ℝ) :=
            hlogQuotX.trans
              (hlog.trans
                (mul_le_mul_of_nonneg_left hlogyp (by norm_num)))
          have hih := ih (X / p) hquotLt (y := p)
            (hY.trans hyp.le) hpprime.two_le (by omega) hlogQuot5
          calc
            |roughSaiasEndpointError (X / p) p| ≤
                roughSaiasInvLogSqEndpointRate C p *
                  ((X / p : ℕ) : ℝ) := hih
            _ = K * ((X / p : ℕ) : ℝ) /
                  Real.log (p : ℝ) ^ 2 := by
              unfold roughSaiasInvLogSqEndpointRate
              dsimp only [K]
              ring
        have hsumAbs :
            |∑ p ∈ roughReversePrimeInterval y X,
                roughSaiasEndpointError (X / p) p| ≤
              ∑ p ∈ roughReversePrimeInterval y X,
                K * ((X / p : ℕ) : ℝ) /
                  Real.log (p : ℝ) ^ 2 := by
          calc
            |∑ p ∈ roughReversePrimeInterval y X,
                roughSaiasEndpointError (X / p) p| ≤
              ∑ p ∈ roughReversePrimeInterval y X,
                |roughSaiasEndpointError (X / p) p| :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ p ∈ roughReversePrimeInterval y X,
                K * ((X / p : ℕ) : ℝ) /
                  Real.log (p : ℝ) ^ 2 := by
              exact Finset.sum_le_sum hquotient
        have hsumScale :
            (∑ p ∈ roughReversePrimeInterval y X,
                K * ((X / p : ℕ) : ℝ) /
                  Real.log (p : ℝ) ^ 2) ≤
              K * (X : ℝ) * roughSaiasPrimeInvLogSqSum y X := by
          unfold roughSaiasPrimeInvLogSqSum
          calc
            (∑ p ∈ roughReversePrimeInterval y X,
                K * ((X / p : ℕ) : ℝ) /
                  Real.log (p : ℝ) ^ 2) ≤
              ∑ p ∈ roughReversePrimeInterval y X,
                K * (X : ℝ) *
                  (1 / ((p : ℝ) * Real.log (p : ℝ) ^ 2)) := by
              apply Finset.sum_le_sum
              intro p hp
              have hpprime : p.Prime := roughReversePrimeInterval_prime hp
              have hlogp : 0 < Real.log (p : ℝ) :=
                Real.log_pos (by exact_mod_cast hpprime.one_lt)
              have hcast : ((X / p : ℕ) : ℝ) ≤
                  (X : ℝ) / (p : ℝ) := Nat.cast_div_le
              calc
                K * ((X / p : ℕ) : ℝ) /
                    Real.log (p : ℝ) ^ 2 ≤
                  K * ((X : ℝ) / (p : ℝ)) /
                    Real.log (p : ℝ) ^ 2 := by
                  exact div_le_div_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hcast hK)
                    (sq_nonneg _)
                _ = K * (X : ℝ) *
                    (1 / ((p : ℝ) * Real.log (p : ℝ) ^ 2)) := by
                  field_simp
            _ = K * (X : ℝ) *
                ∑ p ∈ roughReversePrimeInterval y X,
                  1 / ((p : ℝ) * Real.log (p : ℝ) ^ 2) := by
              rw [Finset.mul_sum]
        have hsqContract : roughSaiasPrimeInvLogSqSum y X ≤
            9 / (10 * Real.log (y : ℝ) ^ 2) :=
          roughSaiasPrimeInvLogSqSum_contraction hZcy hy2 hyX hlog
        have hsumContract :
            (∑ p ∈ roughReversePrimeInterval y X,
                K * ((X / p : ℕ) : ℝ) /
                  Real.log (p : ℝ) ^ 2) ≤
              (9 / 10 * K) * (X : ℝ) /
                Real.log (y : ℝ) ^ 2 := by
          calc
            _ ≤ K * (X : ℝ) * roughSaiasPrimeInvLogSqSum y X :=
              hsumScale
            _ ≤ K * (X : ℝ) *
                (9 / (10 * Real.log (y : ℝ) ^ 2)) := by
              exact mul_le_mul_of_nonneg_left hsqContract
                (mul_nonneg hK (Nat.cast_nonneg X))
            _ = (9 / 10 * K) * (X : ℝ) /
                Real.log (y : ℝ) ^ 2 := by ring
        have hdefectBound :
            |roughSaiasReverseNormalFormDefect X y X| ≤
              C * (X : ℝ) / Real.log (y : ℝ) ^ 2 :=
          hdefect hY₀y hy2 hyX hlog
        have hrec := roughSaiasEndpointError_reverseRecurrence_top
          hX2 hyX.le
        rw [hrec]
        calc
          |roughSaiasReverseNormalFormDefect X y X -
              ∑ p ∈ roughReversePrimeInterval y X,
                roughSaiasEndpointError (X / p) p| ≤
            |roughSaiasReverseNormalFormDefect X y X| +
              |∑ p ∈ roughReversePrimeInterval y X,
                roughSaiasEndpointError (X / p) p| := abs_sub _ _
          _ ≤ C * (X : ℝ) / Real.log (y : ℝ) ^ 2 +
              ∑ p ∈ roughReversePrimeInterval y X,
                K * ((X / p : ℕ) : ℝ) /
                  Real.log (p : ℝ) ^ 2 :=
            add_le_add hdefectBound hsumAbs
          _ ≤ C * (X : ℝ) / Real.log (y : ℝ) ^ 2 +
              (9 / 10 * K) * (X : ℝ) /
                Real.log (y : ℝ) ^ 2 :=
            add_le_add_right hsumContract _
          _ = roughSaiasInvLogSqEndpointRate C y * (X : ℝ) := by
            unfold roughSaiasInvLogSqEndpointRate
            dsimp only [K]
            ring

/-- Direct display of the conditional sharp result against the formal
natural-endpoint `Lambda` normal form. -/
theorem roughSaiasLambdaNormalForm_endpoint_invLogSq_bound_of_defect
    {C : ℝ} {Y₀ X y : ℕ} (hC : 0 ≤ C)
    (hdefect : RoughSaiasReverseNormalFormDefectInvLogSqBound C Y₀)
    (hY : roughSaiasInvLogSqEndpointCutoff Y₀ ≤ y)
    (hy2 : 2 ≤ y) (hX : 0 < X)
    (hlog : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |(FriableAsymptotic.friableCount X y : ℝ) -
        roughSaiasLambdaNormalForm (X : ℝ) y| ≤
      roughSaiasInvLogSqEndpointRate C y * (X : ℝ) := by
  rw [← roughSaiasEndpointError_eq_friableCount_sub_lambdaNormalForm]
  exact roughSaiasInvLogSqEndpointApproximationUpToFive_of_defect
    hC hdefect hY hy2 hX hlog

end

end Erdos390.WholePaper
