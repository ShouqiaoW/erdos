import Erdos390.WholePaper.RoughSaiasRiemannAbsorption
import Erdos390.WholePaper.RoughSaiasQuotientBlocks
import Erdos390.WholePaper.RoughSaiasSharpVariation

/-!
# The sharp fully real correction target

The reverse defect splits directly into:

1. the ordinary Dickman continuous-integral versus prime-theta
   discrepancy, already closed by the existing Riemann and fourth-power
   PNT estimates; and
2. one fully real Saias correction integral versus its matching residual
   prime weight.

This is the minimal analytic target left after all exact base changes,
floor pairings, upper-selector cells, and standard Dickman estimates have
been discharged.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-- The fully real Saias correction after subtracting the ordinary Dickman
integrand. -/
noncomputable def roughSaiasFullyRealCorrectionIntegrand
    (X : ℕ) (s : ℝ) : ℝ :=
  roughSaiasFullyRealBuchstabNormalIntegrand X s -
    FriableAsymptotic.dickmanContinuousWeight (X : ℝ) s

/-- The one remaining correction discrepancy: continuous fully real
correction versus its exactly paired natural-minus-Dickman prime weight. -/
noncomputable def roughSaiasSharpCorrectionObstruction
    (X y Z : ℕ) : ℝ :=
  (∫ s in (y : ℝ)..(Z : ℝ),
      roughSaiasFullyRealCorrectionIntegrand X s) -
    FriableAsymptotic.primeThetaWeightedInterval
      (roughSaiasNaturalMinusDickmanThetaWeight X) y Z

/-- The closed ordinary Dickman continuous-versus-prime discrepancy. -/
noncomputable def roughSaiasDickmanContinuousPrimeDiscrepancy
    (X y Z : ℕ) : ℝ :=
  (∫ s in (y : ℝ)..(Z : ℝ),
      FriableAsymptotic.dickmanContinuousWeight (X : ℝ) s) -
    FriableAsymptotic.primeThetaWeightedInterval
      (FriableAsymptotic.dickmanThetaWeight X) y Z

/-- The irreducible signed discrepancy on the unit cell `[m,m+1]`: its
paired natural quadrature remainder is kept together with the local
prime-minus-integer mass at the same right endpoint. -/
noncomputable def roughSaiasLocalNaturalPrimeCellDiscrepancy
    (X m : ℕ) : ℝ :=
  roughSaiasFullyRealNaturalBuchstabCellRemainder X m -
    roughSaiasNaturalQuotientThetaWeight X (m + 1) *
      (FriableAsymptotic.primeLogIncrement (m + 1) - 1)

/-- Uniformly spread one lower-cell discrepancy over its dual hyperbola
interval.  Below `sqrt X` that interval is nonempty, so summing this average
over the interval recovers the original cell exactly. -/
noncomputable def roughSaiasDualSpreadLocalNaturalPrimeCellDiscrepancy
    (X m : ℕ) : ℝ :=
  roughSaiasLocalNaturalPrimeCellDiscrepancy X m /
    ((roughSaiasDualQuotientInterval X m).card : ℝ)

/-- Uniform dual spread of the purely fully-real natural-cell remainder.
After the global theta transfer is estimated, this is the only lower-block
quantity left; below `sqrt X` its dual average recovers the cell exactly. -/
noncomputable def roughSaiasDualSpreadFullyRealNaturalCellRemainder
    (X m : ℕ) : ℝ :=
  roughSaiasFullyRealNaturalBuchstabCellRemainder X m /
    ((roughSaiasDualQuotientInterval X m).card : ℝ)

/-- Literal formula for the fully real correction integrand. -/
theorem roughSaiasFullyRealCorrectionIntegrand_eq
    {X : ℕ} {s : ℝ} (hX : 0 < X) (hs : 1 < s) :
    roughSaiasFullyRealCorrectionIntegrand X s =
      (((X : ℝ) / s) *
          (roughSaiasFullyRealG s
              (Real.log ((X : ℝ) / s) / Real.log s) -
            rho (Real.log (X : ℝ) / Real.log s - 1)) -
        Int.fract ((X : ℝ) / s)) /
      Real.log s := by
  have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
  have hspos : 0 < s := zero_lt_one.trans hs
  unfold roughSaiasFullyRealCorrectionIntegrand
    roughSaiasFullyRealBuchstabNormalIntegrand
    roughSaiasFullyRealLambdaNormalForm
    FriableAsymptotic.dickmanContinuousWeight
  ring

/-- Exact decomposition of the full reverse defect into the closed Dickman
core and the single sharp correction obstruction. -/
theorem roughSaiasReverseNormalFormDefect_eq_dickman_add_sharpCorrection
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasReverseNormalFormDefect X y Z =
      roughSaiasDickmanContinuousPrimeDiscrepancy X y Z +
        roughSaiasSharpCorrectionObstruction X y Z := by
  have hyZle : y ≤ Z := hyZ.le
  have hf := intervalIntegrable_roughSaiasFullyRealBuchstabNormalIntegrand
    hy2 hyZle hZX hu5
  have hyone : (1 : ℝ) < (y : ℝ) := by
    exact_mod_cast (show 1 < y by omega)
  have hdcont : ContinuousOn
      (FriableAsymptotic.dickmanContinuousWeight (X : ℝ))
      (Set.Icc (y : ℝ) (Z : ℝ)) :=
    (FriableAsymptotic.continuousOn_dickmanContinuousWeight (X : ℝ)).mono
      (fun s hs ↦ by
        rw [Set.mem_Ioi]
        exact hyone.trans_le hs.1)
  have hd : IntervalIntegrable
      (FriableAsymptotic.dickmanContinuousWeight (X : ℝ))
      MeasureTheory.volume (y : ℝ) (Z : ℝ) := by
    rw [← Set.uIcc_of_le (by exact_mod_cast hyZle)] at hdcont
    exact hdcont.intervalIntegrable
  have hintegral := intervalIntegral.integral_sub hf hd
  have hprime :
      FriableAsymptotic.primeThetaWeightedInterval
          (roughSaiasNaturalQuotientThetaWeight X) y Z =
        FriableAsymptotic.primeThetaWeightedInterval
            (FriableAsymptotic.dickmanThetaWeight X) y Z +
          FriableAsymptotic.primeThetaWeightedInterval
            (roughSaiasNaturalMinusDickmanThetaWeight X) y Z := by
    unfold FriableAsymptotic.primeThetaWeightedInterval
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    unfold roughSaiasNaturalMinusDickmanThetaWeight
    ring
  have hbuch := roughSaiasNaturalMain_buchstab_fullyReal
    hy2 hyZle hZX hu5
  have hprimeNatural :=
    roughSaiasPrimeThetaWeightedInterval_eq_naturalSum X y Z
  unfold roughSaiasReverseNormalFormDefect
    roughSaiasDickmanContinuousPrimeDiscrepancy
    roughSaiasSharpCorrectionObstruction
    roughSaiasFullyRealCorrectionIntegrand
  rw [← hprimeNatural, hprime]
  rw [hintegral]
  linarith

/-- The closed Dickman continuous-prime discrepancy is exactly its ordinary
right-endpoint Riemann error minus the Dickman theta transfer. -/
theorem roughSaiasDickmanContinuousPrimeDiscrepancy_eq_riemann_sub_theta
    (X y Z : ℕ) (hyZ : y < Z) :
    roughSaiasDickmanContinuousPrimeDiscrepancy X y Z =
      roughSaiasDickmanBuchstabBlockRemainder X y Z -
        (FriableAsymptotic.primeThetaWeightedInterval
            (FriableAsymptotic.dickmanThetaWeight X) y Z -
          FriableAsymptotic.integerAbelMain
            (FriableAsymptotic.dickmanThetaWeight X) y Z) := by
  unfold roughSaiasDickmanContinuousPrimeDiscrepancy
    roughSaiasDickmanBuchstabBlockRemainder
  rw [FriableAsymptotic.integerAbelMain_eq_sum_Ioc _ hyZ]
  ring

/-- Exact add/subtract form of the one remaining sharp correction.  It is
the signed sum of the paired natural cells, minus the ordinary Dickman
Riemann error, minus the natural-minus-Dickman theta transfer.  In
particular, the lower cells and residual transfer remain paired before any
absolute value is taken. -/
theorem roughSaiasSharpCorrectionObstruction_eq_naturalCells_sub_riemann_sub_residual
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasSharpCorrectionObstruction X y Z =
      (∑ m ∈ Finset.Ico y Z,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m) -
      roughSaiasDickmanBuchstabBlockRemainder X y Z -
      roughSaiasNaturalMinusDickmanThetaTransfer X y Z := by
  have hsharp :=
    roughSaiasReverseNormalFormDefect_eq_dickman_add_sharpCorrection
      hy2 hyZ hZX hu5
  have hcells :=
    roughSaiasReverseNormalFormDefect_eq_naturalCells_sub_naturalTheta
      hy2 hyZ hZX hu5
  have htheta :=
    roughSaiasNaturalThetaErrorTransfer_eq_dickman_add_residual
      (X := X) hyZ
  have hdickman :=
    roughSaiasDickmanContinuousPrimeDiscrepancy_eq_riemann_sub_theta
      X y Z hyZ
  linarith

/-- Fully local form of the reverse defect after weighted boundary
cancellation.  All finite-Abel endpoints, stable quotient blocks, and jump
boundaries have cancelled; what remains is the signed pairing of the natural
cell remainders with one local prime-minus-integer mass sum. -/
theorem roughSaiasReverseNormalFormDefect_eq_naturalCells_sub_localPrimeErrorResidual
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasReverseNormalFormDefect X y Z =
      (∑ m ∈ Finset.Ico y Z,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m) -
      ∑ m ∈ Finset.Ioc y Z,
        roughSaiasNaturalQuotientThetaWeight X m *
          (FriableAsymptotic.primeLogIncrement m - 1) := by
  rw [roughSaiasReverseNormalFormDefect_eq_naturalCells_sub_naturalTheta
      hy2 hyZ hZX hu5,
    roughSaiasNaturalThetaErrorTransfer_eq_localPrimeErrorResidual hyZ]

/-- Cellwise form of the preceding identity.  The natural-cell remainder
and local prime mass are paired before either absolute value is taken. -/
theorem roughSaiasReverseNormalFormDefect_eq_sum_localNaturalPrimeCellDiscrepancy
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasReverseNormalFormDefect X y Z =
      ∑ m ∈ Finset.Ico y Z,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m := by
  rw [roughSaiasReverseNormalFormDefect_eq_naturalCells_sub_localPrimeErrorResidual
      hy2 hyZ hZX hu5,
    FriableAsymptotic.sum_Ioc_shift, ← Finset.sum_sub_distrib]
  rfl

/-- Exact adjacent split of the fully paired local discrepancy. -/
theorem sum_roughSaiasLocalNaturalPrimeCellDiscrepancy_split
    (X : ℕ) {y M Z : ℕ} (hyM : y ≤ M) (hMZ : M ≤ Z) :
    (∑ m ∈ Finset.Ico y Z,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m) =
      (∑ m ∈ Finset.Ico y M,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m) +
      ∑ m ∈ Finset.Ico M Z,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m := by
  rw [← Finset.sum_Ico_consecutive _ hyM hMZ]

/-- A lower cell is exactly recovered by summing its uniform dual spread.
The denominator is the nonzero quotient drop
`X/m-X/(m+1)`. -/
theorem sum_roughSaiasDualSpreadLocalNaturalPrimeCellDiscrepancy_eq
    {X m : ℕ} (hm : 0 < m) (hmsqrt : m ≤ Nat.sqrt X) :
    (∑ _q ∈ roughSaiasDualQuotientInterval X m,
        roughSaiasDualSpreadLocalNaturalPrimeCellDiscrepancy X m) =
      roughSaiasLocalNaturalPrimeCellDiscrepancy X m := by
  have hnonempty :=
    roughSaiasDualQuotientInterval_nonempty_of_le_sqrt hm hmsqrt
  have hcardPos : 0 < (roughSaiasDualQuotientInterval X m).card :=
    Finset.card_pos.mpr hnonempty
  have hcardNe :
      (((roughSaiasDualQuotientInterval X m).card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcardPos)
  unfold roughSaiasDualSpreadLocalNaturalPrimeCellDiscrepancy
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_div_cancel₀ _ hcardNe

/-- Exact hyperbola involution for a whole lower block.  It replaces the
lower index `m ∈ [y,M)` by the upper dual index
`q ∈ (X/M,X/y]`, with `m=X/q` in every summand. -/
theorem sum_roughSaiasLocalNaturalPrimeCellDiscrepancy_eq_dualInvolution
    {X y M : ℕ} (hy : 0 < y) (hyM : y ≤ M)
    (hM : M ≤ Nat.sqrt X + 1) :
    (∑ m ∈ Finset.Ico y M,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m) =
      ∑ q ∈ Finset.Ioc (X / M) (X / y),
        roughSaiasDualSpreadLocalNaturalPrimeCellDiscrepancy X (X / q) := by
  calc
    (∑ m ∈ Finset.Ico y M,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m) =
      ∑ m ∈ Finset.Ico y M,
        ∑ q ∈ roughSaiasDualQuotientInterval X m,
          roughSaiasDualSpreadLocalNaturalPrimeCellDiscrepancy X m := by
            apply Finset.sum_congr rfl
            intro m hmI
            have hmData := Finset.mem_Ico.mp hmI
            symm
            exact
              sum_roughSaiasDualSpreadLocalNaturalPrimeCellDiscrepancy_eq
                (hy.trans_le hmData.1) (by omega)
    _ = ∑ q ∈ Finset.Ioc (X / M) (X / y),
        roughSaiasDualSpreadLocalNaturalPrimeCellDiscrepancy X (X / q) :=
      sum_Ico_sum_roughSaiasDualQuotientInterval_involution
        (fun m _q =>
          roughSaiasDualSpreadLocalNaturalPrimeCellDiscrepancy X m)
        X hy hyM

/-- A purely fully-real lower cell is recovered by summing its uniform
dual spread over the nonempty quotient-drop interval. -/
theorem sum_roughSaiasDualSpreadFullyRealNaturalCellRemainder_eq
    {X m : ℕ} (hm : 0 < m) (hmsqrt : m ≤ Nat.sqrt X) :
    (∑ _q ∈ roughSaiasDualQuotientInterval X m,
        roughSaiasDualSpreadFullyRealNaturalCellRemainder X m) =
      roughSaiasFullyRealNaturalBuchstabCellRemainder X m := by
  have hnonempty :=
    roughSaiasDualQuotientInterval_nonempty_of_le_sqrt hm hmsqrt
  have hcardPos : 0 < (roughSaiasDualQuotientInterval X m).card :=
    Finset.card_pos.mpr hnonempty
  have hcardNe :
      (((roughSaiasDualQuotientInterval X m).card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcardPos)
  unfold roughSaiasDualSpreadFullyRealNaturalCellRemainder
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_div_cancel₀ _ hcardNe

/-- Exact hyperbola involution for the purely fully-real lower-cell block.
Thus, once the theta transfer is closed, the residual is literally an
average over the upper dual interval `(X/M,X/y]`. -/
theorem sum_roughSaiasFullyRealNaturalCells_eq_dualInvolution
    {X y M : ℕ} (hy : 0 < y) (hyM : y ≤ M)
    (hM : M ≤ Nat.sqrt X + 1) :
    (∑ m ∈ Finset.Ico y M,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m) =
      ∑ q ∈ Finset.Ioc (X / M) (X / y),
        roughSaiasDualSpreadFullyRealNaturalCellRemainder X (X / q) := by
  calc
    (∑ m ∈ Finset.Ico y M,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m) =
      ∑ m ∈ Finset.Ico y M,
        ∑ q ∈ roughSaiasDualQuotientInterval X m,
          roughSaiasDualSpreadFullyRealNaturalCellRemainder X m := by
            apply Finset.sum_congr rfl
            intro m hmI
            have hmData := Finset.mem_Ico.mp hmI
            symm
            exact
              sum_roughSaiasDualSpreadFullyRealNaturalCellRemainder_eq
                (hy.trans_le hmData.1) (by omega)
    _ = ∑ q ∈ Finset.Ioc (X / M) (X / y),
        roughSaiasDualSpreadFullyRealNaturalCellRemainder X (X / q) :=
      sum_Ico_sum_roughSaiasDualQuotientInterval_involution
        (fun m _q =>
          roughSaiasDualSpreadFullyRealNaturalCellRemainder X m)
        X hy hyM

/-! ## Closing the lower fully-real quadrature -/

/-- The signed real-quotient endpoint correction is uniformly bounded by
`20/log n` on every compact five-face block.  The only nontrivial point is
that multiplication by the integer quotient cancels the logarithmic gap
between `X/n` and `floor(X/n)`. -/
private theorem roughSaiasFractionalCorrectionThetaWeight_abs_le_twenty_inv_log
    {X a n : ℕ} (hX : 0 < X) (ha3 : 3 ≤ a) (han : a ≤ n)
    (hnX : n ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    |roughSaiasFractionalCorrectionThetaWeight X n| ≤
      20 / Real.log (n : ℝ) := by
  let r : ℝ := (X : ℝ) / (n : ℝ)
  let q : ℝ := ((X / n : ℕ) : ℝ)
  let u : ℝ := Real.log r / Real.log (n : ℝ)
  let v : ℝ := Real.log q / Real.log (n : ℝ)
  have hnOne : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hnpos : 0 < (n : ℝ) := zero_lt_one.trans hnOne
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hnOne
  have hlognOne : 1 ≤ Real.log (n : ℝ) := by
    have hexp : Real.exp 1 < (n : ℝ) :=
      Real.exp_one_lt_three.trans_le (by exact_mod_cast (ha3.trans han))
    exact ((Real.lt_log_iff_exp_lt hnpos).2 hexp).le
  have hqNat : 1 ≤ X / n := Nat.div_pos hnX (by omega)
  have hqpos : 0 < q := by
    dsimp only [q]
    positivity
  have hrpos : 0 < r := by
    dsimp only [r]
    positivity
  have hfloor : r - Int.fract r = q := by
    simpa only [r, q] using roughSaiasRealQuotient_sub_fract_eq_natQuotient X n
  have hrEq : r = q + Int.fract r := by linarith
  have hqr : q ≤ r := by
    rw [hrEq]
    exact le_add_of_nonneg_right (Int.fract_nonneg r)
  have hsubNonneg : 0 ≤ r - q := sub_nonneg.mpr hqr
  have hsubOne : r - q ≤ 1 := by
    rw [hrEq]
    simpa only [add_sub_cancel_left] using (Int.fract_lt_one r).le
  have hlogGapNonneg : 0 ≤ Real.log r - Real.log q :=
    sub_nonneg.mpr (Real.log_le_log hqpos hqr)
  have hlogGap : Real.log r - Real.log q ≤ 1 / q := by
    have hratioPos : 0 < r / q := div_pos hrpos hqpos
    have hlogRatio := Real.log_le_sub_one_of_pos hratioPos
    calc
      Real.log r - Real.log q = Real.log (r / q) := by
        rw [Real.log_div hrpos.ne' hqpos.ne']
      _ ≤ r / q - 1 := hlogRatio
      _ = (r - q) / q := by
        rw [sub_div, div_self hqpos.ne']
      _ ≤ 1 / q := div_le_div_of_nonneg_right hsubOne hqpos.le
  have hu0 : 0 ≤ u := by
    have hrOne : 1 ≤ r := by
      dsimp only [r]
      exact (one_le_div hnpos).2 (by exact_mod_cast hnX)
    exact div_nonneg (Real.log_nonneg hrOne) hlogn.le
  have hqOne : (1 : ℝ) ≤ q := by
    dsimp only [q]
    exact_mod_cast hqNat
  have hv0 : 0 ≤ v :=
    div_nonneg (Real.log_nonneg hqOne) hlogn.le
  have hvu : v ≤ u := by
    dsimp only [u, v]
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hqpos hqr) hlogn.le
  have hu5' : u ≤ 5 := by
    have ha2 : 2 ≤ a := by omega
    have hanR : (a : ℝ) ≤ (n : ℝ) := by exact_mod_cast han
    have hnXR : (n : ℝ) ≤ (X : ℝ) := by exact_mod_cast hnX
    have hface := roughSaiasFullyRealHyperbolaCoordinate_le_five
      hX ha2 hanR hnXR
        (t := (1 : ℝ)) (by norm_num) hu5
    simpa only [u, r, roughSaiasFullyRealHyperbolaCoordinate,
      Real.log_one, sub_zero] using hface
  have hv5 : v ≤ 5 := hvu.trans hu5'
  have huvAbs : |u - v| ≤ 1 / q := by
    rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
    have hdiff : u - v =
        (Real.log r - Real.log q) / Real.log (n : ℝ) := by
      dsimp only [u, v]
      ring
    rw [hdiff]
    calc
      (Real.log r - Real.log q) / Real.log (n : ℝ) ≤
          (1 / q) / Real.log (n : ℝ) :=
        div_le_div_of_nonneg_right hlogGap hlogn.le
      _ ≤ 1 / q := by
        have hqInvNonneg : 0 ≤ 1 / q := by positivity
        apply (div_le_iff₀ hlogn).2
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hlognOne hqInvNonneg)
  have hGdiff : |roughSaiasG n u - roughSaiasG n v| ≤ 3 * |u - v| := by
    simpa only [roughSaiasFullyRealG_nat] using
      (roughSaiasFullyRealG_lipschitz_three hnOne
        (show u ∈ Set.Icc (0 : ℝ) 5 from ⟨hu0, hu5'⟩)
        (show v ∈ Set.Icc (0 : ℝ) 5 from ⟨hv0, hv5⟩))
  have hqG : q * |roughSaiasG n u - roughSaiasG n v| ≤ 3 := by
    calc
      q * |roughSaiasG n u - roughSaiasG n v| ≤ q * (3 * |u - v|) :=
        mul_le_mul_of_nonneg_left hGdiff hqpos.le
      _ ≤ q * (3 * (1 / q)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left huvAbs (by norm_num)) hqpos.le
      _ = 3 := by field_simp [hqpos.ne']
  have hGu : |roughSaiasG n u| ≤ 16 := by
    simpa only [roughSaiasFullyRealG_nat] using
      (roughSaiasFullyRealG_abs_le_sixteen hnOne
        (show u ∈ Set.Icc (0 : ℝ) 5 from ⟨hu0, hu5'⟩))
  have hfractTerm :
      |Int.fract r * (roughSaiasG n u - 1)| ≤ 17 := by
    rw [abs_mul, abs_of_nonneg (Int.fract_nonneg r)]
    have hGminus : |roughSaiasG n u - 1| ≤ |roughSaiasG n u| + 1 := by
      simpa only [abs_one] using (abs_sub (roughSaiasG n u) 1)
    calc
      Int.fract r * |roughSaiasG n u - 1| ≤
          1 * |roughSaiasG n u - 1| :=
        mul_le_mul_of_nonneg_right (Int.fract_lt_one r).le (abs_nonneg _)
      _ ≤ 1 * (|roughSaiasG n u| + 1) :=
        mul_le_mul_of_nonneg_left hGminus (by norm_num)
      _ ≤ 1 * (16 + 1) := by gcongr
      _ = 17 := by norm_num
  have hterm :
      |q * (roughSaiasG n u - roughSaiasG n v) +
          Int.fract r * (roughSaiasG n u - 1)| ≤ 20 := by
    calc
      |q * (roughSaiasG n u - roughSaiasG n v) +
          Int.fract r * (roughSaiasG n u - 1)| ≤
        |q * (roughSaiasG n u - roughSaiasG n v)| +
          |Int.fract r * (roughSaiasG n u - 1)| := abs_add_le _ _
      _ = q * |roughSaiasG n u - roughSaiasG n v| +
          |Int.fract r * (roughSaiasG n u - 1)| := by
        rw [abs_mul, abs_of_pos hqpos]
      _ ≤ 3 + 17 := add_le_add hqG hfractTerm
      _ = 20 := by norm_num
  unfold roughSaiasFractionalCorrectionThetaWeight
    roughSaiasSignedFractionalCorrectionTerm
  change |(q * (roughSaiasG n u - roughSaiasG n v) +
      Int.fract r * (roughSaiasG n u - 1)) / Real.log (n : ℝ)| ≤ _
  rw [abs_div, abs_of_pos hlogn]
  exact div_le_div_of_nonneg_right hterm hlogn.le

/-- Literal rho-minus-fractional-integral form of the fully real Buchstab
integrand. -/
private theorem roughSaiasFullyRealBuchstabNormalIntegrand_eq_rho_sub_fractional
    {X : ℕ} {s : ℝ} (hs : 1 < s) :
    roughSaiasFullyRealBuchstabNormalIntegrand X s =
      ((X : ℝ) / (s * Real.log s)) *
          (rho (Real.log ((X : ℝ) / s) / Real.log s) -
            roughSaiasFullyRealBaseFreeFractionalIntegral ((X : ℝ) / s) s) -
        Int.fract ((X : ℝ) / s) / Real.log s := by
  unfold roughSaiasFullyRealBuchstabNormalIntegrand
    roughSaiasFullyRealLambdaNormalForm
  rw [roughSaiasFullyRealG_eq_rho_sub_baseFree hs]
  ring

/-- The rho component has total variation at most one along the real
natural-endpoint hyperbola path. -/
private theorem sum_abs_rho_fullyRealHyperbolaLogRatio_succ_sub_le_one
    {X a b : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a) (hab : a ≤ b)
    (hbX : b ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |rho (Real.log ((X : ℝ) / (m + 1 : ℕ)) /
              Real.log ((m + 1 : ℕ) : ℝ)) -
          rho (Real.log ((X : ℝ) / (m : ℝ)) /
              Real.log (m : ℝ))|) ≤ 1 := by
  let u : ℕ → ℝ := fun m =>
    Real.log ((X : ℝ) / (m : ℝ)) / Real.log (m : ℝ)
  have huBounds : ∀ m ∈ Finset.Icc a b, u m ∈ Set.Icc (0 : ℝ) 5 := by
    intro m hm
    have hmData := Finset.mem_Icc.mp hm
    have hmOne : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    have hmX : m ≤ X := hmData.2.trans hbX
    have hu0 : 0 ≤ u m := by
      dsimp only [u]
      exact div_nonneg
        (Real.log_nonneg ((one_le_div (by positivity)).2 (by exact_mod_cast hmX)))
        (Real.log_pos hmOne).le
    have hamR : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmData.1
    have hmXR : (m : ℝ) ≤ (X : ℝ) := by exact_mod_cast hmX
    have hu5m := roughSaiasFullyRealHyperbolaCoordinate_le_five
      hX ha2 hamR hmXR
        (t := (1 : ℝ)) (by norm_num) hu5
    have : u m ≤ 5 := by
      simpa only [u, roughSaiasFullyRealHyperbolaCoordinate,
        Real.log_one, sub_zero] using hu5m
    exact ⟨hu0, this⟩
  have huMono : ∀ m ∈ Finset.Ico a b, u (m + 1) ≤ u m := by
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    have hmOne : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    have hnextOne : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 < m + 1 by omega)
    have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hmOne
    have hlogNext : 0 < Real.log ((m + 1 : ℕ) : ℝ) := Real.log_pos hnextOne
    have hlogLe : Real.log (m : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (Nat.le_succ m))
    have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
    have hXR : (X : ℝ) ≠ 0 := by positivity
    have hmNe : (m : ℝ) ≠ 0 := by positivity
    have hnextNe : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    dsimp only [u]
    rw [Real.log_div hXR hnextNe, Real.log_div hXR hmNe]
    have hratio := div_le_div_of_nonneg_left hlogX0 hlogm hlogLe
    calc
      (Real.log (X : ℝ) - Real.log ((m + 1 : ℕ) : ℝ)) /
          Real.log ((m + 1 : ℕ) : ℝ) =
        Real.log (X : ℝ) / Real.log ((m + 1 : ℕ) : ℝ) - 1 := by
          field_simp [hlogNext.ne']
      _ ≤ Real.log (X : ℝ) / Real.log (m : ℝ) - 1 :=
        sub_le_sub_right hratio 1
      _ = (Real.log (X : ℝ) - Real.log (m : ℝ)) /
          Real.log (m : ℝ) := by
        field_simp [hlogm.ne']
  have hrhoMono : ∀ m ∈ Finset.Ico a b, rho (u m) ≤ rho (u (m + 1)) := by
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    exact roughRho_antitoneOn_zero_five
      (huBounds (m + 1) (by rw [Finset.mem_Icc]; omega))
      (huBounds m (by rw [Finset.mem_Icc]; omega))
      (huMono m hm)
  have htelescope :
      (∑ m ∈ Finset.Ico a b, |rho (u (m + 1)) - rho (u m)|) =
        rho (u b) - rho (u a) := by
    calc
      (∑ m ∈ Finset.Ico a b, |rho (u (m + 1)) - rho (u m)|) =
          ∑ m ∈ Finset.Ico a b, (rho (u (m + 1)) - rho (u m)) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [abs_of_nonneg (sub_nonneg.mpr (hrhoMono m hm))]
      _ = rho (u b) - rho (u a) := by
        exact Finset.sum_Ico_sub (fun m => rho (u m)) hab
  have hrhoA0 : 0 ≤ rho (u a) :=
    (rho_pos_on_zero_five (huBounds a (by simp [hab])).1
      (huBounds a (by simp [hab])).2).le
  have hrhoB1 : rho (u b) ≤ 1 :=
    FriableAsymptotic.rho_le_one_of_le_five
      (huBounds b (by simp [hab])).2
  change (∑ m ∈ Finset.Ico a b,
    |rho (u (m + 1)) - rho (u m)|) ≤ 1
  rw [htelescope]
  linarith [hrhoA0, hrhoB1]

set_option maxHeartbeats 800000 in
/-- Pointwise right-endpoint quadrature bound for the full fully-real
Buchstab integrand on a lower natural cell.  Its four terms are,
respectively, coefficient drift, rho variation, the real-hyperbola
fractional-integral ledger, and the harmless bounded sawtooth endpoint. -/
private theorem roughSaiasFullyRealBuchstabNormalIntegrand_cell_abs_sub_right_le
    {X a b m : ℕ} (hX : 0 < X) (ha3 : 3 ≤ a) (hab : a ≤ b)
    (hbX : b ≤ X) (hm : m ∈ Finset.Ico a b)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5)
    {s : ℝ} (hs : s ∈ Set.Icc (m : ℝ) (m + 1 : ℕ)) :
    |roughSaiasFullyRealBuchstabNormalIntegrand X s -
        roughSaiasFullyRealBuchstabNormalIntegrand X (m + 1 : ℕ)| ≤
      16 *
          ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ)) -
            (X : ℝ) /
              (((m + 1 : ℕ) : ℝ) * Real.log ((m + 1 : ℕ) : ℝ))) +
        ((X : ℝ) / ((a : ℝ) * Real.log (a : ℝ))) *
          ((rho (Real.log ((X : ℝ) / (m + 1 : ℕ)) /
                  Real.log ((m + 1 : ℕ) : ℝ)) -
              rho (Real.log ((X : ℝ) / (m : ℝ)) /
                  Real.log (m : ℝ))) +
            roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger
              X a m) +
        2 / Real.log (m : ℝ) := by
  let A : ℝ → ℝ := fun r => (X : ℝ) / (r * Real.log r)
  let u : ℝ → ℝ := fun r => Real.log ((X : ℝ) / r) / Real.log r
  let J : ℝ → ℝ := fun r =>
    roughSaiasFullyRealBaseFreeFractionalIntegral ((X : ℝ) / r) r
  let H : ℝ → ℝ := fun r => rho (u r) - J r
  let P : ℝ → ℝ := fun r => Int.fract ((X : ℝ) / r) / Real.log r
  let n : ℝ := ((m + 1 : ℕ) : ℝ)
  have hmData := Finset.mem_Ico.mp hm
  have hm3 : 3 ≤ m := ha3.trans hmData.1
  have hnextX : m + 1 ≤ X := by omega
  have haOne : (1 : ℝ) < (a : ℝ) := by exact_mod_cast (show 1 < a by omega)
  have hmOne : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hsOne : 1 < s := hmOne.trans_le hs.1
  have hnOne : 1 < n := by
    dsimp only [n]
    exact_mod_cast (show 1 < m + 1 by omega)
  have hloga : 0 < Real.log (a : ℝ) := Real.log_pos haOne
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hmOne
  have hlogs : 0 < Real.log s := Real.log_pos hsOne
  have hlogn : 0 < Real.log n := Real.log_pos hnOne
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast hX
  have has : (a : ℝ) ≤ s :=
    (by exact_mod_cast hmData.1 : (a : ℝ) ≤ (m : ℝ)).trans hs.1
  have hsn : s ≤ n := by simpa only [n] using hs.2
  have hnX : n ≤ (X : ℝ) := by
    dsimp only [n]
    exact_mod_cast hnextX
  have ha2 : 2 ≤ a := by omega
  have hamR : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmData.1
  have hmXR : (m : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast (show m ≤ X by omega)
  have hfaceM := roughSaiasFullyRealHyperbolaCoordinate_le_five
    hX ha2 hamR hmXR
      (t := (1 : ℝ)) (by norm_num) hu5
  have hfaceS := roughSaiasFullyRealHyperbolaCoordinate_le_five
    hX ha2 has (hsn.trans hnX) (t := (1 : ℝ)) (by norm_num) hu5
  have hfaceN := roughSaiasFullyRealHyperbolaCoordinate_le_five
    hX ha2 (has.trans hsn) hnX (t := (1 : ℝ)) (by norm_num) hu5
  have huM5 : u (m : ℝ) ≤ 5 := by
    simpa only [u, roughSaiasFullyRealHyperbolaCoordinate,
      Real.log_one, sub_zero] using hfaceM
  have huS5 : u s ≤ 5 := by
    simpa only [u, roughSaiasFullyRealHyperbolaCoordinate,
      Real.log_one, sub_zero] using hfaceS
  have huN5 : u n ≤ 5 := by
    simpa only [u, n, roughSaiasFullyRealHyperbolaCoordinate,
      Real.log_one, sub_zero] using hfaceN
  have huM0 : 0 ≤ u (m : ℝ) := by
    dsimp only [u]
    exact div_nonneg
      (Real.log_nonneg ((one_le_div (by positivity)).2
        (by exact_mod_cast (show m ≤ X by omega)))) hlogm.le
  have huS0 : 0 ≤ u s := by
    dsimp only [u]
    exact div_nonneg
      (Real.log_nonneg ((one_le_div (by positivity)).2 (hsn.trans hnX))) hlogs.le
  have huN0 : 0 ≤ u n := by
    dsimp only [u]
    exact div_nonneg
      (Real.log_nonneg ((one_le_div (by positivity)).2 hnX)) hlogn.le
  have huAntitone : ∀ {r₀ r₁ : ℝ}, 1 < r₀ → r₀ ≤ r₁ → r₁ ≤ (X : ℝ) →
      u r₁ ≤ u r₀ := by
    intro r₀ r₁ hr₀One hr₀r₁ hr₁X
    have hr₀pos : 0 < r₀ := zero_lt_one.trans hr₀One
    have hr₁One : 1 < r₁ := hr₀One.trans_le hr₀r₁
    have hr₁pos : 0 < r₁ := zero_lt_one.trans hr₁One
    have hlogr₀ : 0 < Real.log r₀ := Real.log_pos hr₀One
    have hlogr₁ : 0 < Real.log r₁ := Real.log_pos hr₁One
    have hlogLe : Real.log r₀ ≤ Real.log r₁ :=
      Real.log_le_log hr₀pos hr₀r₁
    have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
    have hratio := div_le_div_of_nonneg_left hlogX0 hlogr₀ hlogLe
    dsimp only [u]
    rw [Real.log_div hXreal.ne' hr₁pos.ne',
      Real.log_div hXreal.ne' hr₀pos.ne']
    calc
      (Real.log (X : ℝ) - Real.log r₁) / Real.log r₁ =
          Real.log (X : ℝ) / Real.log r₁ - 1 := by
        field_simp [hlogr₁.ne']
      _ ≤ Real.log (X : ℝ) / Real.log r₀ - 1 :=
        sub_le_sub_right hratio 1
      _ = (Real.log (X : ℝ) - Real.log r₀) / Real.log r₀ := by
        field_simp [hlogr₀.ne']
  have huNS : u n ≤ u s := huAntitone hsOne hsn hnX
  have huSM : u s ≤ u (m : ℝ) :=
    huAntitone hmOne hs.1 (hsn.trans hnX)
  have hrhoMS : rho (u (m : ℝ)) ≤ rho (u s) :=
    roughRho_antitoneOn_zero_five
      (show u s ∈ Set.Icc (0 : ℝ) 5 from ⟨huS0, huS5⟩)
      (show u (m : ℝ) ∈ Set.Icc (0 : ℝ) 5 from ⟨huM0, huM5⟩)
      huSM
  have hrhoSN : rho (u s) ≤ rho (u n) :=
    roughRho_antitoneOn_zero_five
      (show u n ∈ Set.Icc (0 : ℝ) 5 from ⟨huN0, huN5⟩)
      (show u s ∈ Set.Icc (0 : ℝ) 5 from ⟨huS0, huS5⟩)
      huNS
  have hrhoDiff : |rho (u s) - rho (u n)| ≤
      rho (u n) - rho (u (m : ℝ)) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hrhoSN)]
    linarith
  have hJdiff : |J s - J n| ≤
      roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m := by
    dsimp only [J, n]
    exact
      roughSaiasFullyRealBaseFreeFractionalIntegral_hyperbola_cell_abs_sub_le
        hX ha2 hab hbX hm hu5 hs
  have hHdiff : |H s - H n| ≤
      (rho (u n) - rho (u (m : ℝ))) +
        roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m := by
    dsimp only [H]
    calc
      |(rho (u s) - J s) - (rho (u n) - J n)| ≤
          |rho (u s) - rho (u n)| + |J s - J n| := by
        have := abs_sub (rho (u s) - rho (u n)) (J s - J n)
        convert this using 1
        all_goals ring
      _ ≤ (rho (u n) - rho (u (m : ℝ))) +
          roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m :=
        add_le_add hrhoDiff hJdiff
  have hHdiffNonneg : 0 ≤
      (rho (u n) - rho (u (m : ℝ))) +
        roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m :=
    (abs_nonneg (H s - H n)).trans hHdiff
  have hHn : |H n| ≤ 16 := by
    have hG := roughSaiasFullyRealG_abs_le_sixteen hnOne
      (show u n ∈ Set.Icc (0 : ℝ) 5 from ⟨huN0, huN5⟩)
    have hEq := roughSaiasFullyRealG_eq_rho_sub_baseFree
      (x := (X : ℝ) / n) hnOne
    dsimp only [H, J]
    rw [← hEq]
    exact hG
  have hlogMS : Real.log (m : ℝ) ≤ Real.log s :=
    Real.log_le_log (zero_lt_one.trans hmOne) hs.1
  have hlogSN : Real.log s ≤ Real.log n :=
    Real.log_le_log (zero_lt_one.trans hsOne) hsn
  have hdenomMS : (m : ℝ) * Real.log (m : ℝ) ≤ s * Real.log s :=
    mul_le_mul hs.1 hlogMS hlogm.le (by positivity)
  have hdenomSN : s * Real.log s ≤ n * Real.log n :=
    mul_le_mul hsn hlogSN hlogs.le (by positivity)
  have hdenomAM : (a : ℝ) * Real.log (a : ℝ) ≤
      (m : ℝ) * Real.log (m : ℝ) := by
    have hlogAM : Real.log (a : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hmData.1)
    exact mul_le_mul (by exact_mod_cast hmData.1) hlogAM hloga.le (by positivity)
  have hAnAs : A n ≤ A s := by
    dsimp only [A]
    exact div_le_div_of_nonneg_left hXreal.le (mul_pos (by positivity) hlogs) hdenomSN
  have hAsAm : A s ≤ A (m : ℝ) := by
    dsimp only [A]
    exact div_le_div_of_nonneg_left hXreal.le
      (mul_pos (by positivity) hlogm) hdenomMS
  have hAmAa : A (m : ℝ) ≤ A (a : ℝ) := by
    dsimp only [A]
    exact div_le_div_of_nonneg_left hXreal.le
      (mul_pos (by positivity) hloga) hdenomAM
  have hAs0 : 0 ≤ A s := by dsimp only [A]; positivity
  have hcoeffDiff : 0 ≤ A s - A n := sub_nonneg.mpr hAnAs
  have hcoeffBound : A s - A n ≤ A (m : ℝ) - A n :=
    sub_le_sub_right hAsAm _
  have hPs0 : 0 ≤ P s := by
    dsimp only [P]
    exact div_nonneg (Int.fract_nonneg _) hlogs.le
  have hPn0 : 0 ≤ P n := by
    dsimp only [P]
    exact div_nonneg (Int.fract_nonneg _) hlogn.le
  have hPs : P s ≤ 1 / Real.log (m : ℝ) := by
    dsimp only [P]
    calc
      Int.fract ((X : ℝ) / s) / Real.log s ≤ 1 / Real.log s :=
        div_le_div_of_nonneg_right
          (Int.fract_lt_one ((X : ℝ) / s)).le hlogs.le
      _ ≤ 1 / Real.log (m : ℝ) :=
        one_div_le_one_div_of_le hlogm hlogMS
  have hPn : P n ≤ 1 / Real.log (m : ℝ) := by
    dsimp only [P]
    calc
      Int.fract ((X : ℝ) / n) / Real.log n ≤ 1 / Real.log n :=
        div_le_div_of_nonneg_right
          (Int.fract_lt_one ((X : ℝ) / n)).le hlogn.le
      _ ≤ 1 / Real.log (m : ℝ) :=
        one_div_le_one_div_of_le hlogm (hlogMS.trans hlogSN)
  have hPdiff : |P s - P n| ≤ 2 / Real.log (m : ℝ) := by
    calc
      |P s - P n| ≤ |P s| + |P n| := abs_sub _ _
      _ = P s + P n := by rw [abs_of_nonneg hPs0, abs_of_nonneg hPn0]
      _ ≤ 1 / Real.log (m : ℝ) + 1 / Real.log (m : ℝ) :=
        add_le_add hPs hPn
      _ = 2 / Real.log (m : ℝ) := by ring
  have hFs := roughSaiasFullyRealBuchstabNormalIntegrand_eq_rho_sub_fractional
    (X := X) hsOne
  have hFn := roughSaiasFullyRealBuchstabNormalIntegrand_eq_rho_sub_fractional
    (X := X) hnOne
  rw [hFs, hFn]
  change |(A s * H s - P s) - (A n * H n - P n)| ≤ _
  calc
    |(A s * H s - P s) - (A n * H n - P n)| ≤
        |A s * H s - A n * H n| + |P s - P n| := by
      have := abs_sub (A s * H s - A n * H n) (P s - P n)
      convert this using 1
      all_goals ring
    _ ≤ ((A s - A n) * |H n| + A s * |H s - H n|) +
        |P s - P n| := by
      have hmain : |A s * H s - A n * H n| ≤
          (A s - A n) * |H n| + A s * |H s - H n| := by
        calc
          |A s * H s - A n * H n| =
              |(A s - A n) * H n + A s * (H s - H n)| := by
            congr 1
            ring
          _ ≤ |(A s - A n) * H n| + |A s * (H s - H n)| :=
            abs_add_le _ _
          _ = (A s - A n) * |H n| + A s * |H s - H n| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hcoeffDiff,
              abs_of_nonneg hAs0]
      exact add_le_add hmain le_rfl
    _ ≤ (A s - A n) * 16 +
          A s * ((rho (u n) - rho (u (m : ℝ))) +
            roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m) +
        2 / Real.log (m : ℝ) := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left hHn hcoeffDiff)
          (mul_le_mul_of_nonneg_left hHdiff hAs0))
        hPdiff
    _ ≤ 16 * (A (m : ℝ) - A n) +
          A (a : ℝ) * ((rho (u n) - rho (u (m : ℝ))) +
            roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m) +
        2 / Real.log (m : ℝ) := by
      have hfirst := mul_le_mul_of_nonneg_right hcoeffBound (by norm_num : (0 : ℝ) ≤ 16)
      have hsecond := mul_le_mul_of_nonneg_right (hAsAm.trans hAmAa) hHdiffNonneg
      nlinarith
    _ = 16 *
          ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ)) -
            (X : ℝ) /
              (((m + 1 : ℕ) : ℝ) * Real.log ((m + 1 : ℕ) : ℝ))) +
        ((X : ℝ) / ((a : ℝ) * Real.log (a : ℝ))) *
          ((rho (Real.log ((X : ℝ) / (m + 1 : ℕ)) /
                  Real.log ((m + 1 : ℕ) : ℝ)) -
              rho (Real.log ((X : ℝ) / (m : ℝ)) /
                  Real.log (m : ℝ))) +
            roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m) +
        2 / Real.log (m : ℝ) := by
      rfl

/-- The paired natural cell itself satisfies the same quadrature ledger,
with `20/log m` added for the exact real-quotient endpoint correction. -/
private theorem roughSaiasFullyRealNaturalBuchstabCellRemainder_abs_le_lowerLedger
    {X a b m : ℕ} (hX : 0 < X) (ha3 : 3 ≤ a) (hab : a ≤ b)
    (hbX : b ≤ X) (hm : m ∈ Finset.Ico a b)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    |roughSaiasFullyRealNaturalBuchstabCellRemainder X m| ≤
      16 *
          ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ)) -
            (X : ℝ) /
              (((m + 1 : ℕ) : ℝ) * Real.log ((m + 1 : ℕ) : ℝ))) +
        ((X : ℝ) / ((a : ℝ) * Real.log (a : ℝ))) *
          ((rho (Real.log ((X : ℝ) / (m + 1 : ℕ)) /
                  Real.log ((m + 1 : ℕ) : ℝ)) -
              rho (Real.log ((X : ℝ) / (m : ℝ)) /
                  Real.log (m : ℝ))) +
            roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger
              X a m) +
        22 / Real.log (m : ℝ) := by
  have hmData := Finset.mem_Ico.mp hm
  have ha2 : 2 ≤ a := by omega
  have hm3 : 3 ≤ m := ha3.trans hmData.1
  have hnextX : m + 1 ≤ X := by omega
  have hmOne : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hnextOne : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < m + 1 by omega)
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hmOne
  have hlogNext : 0 < Real.log ((m + 1 : ℕ) : ℝ) := Real.log_pos hnextOne
  have hlogmNext : Real.log (m : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (Nat.le_succ m))
  have hinvNext : 20 / Real.log ((m + 1 : ℕ) : ℝ) ≤
      20 / Real.log (m : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hlogm hlogmNext
  have hendpoint :
      roughSaiasFullyRealBuchstabNormalIntegrand X (m + 1 : ℕ) -
          roughSaiasNaturalQuotientThetaWeight X (m + 1) =
        roughSaiasFractionalCorrectionThetaWeight X (m + 1) := by
    rw [roughSaiasFullyRealBuchstabNormalIntegrand_nat,
      roughSaiasNormalFormThetaWeight_eq_natural_add_fractional]
    ring
  have hendpointAbs :
      |roughSaiasFullyRealBuchstabNormalIntegrand X (m + 1 : ℕ) -
          roughSaiasNaturalQuotientThetaWeight X (m + 1)| ≤
        20 / Real.log (m : ℝ) := by
    rw [hendpoint]
    exact (roughSaiasFractionalCorrectionThetaWeight_abs_le_twenty_inv_log
      hX ha3 (by omega : a ≤ m + 1) hnextX hu5).trans hinvNext
  let C : ℝ :=
    16 *
        ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ)) -
          (X : ℝ) /
            (((m + 1 : ℕ) : ℝ) * Real.log ((m + 1 : ℕ) : ℝ))) +
      ((X : ℝ) / ((a : ℝ) * Real.log (a : ℝ))) *
        ((rho (Real.log ((X : ℝ) / (m + 1 : ℕ)) /
                Real.log ((m + 1 : ℕ) : ℝ)) -
            rho (Real.log ((X : ℝ) / (m : ℝ)) /
                Real.log (m : ℝ))) +
          roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger
            X a m) +
      22 / Real.log (m : ℝ)
  have hpoint : ∀ s ∈ Set.Icc (m : ℝ) (m + 1 : ℕ),
      |roughSaiasFullyRealBuchstabNormalIntegrand X s -
          roughSaiasNaturalQuotientThetaWeight X (m + 1)| ≤ C := by
    intro s hs
    have hcontinuous :=
      roughSaiasFullyRealBuchstabNormalIntegrand_cell_abs_sub_right_le
        hX ha3 hab hbX hm hu5 hs
    calc
      |roughSaiasFullyRealBuchstabNormalIntegrand X s -
          roughSaiasNaturalQuotientThetaWeight X (m + 1)| ≤
        |roughSaiasFullyRealBuchstabNormalIntegrand X s -
            roughSaiasFullyRealBuchstabNormalIntegrand X (m + 1 : ℕ)| +
          |roughSaiasFullyRealBuchstabNormalIntegrand X (m + 1 : ℕ) -
            roughSaiasNaturalQuotientThetaWeight X (m + 1)| :=
        abs_sub_le _ _ _
      _ ≤
        (16 *
            ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ)) -
              (X : ℝ) /
                (((m + 1 : ℕ) : ℝ) * Real.log ((m + 1 : ℕ) : ℝ))) +
          ((X : ℝ) / ((a : ℝ) * Real.log (a : ℝ))) *
            ((rho (Real.log ((X : ℝ) / (m + 1 : ℕ)) /
                    Real.log ((m + 1 : ℕ) : ℝ)) -
                rho (Real.log ((X : ℝ) / (m : ℝ)) /
                    Real.log (m : ℝ))) +
              roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger
                X a m) +
          2 / Real.log (m : ℝ)) +
        20 / Real.log (m : ℝ) := add_le_add hcontinuous hendpointAbs
      _ = C := by
        dsimp only [C]
        ring
  rw [roughSaiasFullyRealNaturalBuchstabCellRemainder_eq_integral
    ha2 hab hbX hu5 hm]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s : ℝ =>
      roughSaiasFullyRealBuchstabNormalIntegrand X s -
        roughSaiasNaturalQuotientThetaWeight X (m + 1))
    (C := C) (a := (m : ℝ)) (b := (m + 1 : ℕ)) (fun s hsU => by
      rw [Real.norm_eq_abs]
      apply hpoint s
      have hs := Set.uIoc_subset_uIcc hsU
      simpa [Set.uIcc_of_le
        (by norm_num : (m : ℝ) ≤ (m + 1 : ℕ))] using hs)
  simpa only [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_left, abs_one, mul_one, C] using hnorm

/-- The complete lower fully-real natural-cell block has the required
inverse-log-square size.  The constant `40` records, without hidden
cancellation, coefficient drift (`16`), rho variation (`1`), continuous
fractional variation (`1` after scaling), and the two endpoint sawtooth
costs (`22`). -/
theorem abs_sum_roughSaiasFullyRealNaturalCells_lower_le_forty_invLogSq
    {X a b : ℕ} (hX : 0 < X) (ha3 : 3 ≤ a) (hab : a ≤ b)
    (hbX : b ≤ X) (hbSqrt : b ≤ Nat.sqrt X + 1)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    |∑ m ∈ Finset.Ico a b,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m| ≤
      40 * (X : ℝ) / Real.log (a : ℝ) ^ 2 := by
  rcases hab.eq_or_lt with rfl | habLt
  · simp only [Finset.Ico_self, Finset.sum_empty, abs_zero]
    positivity
  · let A : ℕ → ℝ := fun m =>
      (X : ℝ) / ((m : ℝ) * Real.log (m : ℝ))
    let R : ℕ → ℝ := fun m =>
      rho (Real.log ((X : ℝ) / (m : ℝ)) / Real.log (m : ℝ))
    let B : ℕ → ℝ := fun m =>
      roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m
    have hloga : 0 < Real.log (a : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < a by omega))
    have ha2 : 2 ≤ a := by omega
    have hapos : 0 < (a : ℝ) := by positivity
    have hlogale : Real.log (a : ℝ) ≤ (a : ℝ) := by
      have h := Real.log_le_sub_one_of_pos hapos
      linarith
    have hdenom : Real.log (a : ℝ) ^ 2 ≤
        (a : ℝ) * Real.log (a : ℝ) := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right hlogale hloga.le
    have hAaTarget : A a ≤ (X : ℝ) / Real.log (a : ℝ) ^ 2 := by
      dsimp only [A]
      exact div_le_div_of_nonneg_left (by positivity)
        (sq_pos_of_pos hloga) hdenom
    have haSqrt : a ≤ Nat.sqrt X := by omega
    have hlengthSqrt : b - a ≤ Nat.sqrt X := by omega
    have hmulNat : (b - a) * a ≤ X := by
      calc
        (b - a) * a ≤ Nat.sqrt X * Nat.sqrt X :=
          Nat.mul_le_mul hlengthSqrt haSqrt
        _ = (Nat.sqrt X) ^ 2 := by ring
        _ ≤ X := Nat.sqrt_le' X
    have hlength : ((Finset.Ico a b).card : ℝ) ≤ (X : ℝ) / (a : ℝ) := by
      rw [Nat.card_Ico]
      apply (le_div_iff₀ hapos).2
      exact_mod_cast hmulNat
    have hcoeffTelescope :
        (∑ m ∈ Finset.Ico a b, (A m - A (m + 1))) = A a - A b := by
      simpa only [neg_sub_neg] using
        (Finset.sum_Ico_sub (fun m => -A m) hab)
    have hcoeffSum :
        (∑ m ∈ Finset.Ico a b, (A m - A (m + 1))) ≤ A a := by
      rw [hcoeffTelescope]
      have hAb : 0 ≤ A b := by
        dsimp only [A]
        have hbOne : (1 : ℝ) < (b : ℝ) := by
          exact_mod_cast (show 1 < b by omega)
        exact div_nonneg (by positivity)
          (mul_nonneg (by positivity) (Real.log_pos hbOne).le)
      linarith
    have hrhoSum :
        (∑ m ∈ Finset.Ico a b, (R (m + 1) - R m)) ≤ 1 := by
      calc
        (∑ m ∈ Finset.Ico a b, (R (m + 1) - R m)) ≤
            ∑ m ∈ Finset.Ico a b, |R (m + 1) - R m| := by
          apply Finset.sum_le_sum
          intro m _hm
          exact le_abs_self _
        _ ≤ 1 := by
          simpa only [R] using
            (sum_abs_rho_fullyRealHyperbolaLogRatio_succ_sub_le_one
              hX ha2 habLt.le hbX hu5)
    have hBSum : (∑ m ∈ Finset.Ico a b, B m) ≤
        2 / Real.log (a : ℝ) := by
      simpa only [B] using
        (sum_roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger_le_two_inv_log
          hX ha2 habLt.le hbX hu5)
    have hinvSum :
        (∑ m ∈ Finset.Ico a b, 1 / Real.log (m : ℝ)) ≤
          ((Finset.Ico a b).card : ℝ) / Real.log (a : ℝ) := by
      calc
        (∑ m ∈ Finset.Ico a b, 1 / Real.log (m : ℝ)) ≤
            ∑ _m ∈ Finset.Ico a b, 1 / Real.log (a : ℝ) := by
          apply Finset.sum_le_sum
          intro m hm
          have hmData := Finset.mem_Ico.mp hm
          have hlogam : Real.log (a : ℝ) ≤ Real.log (m : ℝ) :=
            Real.log_le_log hapos (by exact_mod_cast hmData.1)
          exact one_div_le_one_div_of_le hloga hlogam
        _ = ((Finset.Ico a b).card : ℝ) / Real.log (a : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
    have hInvAtA :
        ((Finset.Ico a b).card : ℝ) / Real.log (a : ℝ) ≤ A a := by
      dsimp only [A]
      calc
        ((Finset.Ico a b).card : ℝ) / Real.log (a : ℝ) ≤
            ((X : ℝ) / (a : ℝ)) / Real.log (a : ℝ) :=
          div_le_div_of_nonneg_right hlength hloga.le
        _ = (X : ℝ) / ((a : ℝ) * Real.log (a : ℝ)) := by ring
    have hJTarget : A a * (2 / Real.log (a : ℝ)) ≤
        (X : ℝ) / Real.log (a : ℝ) ^ 2 := by
      have htwoA : (2 : ℝ) / (a : ℝ) ≤ 1 := by
        rw [div_le_one hapos]
        exact_mod_cast ha2
      have htargetNonneg : 0 ≤ (X : ℝ) / Real.log (a : ℝ) ^ 2 := by
        positivity
      calc
        A a * (2 / Real.log (a : ℝ)) =
            ((2 : ℝ) / (a : ℝ)) *
              ((X : ℝ) / Real.log (a : ℝ) ^ 2) := by
          dsimp only [A]
          field_simp [hapos.ne', hloga.ne']
        _ ≤ 1 * ((X : ℝ) / Real.log (a : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right htwoA htargetNonneg
        _ = (X : ℝ) / Real.log (a : ℝ) ^ 2 := one_mul _
    let E : ℕ → ℝ := fun m =>
      16 * (A m - A (m + 1)) +
        A a * ((R (m + 1) - R m) + B m) +
        22 * (1 / Real.log (m : ℝ))
    have hcells :
        |∑ m ∈ Finset.Ico a b,
            roughSaiasFullyRealNaturalBuchstabCellRemainder X m| ≤
          ∑ m ∈ Finset.Ico a b, E m := by
      calc
        |∑ m ∈ Finset.Ico a b,
            roughSaiasFullyRealNaturalBuchstabCellRemainder X m| ≤
          ∑ m ∈ Finset.Ico a b,
            |roughSaiasFullyRealNaturalBuchstabCellRemainder X m| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Finset.Ico a b, E m := by
          apply Finset.sum_le_sum
          intro m hm
          have hcell :=
            roughSaiasFullyRealNaturalBuchstabCellRemainder_abs_le_lowerLedger
              hX ha3 habLt.le hbX hm hu5
          simpa only [E, A, R, B, div_eq_mul_inv, one_mul] using hcell
    have hEexpand :
        (∑ m ∈ Finset.Ico a b, E m) =
          (∑ m ∈ Finset.Ico a b, 16 * (A m - A (m + 1))) +
          (∑ m ∈ Finset.Ico a b, A a * (R (m + 1) - R m)) +
          (∑ m ∈ Finset.Ico a b, A a * B m) +
          ∑ m ∈ Finset.Ico a b, 22 * (1 / Real.log (m : ℝ)) := by
      simp only [E, mul_add, Finset.sum_add_distrib]
      ring
    have htermCoeff :
        (∑ m ∈ Finset.Ico a b, 16 * (A m - A (m + 1))) ≤
          16 * A a := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hcoeffSum (by norm_num)
    have htermRho :
        (∑ m ∈ Finset.Ico a b, A a * (R (m + 1) - R m)) ≤ A a := by
      rw [← Finset.mul_sum]
      have hAa0 : 0 ≤ A a := by dsimp only [A]; positivity
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hrhoSum hAa0
    have htermB :
        (∑ m ∈ Finset.Ico a b, A a * B m) ≤
          (X : ℝ) / Real.log (a : ℝ) ^ 2 := by
      rw [← Finset.mul_sum]
      exact (mul_le_mul_of_nonneg_left hBSum (by dsimp only [A]; positivity)).trans
        hJTarget
    have htermInv :
        (∑ m ∈ Finset.Ico a b, 22 * (1 / Real.log (m : ℝ))) ≤
          22 * A a := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hinvSum.trans hInvAtA) (by norm_num)
    rw [hEexpand] at hcells
    calc
      |∑ m ∈ Finset.Ico a b,
          roughSaiasFullyRealNaturalBuchstabCellRemainder X m| ≤
        (∑ m ∈ Finset.Ico a b, 16 * (A m - A (m + 1))) +
        (∑ m ∈ Finset.Ico a b, A a * (R (m + 1) - R m)) +
        (∑ m ∈ Finset.Ico a b, A a * B m) +
        ∑ m ∈ Finset.Ico a b, 22 * (1 / Real.log (m : ℝ)) := hcells
      _ ≤ 16 * A a + A a +
          (X : ℝ) / Real.log (a : ℝ) ^ 2 + 22 * A a :=
        add_le_add (add_le_add (add_le_add htermCoeff htermRho) htermB) htermInv
      _ = 39 * A a + (X : ℝ) / Real.log (a : ℝ) ^ 2 := by ring
      _ ≤ 39 * ((X : ℝ) / Real.log (a : ℝ) ^ 2) +
          (X : ℝ) / Real.log (a : ℝ) ^ 2 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hAaTarget
            (by norm_num : (0 : ℝ) ≤ 39))
          le_rfl
      _ = 40 * (X : ℝ) / Real.log (a : ℝ) ^ 2 := by ring

/-- Exact dual-average form of the closed lower quadrature. -/
theorem abs_sum_roughSaiasDualSpreadFullyRealNaturalCellRemainder_le_forty_invLogSq
    {X y : ℕ} (hX : 0 < X) (hy3 : 3 ≤ y)
    (hySqrt : y ≤ Nat.sqrt X + 1)
    (hMX : Nat.sqrt X + 1 ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |∑ q ∈ Finset.Ioc (X / (Nat.sqrt X + 1)) (X / y),
        roughSaiasDualSpreadFullyRealNaturalCellRemainder X (X / q)| ≤
      40 * (X : ℝ) / Real.log (y : ℝ) ^ 2 := by
  rw [← sum_roughSaiasFullyRealNaturalCells_eq_dualInvolution
    (show 0 < y by omega) hySqrt le_rfl]
  exact abs_sum_roughSaiasFullyRealNaturalCells_lower_le_forty_invLogSq
    hX hy3 hySqrt hMX le_rfl hu5

/-- The signed local block is literally the fully real continuous mass
minus its paired natural prime-theta mass.  This is the smallest
non-averaged analytic residual left by the exact cell decomposition. -/
theorem sum_roughSaiasLocalNaturalPrimeCellDiscrepancy_eq_integral_sub_primeTheta
    {X y M : ℕ} (hy2 : 2 ≤ y) (hyM : y < M) (hMX : M ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico y M,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m) =
      (∫ s in (y : ℝ)..(M : ℝ),
        roughSaiasFullyRealBuchstabNormalIntegrand X s) -
      FriableAsymptotic.primeThetaWeightedInterval
        (roughSaiasNaturalQuotientThetaWeight X) y M := by
  rw [← roughSaiasReverseNormalFormDefect_eq_sum_localNaturalPrimeCellDiscrepancy
      hy2 hyM hMX hu5]
  have hbuch := roughSaiasNaturalMain_buchstab_fullyReal
    hy2 hyM.le hMX hu5
  unfold roughSaiasReverseNormalFormDefect
  rw [← roughSaiasPrimeThetaWeightedInterval_eq_naturalSum]
  linarith

/-- On the upper selector face, consecutive paired natural theta weights
are controlled by the already-summed selector cell ledger. -/
theorem roughSaiasNaturalQuotientThetaWeight_succ_sub_abs_le_selectorCellLedger
    {X m : ℕ} (hm3 : 3 ≤ m) (hupper : X ≤ (m - 1) ^ 2) :
    |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
        roughSaiasNaturalQuotientThetaWeight X m| ≤
      roughSaiasSelectorCellLedger X m := by
  have hpred2 : 2 ≤ m - 1 := by omega
  have hpredSucc : m - 1 + 1 = m := by omega
  have hpredLe : m - 1 ≤ m := by omega
  have hupperNext : X ≤ m ^ 2 :=
    hupper.trans (Nat.pow_le_pow_left hpredLe 2)
  have hnow :=
    roughSaiasNaturalQuotientThetaWeight_eq_selector_of_sq_le
      (X := X) (m := m - 1) hpred2 hupper
  have hnext :=
    roughSaiasNaturalQuotientThetaWeight_eq_selector_of_sq_le
      (X := X) (m := m) (by omega) hupperNext
  rw [hpredSucc] at hnow
  have hcell := roughSaiasRealQuotientSelector_cell_sub_right_abs_le
    (X := X) (m := m) (by omega)
      (s := (m : ℝ)) (by constructor <;> norm_num)
  rw [hnext, hnow, abs_sub_comm]
  simpa only [roughSaiasSelectorCellLedger] using hcell

/-- The selector ledger is exactly the drop of the positive coefficient
`(X / m) / log m`, independently of whether the cell is above or below
the square-root transition. -/
theorem roughSaiasNatHyperbolaCoefficient_sub_succ_eq_selectorCellLedger
    (X m : ℕ) :
    ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) -
        ((X / (m + 1) : ℕ) : ℝ) /
          Real.log ((m + 1 : ℕ) : ℝ) =
      roughSaiasSelectorCellLedger X m := by
  unfold roughSaiasSelectorCellLedger
  ring

/-- Lower-face pointwise variation of the full natural theta weight.  The
coefficient drift is charged to the existing selector ledger, while the
genuinely smooth part is split into rho variation and the common-cap
fractional-integral variation. -/
theorem roughSaiasNaturalQuotientThetaWeight_succ_sub_abs_le_hyperbolaComponents
    {X a b m : ℕ} (ha2 : 2 ≤ a) (_hab : a ≤ b) (hbX : b ≤ X)
    (hm : m ∈ Finset.Ico a b)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
        roughSaiasNaturalQuotientThetaWeight X m| ≤
      16 * roughSaiasSelectorCellLedger X m +
        ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ))) *
          (|rho (Real.log ((X / (m + 1) : ℕ) : ℝ) /
                  Real.log ((m + 1 : ℕ) : ℝ)) -
              rho (Real.log ((X / m : ℕ) : ℝ) /
                Real.log (m : ℝ))| +
            |roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
              roughSaiasBaseFreeFractionalIntegral (X / m) m|) := by
  have hmData := Finset.mem_Ico.mp hm
  have hm2 : 2 ≤ m := ha2.trans hmData.1
  have hnextX : m + 1 ≤ X := by omega
  have hqNow : 1 ≤ X / m := Nat.div_pos (by omega) (by omega)
  have hqNext : 1 ≤ X / (m + 1) := Nat.div_pos hnextX (by omega)
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogNext : 0 < Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m + 1 by omega))
  let A₀ : ℝ := ((X / m : ℕ) : ℝ) / Real.log (m : ℝ)
  let A₁ : ℝ := ((X / (m + 1) : ℕ) : ℝ) /
    Real.log ((m + 1 : ℕ) : ℝ)
  let u₀ : ℝ := Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ)
  let u₁ : ℝ := Real.log ((X / (m + 1) : ℕ) : ℝ) /
    Real.log ((m + 1 : ℕ) : ℝ)
  let I₀ : ℝ := roughSaiasBaseFreeFractionalIntegral (X / m) m
  let I₁ : ℝ :=
    roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1)
  have hcoeff : A₀ - A₁ = roughSaiasSelectorCellLedger X m := by
    simpa only [A₀, A₁] using
      roughSaiasNatHyperbolaCoefficient_sub_succ_eq_selectorCellLedger X m
  have hledgerNonneg : 0 ≤ roughSaiasSelectorCellLedger X m := by
    have hdrop :=
      roughSaiasNaturalQuotientDrop_nonneg (m := m) X (by omega)
    unfold roughSaiasSelectorCellLedger
    exact add_nonneg
      (div_nonneg hdrop hlogm.le)
      (mul_nonneg (by positivity) (roughSaias_invLog_succ_sub_nonneg hm2))
  have hA₁A₀ : A₁ ≤ A₀ := by linarith
  have hA₀nonneg : 0 ≤ A₀ := by
    exact div_nonneg (by positivity) hlogm.le
  have hA₀bound : A₀ ≤
      (X : ℝ) / ((m : ℝ) * Real.log (m : ℝ)) := by
    calc
      A₀ ≤ ((X : ℝ) / (m : ℝ)) / Real.log (m : ℝ) := by
        exact div_le_div_of_nonneg_right Nat.cast_div_le hlogm.le
      _ = (X : ℝ) / ((m : ℝ) * Real.log (m : ℝ)) := by ring
  have hu₁0 : 0 ≤ u₁ := by
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hqNext)) hlogNext.le
  have hu₁5 : u₁ ≤ 5 := by
    simpa only [u₁] using roughSaiasNatHyperbolaLogRatio_le_five
      ha2 (by omega) (by omega) hu5
  have hB₁ : |rho u₁ - I₁| ≤ 16 := by
    have hG : |roughSaiasG (m + 1) u₁| ≤ 16 := by
      rw [← roughSaiasFullyRealG_nat]
      exact roughSaiasFullyRealG_abs_le_sixteen
        (by exact_mod_cast (show 1 < m + 1 by omega)) ⟨hu₁0, hu₁5⟩
    have hbase := roughSaiasG_at_natQuotient_eq_baseFree
      (q := X / (m + 1)) (m := m + 1) (by omega)
    rw [hbase] at hG
    simpa only [u₁, I₁] using hG
  have hrearrange :
      roughSaiasBaseFreeNaturalThetaWeight (X / (m + 1)) (m + 1) -
          roughSaiasBaseFreeNaturalThetaWeight (X / m) m =
        (A₁ - A₀) * (rho u₁ - I₁) +
          A₀ * ((rho u₁ - rho u₀) - (I₁ - I₀)) := by
    unfold roughSaiasBaseFreeNaturalThetaWeight A₀ A₁ u₀ u₁ I₀ I₁
    ring
  rw [roughSaiasNaturalQuotientThetaWeight_diff_eq_baseFree hm2,
    hrearrange]
  calc
    |(A₁ - A₀) * (rho u₁ - I₁) +
        A₀ * ((rho u₁ - rho u₀) - (I₁ - I₀))| ≤
      |A₁ - A₀| * |rho u₁ - I₁| +
        |A₀| * |(rho u₁ - rho u₀) - (I₁ - I₀)| := by
      simpa only [abs_mul] using
        (abs_add_le ((A₁ - A₀) * (rho u₁ - I₁))
          (A₀ * ((rho u₁ - rho u₀) - (I₁ - I₀))))
    _ = roughSaiasSelectorCellLedger X m * |rho u₁ - I₁| +
        A₀ * |(rho u₁ - rho u₀) - (I₁ - I₀)| := by
      simp only [abs_of_nonpos (sub_nonpos.mpr hA₁A₀),
        abs_of_nonneg hA₀nonneg, neg_sub, hcoeff]
    _ ≤ 16 * roughSaiasSelectorCellLedger X m +
        A₀ * (|rho u₁ - rho u₀| + |I₁ - I₀|) := by
      have hfirst := mul_le_mul_of_nonneg_left hB₁ hledgerNonneg
      have hsecond := mul_le_mul_of_nonneg_left
        (abs_sub (rho u₁ - rho u₀) (I₁ - I₀)) hA₀nonneg
      calc
        roughSaiasSelectorCellLedger X m * |rho u₁ - I₁| +
            A₀ * |(rho u₁ - rho u₀) - (I₁ - I₀)| ≤
          roughSaiasSelectorCellLedger X m * 16 +
            A₀ * (|rho u₁ - rho u₀| + |I₁ - I₀|) :=
          add_le_add hfirst hsecond
        _ = 16 * roughSaiasSelectorCellLedger X m +
            A₀ * (|rho u₁ - rho u₀| + |I₁ - I₀|) := by ring
    _ ≤ 16 * roughSaiasSelectorCellLedger X m +
        ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ))) *
          (|rho u₁ - rho u₀| + |I₁ - I₀|) := by
      exact add_le_add
        le_rfl
        (mul_le_mul_of_nonneg_right hA₀bound
          (add_nonneg (abs_nonneg _) (abs_nonneg _)))
    _ = 16 * roughSaiasSelectorCellLedger X m +
        ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ))) *
          (|rho (Real.log ((X / (m + 1) : ℕ) : ℝ) /
                  Real.log ((m + 1 : ℕ) : ℝ)) -
              rho (Real.log ((X / m : ℕ) : ℝ) /
                Real.log (m : ℝ))| +
            |roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
              roughSaiasBaseFreeFractionalIntegral (X / m) m|) := by
      rfl

/-- Fourth-power PNT weighting of all upper selector ledgers.  The quotient
jump part uses the weighted hyperbola telescope, while the reciprocal-log
part uses only the harmonic bound. -/
theorem sum_roughSaiasSelectorCellLedger_mul_fourth_le
    {C : ℝ} (hC : 0 ≤ C) (X : ℕ) {M Z : ℕ}
    (hM2 : 2 ≤ M) (hMZ : M ≤ Z) :
    (∑ m ∈ Finset.Ico M Z,
        roughSaiasSelectorCellLedger X m *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) ≤
      C * (X : ℝ) * (2 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 5 +
        C * (X : ℝ) * (1 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 6 := by
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hpoint : ∀ m ∈ Finset.Ico M Z,
      roughSaiasSelectorCellLedger X m *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) ≤
        (C / Real.log (M : ℝ) ^ 5) *
            ((m : ℝ) * roughSaiasNaturalQuotientDrop X m) +
          (C * (X : ℝ) / Real.log (M : ℝ) ^ 6) *
            (1 / (m : ℝ)) := by
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    have hm2 : 2 ≤ m := hM2.trans hmData.1
    have hmpos : 0 < (m : ℝ) := by positivity
    have hlogm : 0 < Real.log (m : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    have hlogMm : Real.log (M : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log
        (by exact_mod_cast (show 0 < M by omega))
        (by exact_mod_cast hmData.1)
    have hpow4 : Real.log (M : ℝ) ^ 4 ≤
        Real.log (m : ℝ) ^ 4 :=
      pow_le_pow_left₀ hlogM.le hlogMm 4
    have hfactorNonneg :
        0 ≤ C * ((m : ℝ) / Real.log (m : ℝ) ^ 4) := by
      positivity
    have hfactorBound :
        C * ((m : ℝ) / Real.log (m : ℝ) ^ 4) ≤
          C * ((m : ℝ) / Real.log (M : ℝ) ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact div_le_div_of_nonneg_left (by positivity)
        (pow_pos hlogM 4) hpow4
    have hdrop : 0 ≤ roughSaiasNaturalQuotientDrop X m :=
      roughSaiasNaturalQuotientDrop_nonneg X (by omega)
    have hmajorantNonneg :
        0 ≤ roughSaiasNaturalQuotientDrop X m /
              Real.log (M : ℝ) +
            ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
              (1 / (m : ℝ) ^ 2) := by
      exact add_nonneg
        (div_nonneg hdrop hlogM.le)
        (mul_nonneg
          (div_nonneg (by positivity) (sq_nonneg _))
          (one_div_nonneg.mpr (sq_nonneg _)))
    calc
      roughSaiasSelectorCellLedger X m *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) ≤
        (roughSaiasNaturalQuotientDrop X m / Real.log (M : ℝ) +
            ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
              (1 / (m : ℝ) ^ 2)) *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_right
          (roughSaiasSelectorCellLedger_le_drop_add_invSq
            X hM2 hmData.1) hfactorNonneg
      _ ≤
        (roughSaiasNaturalQuotientDrop X m / Real.log (M : ℝ) +
            ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
              (1 / (m : ℝ) ^ 2)) *
          (C * ((m : ℝ) / Real.log (M : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_left hfactorBound hmajorantNonneg
      _ = (C / Real.log (M : ℝ) ^ 5) *
            ((m : ℝ) * roughSaiasNaturalQuotientDrop X m) +
          (C * (X : ℝ) / Real.log (M : ℝ) ^ 6) *
            (1 / (m : ℝ)) := by
        field_simp [hlogM.ne', hmpos.ne']
  have hmoment := sum_mul_roughSaiasNaturalQuotientDrop_le X hMZ
  have hharmonicIco :
      (∑ m ∈ Finset.Ico M Z, 1 / (m : ℝ)) ≤
        1 + Real.log (Z : ℝ) := by
    calc
      (∑ m ∈ Finset.Ico M Z, 1 / (m : ℝ)) ≤
          ∑ m ∈ Finset.Ioc (M - 1) Z, 1 / (m : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          rw [Finset.mem_Ico] at hm
          rw [Finset.mem_Ioc]
          omega
        · intro m _hm _hnot
          positivity
      _ ≤ 1 + Real.log (Z : ℝ) :=
        FriableAsymptotic.harmonic_Ioc_le
  calc
    (∑ m ∈ Finset.Ico M Z,
        roughSaiasSelectorCellLedger X m *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) ≤
      ∑ m ∈ Finset.Ico M Z,
        ((C / Real.log (M : ℝ) ^ 5) *
            ((m : ℝ) * roughSaiasNaturalQuotientDrop X m) +
          (C * (X : ℝ) / Real.log (M : ℝ) ^ 6) *
            (1 / (m : ℝ))) :=
      Finset.sum_le_sum hpoint
    _ = (C / Real.log (M : ℝ) ^ 5) *
          (∑ m ∈ Finset.Ico M Z,
            (m : ℝ) * roughSaiasNaturalQuotientDrop X m) +
        (C * (X : ℝ) / Real.log (M : ℝ) ^ 6) *
          (∑ m ∈ Finset.Ico M Z, 1 / (m : ℝ)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (C / Real.log (M : ℝ) ^ 5) *
          ((X : ℝ) * (2 + Real.log (Z : ℝ))) +
        (C * (X : ℝ) / Real.log (M : ℝ) ^ 6) *
          (1 + Real.log (Z : ℝ)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hmoment (by positivity))
        (mul_le_mul_of_nonneg_left hharmonicIco (by positivity))
    _ = C * (X : ℝ) * (2 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 5 +
        C * (X : ℝ) * (1 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 6 := by ring

/-- Fourth-power weighted variation of the natural theta weight on an
arbitrary hyperbola block.  This is the lower-face counterpart of the
selector estimate: coefficient drift uses the same selector ledger, while
rho and fractional-integral variations telescope globally. -/
theorem sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_hyperbola
    {C : ℝ} (hC : 0 ≤ C) {X a b : ℕ}
    (ha2 : 2 ≤ a) (hab : a ≤ b) (hbX : b ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) ≤
      16 * (C * (X : ℝ) * (2 + Real.log (b : ℝ)) /
          Real.log (a : ℝ) ^ 5 +
        C * (X : ℝ) * (1 + Real.log (b : ℝ)) /
          Real.log (a : ℝ) ^ 6) +
        (C * (X : ℝ) / Real.log (a : ℝ) ^ 5) *
          (1 + 2 / Real.log (a : ℝ)) := by
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hCX : 0 ≤ C * (X : ℝ) := by positivity
  let R : ℕ → ℝ := fun m =>
    |rho (Real.log ((X / (m + 1) : ℕ) : ℝ) /
          Real.log ((m + 1 : ℕ) : ℝ)) -
      rho (Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ))| +
    |roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
      roughSaiasBaseFreeFractionalIntegral (X / m) m|
  have hRnonneg : ∀ m, 0 ≤ R m := fun m =>
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hpoint : ∀ m ∈ Finset.Ico a b,
      |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) ≤
        16 * (roughSaiasSelectorCellLedger X m *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) +
        (C * (X : ℝ) / Real.log (a : ℝ) ^ 5) * R m := by
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    have hm2 : 2 ≤ m := ha2.trans hmData.1
    have hmpos : 0 < (m : ℝ) := by positivity
    have hlogm : 0 < Real.log (m : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    have hlogam : Real.log (a : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hmData.1)
    have hpow5 : Real.log (a : ℝ) ^ 5 ≤ Real.log (m : ℝ) ^ 5 :=
      pow_le_pow_left₀ hloga.le hlogam 5
    have hcoeff :
        ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ))) *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) =
          C * (X : ℝ) / Real.log (m : ℝ) ^ 5 := by
      field_simp [hmpos.ne', hlogm.ne']
    have hcoeffLe : C * (X : ℝ) / Real.log (m : ℝ) ^ 5 ≤
        C * (X : ℝ) / Real.log (a : ℝ) ^ 5 :=
      div_le_div_of_nonneg_left hCX (pow_pos hloga 5) hpow5
    have hweightNonneg :
        0 ≤ C * ((m : ℝ) / Real.log (m : ℝ) ^ 4) := by positivity
    have hbase :=
      roughSaiasNaturalQuotientThetaWeight_succ_sub_abs_le_hyperbolaComponents
        ha2 hab hbX hm hu5
    have hmul := mul_le_mul_of_nonneg_right hbase hweightNonneg
    calc
      |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) ≤
        (16 * roughSaiasSelectorCellLedger X m +
          ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ))) * R m) *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) := by
          simpa only [R] using hmul
      _ = 16 * (roughSaiasSelectorCellLedger X m *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) +
          (C * (X : ℝ) / Real.log (m : ℝ) ^ 5) * R m := by
        rw [← hcoeff]
        ring
      _ ≤ 16 * (roughSaiasSelectorCellLedger X m *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) +
          (C * (X : ℝ) / Real.log (a : ℝ) ^ 5) * R m :=
        add_le_add
          le_rfl
          (mul_le_mul_of_nonneg_right hcoeffLe (hRnonneg m))
  have hselector := sum_roughSaiasSelectorCellLedger_mul_fourth_le
    hC X ha2 hab
  have hRsum : (∑ m ∈ Finset.Ico a b, R m) ≤
      1 + 2 / Real.log (a : ℝ) := by
    have hrho := sum_abs_rho_natHyperbolaLogRatio_succ_sub_le_one
      ha2 hab hbX hu5
    have hI :=
      roughSaiasBaseFreeFractionalIntegral_hyperbola_sum_abs_succ_sub_le_two_inv_log
        ha2 hab hbX hu5
    calc
      (∑ m ∈ Finset.Ico a b, R m) =
          (∑ m ∈ Finset.Ico a b,
            |rho (Real.log ((X / (m + 1) : ℕ) : ℝ) /
                  Real.log ((m + 1 : ℕ) : ℝ)) -
              rho (Real.log ((X / m : ℕ) : ℝ) /
                Real.log (m : ℝ))|) +
          ∑ m ∈ Finset.Ico a b,
            |roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
              roughSaiasBaseFreeFractionalIntegral (X / m) m| := by
        simp only [R, Finset.sum_add_distrib]
      _ ≤ 1 + 2 / Real.log (a : ℝ) := add_le_add hrho hI
  calc
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) ≤
      ∑ m ∈ Finset.Ico a b,
        (16 * (roughSaiasSelectorCellLedger X m *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) +
        (C * (X : ℝ) / Real.log (a : ℝ) ^ 5) * R m) :=
      Finset.sum_le_sum hpoint
    _ = 16 * (∑ m ∈ Finset.Ico a b,
          roughSaiasSelectorCellLedger X m *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) +
        (C * (X : ℝ) / Real.log (a : ℝ) ^ 5) *
          (∑ m ∈ Finset.Ico a b, R m) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 16 * (C * (X : ℝ) * (2 + Real.log (b : ℝ)) /
          Real.log (a : ℝ) ^ 5 +
        C * (X : ℝ) * (1 + Real.log (b : ℝ)) /
          Real.log (a : ℝ) ^ 6) +
        (C * (X : ℝ) / Real.log (a : ℝ) ^ 5) *
          (1 + 2 / Real.log (a : ℝ)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hselector (by norm_num))
        (mul_le_mul_of_nonneg_left hRsum (by positivity))

/-- The arbitrary-face hyperbola variation is already at the target
inverse-log-square scale. -/
theorem sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_invLogSq
    {C : ℝ} (hC : 0 ≤ C) {X a b : ℕ}
    (ha3 : 3 ≤ a) (hab : a ≤ b) (hbX : b ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) ≤
      211 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2 := by
  have hapos : 0 < (a : ℝ) := by positivity
  have hbpos : 0 < (b : ℝ) := by
    exact_mod_cast (show 0 < b by omega)
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogaOne : 1 ≤ Real.log (a : ℝ) := by
    have hexp : Real.exp 1 < (a : ℝ) :=
      Real.exp_one_lt_three.trans_le (by exact_mod_cast ha3)
    exact ((Real.lt_log_iff_exp_lt hapos).2 hexp).le
  have hlogbX : Real.log (b : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hbpos (by exact_mod_cast hbX)
  have hlogX : Real.log (X : ℝ) ≤ 5 * Real.log (a : ℝ) :=
    (div_le_iff₀ hloga).mp hu5
  have hlogb : Real.log (b : ℝ) ≤ 5 * Real.log (a : ℝ) :=
    hlogbX.trans hlogX
  have hbracketTwo : 2 + Real.log (b : ℝ) ≤
      7 * Real.log (a : ℝ) := by linarith
  have hbracketOne : 1 + Real.log (b : ℝ) ≤
      6 * Real.log (a : ℝ) := by linarith
  have hCX : 0 ≤ C * (X : ℝ) := by positivity
  have hfirst :
      C * (X : ℝ) * (2 + Real.log (b : ℝ)) /
          Real.log (a : ℝ) ^ 5 ≤
        7 * C * (X : ℝ) / Real.log (a : ℝ) ^ 4 := by
    calc
      C * (X : ℝ) * (2 + Real.log (b : ℝ)) /
            Real.log (a : ℝ) ^ 5 ≤
          C * (X : ℝ) * (7 * Real.log (a : ℝ)) /
            Real.log (a : ℝ) ^ 5 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbracketTwo hCX)
          (pow_nonneg hloga.le 5)
      _ = 7 * C * (X : ℝ) / Real.log (a : ℝ) ^ 4 := by
        field_simp [hloga.ne']
  have hsecond :
      C * (X : ℝ) * (1 + Real.log (b : ℝ)) /
          Real.log (a : ℝ) ^ 6 ≤
        6 * C * (X : ℝ) / Real.log (a : ℝ) ^ 5 := by
    calc
      C * (X : ℝ) * (1 + Real.log (b : ℝ)) /
            Real.log (a : ℝ) ^ 6 ≤
          C * (X : ℝ) * (6 * Real.log (a : ℝ)) /
            Real.log (a : ℝ) ^ 6 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbracketOne hCX)
          (pow_nonneg hloga.le 6)
      _ = 6 * C * (X : ℝ) / Real.log (a : ℝ) ^ 5 := by
        field_simp [hloga.ne']
  have hpowTwoFour : Real.log (a : ℝ) ^ 2 ≤ Real.log (a : ℝ) ^ 4 := by
    calc
      Real.log (a : ℝ) ^ 2 = Real.log (a : ℝ) ^ 2 * 1 := by ring
      _ ≤ Real.log (a : ℝ) ^ 2 * Real.log (a : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hlogaOne) (sq_nonneg _)
      _ = Real.log (a : ℝ) ^ 4 := by ring
  have hpowTwoFive : Real.log (a : ℝ) ^ 2 ≤ Real.log (a : ℝ) ^ 5 := by
    calc
      Real.log (a : ℝ) ^ 2 = Real.log (a : ℝ) ^ 2 * 1 := by ring
      _ ≤ Real.log (a : ℝ) ^ 2 * Real.log (a : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hlogaOne) (sq_nonneg _)
      _ = Real.log (a : ℝ) ^ 5 := by ring
  have hfirstTarget :
      7 * C * (X : ℝ) / Real.log (a : ℝ) ^ 4 ≤
        7 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity)
      (pow_pos hloga 2) hpowTwoFour
  have hsecondTarget :
      6 * C * (X : ℝ) / Real.log (a : ℝ) ^ 5 ≤
        6 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity)
      (pow_pos hloga 2) hpowTwoFive
  have hinvLeOne : 1 / Real.log (a : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hlogaOne
  have hthirdBracket : 1 + 2 / Real.log (a : ℝ) ≤ 3 := by
    calc
      1 + 2 / Real.log (a : ℝ) =
          1 + 2 * (1 / Real.log (a : ℝ)) := by ring
      _ ≤ 1 + 2 * 1 :=
        add_le_add
          le_rfl
          (mul_le_mul_of_nonneg_left hinvLeOne
            (by norm_num : (0 : ℝ) ≤ 2))
      _ = 3 := by norm_num
  have hthirdCoeff :
      C * (X : ℝ) / Real.log (a : ℝ) ^ 5 ≤
        C * (X : ℝ) / Real.log (a : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left hCX (pow_pos hloga 2) hpowTwoFive
  have hthird :
      (C * (X : ℝ) / Real.log (a : ℝ) ^ 5) *
          (1 + 2 / Real.log (a : ℝ)) ≤
        3 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2 := by
    calc
      (C * (X : ℝ) / Real.log (a : ℝ) ^ 5) *
          (1 + 2 / Real.log (a : ℝ)) ≤
        (C * (X : ℝ) / Real.log (a : ℝ) ^ 2) * 3 :=
          mul_le_mul hthirdCoeff hthirdBracket (by positivity) (by positivity)
      _ = 3 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2 := by ring
  have hfull := sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_hyperbola
    hC (show 2 ≤ a by omega) hab hbX hu5
  calc
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) ≤
      16 * (C * (X : ℝ) * (2 + Real.log (b : ℝ)) /
          Real.log (a : ℝ) ^ 5 +
        C * (X : ℝ) * (1 + Real.log (b : ℝ)) /
          Real.log (a : ℝ) ^ 6) +
        (C * (X : ℝ) / Real.log (a : ℝ) ^ 5) *
          (1 + 2 / Real.log (a : ℝ)) := hfull
    _ ≤ 16 * (7 * C * (X : ℝ) / Real.log (a : ℝ) ^ 4 +
        6 * C * (X : ℝ) / Real.log (a : ℝ) ^ 5) +
        3 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by norm_num))
        hthird
    _ ≤ 16 * (7 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2 +
        6 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2) +
        3 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (add_le_add hfirstTarget hsecondTarget)
          (by norm_num : (0 : ℝ) ≤ 16))
        le_rfl
    _ = 211 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2 := by ring

/-- The fourth-power PNT variation ledger is controlled on every compact
Saias face, with no square-root or selector assumption. -/
theorem roughSaiasNaturalThetaPNTVariationLedger_fourth_le_invLogSq
    {C : ℝ} (hC : 0 ≤ C) {X y Z : ℕ}
    (hy3 : 3 ≤ y) (hyZ : y ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ) C X y Z ≤
      211 * C * (X : ℝ) / Real.log (y : ℝ) ^ 2 := by
  have hedgeSubset : Finset.Ioc y (Z - 1) ⊆ Finset.Ico y Z := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    rw [Finset.mem_Ico]
    omega
  have hnonneg : ∀ m ∈ Finset.Ico y Z,
      0 ≤ |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
        (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) := by
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    have hlogm : 0 < Real.log (m : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    exact mul_nonneg (abs_nonneg _) (by positivity)
  unfold roughSaiasNaturalThetaPNTVariationLedger
  rw [← Nat.cast_ofNat (n := 4)]
  simp_rw [Real.rpow_natCast]
  calc
    (∑ m ∈ Finset.Ioc y (Z - 1),
        |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) ≤
      ∑ m ∈ Finset.Ico y Z,
        |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hedgeSubset
        (fun m hm _hnot => hnonneg m hm)
    _ ≤ 211 * C * (X : ℝ) / Real.log (y : ℝ) ^ 2 :=
      sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_invLogSq
        hC hy3 hyZ hZX hu5

/-- On a range lying above the square-root transition, the complete
fourth-power natural-theta variation ledger is bounded by the explicit
hyperbola first moment and one harmonic tail. -/
theorem roughSaiasNaturalThetaPNTVariationLedger_fourth_le_upper_explicit
    {C : ℝ} (hC : 0 ≤ C) {X M Z : ℕ}
    (hM2 : 2 ≤ M) (hMZ : M ≤ Z) (hupper : X ≤ M ^ 2) :
    roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ) C X M Z ≤
      C * (X : ℝ) * (2 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 5 +
        C * (X : ℝ) * (1 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 6 := by
  have hedgeSubset : Finset.Ioc M (Z - 1) ⊆ Finset.Ico M Z := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    rw [Finset.mem_Ico]
    omega
  have hpoint : ∀ m ∈ Finset.Ioc M (Z - 1),
      |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) ≤
        roughSaiasSelectorCellLedger X m *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) := by
    intro m hm
    have hmData := Finset.mem_Ioc.mp hm
    have hMmPred : M ≤ m - 1 := by omega
    have hupperPred : X ≤ (m - 1) ^ 2 :=
      hupper.trans (Nat.pow_le_pow_left hMmPred 2)
    exact mul_le_mul_of_nonneg_right
      (roughSaiasNaturalQuotientThetaWeight_succ_sub_abs_le_selectorCellLedger
        (by omega) hupperPred) (by positivity)
  have hnonneg : ∀ m ∈ Finset.Ico M Z,
      0 ≤ roughSaiasSelectorCellLedger X m *
        (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) := by
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    have hm2 : 2 ≤ m := hM2.trans hmData.1
    have hlogm : 0 < Real.log (m : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    have hdrop : 0 ≤ roughSaiasNaturalQuotientDrop X m :=
      roughSaiasNaturalQuotientDrop_nonneg X (by omega)
    have hledger : 0 ≤ roughSaiasSelectorCellLedger X m := by
      unfold roughSaiasSelectorCellLedger
      exact add_nonneg
        (div_nonneg hdrop hlogm.le)
        (mul_nonneg (by positivity)
          (roughSaias_invLog_succ_sub_nonneg hm2))
    exact mul_nonneg hledger (by positivity)
  unfold roughSaiasNaturalThetaPNTVariationLedger
  rw [← Nat.cast_ofNat (n := 4)]
  simp_rw [Real.rpow_natCast]
  calc
    (∑ m ∈ Finset.Ioc M (Z - 1),
        |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) ≤
      ∑ m ∈ Finset.Ioc M (Z - 1),
        roughSaiasSelectorCellLedger X m *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) :=
      Finset.sum_le_sum hpoint
    _ ≤ ∑ m ∈ Finset.Ico M Z,
        roughSaiasSelectorCellLedger X m *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hedgeSubset
        (fun m hm _hnot ↦ hnonneg m hm)
    _ ≤ _ := sum_roughSaiasSelectorCellLedger_mul_fourth_le
      hC X hM2 hMZ

/-- The explicit upper-selector variation is already at the target
inverse-log-square scale. -/
theorem roughSaiasNaturalThetaPNTVariationLedger_fourth_le_upper_invLogSq
    {C : ℝ} (hC : 0 ≤ C) {X M Z : ℕ}
    (hM3 : 3 ≤ M) (hMZ : M ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (M : ℝ) ≤ 5)
    (hupper : X ≤ M ^ 2) :
    roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ) C X M Z ≤
      13 * C * (X : ℝ) / Real.log (M : ℝ) ^ 2 := by
  have hMpos : 0 < (M : ℝ) := by positivity
  have hZpos : 0 < (Z : ℝ) := by
    exact_mod_cast (show 0 < Z by omega)
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hlogMOne : 1 ≤ Real.log (M : ℝ) := by
    have hexp : Real.exp 1 < (M : ℝ) :=
      Real.exp_one_lt_three.trans_le (by exact_mod_cast hM3)
    exact ((Real.lt_log_iff_exp_lt hMpos).2 hexp).le
  have hlogZX : Real.log (Z : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hZpos (by exact_mod_cast hZX)
  have hlogX : Real.log (X : ℝ) ≤ 5 * Real.log (M : ℝ) :=
    (div_le_iff₀ hlogM).mp hu5
  have hlogZ : Real.log (Z : ℝ) ≤ 5 * Real.log (M : ℝ) :=
    hlogZX.trans hlogX
  have hbracketTwo :
      2 + Real.log (Z : ℝ) ≤ 7 * Real.log (M : ℝ) := by
    linarith
  have hbracketOne :
      1 + Real.log (Z : ℝ) ≤ 6 * Real.log (M : ℝ) := by
    linarith
  have hCX : 0 ≤ C * (X : ℝ) := by positivity
  have hfirst :
      C * (X : ℝ) * (2 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 5 ≤
        7 * C * (X : ℝ) / Real.log (M : ℝ) ^ 4 := by
    calc
      C * (X : ℝ) * (2 + Real.log (Z : ℝ)) /
            Real.log (M : ℝ) ^ 5 ≤
          C * (X : ℝ) * (7 * Real.log (M : ℝ)) /
            Real.log (M : ℝ) ^ 5 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbracketTwo hCX)
          (pow_nonneg hlogM.le 5)
      _ = 7 * C * (X : ℝ) / Real.log (M : ℝ) ^ 4 := by
        field_simp [hlogM.ne']
  have hsecond :
      C * (X : ℝ) * (1 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 6 ≤
        6 * C * (X : ℝ) / Real.log (M : ℝ) ^ 5 := by
    calc
      C * (X : ℝ) * (1 + Real.log (Z : ℝ)) /
            Real.log (M : ℝ) ^ 6 ≤
          C * (X : ℝ) * (6 * Real.log (M : ℝ)) /
            Real.log (M : ℝ) ^ 6 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbracketOne hCX)
          (pow_nonneg hlogM.le 6)
      _ = 6 * C * (X : ℝ) / Real.log (M : ℝ) ^ 5 := by
        field_simp [hlogM.ne']
  have hpowTwoFour : Real.log (M : ℝ) ^ 2 ≤
      Real.log (M : ℝ) ^ 4 := by
    calc
      Real.log (M : ℝ) ^ 2 = Real.log (M : ℝ) ^ 2 * 1 := by ring
      _ ≤ Real.log (M : ℝ) ^ 2 * Real.log (M : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hlogMOne)
          (sq_nonneg _)
      _ = Real.log (M : ℝ) ^ 4 := by ring
  have hpowTwoFive : Real.log (M : ℝ) ^ 2 ≤
      Real.log (M : ℝ) ^ 5 := by
    calc
      Real.log (M : ℝ) ^ 2 = Real.log (M : ℝ) ^ 2 * 1 := by ring
      _ ≤ Real.log (M : ℝ) ^ 2 * Real.log (M : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hlogMOne)
          (sq_nonneg _)
      _ = Real.log (M : ℝ) ^ 5 := by ring
  have hfirstTarget :
      7 * C * (X : ℝ) / Real.log (M : ℝ) ^ 4 ≤
        7 * C * (X : ℝ) / Real.log (M : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity)
      (pow_pos hlogM 2) hpowTwoFour
  have hsecondTarget :
      6 * C * (X : ℝ) / Real.log (M : ℝ) ^ 5 ≤
        6 * C * (X : ℝ) / Real.log (M : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity)
      (pow_pos hlogM 2) hpowTwoFive
  calc
    roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ) C X M Z ≤
      C * (X : ℝ) * (2 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 5 +
      C * (X : ℝ) * (1 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 6 :=
      roughSaiasNaturalThetaPNTVariationLedger_fourth_le_upper_explicit
        hC (by omega) hMZ hupper
    _ ≤ 7 * C * (X : ℝ) / Real.log (M : ℝ) ^ 4 +
        6 * C * (X : ℝ) / Real.log (M : ℝ) ^ 5 :=
      add_le_add hfirst hsecond
    _ ≤ 7 * C * (X : ℝ) / Real.log (M : ℝ) ^ 2 +
        6 * C * (X : ℝ) / Real.log (M : ℝ) ^ 2 :=
      add_le_add hfirstTarget hsecondTarget
    _ = 13 * C * (X : ℝ) / Real.log (M : ℝ) ^ 2 := by ring

/-- The full natural-theta prime-minus-integer transfer is closed on the
upper selector face. -/
theorem roughSaiasNaturalThetaErrorTransfer_abs_le_upper_invLogSq
    {X M Z : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ M)
    (hM3 : 3 ≤ M) (hMZ : M < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (M : ℝ) ≤ 5)
    (hupper : X ≤ M ^ 2) :
    |roughSaiasNaturalThetaErrorTransfer X M Z| ≤
      45 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
        Real.log (M : ℝ) ^ 2 := by
  have htransfer :=
    roughSaiasNaturalThetaErrorTransfer_abs_le_endpoint_add_variation_fourthPower
      hY (by omega) hMZ hZX hu5
  have hendpoint :=
    roughSaiasNaturalThetaPNTEndpointEnvelope_fourth_le_invLogSq
      (C := roughSaiasThetaFourthPowerConstant) (X := X)
      roughSaiasThetaFourthPowerConstant_pos.le hM3 hMZ
  have hvariation :=
    roughSaiasNaturalThetaPNTVariationLedger_fourth_le_upper_invLogSq
      roughSaiasThetaFourthPowerConstant_pos.le hM3 hMZ.le hZX hu5 hupper
  calc
    |roughSaiasNaturalThetaErrorTransfer X M Z| ≤
      roughSaiasNaturalThetaPNTEndpointEnvelope (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X M Z +
        roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X M Z := htransfer
    _ ≤ 32 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
          Real.log (M : ℝ) ^ 2 +
        13 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
          Real.log (M : ℝ) ^ 2 :=
      add_le_add hendpoint hvariation
    _ = 45 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
        Real.log (M : ℝ) ^ 2 := by ring

/-- The full natural-theta prime-minus-integer transfer is closed on every
compact Saias face.  No square-root or upper-selector condition remains. -/
theorem roughSaiasNaturalThetaErrorTransfer_abs_le_invLogSq
    {X y Z : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy3 : 3 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasNaturalThetaErrorTransfer X y Z| ≤
      243 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 := by
  have htransfer :=
    roughSaiasNaturalThetaErrorTransfer_abs_le_endpoint_add_variation_fourthPower
      hY (by omega) hyZ hZX hu5
  have hendpoint :=
    roughSaiasNaturalThetaPNTEndpointEnvelope_fourth_le_invLogSq
      (C := roughSaiasThetaFourthPowerConstant) (X := X)
      roughSaiasThetaFourthPowerConstant_pos.le hy3 hyZ
  have hvariation :=
    roughSaiasNaturalThetaPNTVariationLedger_fourth_le_invLogSq
      roughSaiasThetaFourthPowerConstant_pos.le hy3 hyZ.le hZX hu5
  calc
    |roughSaiasNaturalThetaErrorTransfer X y Z| ≤
      roughSaiasNaturalThetaPNTEndpointEnvelope (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X y Z +
        roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X y Z := htransfer
    _ ≤ 32 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
        211 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 :=
      add_le_add hendpoint hvariation
    _ = 243 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 := by ring

/-- After the global fourth-PNT transfer is closed, the exact remaining
analytic residual is only the lower fully-real natural-cell block. -/
theorem roughSaiasReverseNormalFormDefect_abs_le_lowerNaturalCells_add_invLogSq
    {X y M Z : ℕ} (hX : 0 < X)
    (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy3 : 3 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hyM : y ≤ M) (hMZ : M ≤ Z) (hupper : X ≤ M ^ 2) :
    |roughSaiasReverseNormalFormDefect X y Z| ≤
      |∑ m ∈ Finset.Ico y M,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m| +
      (3 + 243 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 := by
  have hnatural :=
    roughSaiasNaturalIntegerAbelConsistencyDefect_abs_le_lowerCells_add_three
      hX (by omega) hyZ hZX hu5 hyM hMZ hupper
  have htheta :=
    roughSaiasNaturalThetaErrorTransfer_abs_le_invLogSq
      hY hy3 hyZ hZX hu5
  rw [roughSaiasReverseNormalFormDefect_eq_naturalAbel_sub_theta]
  calc
    |roughSaiasNaturalIntegerAbelConsistencyDefect X y Z -
        roughSaiasNaturalThetaErrorTransfer X y Z| ≤
      |roughSaiasNaturalIntegerAbelConsistencyDefect X y Z| +
        |roughSaiasNaturalThetaErrorTransfer X y Z| := abs_sub _ _
    _ ≤
      (|∑ m ∈ Finset.Ico y M,
          roughSaiasFullyRealNaturalBuchstabCellRemainder X m| +
        3 * (X : ℝ) / Real.log (y : ℝ) ^ 2) +
      243 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 :=
      add_le_add hnatural htheta
    _ = |∑ m ∈ Finset.Ico y M,
          roughSaiasFullyRealNaturalBuchstabCellRemainder X m| +
        (3 + 243 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 := by ring

/-- Canonical dual form of the exact residual.  In the lower case
`y ≤ sqrt X + 1`, all unclosed mass has been transported to the upper
hyperbola interval; every index there satisfies `X/q ≤ q`. -/
theorem roughSaiasReverseNormalFormDefect_self_abs_le_dualLowerNaturalCells_add_invLogSq
    {X y : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy3 : 3 ≤ y) (hyX : y < X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hysqrt : y ≤ Nat.sqrt X + 1) :
    |roughSaiasReverseNormalFormDefect X y X| ≤
      |∑ q ∈ Finset.Ioc (X / (Nat.sqrt X + 1)) (X / y),
        roughSaiasDualSpreadFullyRealNaturalCellRemainder X (X / q)| +
      (3 + 243 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 := by
  have hX2 : 2 ≤ X := by omega
  have hMX : Nat.sqrt X + 1 ≤ X := by
    have htransition := roughSaiasSelectorTransition_le hX2 hyX.le
    simpa only [roughSaiasSelectorTransition, max_eq_right hysqrt] using
      htransition
  have hupper : X ≤ (Nat.sqrt X + 1) ^ 2 :=
    (Nat.lt_succ_sqrt' X).le
  have hbase :=
    roughSaiasReverseNormalFormDefect_abs_le_lowerNaturalCells_add_invLogSq
      (show 0 < X by omega) hY hy3 hyX le_rfl hu5 hysqrt hMX hupper
  rw [sum_roughSaiasFullyRealNaturalCells_eq_dualInvolution
      (show 0 < y by omega) hysqrt le_rfl] at hbase
  exact hbase

/-- The whole paired local discrepancy above a square-root transition has
the target inverse-log-square size. -/
theorem abs_sum_roughSaiasLocalNaturalPrimeCellDiscrepancy_upper_le_invLogSq
    {X M Z : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ M)
    (hM3 : 3 ≤ M) (hMZ : M ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (M : ℝ) ≤ 5)
    (hupper : X ≤ M ^ 2) :
    |∑ m ∈ Finset.Ico M Z,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m| ≤
      (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (M : ℝ) ^ 2 := by
  rcases hMZ.eq_or_lt with rfl | hMZlt
  · simp only [Finset.Ico_self, Finset.sum_empty, abs_zero]
    exact div_nonneg
      (mul_nonneg
        (add_nonneg (by norm_num)
          (mul_nonneg (by norm_num)
            roughSaiasThetaFourthPowerConstant_pos.le))
        (by positivity))
      (sq_nonneg _)
  · have hXpos : 0 < X := by omega
    have hM2 : 2 ≤ M := by omega
    have hcells :=
      abs_sum_roughSaiasFullyRealNaturalCells_upper_le_three_invLogSq
        hXpos hM2 hMZlt.le hupper
    have htheta :=
      roughSaiasNaturalThetaErrorTransfer_abs_le_upper_invLogSq
        hY hM3 hMZlt hZX hu5 hupper
    calc
      |∑ m ∈ Finset.Ico M Z,
          roughSaiasLocalNaturalPrimeCellDiscrepancy X m| =
        |(∑ m ∈ Finset.Ico M Z,
            roughSaiasFullyRealNaturalBuchstabCellRemainder X m) -
          roughSaiasNaturalThetaErrorTransfer X M Z| := by
        exact congrArg (fun t : ℝ => |t|)
          ((roughSaiasReverseNormalFormDefect_eq_sum_localNaturalPrimeCellDiscrepancy
              hM2 hMZlt hZX hu5).symm.trans
            (roughSaiasReverseNormalFormDefect_eq_naturalCells_sub_naturalTheta
              hM2 hMZlt hZX hu5))
      _ ≤ |∑ m ∈ Finset.Ico M Z,
            roughSaiasFullyRealNaturalBuchstabCellRemainder X m| +
          |roughSaiasNaturalThetaErrorTransfer X M Z| := abs_sub _ _
      _ ≤ 3 * (X : ℝ) / Real.log (M : ℝ) ^ 2 +
          45 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
            Real.log (M : ℝ) ^ 2 := add_le_add hcells htheta
      _ = (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (M : ℝ) ^ 2 := by ring

/-- Sharp reduction after closing the complete upper selector block.  Only
the signed local pairing below the square-root transition remains. -/
theorem roughSaiasReverseNormalFormDefect_abs_le_lowerLocal_add_upperInvLogSq
    {X y M Z : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy3 : 3 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hyM : y ≤ M) (hMZ : M ≤ Z) (hupper : X ≤ M ^ 2) :
    |roughSaiasReverseNormalFormDefect X y Z| ≤
      |∑ m ∈ Finset.Ico y M,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m| +
      (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 := by
  have hy2 : 2 ≤ y := by omega
  have hypos : 0 < (y : ℝ) := by
    exact_mod_cast (show 0 < y by omega)
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogyM : Real.log (y : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log hypos (by exact_mod_cast hyM)
  have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hu5M : Real.log (X : ℝ) / Real.log (M : ℝ) ≤ 5 :=
    (div_le_div_of_nonneg_left hlogX0 hlogy hlogyM).trans hu5
  have hupperBound :=
    abs_sum_roughSaiasLocalNaturalPrimeCellDiscrepancy_upper_le_invLogSq
      (hY.trans hyM) (hy3.trans hyM) hMZ hZX hu5M hupper
  have hpowers : Real.log (y : ℝ) ^ 2 ≤ Real.log (M : ℝ) ^ 2 :=
    pow_le_pow_left₀ hlogy.le hlogyM 2
  have hcoeffNonneg :
      0 ≤ (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) :=
    mul_nonneg
      (add_nonneg (by norm_num)
        (mul_nonneg (by norm_num)
          roughSaiasThetaFourthPowerConstant_pos.le))
      (by positivity)
  have hupperAtY :
      |∑ m ∈ Finset.Ico M Z,
          roughSaiasLocalNaturalPrimeCellDiscrepancy X m| ≤
        (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 :=
    hupperBound.trans
      (div_le_div_of_nonneg_left hcoeffNonneg (pow_pos hlogy 2) hpowers)
  rw [roughSaiasReverseNormalFormDefect_eq_sum_localNaturalPrimeCellDiscrepancy
      hy2 hyZ hZX hu5,
    sum_roughSaiasLocalNaturalPrimeCellDiscrepancy_split X hyM hMZ]
  exact (abs_add_le _ _).trans (add_le_add le_rfl hupperAtY)

/-- Canonical square-root-transition version of the preceding reduction. -/
theorem roughSaiasReverseNormalFormDefect_self_abs_le_canonicalLowerLocal_add_upperInvLogSq
    {X y : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy3 : 3 ≤ y) (hyX : y < X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasReverseNormalFormDefect X y X| ≤
      |∑ m ∈ Finset.Ico y (roughSaiasSelectorTransition X y),
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m| +
      (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 := by
  have hX2 : 2 ≤ X := by omega
  exact
    roughSaiasReverseNormalFormDefect_abs_le_lowerLocal_add_upperInvLogSq
      hY hy3 hyX le_rfl hu5
        (le_roughSaiasSelectorTransition X y)
        (roughSaiasSelectorTransition_le hX2 hyX.le)
        (roughSaiasSelectorTransition_sq_ge X y)

/-- If the original endpoint is already above the square-root transition,
the lower residual is empty and the upper estimate closes the whole
defect. -/
theorem roughSaiasReverseNormalFormDefect_self_abs_le_upperInvLogSq_of_sqrt_succ_le
    {X y : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy3 : 3 ≤ y) (hyX : y < X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hsqrt : Nat.sqrt X + 1 ≤ y) :
    |roughSaiasReverseNormalFormDefect X y X| ≤
      (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 := by
  have htransition : roughSaiasSelectorTransition X y = y := by
    simp only [roughSaiasSelectorTransition, max_eq_left hsqrt]
  simpa only [htransition, Finset.Ico_self, Finset.sum_empty, abs_zero,
    zero_add] using
      (roughSaiasReverseNormalFormDefect_self_abs_le_canonicalLowerLocal_add_upperInvLogSq
        hY hy3 hyX hu5)

/-- In the only remaining case `y ≤ sqrt X + 1`, the lower obstruction is
reindexed exactly onto the upper hyperbola interval.  Every displayed
index `q` satisfies `X/q ≤ q` by
`natDiv_le_self_of_mem_div_Ioc_of_le_sqrt_succ`. -/
theorem roughSaiasReverseNormalFormDefect_self_abs_le_dualLower_add_upperInvLogSq
    {X y : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy3 : 3 ≤ y) (hyX : y < X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hysqrt : y ≤ Nat.sqrt X + 1) :
    |roughSaiasReverseNormalFormDefect X y X| ≤
      |∑ q ∈ Finset.Ioc (X / (Nat.sqrt X + 1)) (X / y),
        roughSaiasDualSpreadLocalNaturalPrimeCellDiscrepancy X (X / q)| +
      (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 := by
  have hX2 : 2 ≤ X := by omega
  have hMX : Nat.sqrt X + 1 ≤ X := by
    have htransition := roughSaiasSelectorTransition_le hX2 hyX.le
    simpa only [roughSaiasSelectorTransition, max_eq_right hysqrt] using
      htransition
  have hupper : X ≤ (Nat.sqrt X + 1) ^ 2 :=
    (Nat.lt_succ_sqrt' X).le
  have hbase :=
    roughSaiasReverseNormalFormDefect_abs_le_lowerLocal_add_upperInvLogSq
      hY hy3 hyX le_rfl hu5 hysqrt hMX hupper
  rw [sum_roughSaiasLocalNaturalPrimeCellDiscrepancy_eq_dualInvolution
      (show 0 < y by omega) hysqrt le_rfl] at hbase
  exact hbase

/-- The ordinary Dickman continuous-prime discrepancy has the target
inverse-log-square size beyond the two already closed cutoffs. -/
theorem roughSaiasDickmanContinuousPrimeDiscrepancy_abs_le_invLogSq
    {X y Z : ℕ} (hYtheta : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hYriemann : roughSaiasRiemannAbsorptionCutoff ≤ y)
    (hX : 1 ≤ X) (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasDickmanContinuousPrimeDiscrepancy X y Z| ≤
      (1 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 := by
  have hriemann := roughSaiasDickmanBuchstabBlockRemainder_abs_le_invLogSq
    hYriemann hX hy2 hyZ.le hZX hu5
  have htheta := roughSaiasDickmanThetaTransfer_abs_le_invLogSq_fourthPower
    hYtheta hX hy2 hyZ hZX hu5
  have hidentity :=
    roughSaiasDickmanContinuousPrimeDiscrepancy_eq_riemann_sub_theta
      X y Z hyZ
  rw [hidentity]
  calc
    |roughSaiasDickmanBuchstabBlockRemainder X y Z -
        (FriableAsymptotic.primeThetaWeightedInterval
            (FriableAsymptotic.dickmanThetaWeight X) y Z -
          FriableAsymptotic.integerAbelMain
            (FriableAsymptotic.dickmanThetaWeight X) y Z)| ≤
      |roughSaiasDickmanBuchstabBlockRemainder X y Z| +
        |FriableAsymptotic.primeThetaWeightedInterval
            (FriableAsymptotic.dickmanThetaWeight X) y Z -
          FriableAsymptotic.integerAbelMain
            (FriableAsymptotic.dickmanThetaWeight X) y Z| := abs_sub _ _
    _ ≤ (X : ℝ) / Real.log (y : ℝ) ^ 2 +
        500 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 := add_le_add hriemann htheta
    _ = (1 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 := by ring

/-- Final sharp reduction: all standard terms are closed, and the literal
fully real correction discrepancy is the only remaining analytic target. -/
theorem roughSaiasReverseNormalFormDefect_abs_le_closed_add_sharpCorrection
    {X y Z : ℕ} (hYtheta : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hYriemann : roughSaiasRiemannAbsorptionCutoff ≤ y)
    (hX : 1 ≤ X) (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasReverseNormalFormDefect X y Z| ≤
      (1 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
        |roughSaiasSharpCorrectionObstruction X y Z| := by
  rw [roughSaiasReverseNormalFormDefect_eq_dickman_add_sharpCorrection
    hy2 hyZ hZX hu5]
  calc
    |roughSaiasDickmanContinuousPrimeDiscrepancy X y Z +
        roughSaiasSharpCorrectionObstruction X y Z| ≤
      |roughSaiasDickmanContinuousPrimeDiscrepancy X y Z| +
        |roughSaiasSharpCorrectionObstruction X y Z| := abs_add_le _ _
    _ ≤ (1 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
        |roughSaiasSharpCorrectionObstruction X y Z| :=
      add_le_add
        (roughSaiasDickmanContinuousPrimeDiscrepancy_abs_le_invLogSq
          hYtheta hYriemann hX hy2 hyZ hZX hu5) le_rfl

/-! ## Closed sharp defect and endpoint witnesses -/

/-- A concrete inverse-log-square constant for the fully closed reverse
normal-form defect.  The lower hyperbola block costs `40`; the remaining
integer-Abel and fourth-power theta terms cost
`3 + 243 * roughSaiasThetaFourthPowerConstant`. -/
noncomputable def roughSaiasSharpDefectConstant : ℝ :=
  43 + 243 * roughSaiasThetaFourthPowerConstant

/-- The only extra lower cutoff needed by the closed sharp defect is `3`. -/
noncomputable def roughSaiasSharpDefectCutoff : ℕ :=
  max 3 roughSaiasThetaFourthPowerCutoff

/-- The reverse normal-form defect at its natural endpoint has the sharp
inverse-log-square size throughout the compact face `log X / log y ≤ 5`.
The proof splits at the square-root transition: the upper case was already
closed, while the lower case is exactly the fully-real natural-cell
quadrature proved above. -/
theorem roughSaiasReverseNormalFormDefect_self_abs_le_sharp_invLogSq
    {X y : ℕ} (hY : roughSaiasSharpDefectCutoff ≤ y)
    (hyX : y < X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasReverseNormalFormDefect X y X| ≤
      roughSaiasSharpDefectConstant * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 := by
  have hy3 : 3 ≤ y := by
    exact (le_max_left 3 roughSaiasThetaFourthPowerCutoff).trans hY
  have hYtheta : roughSaiasThetaFourthPowerCutoff ≤ y := by
    exact (le_max_right 3 roughSaiasThetaFourthPowerCutoff).trans hY
  have hXpos : 0 < X := by omega
  have hX2 : 2 ≤ X := by omega
  have hCtheta : 0 ≤ roughSaiasThetaFourthPowerConstant :=
    roughSaiasThetaFourthPowerConstant_pos.le
  have htargetNonneg :
      0 ≤ (X : ℝ) / Real.log (y : ℝ) ^ 2 := by positivity
  by_cases hsqrt : Nat.sqrt X + 1 ≤ y
  · have hupper :=
      roughSaiasReverseNormalFormDefect_self_abs_le_upperInvLogSq_of_sqrt_succ_le
        hYtheta hy3 hyX hu5 hsqrt
    have hconst :
        3 + 45 * roughSaiasThetaFourthPowerConstant ≤
          roughSaiasSharpDefectConstant := by
      unfold roughSaiasSharpDefectConstant
      nlinarith
    calc
      |roughSaiasReverseNormalFormDefect X y X| ≤
          (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
            Real.log (y : ℝ) ^ 2 := hupper
      _ = (3 + 45 * roughSaiasThetaFourthPowerConstant) *
            ((X : ℝ) / Real.log (y : ℝ) ^ 2) := by ring
      _ ≤ roughSaiasSharpDefectConstant *
            ((X : ℝ) / Real.log (y : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hconst htargetNonneg
      _ = roughSaiasSharpDefectConstant * (X : ℝ) /
            Real.log (y : ℝ) ^ 2 := by ring
  · have hysqrt : y ≤ Nat.sqrt X + 1 := by omega
    have hMX : Nat.sqrt X + 1 ≤ X := by
      have htransition := roughSaiasSelectorTransition_le hX2 hyX.le
      exact (le_max_right y (Nat.sqrt X + 1)).trans htransition
    have hupperNat : X ≤ (Nat.sqrt X + 1) ^ 2 :=
      (Nat.lt_succ_sqrt' X).le
    have hbase :=
      roughSaiasReverseNormalFormDefect_abs_le_lowerNaturalCells_add_invLogSq
        hXpos hYtheta hy3 hyX le_rfl hu5 hysqrt hMX hupperNat
    have hlower :=
      abs_sum_roughSaiasFullyRealNaturalCells_lower_le_forty_invLogSq
        hXpos hy3 hysqrt hMX le_rfl hu5
    calc
      |roughSaiasReverseNormalFormDefect X y X| ≤
          |∑ m ∈ Finset.Ico y (Nat.sqrt X + 1),
              roughSaiasFullyRealNaturalBuchstabCellRemainder X m| +
            (3 + 243 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
              Real.log (y : ℝ) ^ 2 := hbase
      _ ≤ 40 * (X : ℝ) / Real.log (y : ℝ) ^ 2 +
            (3 + 243 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
              Real.log (y : ℝ) ^ 2 := add_le_add hlower le_rfl
      _ = roughSaiasSharpDefectConstant * (X : ℝ) /
            Real.log (y : ℝ) ^ 2 := by
        unfold roughSaiasSharpDefectConstant
        ring

/-- The concrete constant and cutoff above satisfy the abstract sharp
reverse-normal-form defect interface used by endpoint induction. -/
theorem roughSaiasSharpReverseNormalFormDefectInvLogSqBound :
    RoughSaiasReverseNormalFormDefectInvLogSqBound
      roughSaiasSharpDefectConstant roughSaiasSharpDefectCutoff := by
  intro X y hY hy2 hyX hlog
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5 :=
    (div_le_iff₀ hlogy).2 hlog
  exact roughSaiasReverseNormalFormDefect_self_abs_le_sharp_invLogSq
    hY hyX hu5

/-- Unconditional paper-scale endpoint approximation obtained from the
closed sharp reverse-normal-form defect. -/
theorem roughSaiasSharpEndpointApproximationUpToFive :
    RoughSaiasEndpointApproximationUpToFive
      (roughSaiasInvLogSqEndpointRate roughSaiasSharpDefectConstant)
      (roughSaiasInvLogSqEndpointCutoff roughSaiasSharpDefectCutoff) := by
  apply roughSaiasInvLogSqEndpointApproximationUpToFive_of_defect
  · unfold roughSaiasSharpDefectConstant
    have hCtheta : 0 ≤ roughSaiasThetaFourthPowerConstant :=
      roughSaiasThetaFourthPowerConstant_pos.le
    positivity
  · exact roughSaiasSharpReverseNormalFormDefectInvLogSqBound

end

end Erdos390.WholePaper
