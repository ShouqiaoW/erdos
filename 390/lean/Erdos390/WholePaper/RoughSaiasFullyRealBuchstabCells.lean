import Erdos390.WholePaper.RoughSaiasFullyRealNormalForm
import Erdos390.WholePaper.RoughSaiasFunctionalBuchstab

/-!
# Unit-cell decomposition of the fully real Buchstab integral

The functional continuous-Buchstab identity is converted here into the
project's natural-base normal forms.  On a cell `s ∈ [m,m+1]`, the inner
term is split exactly into

* quotient drift at the current real base `s`, and
* real-base drift from `s` to the natural endpoint `m+1`.

No equality between the real and natural bases is left as a premise.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full

noncomputable section

noncomputable def roughSaiasFullyRealBuchstabNormalIntegrand
    (X : ℕ) (s : ℝ) : ℝ :=
  roughSaiasFullyRealLambdaNormalForm ((X : ℝ) / s) s /
    Real.log s

noncomputable def roughSaiasRealQuotientSelectorIntegrand
    (X : ℕ) (s : ℝ) : ℝ :=
  (((⌊(X : ℝ) / s⌋₊ : ℕ) : ℝ)) / Real.log s

/-- Above the square-root transition the fully real inner normal form is
on its initial face, hence is exactly the real quotient selector. -/
theorem roughSaiasFullyRealBuchstabNormalIntegrand_eq_selector
    {X : ℕ} {s : ℝ} (hX : 0 < X) (hs : 1 < s)
    (hupper : (X : ℝ) ≤ s ^ 2) :
    roughSaiasFullyRealBuchstabNormalIntegrand X s =
      roughSaiasRealQuotientSelectorIntegrand X s := by
  have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
  have hspos : 0 < s := zero_lt_one.trans hs
  have hqpos : 0 < (X : ℝ) / s := div_pos hXR hspos
  have hqs : (X : ℝ) / s ≤ s := by
    apply (div_le_iff₀ hspos).2
    simpa [pow_two] using hupper
  have hlogq : Real.log ((X : ℝ) / s) ≤ Real.log s :=
    Real.log_le_log hqpos hqs
  have hcoord : Real.log ((X : ℝ) / s) / Real.log s ≤ 1 :=
    (div_le_one (Real.log_pos hs)).2 hlogq
  unfold roughSaiasFullyRealBuchstabNormalIntegrand
    roughSaiasRealQuotientSelectorIntegrand
  rw [roughSaiasFullyRealLambdaNormalForm_eq_floor_of_le_one
    hqpos.le hcoord]

theorem roughSaiasFullyRealBuchstabNormalIntegrand_eq_selector_on_cell
    {X m : ℕ} (hX : 0 < X) (hm2 : 2 ≤ m)
    (hupper : X ≤ m ^ 2) {s : ℝ}
    (hs : s ∈ Set.Icc (m : ℝ) (m + 1 : ℕ)) :
    roughSaiasFullyRealBuchstabNormalIntegrand X s =
      roughSaiasRealQuotientSelectorIntegrand X s := by
  have hms : (m : ℝ) ≤ s := hs.1
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hs2 : (m : ℝ) ^ 2 ≤ s ^ 2 := by nlinarith
  have hupperR : (X : ℝ) ≤ s ^ 2 :=
    (by exact_mod_cast hupper : (X : ℝ) ≤ (m : ℝ) ^ 2).trans hs2
  have hsone : 1 < s :=
    (by exact_mod_cast (show 1 < m by omega) : (1 : ℝ) < (m : ℝ)).trans_le hs.1
  exact roughSaiasFullyRealBuchstabNormalIntegrand_eq_selector
    hX hsone hupperR

/-- On the natural range `y ≤ s ≤ Z ≤ X`, the fixed outer cutoff
`X` is canonical for the inner Stieltjes functional, and the latter is the
fully real normal form. -/
theorem roughSaiasLambdaStieltjesWithCutoff_inner_eq_fullyReal
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    {s : ℝ} (hs : s ∈ Set.Icc (y : ℝ) (Z : ℝ)) :
    roughSaiasLambdaStieltjesWithCutoff X ((X : ℝ) / s) s =
      roughSaiasFullyRealLambdaNormalForm ((X : ℝ) / s) s := by
  have hyone : 1 < (y : ℝ) := by
    exact_mod_cast (show 1 < y by omega)
  have hsone : 1 < s := hyone.trans_le hs.1
  have hspos : 0 < s := zero_lt_one.trans hsone
  have hXposNat : 0 < X := by omega
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast hXposNat
  have hsX : s ≤ (X : ℝ) :=
    hs.2.trans (by exact_mod_cast hZX)
  have hinnerPos : 0 < (X : ℝ) / s := div_pos hXpos hspos
  have hinnerOne : 1 ≤ (X : ℝ) / s :=
    (one_le_div hspos).2 hsX
  have hinnerCap : (X : ℝ) / s ≤ (X : ℝ) :=
    div_le_self hXpos.le hsone.le
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos hyone
  have hlogs : 0 < Real.log s := Real.log_pos hsone
  have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hlogys : Real.log (y : ℝ) ≤ Real.log s :=
    Real.log_le_log (zero_lt_one.trans hyone) hs.1
  have hratio : Real.log (X : ℝ) / Real.log s ≤ 5 :=
    (div_le_div_of_nonneg_left hlogX0 hlogy hlogys).trans hu5
  have hinnerFace :
      Real.log ((X : ℝ) / s) / Real.log s ≤ 5 := by
    rw [Real.log_div hXpos.ne' hspos.ne']
    calc
      (Real.log (X : ℝ) - Real.log s) / Real.log s =
          Real.log (X : ℝ) / Real.log s - 1 := by
        field_simp [hlogs.ne']
      _ ≤ 5 := by linarith
  rw [roughSaiasLambdaStieltjesWithCutoff_eq_canonical
    hinnerPos hsone hinnerCap]
  exact roughSaiasLambdaStieltjes_eq_fullyRealNormalForm
    hinnerOne hsone hinnerFace

/-- Exact continuous Buchstab for natural outer endpoints, with every
inner term expressed in the fully real Saias normal form. -/
theorem roughSaiasNaturalMain_buchstab_fullyReal
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasNaturalMain X y =
      roughSaiasNaturalMain X Z -
        ∫ s in (y : ℝ)..(Z : ℝ),
          roughSaiasFullyRealBuchstabNormalIntegrand X s := by
  have hXpos : 0 < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have hyone : 1 < (y : ℝ) := by
    exact_mod_cast (show 1 < y by omega)
  have hyZR : (y : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hyZ
  have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hZone : 1 < (Z : ℝ) := hyone.trans_le hyZR
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos hyone
  have hlogyZ : Real.log (y : ℝ) ≤ Real.log (Z : ℝ) :=
    Real.log_le_log (zero_lt_one.trans hyone) hyZR
  have hu5Z : Real.log (X : ℝ) / Real.log (Z : ℝ) ≤ 5 :=
    (div_le_div_of_nonneg_left hlogX0 hlogy hlogyZ).trans hu5
  have hbuch := roughSaiasLambdaStieltjesWithCutoff_buchstab_unconditional
    (R := X) (x := (X : ℝ)) (y := (y : ℝ)) (z := (Z : ℝ))
    hXpos hyone hyZR (hu5.trans (by norm_num))
  have hyEndpoint :
      roughSaiasLambdaStieltjesWithCutoff X (X : ℝ) (y : ℝ) =
        roughSaiasNaturalMain X y := by
    rw [← roughSaiasLambdaStieltjes_nat X (y : ℝ),
      roughSaiasLambdaStieltjes_nat_eq_normalForm
        (show 1 ≤ X by omega) hy2 hu5,
      roughSaiasNaturalMain_eq_lambdaNormalForm]
  have hZEndpoint :
      roughSaiasLambdaStieltjesWithCutoff X (X : ℝ) (Z : ℝ) =
        roughSaiasNaturalMain X Z := by
    rw [← roughSaiasLambdaStieltjes_nat X (Z : ℝ),
      roughSaiasLambdaStieltjes_nat_eq_normalForm
        (show 1 ≤ X by omega) (by omega) hu5Z,
      roughSaiasNaturalMain_eq_lambdaNormalForm]
  have hinner :
      (∫ s in (y : ℝ)..(Z : ℝ),
          roughSaiasLambdaStieltjesWithCutoff X ((X : ℝ) / s) s /
            Real.log s) =
        ∫ s in (y : ℝ)..(Z : ℝ),
          roughSaiasFullyRealBuchstabNormalIntegrand X s := by
    apply intervalIntegral.integral_congr
    intro s hsU
    have hsI : s ∈ Set.Icc (y : ℝ) (Z : ℝ) := by
      simpa [Set.uIcc_of_le hyZR] using hsU
    unfold roughSaiasFullyRealBuchstabNormalIntegrand
    change
      roughSaiasLambdaStieltjesWithCutoff X ((X : ℝ) / s) s /
          Real.log s =
        roughSaiasFullyRealLambdaNormalForm ((X : ℝ) / s) s /
          Real.log s
    rw [roughSaiasLambdaStieltjesWithCutoff_inner_eq_fullyReal
      hy2 hyZ hZX hu5 hsI]
  rw [hyEndpoint, hZEndpoint, hinner] at hbuch
  exact hbuch

theorem intervalIntegrable_roughSaiasFullyRealBuchstabNormalIntegrand
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    IntervalIntegrable
      (roughSaiasFullyRealBuchstabNormalIntegrand X)
      volume (y : ℝ) (Z : ℝ) := by
  have hXpos : 0 < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have hyone : 1 < (y : ℝ) := by
    exact_mod_cast (show 1 < y by omega)
  have hyZR : (y : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hyZ
  have hcap :=
    intervalIntegrable_roughSaiasLambdaStieltjesWithCutoff_buchstab
      (R := X) hXpos hyone hyZR (hu5.trans (by norm_num))
  apply hcap.congr
  intro s hsU
  have hsI : s ∈ Set.Icc (y : ℝ) (Z : ℝ) := by
    have hsU' : s ∈ Set.uIcc (y : ℝ) (Z : ℝ) :=
      Set.uIoc_subset_uIcc hsU
    simpa [Set.uIcc_of_le hyZR] using hsU'
  unfold roughSaiasFullyRealBuchstabNormalIntegrand
  change
    roughSaiasLambdaStieltjesWithCutoff X ((X : ℝ) / s) s /
        Real.log s =
      roughSaiasFullyRealLambdaNormalForm ((X : ℝ) / s) s /
        Real.log s
  rw [roughSaiasLambdaStieltjesWithCutoff_inner_eq_fullyReal
    hy2 hyZ hZX hu5 hsI]

/-! ## Natural unit cells -/

theorem integral_roughSaiasFullyRealBuchstab_eq_sum_cells
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    (∫ s in (y : ℝ)..(Z : ℝ),
        roughSaiasFullyRealBuchstabNormalIntegrand X s) =
      ∑ m ∈ Finset.Ico y Z,
        ∫ s in (m : ℝ)..(m + 1 : ℕ),
          roughSaiasFullyRealBuchstabNormalIntegrand X s := by
  have hglobal :=
    intervalIntegrable_roughSaiasFullyRealBuchstabNormalIntegrand
      hy2 hyZ hZX hu5
  have hint : ∀ m ∈ Finset.Ico y Z,
      IntervalIntegrable (roughSaiasFullyRealBuchstabNormalIntegrand X)
        volume (m : ℝ) (m + 1 : ℕ) := by
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    have hsubset : Set.uIcc (m : ℝ) (m + 1 : ℕ) ⊆
        Set.uIcc (y : ℝ) (Z : ℝ) := by
      rw [Set.uIcc_of_le (by norm_num : (m : ℝ) ≤ (m + 1 : ℕ)),
        Set.uIcc_of_le (by exact_mod_cast hyZ)]
      exact Set.Icc_subset_Icc
        (by exact_mod_cast hmData.1) (by exact_mod_cast (show m + 1 ≤ Z by omega))
    exact hglobal.mono_set hsubset
  symm
  exact intervalIntegral.sum_integral_adjacent_intervals_Ico hyZ
    (fun m hm ↦ hint m (Finset.mem_Ico.mpr hm))

/-- Right-endpoint sample on a unit cell, in the existing natural-base
theta weight. -/
theorem roughSaiasFullyRealBuchstabNormalIntegrand_nat
    (X m : ℕ) :
    roughSaiasFullyRealBuchstabNormalIntegrand X (m : ℝ) =
      roughSaiasNormalFormThetaWeight X m := by
  unfold roughSaiasFullyRealBuchstabNormalIntegrand
    roughSaiasNormalFormThetaWeight roughSaiasContinuousPrimeNormalForm
  rw [roughSaiasFullyRealLambdaNormalForm_nat]

theorem roughSaiasNormalFormThetaWeight_eq_selector_of_sq_le
    {X m : ℕ} (hX : 0 < X) (hm2 : 2 ≤ m) (hupper : X ≤ m ^ 2) :
    roughSaiasNormalFormThetaWeight X (m + 1) =
      roughSaiasRealQuotientSelectorIntegrand X (m + 1 : ℕ) := by
  rw [← roughSaiasFullyRealBuchstabNormalIntegrand_nat]
  apply roughSaiasFullyRealBuchstabNormalIntegrand_eq_selector
  · exact hX
  · exact_mod_cast (show 1 < m + 1 by omega)
  · have hmle : m ^ 2 ≤ (m + 1) ^ 2 := by nlinarith
    exact_mod_cast hupper.trans hmle

/-- Quotient drift inside the cell, with the real base held fixed. -/
noncomputable def roughSaiasFullyRealCellQuotientDrift
    (X m : ℕ) (s : ℝ) : ℝ :=
  (roughSaiasFullyRealLambdaNormalForm ((X : ℝ) / s) s -
      roughSaiasFullyRealLambdaNormalForm
        ((X : ℝ) / (m + 1 : ℕ)) s) /
    Real.log s

/-- Base drift from the current real base to the right natural endpoint. -/
noncomputable def roughSaiasFullyRealCellBaseDrift
    (X m : ℕ) (s : ℝ) : ℝ :=
  roughSaiasFullyRealLambdaNormalForm
        ((X : ℝ) / (m + 1 : ℕ)) s /
      Real.log s -
    roughSaiasNormalFormThetaWeight X (m + 1)

theorem roughSaiasFullyReal_cell_integrand_sub_sample
    (X m : ℕ) (s : ℝ) :
    roughSaiasFullyRealBuchstabNormalIntegrand X s -
        roughSaiasNormalFormThetaWeight X (m + 1) =
      roughSaiasFullyRealCellQuotientDrift X m s +
        roughSaiasFullyRealCellBaseDrift X m s := by
  unfold roughSaiasFullyRealBuchstabNormalIntegrand
    roughSaiasFullyRealCellQuotientDrift
    roughSaiasFullyRealCellBaseDrift
  ring

noncomputable def roughSaiasFullyRealBuchstabCellRemainder
    (X m : ℕ) : ℝ :=
  ∫ s in (m : ℝ)..(m + 1 : ℕ),
    (roughSaiasFullyRealBuchstabNormalIntegrand X s -
      roughSaiasNormalFormThetaWeight X (m + 1))

/-- On an upper selector cell, the real-base remainder has no hidden `G`:
it is exactly the quotient-selector quadrature error. -/
theorem roughSaiasFullyRealBuchstabCellRemainder_eq_selector
    {X m : ℕ} (hX : 0 < X) (hm2 : 2 ≤ m) (hupper : X ≤ m ^ 2) :
    roughSaiasFullyRealBuchstabCellRemainder X m =
      ∫ s in (m : ℝ)..(m + 1 : ℕ),
        (roughSaiasRealQuotientSelectorIntegrand X s -
          roughSaiasRealQuotientSelectorIntegrand X (m + 1 : ℕ)) := by
  unfold roughSaiasFullyRealBuchstabCellRemainder
  apply intervalIntegral.integral_congr
  intro s hsU
  have hsI : s ∈ Set.Icc (m : ℝ) (m + 1 : ℕ) := by
    simpa [Set.uIcc_of_le
      (by norm_num : (m : ℝ) ≤ (m + 1 : ℕ))] using hsU
  change
    roughSaiasFullyRealBuchstabNormalIntegrand X s -
        roughSaiasNormalFormThetaWeight X (m + 1) =
      roughSaiasRealQuotientSelectorIntegrand X s -
        roughSaiasRealQuotientSelectorIntegrand X (m + 1 : ℕ)
  rw [roughSaiasFullyRealBuchstabNormalIntegrand_eq_selector_on_cell
      hX hm2 hupper hsI,
    roughSaiasNormalFormThetaWeight_eq_selector_of_sq_le hX hm2 hupper]

/-- Pointwise right-endpoint quadrature bound for the quotient selector.
The first term is the exact natural quotient drop; hence its sum telescopes.
The second is only the variation of `1/log`. -/
theorem roughSaiasRealQuotientSelector_cell_sub_right_abs_le
    {X m : ℕ} (hm2 : 2 ≤ m) {s : ℝ}
    (hs : s ∈ Set.Icc (m : ℝ) (m + 1 : ℕ)) :
    |roughSaiasRealQuotientSelectorIntegrand X s -
        roughSaiasRealQuotientSelectorIntegrand X (m + 1 : ℕ)| ≤
      (((X / m : ℕ) : ℝ) - ((X / (m + 1) : ℕ) : ℝ)) /
          Real.log (m : ℝ) +
        ((X / (m + 1) : ℕ) : ℝ) *
          (1 / Real.log (m : ℝ) -
            1 / Real.log ((m + 1 : ℕ) : ℝ)) := by
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hmpos : 0 < (m : ℝ) := zero_lt_one.trans hmone
  have hspos : 0 < s := hmpos.trans_le hs.1
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := by positivity
  have hrealLower :
      (X : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ (X : ℝ) / s :=
    div_le_div_of_nonneg_left hX0 hspos hs.2
  have hrealUpper :
      (X : ℝ) / s ≤ (X : ℝ) / (m : ℝ) :=
    div_le_div_of_nonneg_left hX0 hmpos hs.1
  have hfloorLower := Nat.floor_le_floor hrealLower
  have hfloorUpper := Nat.floor_le_floor hrealUpper
  rw [Nat.floor_div_eq_div] at hfloorLower hfloorUpper
  let A : ℝ := (((⌊(X : ℝ) / s⌋₊ : ℕ) : ℝ))
  let q₀ : ℝ := ((X / m : ℕ) : ℝ)
  let q₁ : ℝ := ((X / (m + 1) : ℕ) : ℝ)
  have hq₁A : q₁ ≤ A := by
    dsimp [q₁, A]
    exact_mod_cast hfloorLower
  have hAq₀ : A ≤ q₀ := by
    dsimp [A, q₀]
    exact_mod_cast hfloorUpper
  have hq₁0 : 0 ≤ q₁ := by positivity
  have hq₁q₀ : q₁ ≤ q₀ := hq₁A.trans hAq₀
  have hLm : 0 < Real.log (m : ℝ) := Real.log_pos hmone
  have hsone : 1 < s := hmone.trans_le hs.1
  have hLs : 0 < Real.log s := Real.log_pos hsone
  have hLmLs : Real.log (m : ℝ) ≤ Real.log s :=
    Real.log_le_log hmpos hs.1
  have hLsL1 : Real.log s ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_le_log hspos hs.2
  have hInvLmLs : 1 / Real.log s ≤ 1 / Real.log (m : ℝ) :=
    one_div_le_one_div_of_le hLm hLmLs
  have hselectorNonneg :
      0 ≤ A / Real.log s - q₁ / Real.log ((m + 1 : ℕ) : ℝ) := by
    have hleft : q₁ / Real.log ((m + 1 : ℕ) : ℝ) ≤
        q₁ / Real.log s :=
      div_le_div_of_nonneg_left hq₁0 hLs hLsL1
    have hright : q₁ / Real.log s ≤ A / Real.log s :=
      div_le_div_of_nonneg_right hq₁A hLs.le
    linarith
  have hfirst :
      (A - q₁) / Real.log s ≤
        (q₀ - q₁) / Real.log (m : ℝ) := by
    calc
      (A - q₁) / Real.log s ≤
          (q₀ - q₁) / Real.log s :=
        div_le_div_of_nonneg_right (sub_le_sub_right hAq₀ q₁) hLs.le
      _ ≤ (q₀ - q₁) / Real.log (m : ℝ) :=
        div_le_div_of_nonneg_left (sub_nonneg.mpr hq₁q₀) hLm hLmLs
  have hsecond :
      q₁ * (1 / Real.log s -
          1 / Real.log ((m + 1 : ℕ) : ℝ)) ≤
        q₁ * (1 / Real.log (m : ℝ) -
          1 / Real.log ((m + 1 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left
      (sub_le_sub_right hInvLmLs _ ) hq₁0
  unfold roughSaiasRealQuotientSelectorIntegrand
  rw [Nat.floor_div_eq_div]
  change |A / Real.log s - q₁ / Real.log ((m + 1 : ℕ) : ℝ)| ≤ _
  rw [abs_of_nonneg hselectorNonneg]
  calc
    A / Real.log s - q₁ / Real.log ((m + 1 : ℕ) : ℝ) =
        (A - q₁) / Real.log s +
          q₁ * (1 / Real.log s -
            1 / Real.log ((m + 1 : ℕ) : ℝ)) := by ring
    _ ≤ (q₀ - q₁) / Real.log (m : ℝ) +
        q₁ * (1 / Real.log (m : ℝ) -
          1 / Real.log ((m + 1 : ℕ) : ℝ)) :=
      add_le_add hfirst hsecond
    _ = (((X / m : ℕ) : ℝ) - ((X / (m + 1) : ℕ) : ℝ)) /
          Real.log (m : ℝ) +
        ((X / (m + 1) : ℕ) : ℝ) *
          (1 / Real.log (m : ℝ) -
            1 / Real.log ((m + 1 : ℕ) : ℝ)) := by rfl

theorem roughSaiasFullyRealBuchstabCellRemainder_abs_le_selectorLedger
    {X m : ℕ} (hX : 0 < X) (hm2 : 2 ≤ m) (hupper : X ≤ m ^ 2) :
    |roughSaiasFullyRealBuchstabCellRemainder X m| ≤
      (((X / m : ℕ) : ℝ) - ((X / (m + 1) : ℕ) : ℝ)) /
          Real.log (m : ℝ) +
        ((X / (m + 1) : ℕ) : ℝ) *
          (1 / Real.log (m : ℝ) -
            1 / Real.log ((m + 1 : ℕ) : ℝ)) := by
  rw [roughSaiasFullyRealBuchstabCellRemainder_eq_selector hX hm2 hupper]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s : ℝ ↦
      roughSaiasRealQuotientSelectorIntegrand X s -
        roughSaiasRealQuotientSelectorIntegrand X (m + 1 : ℕ))
    (C :=
      (((X / m : ℕ) : ℝ) - ((X / (m + 1) : ℕ) : ℝ)) /
          Real.log (m : ℝ) +
        ((X / (m + 1) : ℕ) : ℝ) *
          (1 / Real.log (m : ℝ) -
            1 / Real.log ((m + 1 : ℕ) : ℝ)))
    (a := (m : ℝ)) (b := (m + 1 : ℕ)) (fun s hs ↦ by
      rw [Real.norm_eq_abs]
      apply roughSaiasRealQuotientSelector_cell_sub_right_abs_le hm2
      have hs' := Set.uIoc_subset_uIcc hs
      simpa [Set.uIcc_of_le
        (by norm_num : (m : ℝ) ≤ (m + 1 : ℕ))] using hs')
  simpa only [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_left, abs_one, mul_one] using hnorm

noncomputable def roughSaiasSelectorCellLedger (X m : ℕ) : ℝ :=
  (((X / m : ℕ) : ℝ) - ((X / (m + 1) : ℕ) : ℝ)) /
      Real.log (m : ℝ) +
    ((X / (m + 1) : ℕ) : ℝ) *
      (1 / Real.log (m : ℝ) -
        1 / Real.log ((m + 1 : ℕ) : ℝ))

theorem abs_sum_roughSaiasFullyRealBuchstabCellRemainder_le_selectorLedger
    {X M Z : ℕ} (hX : 0 < X) (hM2 : 2 ≤ M)
    (hupper : X ≤ M ^ 2) :
    |∑ m ∈ Finset.Ico M Z,
        roughSaiasFullyRealBuchstabCellRemainder X m| ≤
      ∑ m ∈ Finset.Ico M Z, roughSaiasSelectorCellLedger X m := by
  calc
    |∑ m ∈ Finset.Ico M Z,
        roughSaiasFullyRealBuchstabCellRemainder X m| ≤
      ∑ m ∈ Finset.Ico M Z,
        |roughSaiasFullyRealBuchstabCellRemainder X m| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Ico M Z,
        roughSaiasSelectorCellLedger X m := by
      apply Finset.sum_le_sum
      intro m hm
      have hmData := Finset.mem_Ico.mp hm
      have hm2 : 2 ≤ m := hM2.trans hmData.1
      have hMmSq : M ^ 2 ≤ m ^ 2 := by nlinarith
      have hXmSq : X ≤ m ^ 2 := hupper.trans hMmSq
      simpa [roughSaiasSelectorCellLedger] using
        roughSaiasFullyRealBuchstabCellRemainder_abs_le_selectorLedger
          hX hm2 hXmSq

theorem roughSaiasFullyRealBuchstabCellRemainder_eq_drifts
    (X m : ℕ) :
    roughSaiasFullyRealBuchstabCellRemainder X m =
      ∫ s in (m : ℝ)..(m + 1 : ℕ),
        (roughSaiasFullyRealCellQuotientDrift X m s +
          roughSaiasFullyRealCellBaseDrift X m s) := by
  unfold roughSaiasFullyRealBuchstabCellRemainder
  apply intervalIntegral.integral_congr
  intro s _hs
  exact roughSaiasFullyReal_cell_integrand_sub_sample X m s

theorem integral_roughSaiasFullyRealBuchstab_cell_eq_sample_add_remainder
    {X y Z m : ℕ} (hy2 : 2 ≤ y) (hyZ : y ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hm : m ∈ Finset.Ico y Z) :
    (∫ s in (m : ℝ)..(m + 1 : ℕ),
        roughSaiasFullyRealBuchstabNormalIntegrand X s) =
      roughSaiasNormalFormThetaWeight X (m + 1) +
        roughSaiasFullyRealBuchstabCellRemainder X m := by
  have hmData := Finset.mem_Ico.mp hm
  have hmle : m ≤ m + 1 := by omega
  have hym : y ≤ m := hmData.1
  have hmZ : m + 1 ≤ Z := by omega
  have hglobal :=
    intervalIntegrable_roughSaiasFullyRealBuchstabNormalIntegrand
      hy2 hyZ hZX hu5
  have hsubset : Set.uIcc (m : ℝ) (m + 1 : ℕ) ⊆
      Set.uIcc (y : ℝ) (Z : ℝ) := by
    rw [Set.uIcc_of_le (by exact_mod_cast hmle),
      Set.uIcc_of_le (by exact_mod_cast hyZ)]
    exact Set.Icc_subset_Icc (by exact_mod_cast hym) (by exact_mod_cast hmZ)
  have hcell := hglobal.mono_set hsubset
  have hconst : IntervalIntegrable
      (fun _ : ℝ ↦ roughSaiasNormalFormThetaWeight X (m + 1))
      volume (m : ℝ) (m + 1 : ℕ) :=
    continuous_const.intervalIntegrable _ _
  unfold roughSaiasFullyRealBuchstabCellRemainder
  rw [intervalIntegral.integral_sub hcell hconst]
  simp

/-- The natural endpoint difference is the discrete right-endpoint main
term plus the exact fully real cell remainders. -/
theorem roughSaiasNaturalMain_buchstab_sum_cells
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasNaturalMain X y =
      roughSaiasNaturalMain X Z -
        (FriableAsymptotic.integerAbelMain
          (roughSaiasNormalFormThetaWeight X) y Z +
          ∑ m ∈ Finset.Ico y Z,
            roughSaiasFullyRealBuchstabCellRemainder X m) := by
  have hcontinuous := roughSaiasNaturalMain_buchstab_fullyReal
    hy2 hyZ.le hZX hu5
  rw [integral_roughSaiasFullyRealBuchstab_eq_sum_cells
      hy2 hyZ.le hZX hu5]
    at hcontinuous
  have hcells :
      (∑ m ∈ Finset.Ico y Z,
          ∫ s in (m : ℝ)..(m + 1 : ℕ),
            roughSaiasFullyRealBuchstabNormalIntegrand X s) =
        ∑ m ∈ Finset.Ico y Z,
          (roughSaiasNormalFormThetaWeight X (m + 1) +
            roughSaiasFullyRealBuchstabCellRemainder X m) := by
    apply Finset.sum_congr rfl
    intro m hm
    exact integral_roughSaiasFullyRealBuchstab_cell_eq_sample_add_remainder
      hy2 hyZ.le hZX hu5 hm
  rw [hcells, Finset.sum_add_distrib] at hcontinuous
  have hsamples :
      (∑ m ∈ Finset.Ico y Z,
          roughSaiasNormalFormThetaWeight X (m + 1)) =
        FriableAsymptotic.integerAbelMain
          (roughSaiasNormalFormThetaWeight X) y Z := by
    rw [FriableAsymptotic.integerAbelMain_eq_sum_Ioc _ hyZ,
      FriableAsymptotic.sum_Ioc_shift]
  rw [hsamples] at hcontinuous
  exact hcontinuous

/-- Exact quadrature interpretation of the integer Abel consistency term. -/
theorem roughSaiasIntegerAbelConsistencyDefect_eq_cellRemainders
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasIntegerAbelConsistencyDefect X y Z =
      ∑ m ∈ Finset.Ico y Z,
        roughSaiasFullyRealBuchstabCellRemainder X m := by
  have hcells := roughSaiasNaturalMain_buchstab_sum_cells
    hy2 hyZ hZX hu5
  unfold roughSaiasIntegerAbelConsistencyDefect
  linarith

/-- The signed Abel center is now an explicit sum of fully real unit-cell
drifts plus the still-signed prime floor corrections. -/
theorem roughSaiasSignedAbelCenter_eq_cellRemainders_add_signedFloor
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasSignedAbelCenter X y Z =
      (∑ m ∈ Finset.Ico y Z,
        roughSaiasFullyRealBuchstabCellRemainder X m) +
      ∑ p ∈ roughReversePrimeInterval y Z,
        roughSaiasSignedFractionalCorrectionTerm X p := by
  unfold roughSaiasSignedAbelCenter
  rw [roughSaiasIntegerAbelConsistencyDefect_eq_cellRemainders
    hy2 hyZ hZX hu5]

/-- Fully explicit exact decomposition of the reverse normal-form defect:
real-base unit-cell quadrature, signed quotient floors, and the theta
transfer are the only three terms. -/
theorem roughSaiasReverseNormalFormDefect_eq_cells_add_floor_sub_theta
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasReverseNormalFormDefect X y Z =
      (∑ m ∈ Finset.Ico y Z,
        roughSaiasFullyRealBuchstabCellRemainder X m) +
      (∑ p ∈ roughReversePrimeInterval y Z,
        roughSaiasSignedFractionalCorrectionTerm X p) -
      roughSaiasThetaErrorTransfer X y Z := by
  rw [roughSaiasReverseNormalFormDefect_eq_signedAbelCenter_sub_theta,
    roughSaiasSignedAbelCenter_eq_cellRemainders_add_signedFloor
      hy2 hyZ hZX hu5]

end

end Erdos390.WholePaper
