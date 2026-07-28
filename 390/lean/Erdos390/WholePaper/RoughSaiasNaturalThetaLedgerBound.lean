import Erdos390.WholePaper.RoughSaiasFullyRealNaturalCells

/-!
# Deterministic reduction of the natural-theta transfer ledger

The fourth-power PNT input is already unconditional in the project.  This
file bounds both endpoint coefficients in its finite-Abel ledger and leaves
only one explicit weighted discrete variation of the paired natural theta
weight.  Thus neither a defect bound nor a signed-floor estimate remains as
an input to the theta transfer.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-- The sole interior term left in the natural-theta finite-Abel ledger. -/
noncomputable def roughSaiasNaturalThetaPNTVariationLedger
    (A C : ℝ) (X y Z : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioc y (Z - 1),
    |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
        roughSaiasNaturalQuotientThetaWeight X m| *
      (C * ((m : ℝ) / Real.log (m : ℝ) ^ A))

/-- Elementary endpoint envelope after using `|G| ≤ 16`. -/
noncomputable def roughSaiasNaturalThetaPNTEndpointEnvelope
    (A C : ℝ) (X y Z : ℕ) : ℝ :=
  (16 * (X : ℝ) / ((Z : ℝ) * Real.log (Z : ℝ))) *
      (C * ((Z : ℝ) / Real.log (Z : ℝ) ^ A)) +
    (16 * (X : ℝ) /
        (((y + 1 : ℕ) : ℝ) * Real.log ((y + 1 : ℕ) : ℝ))) *
      (C * ((y : ℝ) / Real.log (y : ℝ) ^ A))

/-- Uniform size bound for the paired natural theta weight throughout the
compact Buchstab interval. -/
theorem roughSaiasNaturalQuotientThetaWeight_abs_le_sixteen
    {X y Z m : ℕ} (hy2 : 2 ≤ y) (_hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hm : m ∈ Finset.Ioc y Z) :
    |roughSaiasNaturalQuotientThetaWeight X m| ≤
      16 * (X : ℝ) / ((m : ℝ) * Real.log (m : ℝ)) := by
  have hmData := Finset.mem_Ioc.mp hm
  have hm2 : 2 ≤ m := by omega
  have hmposNat : 0 < m := by omega
  have hmX : m ≤ X := hmData.2.trans hZX
  have hquotientPos : 0 < X / m := Nat.div_pos hmX hmposNat
  have hquotientOne : 1 ≤ X / m := hquotientPos
  have hquotientX : X / m ≤ X := Nat.div_le_self X m
  have hypos : 0 < (y : ℝ) := by
    exact_mod_cast (show 0 < y by omega)
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hmposNat
  have hXpos : 0 < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have hquotientPosR : 0 < ((X / m : ℕ) : ℝ) := by
    exact_mod_cast hquotientPos
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogq0 : 0 ≤ Real.log ((X / m : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hquotientOne)
  have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hlogqX : Real.log ((X / m : ℕ) : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hquotientPosR (by exact_mod_cast hquotientX)
  have hlogym : Real.log (y : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log hypos (by exact_mod_cast hmData.1.le)
  have hcoord0 :
      0 ≤ Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) :=
    div_nonneg hlogq0 hlogm.le
  have hcoord5 :
      Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) ≤ 5 := by
    calc
      Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) ≤
          Real.log (X : ℝ) / Real.log (m : ℝ) :=
        div_le_div_of_nonneg_right hlogqX hlogm.le
      _ ≤ Real.log (X : ℝ) / Real.log (y : ℝ) :=
        div_le_div_of_nonneg_left hlogX0 hlogy hlogym
      _ ≤ 5 := hu5
  have hG :
      |roughSaiasG m
          (Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ))| ≤ 16 := by
    rw [← roughSaiasFullyRealG_nat]
    exact roughSaiasFullyRealG_abs_le_sixteen
      (by exact_mod_cast (show 1 < m by omega)) ⟨hcoord0, hcoord5⟩
  have hquotientReal : ((X / m : ℕ) : ℝ) ≤
      (X : ℝ) / (m : ℝ) := Nat.cast_div_le
  unfold roughSaiasNaturalQuotientThetaWeight roughSaiasNaturalMain
    FriableAsymptotic.dickmanU
  rw [abs_div, abs_mul, abs_of_nonneg (by positivity), abs_of_pos hlogm]
  calc
    ((X / m : ℕ) : ℝ) *
          |roughSaiasG m
            (Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ))| /
        Real.log (m : ℝ) ≤
      (((X : ℝ) / (m : ℝ)) * 16) / Real.log (m : ℝ) := by
        apply div_le_div_of_nonneg_right _ hlogm.le
        exact mul_le_mul hquotientReal hG (abs_nonneg _) (by positivity)
    _ = 16 * (X : ℝ) / ((m : ℝ) * Real.log (m : ℝ)) := by
      ring

/-- Both endpoint terms in the natural-theta PNT ledger are now explicit;
only its interior weighted variation remains. -/
theorem roughSaiasNaturalThetaPNTLedger_le_endpoint_add_variation
    {A C : ℝ} {X y Z : ℕ} (hC : 0 ≤ C)
    (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasNaturalThetaPNTLedger A C X y Z ≤
      roughSaiasNaturalThetaPNTEndpointEnvelope A C X y Z +
        roughSaiasNaturalThetaPNTVariationLedger A C X y Z := by
  have hZmem : Z ∈ Finset.Ioc y Z := Finset.mem_Ioc.mpr ⟨hyZ, le_rfl⟩
  have hy1mem : y + 1 ∈ Finset.Ioc y Z :=
    Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  have hZend := roughSaiasNaturalQuotientThetaWeight_abs_le_sixteen
    hy2 hyZ hZX hu5 hZmem
  have hyend := roughSaiasNaturalQuotientThetaWeight_abs_le_sixteen
    hy2 hyZ hZX hu5 hy1mem
  have hZfactor : 0 ≤
      C * ((Z : ℝ) / Real.log (Z : ℝ) ^ A) := by positivity
  have hyfactor : 0 ≤
      C * ((y : ℝ) / Real.log (y : ℝ) ^ A) := by positivity
  unfold roughSaiasNaturalThetaPNTLedger
    roughSaiasNaturalThetaPNTEndpointEnvelope
    roughSaiasNaturalThetaPNTVariationLedger
  exact add_le_add
    (add_le_add
      (mul_le_mul_of_nonneg_right hZend hZfactor)
      (mul_le_mul_of_nonneg_right hyend hyfactor))
    le_rfl

/-- At fourth-power PNT strength the two endpoint terms have an additional
full reciprocal logarithm. -/
theorem roughSaiasNaturalThetaPNTEndpointEnvelope_fourth_le
    {C : ℝ} {X y Z : ℕ} (hC : 0 ≤ C) (hy2 : 2 ≤ y) (hyZ : y < Z) :
    roughSaiasNaturalThetaPNTEndpointEnvelope (4 : ℝ) C X y Z ≤
      32 * C * (X : ℝ) / Real.log (y : ℝ) ^ 5 := by
  have hypos : 0 < (y : ℝ) := by
    exact_mod_cast (show 0 < y by omega)
  have hy1pos : 0 < ((y + 1 : ℕ) : ℝ) := by positivity
  have hZpos : 0 < (Z : ℝ) := by
    exact_mod_cast (show 0 < Z by omega)
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogy1 : 0 < Real.log ((y + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y + 1 by omega))
  have hlogZ : 0 < Real.log (Z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  have hlogyZ : Real.log (y : ℝ) ≤ Real.log (Z : ℝ) :=
    Real.log_le_log hypos (by exact_mod_cast hyZ.le)
  have hlogyy1 : Real.log (y : ℝ) ≤
      Real.log ((y + 1 : ℕ) : ℝ) :=
    Real.log_le_log hypos (by exact_mod_cast (Nat.le_succ y))
  have hnumerator : 0 ≤ 16 * C * (X : ℝ) := by positivity
  have hZpow : Real.log (y : ℝ) ^ 5 ≤ Real.log (Z : ℝ) ^ 5 :=
    pow_le_pow_left₀ hlogy.le hlogyZ 5
  have hZterm :
      (16 * (X : ℝ) / ((Z : ℝ) * Real.log (Z : ℝ))) *
          (C * ((Z : ℝ) / Real.log (Z : ℝ) ^ 4)) ≤
        16 * C * (X : ℝ) / Real.log (y : ℝ) ^ 5 := by
    calc
      (16 * (X : ℝ) / ((Z : ℝ) * Real.log (Z : ℝ))) *
          (C * ((Z : ℝ) / Real.log (Z : ℝ) ^ 4)) =
        16 * C * (X : ℝ) / Real.log (Z : ℝ) ^ 5 := by
          field_simp [hZpos.ne', hlogZ.ne']
      _ ≤ 16 * C * (X : ℝ) / Real.log (y : ℝ) ^ 5 :=
        div_le_div_of_nonneg_left hnumerator (pow_pos hlogy 5) hZpow
  have hyDenom :
      (y : ℝ) * Real.log (y : ℝ) ≤
        ((y + 1 : ℕ) : ℝ) * Real.log ((y + 1 : ℕ) : ℝ) := by
    exact mul_le_mul (by exact_mod_cast (Nat.le_succ y)) hlogyy1
      hlogy.le (by positivity)
  have hyWeight :
      16 * (X : ℝ) /
          (((y + 1 : ℕ) : ℝ) * Real.log ((y + 1 : ℕ) : ℝ)) ≤
        16 * (X : ℝ) / ((y : ℝ) * Real.log (y : ℝ)) :=
    div_le_div_of_nonneg_left (by positivity)
      (mul_pos hypos hlogy) hyDenom
  have hyFactor : 0 ≤ C * ((y : ℝ) / Real.log (y : ℝ) ^ 4) := by
    positivity
  have hyTerm :
      (16 * (X : ℝ) /
          (((y + 1 : ℕ) : ℝ) * Real.log ((y + 1 : ℕ) : ℝ))) *
          (C * ((y : ℝ) / Real.log (y : ℝ) ^ 4)) ≤
        16 * C * (X : ℝ) / Real.log (y : ℝ) ^ 5 := by
    calc
      (16 * (X : ℝ) /
          (((y + 1 : ℕ) : ℝ) * Real.log ((y + 1 : ℕ) : ℝ))) *
          (C * ((y : ℝ) / Real.log (y : ℝ) ^ 4)) ≤
        (16 * (X : ℝ) / ((y : ℝ) * Real.log (y : ℝ))) *
          (C * ((y : ℝ) / Real.log (y : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_right hyWeight hyFactor
      _ = 16 * C * (X : ℝ) / Real.log (y : ℝ) ^ 5 := by
        field_simp [hypos.ne', hlogy.ne']
  unfold roughSaiasNaturalThetaPNTEndpointEnvelope
  have hZpowFour : Real.log (Z : ℝ) ^ (4 : ℝ) =
      Real.log (Z : ℝ) ^ (4 : ℕ) := by
    simpa only [Nat.cast_ofNat] using
      Real.rpow_natCast (Real.log (Z : ℝ)) 4
  have hypowFour : Real.log (y : ℝ) ^ (4 : ℝ) =
      Real.log (y : ℝ) ^ (4 : ℕ) := by
    simpa only [Nat.cast_ofNat] using
      Real.rpow_natCast (Real.log (y : ℝ)) 4
  rw [hZpowFour, hypowFour]
  calc
    (16 * (X : ℝ) / ((Z : ℝ) * Real.log (Z : ℝ))) *
          (C * ((Z : ℝ) / Real.log (Z : ℝ) ^ 4)) +
        (16 * (X : ℝ) /
          (((y + 1 : ℕ) : ℝ) * Real.log ((y + 1 : ℕ) : ℝ))) *
          (C * ((y : ℝ) / Real.log (y : ℝ) ^ 4)) ≤
      16 * C * (X : ℝ) / Real.log (y : ℝ) ^ 5 +
        16 * C * (X : ℝ) / Real.log (y : ℝ) ^ 5 :=
      add_le_add hZterm hyTerm
    _ = 32 * C * (X : ℝ) / Real.log (y : ℝ) ^ 5 := by ring

/-- For `y ≥ 3`, the endpoint envelope is already of the target
inverse-log-square size. -/
theorem roughSaiasNaturalThetaPNTEndpointEnvelope_fourth_le_invLogSq
    {C : ℝ} {X y Z : ℕ} (hC : 0 ≤ C) (hy3 : 3 ≤ y) (hyZ : y < Z) :
    roughSaiasNaturalThetaPNTEndpointEnvelope (4 : ℝ) C X y Z ≤
      32 * C * (X : ℝ) / Real.log (y : ℝ) ^ 2 := by
  have hypos : 0 < (y : ℝ) := by positivity
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogyOne : 1 ≤ Real.log (y : ℝ) := by
    have hexp : Real.exp 1 < (y : ℝ) :=
      Real.exp_one_lt_three.trans_le (by exact_mod_cast hy3)
    exact ((Real.lt_log_iff_exp_lt hypos).2 hexp).le
  have honeCube : 1 ≤ Real.log (y : ℝ) ^ 3 := one_le_pow₀ hlogyOne
  have hpowers : Real.log (y : ℝ) ^ 2 ≤ Real.log (y : ℝ) ^ 5 := by
    calc
      Real.log (y : ℝ) ^ 2 = Real.log (y : ℝ) ^ 2 * 1 := by ring
      _ ≤ Real.log (y : ℝ) ^ 2 * Real.log (y : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left honeCube (sq_nonneg _)
      _ = Real.log (y : ℝ) ^ 5 := by ring
  have hnumerator : 0 ≤ 32 * C * (X : ℝ) := by positivity
  exact (roughSaiasNaturalThetaPNTEndpointEnvelope_fourth_le
    hC (by omega) hyZ).trans
      (div_le_div_of_nonneg_left hnumerator (pow_pos hlogy 2) hpowers)

/-- General PNT-to-theta transfer with the endpoint estimates already
discharged. -/
theorem roughSaiasNaturalThetaErrorTransfer_abs_le_endpoint_add_variation
    {A C : ℝ} {X₀ X y Z : ℕ}
    (htheta : ∀ T, X₀ ≤ T →
      |FriableAsymptotic.primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / Real.log (T : ℝ) ^ A))
    (hC : 0 ≤ C) (hX₀y : X₀ ≤ y)
    (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasNaturalThetaErrorTransfer X y Z| ≤
      roughSaiasNaturalThetaPNTEndpointEnvelope A C X y Z +
        roughSaiasNaturalThetaPNTVariationLedger A C X y Z := by
  exact (roughSaiasNaturalThetaErrorTransfer_abs_le_pntLedger
    htheta hX₀y hyZ).trans
      (roughSaiasNaturalThetaPNTLedger_le_endpoint_add_variation
        hC hy2 hyZ hZX hu5)

/-- Closed fourth-power specialization.  No analytic premise remains; the
only unestimated object is the explicit deterministic weight variation. -/
theorem roughSaiasNaturalThetaErrorTransfer_abs_le_endpoint_add_variation_fourthPower
    {X y Z : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasNaturalThetaErrorTransfer X y Z| ≤
      roughSaiasNaturalThetaPNTEndpointEnvelope (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X y Z +
        roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X y Z := by
  exact roughSaiasNaturalThetaErrorTransfer_abs_le_endpoint_add_variation
    roughSaiasThetaFourthPower_bound
      roughSaiasThetaFourthPowerConstant_pos.le hY
        hy2 hyZ hZX hu5

/-- On the upper selector face, the complete reverse defect is reduced to
the already bounded cells, two explicit endpoint terms, and one local
natural-theta variation ledger. -/
theorem roughSaiasReverseNormalFormDefect_abs_le_cells_endpoint_variation
    {X y Z : ℕ} (hX : 0 < X) (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hupper : X ≤ y ^ 2) :
    |roughSaiasReverseNormalFormDefect X y Z| ≤
      3 * (X : ℝ) / Real.log (y : ℝ) ^ 2 +
        roughSaiasNaturalThetaPNTEndpointEnvelope (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X y Z +
        roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X y Z := by
  have hnatural :=
    roughSaiasNaturalIntegerAbelConsistencyDefect_abs_le_three_invLogSq_of_sq_le'
      hX hy2 hyZ hZX hu5 hupper
  have htheta :=
    roughSaiasNaturalThetaErrorTransfer_abs_le_endpoint_add_variation_fourthPower
      hY hy2 hyZ hZX hu5
  rw [roughSaiasReverseNormalFormDefect_eq_naturalAbel_sub_theta]
  calc
    |roughSaiasNaturalIntegerAbelConsistencyDefect X y Z -
        roughSaiasNaturalThetaErrorTransfer X y Z| ≤
      |roughSaiasNaturalIntegerAbelConsistencyDefect X y Z| +
        |roughSaiasNaturalThetaErrorTransfer X y Z| := abs_sub _ _
    _ ≤ 3 * (X : ℝ) / Real.log (y : ℝ) ^ 2 +
        (roughSaiasNaturalThetaPNTEndpointEnvelope (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X y Z +
        roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X y Z) :=
      add_le_add hnatural htheta
    _ = 3 * (X : ℝ) / Real.log (y : ℝ) ^ 2 +
        roughSaiasNaturalThetaPNTEndpointEnvelope (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X y Z +
        roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X y Z := by ring

end

end Erdos390.WholePaper
