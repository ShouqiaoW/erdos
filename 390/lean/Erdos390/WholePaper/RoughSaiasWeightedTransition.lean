import Erdos390.WholePaper.RoughSaiasNormalization
import Erdos390.WholePaper.RoughTransitionBalancedBlock

/-!
# Paper-scale weighted Saias transitions

The local residual predicate used by the method-of-steps development asks
for a short-interval estimate at every pair of natural endpoints.  That is
stronger than the Hildebrand--Tenenbaum--Saias input used in the paper.
The paper only needs one fixed four-endpoint block.  In that block the two
short increments have coefficients `1` and `delta * alpha`, while the broad
half-scale increment already has the coefficient `delta * beta / L`.

This file records that weaker and directly usable interface.  The endpoint
HT--Saias envelope contributes

`eta(y) * (A + B) + 5 * (B - A) / log y`

to a specified pair.  We retain those three contributions with their exact
block coefficients and close them to the existing
`roughPhysicalFriableCombination`.  No universal adjacent-pair regularity,
prime-transition predicate, selector conclusion, or new axiom is assumed.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-! ## A transition budget for one specified pair -/

/-- The exact two-endpoint ledger obtained from an HT--Saias endpoint
envelope and the deterministic normal-form correction. -/
def roughSaiasPairTransitionBudget
    (eta : ℕ → ℝ) (A B y : ℕ) : ℝ :=
  eta y * ((A : ℝ) + (B : ℝ)) +
    5 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ)

/-- HT--Saias endpoint approximation gives the desired residual increment
bound at any *specified* ordered pair.  Unlike the prime-transition ledger
form, this statement also covers the initial face `B <= y`; no reverse
Buchstab recurrence or universal local predicate is needed. -/
theorem roughFriableResidual_difference_abs_le_of_saiasEndpointApproximation
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ A B y : ℕ}
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hA : 0 < A) (hAB : A ≤ B)
    (hlogB : Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |roughFriableResidual B y - roughFriableResidual A y| ≤
      roughSaiasPairTransitionBudget eta A B y := by
  have hB : 0 < B := hA.trans_le hAB
  have hlogA : Real.log (A : ℝ) ≤
      5 * Real.log (y : ℝ) := by
    have hABlog : Real.log (A : ℝ) ≤ Real.log (B : ℝ) :=
      Real.log_le_log (by exact_mod_cast hA) (by exact_mod_cast hAB)
    exact hABlog.trans hlogB
  have herrorA : |roughSaiasEndpointError A y| ≤ eta y * (A : ℝ) :=
    happrox hY hy2 hA hlogA
  have herrorB : |roughSaiasEndpointError B y| ≤ eta y * (B : ℝ) :=
    happrox hY hy2 hB hlogB
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hB5 : FriableAsymptotic.dickmanU B y ≤ 5 := by
    dsimp [FriableAsymptotic.dickmanU]
    exact (div_le_iff₀ hlogy).2 hlogB
  have hcorrection := roughSaiasDickmanCorrection_difference_abs_le
    hBV hA hAB hy2 hB5
  rw [roughFriableResidual_difference_eq_saias]
  calc
    |(roughSaiasEndpointError B y - roughSaiasEndpointError A y) +
        (roughSaiasDickmanCorrection B y -
          roughSaiasDickmanCorrection A y)| ≤
      |roughSaiasEndpointError B y - roughSaiasEndpointError A y| +
        |roughSaiasDickmanCorrection B y -
          roughSaiasDickmanCorrection A y| := abs_add_le _ _
    _ ≤ (|roughSaiasEndpointError B y| +
          |roughSaiasEndpointError A y|) +
        |roughSaiasDickmanCorrection B y -
          roughSaiasDickmanCorrection A y| := by
      exact add_le_add (abs_sub _ _) le_rfl
    _ ≤ (eta y * (B : ℝ) + eta y * (A : ℝ)) +
        5 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) :=
      add_le_add (add_le_add herrorB herrorA) hcorrection
    _ = roughSaiasPairTransitionBudget eta A B y := by
      unfold roughSaiasPairTransitionBudget
      ring

/-! ## The literal weighted four-endpoint block -/

/-- The three residual transitions occurring in the paper's expanded
four-endpoint block.  The last summand is deliberately displayed with the
coefficient `|delta * (beta / L)|`: this is the broad half-scale pair, and
its paper-scale absorption uses that pre-existing `1/L`. -/
def roughPhysicalSaiasTransitionBudget
    (eta : ℕ → ℝ) (δ α β L : ℝ)
    (Xplus X Xminus Xhalf y : ℕ) : ℝ :=
  roughSaiasPairTransitionBudget eta X Xplus y +
    |δ * α| * roughSaiasPairTransitionBudget eta Xminus X y +
    |δ * (β / L)| *
      roughSaiasPairTransitionBudget eta Xhalf Xminus y

/-- The already-proved Dickman main-term and integer-endpoint imbalance
ledger, named so that the final paper-scale absorption statement is short
and can be consumed without unfolding the four coordinates. -/
def roughPhysicalDickmanTransitionLedger
    (δ α β L : ℝ) (Xplus X Xminus Xhalf y : ℕ) : ℝ :=
  (∑ i : Fin 4,
    |roughPhysicalBlockCoefficient δ α β L i| *
      (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) *
        |FriableAsymptotic.dickmanU
              (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i) y -
          FriableAsymptotic.dickmanU X y|) +
  |∑ i : Fin 4,
    roughPhysicalBlockCoefficient δ α β L i *
      (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ)|

/-- The complete residual part of the physical block is bounded by the
three *weighted* Saias pair ledgers.  In particular, no
`RoughFriableResidualLocalRegularity` or
`RoughFriablePrimeTransitionEstimateUpToFive` premise appears. -/
theorem roughPhysicalResidualTransition_abs_le_of_saiasEndpointApproximation
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ : ℕ}
    {δ α β L : ℝ} {Xplus X Xminus Xhalf y : ℕ}
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hhalf : 0 < Xhalf) (hHalfMinus : Xhalf ≤ Xminus)
    (hMinusX : Xminus ≤ X) (hXPlus : X ≤ Xplus)
    (hlogs : ∀ i : Fin 4,
      Real.log
          (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) ≤
        5 * Real.log (y : ℝ)) :
    |roughPhysicalResidualTransition δ α β L
        Xplus X Xminus Xhalf y| ≤
      roughPhysicalSaiasTransitionBudget eta δ α β L
        Xplus X Xminus Xhalf y := by
  have hminus : 0 < Xminus := hhalf.trans_le hHalfMinus
  have hx : 0 < X := hminus.trans_le hMinusX
  have hupper :=
    roughFriableResidual_difference_abs_le_of_saiasEndpointApproximation
      hBV happrox hY hy2 hx hXPlus (hlogs (0 : Fin 4))
  have hlower :=
    roughFriableResidual_difference_abs_le_of_saiasEndpointApproximation
      hBV happrox hY hy2 hminus hMinusX (hlogs (1 : Fin 4))
  have hbroad :
      |roughFriableResidual Xhalf y - roughFriableResidual Xminus y| ≤
        roughSaiasPairTransitionBudget eta Xhalf Xminus y := by
    simpa only [abs_sub_comm] using
      roughFriableResidual_difference_abs_le_of_saiasEndpointApproximation
        hBV happrox hY hy2 hhalf hHalfMinus (hlogs (2 : Fin 4))
  unfold roughPhysicalResidualTransition
  calc
    |(roughFriableResidual Xplus y - roughFriableResidual X y) -
        δ * α *
          (roughFriableResidual X y - roughFriableResidual Xminus y) +
        δ * (β / L) *
          (roughFriableResidual Xhalf y -
            roughFriableResidual Xminus y)| ≤
      |roughFriableResidual Xplus y - roughFriableResidual X y| +
        |δ * α| *
          |roughFriableResidual X y - roughFriableResidual Xminus y| +
        |δ * (β / L)| *
          |roughFriableResidual Xhalf y -
            roughFriableResidual Xminus y| := by
      calc
        _ ≤ |(roughFriableResidual Xplus y -
                roughFriableResidual X y) -
              δ * α *
                (roughFriableResidual X y -
                  roughFriableResidual Xminus y)| +
            |δ * (β / L) *
              (roughFriableResidual Xhalf y -
                roughFriableResidual Xminus y)| := abs_add_le _ _
        _ ≤ (|roughFriableResidual Xplus y -
                roughFriableResidual X y| +
              |δ * α *
                (roughFriableResidual X y -
                  roughFriableResidual Xminus y)|) +
            |δ * (β / L) *
              (roughFriableResidual Xhalf y -
                roughFriableResidual Xminus y)| := by
          exact add_le_add (abs_sub _ _) le_rfl
        _ = _ := by simp only [abs_mul]
    _ ≤ roughSaiasPairTransitionBudget eta X Xplus y +
        |δ * α| * roughSaiasPairTransitionBudget eta Xminus X y +
        |δ * (β / L)| *
          roughSaiasPairTransitionBudget eta Xhalf Xminus y := by
      exact add_le_add
        (add_le_add hupper
          (mul_le_mul_of_nonneg_left hlower (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left hbroad (abs_nonneg _))
    _ = roughPhysicalSaiasTransitionBudget eta δ α β L
        Xplus X Xminus Xhalf y := rfl

/-- The paper-scale weighted transition closes directly to the existing
four-endpoint friable selector expression.  The first summand is entirely
deterministic.  The second is the three-pair HT--Saias ledger above. -/
theorem roughPhysicalFriableCombination_abs_le_of_saiasEndpointApproximation
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ : ℕ}
    {δ α β L : ℝ} {Xplus X Xminus Xhalf y : ℕ}
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hhalf : 0 < Xhalf) (hHalfMinus : Xhalf ≤ Xminus)
    (hMinusX : Xminus ≤ X) (hXPlus : X ≤ Xplus)
    (hlogs : ∀ i : Fin 4,
      Real.log
          (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) ≤
        5 * Real.log (y : ℝ)) :
    |roughPhysicalFriableCombination δ α β L
        Xplus X Xminus Xhalf y| ≤
      roughPhysicalDickmanTransitionLedger δ α β L
          Xplus X Xminus Xhalf y +
        roughPhysicalSaiasTransitionBudget eta δ α β L
          Xplus X Xminus Xhalf y := by
  have hminus : 0 < Xminus := hhalf.trans_le hHalfMinus
  have hx : 0 < X := hminus.trans_le hMinusX
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hcoordinate5 : ∀ i : Fin 4,
      FriableAsymptotic.dickmanU
          (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i) y ≤ 5 := by
    intro i
    simp only [FriableAsymptotic.dickmanU]
    exact (div_le_iff₀ hlogY).2 (hlogs i)
  have hbase5 : FriableAsymptotic.dickmanU X y ≤ 5 := by
    have h := hcoordinate5 (1 : Fin 4)
    simpa only [roughPhysicalNatEndpoint] using h
  have hbase0 : 0 ≤ FriableAsymptotic.dickmanU X y := by
    simp only [FriableAsymptotic.dickmanU]
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega)))
      hlogY.le
  have hmain :
      |roughPhysicalDickmanCombination δ α β L
          Xplus X Xminus Xhalf y| ≤
        roughPhysicalDickmanTransitionLedger δ α β L
          Xplus X Xminus Xhalf y := by
    simpa only [roughPhysicalDickmanCombination,
      roughPhysicalDickmanTransitionLedger] using
      roughFriableMain_abs_le_with_balanceError
        (I := Finset.univ)
        (coeff := roughPhysicalBlockCoefficient δ α β L)
        (endpoint := roughPhysicalNatEndpoint
          Xplus X Xminus Xhalf)
        (base := X) (y := y)
        (fun i _hi ↦ hcoordinate5 i) hbase0 hbase5
  have htransition :
      |roughPhysicalResidualTransition δ α β L
          Xplus X Xminus Xhalf y| ≤
        roughPhysicalSaiasTransitionBudget eta δ α β L
          Xplus X Xminus Xhalf y :=
    roughPhysicalResidualTransition_abs_le_of_saiasEndpointApproximation
      (δ := δ) (α := α) (β := β) (L := L)
      hBV happrox hY hy2 hhalf hHalfMinus hMinusX hXPlus hlogs
  rw [roughPhysicalFriableCombination_eq_main_add_residualTransition]
  calc
    |roughPhysicalDickmanCombination δ α β L
          Xplus X Xminus Xhalf y +
        roughPhysicalResidualTransition δ α β L
          Xplus X Xminus Xhalf y| ≤
      |roughPhysicalDickmanCombination δ α β L
          Xplus X Xminus Xhalf y| +
        |roughPhysicalResidualTransition δ α β L
          Xplus X Xminus Xhalf y| := abs_add_le _ _
    _ ≤ roughPhysicalDickmanTransitionLedger δ α β L
          Xplus X Xminus Xhalf y +
        roughPhysicalSaiasTransitionBudget eta δ α β L
          Xplus X Xminus Xhalf y := add_le_add hmain htransition

/-! ## Paper-scale absorption and selector-facing closure -/

/-- Once the deterministic displacement/rounding ledger and the weighted
HT--Saias ledger have been absorbed at their paper scales, the existing
four-endpoint selector target inherits their sum.  This wrapper does not
weaken that target: its left side is literally
`roughPhysicalFriableCombination`. -/
theorem roughPhysicalFriableCombination_abs_le_of_saiasPaperScale
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ : ℕ}
    {δ α β L mainAllowance transitionAllowance : ℝ}
    {Xplus X Xminus Xhalf y : ℕ}
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hhalf : 0 < Xhalf) (hHalfMinus : Xhalf ≤ Xminus)
    (hMinusX : Xminus ≤ X) (hXPlus : X ≤ Xplus)
    (hlogs : ∀ i : Fin 4,
      Real.log
          (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) ≤
        5 * Real.log (y : ℝ))
    (hmain : roughPhysicalDickmanTransitionLedger δ α β L
        Xplus X Xminus Xhalf y ≤ mainAllowance)
    (htransition : roughPhysicalSaiasTransitionBudget eta δ α β L
        Xplus X Xminus Xhalf y ≤ transitionAllowance) :
    |roughPhysicalFriableCombination δ α β L
        Xplus X Xminus Xhalf y| ≤
      mainAllowance + transitionAllowance := by
  exact
    (roughPhysicalFriableCombination_abs_le_of_saiasEndpointApproximation
      hBV happrox hY hy2 hhalf hHalfMinus hMinusX hXPlus hlogs).trans
      (add_le_add hmain htransition)

/-- Symmetric paper-scale form: if each of the two finite ledgers is at
most `E`, the literal selector block is at most `2*E`. -/
theorem roughPhysicalFriableCombination_abs_le_two_mul_of_saiasPaperScale
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ : ℕ}
    {δ α β L E : ℝ} {Xplus X Xminus Xhalf y : ℕ}
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hhalf : 0 < Xhalf) (hHalfMinus : Xhalf ≤ Xminus)
    (hMinusX : Xminus ≤ X) (hXPlus : X ≤ Xplus)
    (hlogs : ∀ i : Fin 4,
      Real.log
          (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) ≤
        5 * Real.log (y : ℝ))
    (hmain : roughPhysicalDickmanTransitionLedger δ α β L
        Xplus X Xminus Xhalf y ≤ E)
    (htransition : roughPhysicalSaiasTransitionBudget eta δ α β L
        Xplus X Xminus Xhalf y ≤ E) :
    |roughPhysicalFriableCombination δ α β L
        Xplus X Xminus Xhalf y| ≤ 2 * E := by
  have h := roughPhysicalFriableCombination_abs_le_of_saiasPaperScale
    hBV happrox hY hy2 hhalf hHalfMinus hMinusX hXPlus hlogs
      hmain htransition
  nlinarith

end

end Erdos390.WholePaper
