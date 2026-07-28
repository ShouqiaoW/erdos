import Erdos390.WholePaper.RoughSaiasCanonicalRowBridge

/-! Literal statement checks for the canonical-row Saias consumer. -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example {y : ℕ} {A : Finset ℕ}
    (row : CanonicalCompleteRoughRow y A) :
    0 < row.1 ∧
      ∀ p, (row.1).factorization p ≠ 0 → y < p := by
  simpa only [IsCompleteRoughLabel] using
    isCompleteRoughLabel_of_canonicalCompleteRoughRow row

example {y label s : ℕ}
    (hlabel : IsCompleteRoughLabel y label)
    (hs : s ∈ Nat.smoothNumbers (y + 1)) :
    completeRoughLabel y (label * s) = label :=
  completeRoughLabel_mul_eq_of_isCompleteRoughLabel_of_smooth hlabel hs

example {lo hi y label : ℕ}
    (hlabel : IsCompleteRoughLabel y label) :
    (completeRoughRowFiber y (Finset.Ioc lo hi) label).card =
      (Erdos390.Full.StructuredCells.smoothInterval
        (lo / label) (hi / label) y).card :=
  completeRoughRowFiber_Ioc_card_eq_smoothInterval hlabel

example {W y label : ℕ} (hWy : W ≤ y)
    (hlabel : IsCompleteRoughLabel y label) :
    Nat.Coprime label (roughHeadModulus W) :=
  isCompleteRoughLabel_coprime_roughHeadModulus hWy hlabel

example {W lo hi y label : ℕ}
    (hlabel : IsCompleteRoughLabel y label)
    (hcop : Nat.Coprime label (roughHeadModulus W)) :
    (completeRoughRowFiber y
        (roughHeadFree W (Finset.Ioc lo hi)) label).card =
      (roughHeadFreeSmoothInterval W (lo / label) (hi / label) y).card :=
  completeRoughRowFiber_headFreeIoc_card_eq_headFreeSmoothInterval
    hlabel hcop

example (W n h K y : ℕ) (α β L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) :
    ∑ a ∈ rowSet
        (canonicalCompleteRoughRow y (roughRawCandidateSet n h K)) row,
      roughHeadCompatibleRawWeight W n h K α β L
        (canonicalCompleteRoughCandidateValue
          (roughRawCandidateSet n h K) a) =
      roughHeadCompatibleRawRowMass W n h K y row.1 α β L :=
  sum_canonicalCompleteRoughRowSet_rawWeight_eq_rawRowMass
    W n h K y α β L row

example (W n h K y : ℕ) (α β L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) :
    roughCanonicalRawRowQuotaError W n h K y α β L row =
      (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) -
        roughHeadCompatibleRawRowMass W n h K y row.1 α β L :=
  roughCanonicalRawRowQuotaError_eq_target_sub_rawRowMass
    W n h K y α β L row

example {n h K y : ℕ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) :
    (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) =
      (Erdos390.Full.FriableAsymptotic.friableCount
          ((2 * n + h) / row.1) y : ℝ) -
        (Erdos390.Full.FriableAsymptotic.friableCount
          ((2 * n) / row.1) y : ℝ) :=
  roughUpperCompleteRoughRowTarget_eq_friableEndpoints row

example (W n h K y label : ℕ) (α β L : ℝ) :
    roughHeadCompatibleRawRowMass W n h K y label α β L =
      α * ((completeRoughRowFiber y
        (roughHeadFree W (roughHighLowerBlock n h K)) label).card : ℝ) +
      (β / L) * ((completeRoughRowFiber y
        (roughHeadFree W (roughBroadLowerBlock n h K)) label).card : ℝ) :=
  roughHeadCompatibleRawRowMass_eq_headFreeRowCards
    W n h K y label α β L

example {W n h K y : ℕ} (hWy : W ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) (α β L : ℝ) :
    roughHeadCompatibleRawRowMass W n h K y row.1 α β L =
      roughHeadFreeSmoothPhysicalBlock W
        (n / row.1) ((2 * n - K * h) / row.1)
          ((2 * n) / row.1) y α (β / L) :=
  roughHeadCompatibleRawRowMass_eq_headFreeSmoothPhysicalBlock
    hWy row α β L

example {W n h K y : ℕ} (hWy : W ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) (α β L : ℝ) :
    roughHeadCompatibleRawRowMass W n h K y row.1 α β L =
      ∑ d ∈ (roughHeadModulus W).divisors,
        (ArithmeticFunction.moebius d : ℝ) *
          roughSmoothPhysicalBlock
            ((n / row.1) / d)
            (((2 * n - K * h) / row.1) / d)
            (((2 * n) / row.1) / d) y α (β / L) :=
  roughHeadCompatibleRawRowMass_eq_headDivisorShift hWy row α β L

example {W n h K y : ℕ} (hWy : W ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) (α β L : ℝ) :
    |roughHeadCompatibleRawRowMass W n h K y row.1 α β L -
        roughHeadDensity W *
          roughSmoothPhysicalBlock
            (n / row.1) ((2 * n - K * h) / row.1)
              ((2 * n) / row.1) y α (β / L)| ≤
      ∑ d ∈ (roughHeadModulus W).divisors,
        |(ArithmeticFunction.moebius d : ℝ)| *
          |roughSmoothPhysicalBlock
              ((n / row.1) / d)
              (((2 * n - K * h) / row.1) / d)
              (((2 * n) / row.1) / d) y α (β / L) -
            roughSmoothPhysicalBlock
              (n / row.1) ((2 * n - K * h) / row.1)
                ((2 * n) / row.1) y α (β / L) / (d : ℝ)| :=
  roughHeadCompatibleRawRowMass_sub_densityPhysicalBlock_abs_le
    hWy row α β L

example {W n h K y : ℕ} (hWy : W ≤ y) (hKh : K * h ≤ n)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) (α β L : ℝ) :
    |roughHeadCompatibleRawRowMass W n h K y row.1 α β L -
      roughHeadDensity W * roughPhysicalLowerFriableMass α β L
        ((2 * n) / row.1) ((2 * n - K * h) / row.1)
          (n / row.1) y| ≤
      roughCanonicalFixedHeadShiftLedger W n h K y α β L row :=
  roughHeadCompatibleRawRowMass_sub_densityLower_abs_le
    hWy hKh row α β L

example {W n h K y : ℕ} {α β L δ : ℝ}
    {Xplus X Xminus Xhalf : ℕ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hupper : (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) =
      (Erdos390.Full.FriableAsymptotic.friableCount Xplus y : ℝ) -
        (Erdos390.Full.FriableAsymptotic.friableCount X y : ℝ))
    (hraw : roughHeadCompatibleRawRowMass
        W n h K y row.1 α β L =
      δ * roughPhysicalLowerFriableMass
        α β L X Xminus Xhalf y) :
    roughCanonicalRawRowQuotaError W n h K y α β L row =
      roughPhysicalFriableCombination δ α β L
        Xplus X Xminus Xhalf y :=
  roughCanonicalRawRowQuotaError_eq_physicalFriableCombination
    row hupper hraw

example {W n h K y : ℕ} {α β L δ : ℝ}
    {Xplus X Xminus Xhalf : ℕ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hupper : (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) =
      (Erdos390.Full.FriableAsymptotic.friableCount Xplus y : ℝ) -
        (Erdos390.Full.FriableAsymptotic.friableCount X y : ℝ)) :
    |roughCanonicalRawRowQuotaError W n h K y α β L row -
        roughPhysicalFriableCombination δ α β L
          Xplus X Xminus Xhalf y| =
      |roughHeadCompatibleRawRowMass W n h K y row.1 α β L -
        δ * roughPhysicalLowerFriableMass
          α β L X Xminus Xhalf y| :=
  roughCanonicalRawRowQuotaError_sub_physicalFriableCombination_abs
    row hupper

example (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ W n h K y : ℕ}
    {α β L δ mainAllowance transitionAllowance headAllowance : ℝ}
    {Xplus X Xminus Xhalf : ℕ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hupper : (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) =
      (Erdos390.Full.FriableAsymptotic.friableCount Xplus y : ℝ) -
        (Erdos390.Full.FriableAsymptotic.friableCount X y : ℝ))
    (hhead : |roughHeadCompatibleRawRowMass
        W n h K y row.1 α β L -
      δ * roughPhysicalLowerFriableMass
        α β L X Xminus Xhalf y| ≤ headAllowance)
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
    |roughCanonicalRawRowQuotaError W n h K y α β L row| ≤
      mainAllowance + transitionAllowance + headAllowance :=
  roughCanonicalRawRowQuotaError_abs_le_of_saiasPaperScale
    hBV row hupper hhead happrox hY hy2 hhalf hHalfMinus hMinusX hXPlus
      hlogs hmain htransition

example (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ W n h K y : ℕ}
    {α β L δ mainAllowance transitionAllowance headAllowance : ℝ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hrowN : row.1 ≤ n) (hKh : K * h ≤ n)
    (hhead : |roughHeadCompatibleRawRowMass
        W n h K y row.1 α β L -
      δ * roughPhysicalLowerFriableMass α β L
        ((2 * n) / row.1) ((2 * n - K * h) / row.1)
          (n / row.1) y| ≤ headAllowance)
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hlogs : ∀ i : Fin 4,
      Real.log (roughPhysicalNatEndpoint
          ((2 * n + h) / row.1) ((2 * n) / row.1)
          ((2 * n - K * h) / row.1) (n / row.1) i : ℝ) ≤
        5 * Real.log (y : ℝ))
    (hmain : roughPhysicalDickmanTransitionLedger δ α β L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤
      mainAllowance)
    (htransition : roughPhysicalSaiasTransitionBudget eta δ α β L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤
      transitionAllowance) :
    |roughCanonicalRawRowQuotaError W n h K y α β L row| ≤
      mainAllowance + transitionAllowance + headAllowance :=
  roughCanonicalRawRowQuotaError_abs_le_of_literalSaiasPaperScale
    hBV row hrowN hKh hhead happrox hY hy2 hlogs hmain htransition

example (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ W n h K y : ℕ}
    {α β L mainAllowance transitionAllowance : ℝ}
    (hWy : W ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hrowN : row.1 ≤ n) (hKh : K * h ≤ n)
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hlogs : ∀ i : Fin 4,
      Real.log (roughPhysicalNatEndpoint
          ((2 * n + h) / row.1) ((2 * n) / row.1)
          ((2 * n - K * h) / row.1) (n / row.1) i : ℝ) ≤
        5 * Real.log (y : ℝ))
    (hmain : roughPhysicalDickmanTransitionLedger
        (roughHeadDensity W) α β L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤
      mainAllowance)
    (htransition : roughPhysicalSaiasTransitionBudget eta
        (roughHeadDensity W) α β L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤
      transitionAllowance) :
    |roughCanonicalRawRowQuotaError W n h K y α β L row| ≤
      mainAllowance + transitionAllowance +
        roughCanonicalFixedHeadShiftLedger W n h K y α β L row :=
  roughCanonicalRawRowQuotaError_abs_le_of_literalSaiasAndHeadLedger
    hBV hWy row hrowN hKh happrox hY hy2 hlogs hmain htransition

example (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ W n h K y : ℕ}
    {α β L E : ℝ}
    (hWy : W ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hrowN : row.1 ≤ n) (hKh : K * h ≤ n)
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hlogs : ∀ i : Fin 4,
      Real.log (roughPhysicalNatEndpoint
          ((2 * n + h) / row.1) ((2 * n) / row.1)
          ((2 * n - K * h) / row.1) (n / row.1) i : ℝ) ≤
        5 * Real.log (y : ℝ))
    (hmain : roughPhysicalDickmanTransitionLedger
        (roughHeadDensity W) α β L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤ E)
    (htransition : roughPhysicalSaiasTransitionBudget eta
        (roughHeadDensity W) α β L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤ E)
    (hhead : roughCanonicalFixedHeadShiftLedger
        W n h K y α β L row ≤ E) :
    |roughCanonicalRawRowQuotaError W n h K y α β L row| ≤ 3 * E :=
  roughCanonicalRawRowQuotaError_abs_le_three_mul_paperAllowance
    hBV hWy row hrowN hKh happrox hY hy2 hlogs hmain htransition hhead

end

end Erdos390.WholePaper
