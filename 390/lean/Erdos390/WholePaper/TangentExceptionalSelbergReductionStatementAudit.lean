import Erdos390.WholePaper.TangentExceptionalSelbergReduction

/-! # Statement audit for the exceptional-row Selberg reduction -/

open Filter Topology
open scoped BigOperators ArithmeticFunction

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

example (d : ℕ) :
    tangentReciprocalArithmeticFunction d =
      if d = 0 then 0 else 1 / (d : ℝ) :=
  rfl

example :
    tangentReciprocalArithmeticFunction.IsMultiplicative :=
  tangentReciprocalArithmeticFunction_isMultiplicative

example {d : ℕ} (hd : 0 < d) :
    tangentReciprocalArithmeticFunction d = 1 / (d : ℝ) :=
  tangentReciprocalArithmeticFunction_apply_of_pos hd

example (y : ℕ) : Squarefree (roughHeadModulus y) :=
  roughHeadModulus_squarefree y

example (y a : ℕ) :
    Nat.Coprime (completeRoughLabel y a) (roughHeadModulus y) :=
  completeRoughLabel_coprime_roughHeadModulus y a

example (P lo hi : ℕ) (hP : Squarefree P) :
    let s := tangentIntervalReciprocalSieve P lo hi hP
    (s.support, s.prodPrimes, s.weights, s.totalMass, s.nu) =
      (Finset.Ioc lo hi, P, (fun _ : ℕ ↦ (1 : ℝ)),
        ((hi - lo : ℕ) : ℝ), tangentReciprocalArithmeticFunction) :=
  rfl

example (P lo hi : ℕ) (hP : Squarefree P) :
    (tangentIntervalReciprocalSieve P lo hi hP).siftedSum =
      ((reducedResidueIoc P lo hi).card : ℝ) :=
  tangentIntervalReciprocalSieve_siftedSum P lo hi hP

example {P lo hi : ℕ} (hP : Squarefree P)
    (muPlus : ℕ → ℝ)
    (hmuPlus : BoundingSieve.IsUpperMoebius muPlus) :
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
      let s := tangentIntervalReciprocalSieve P lo hi hP
      s.totalMass * s.mainSum muPlus + s.errSum muPlus :=
  reducedResidueIoc_card_le_abstractSelberg hP muPlus hmuPlus

example {D lo hi : ℕ} (hD : 0 < D) :
    ((Finset.Ioc lo hi).filter (D ∣ ·)).card = hi / D - lo / D :=
  Ioc_filter_dvd_card_eq_div_sub_div hD

example {P lo hi D : ℕ} (hP : Squarefree P) (hD : 0 < D) :
    (tangentIntervalReciprocalSieve P lo hi hP).multSum D =
      ((hi / D - lo / D : ℕ) : ℝ) :=
  tangentIntervalReciprocalSieve_multSum hP hD

example {P lo hi D : ℕ} (hP : Squarefree P) (hD : 0 < D)
    (hlohi : lo ≤ hi) :
    |(tangentIntervalReciprocalSieve P lo hi hP).rem D| < 1 :=
  tangentIntervalReciprocalSieve_rem_abs_lt_one hP hD hlohi

example {P lo hi D : ℕ} (hP : Squarefree P) (hD : 0 < D) :
    |(tangentIntervalReciprocalSieve P lo hi hP).rem D| < 1 :=
  tangentIntervalReciprocalSieve_rem_abs_lt_one_total hP hD

example {P lo hi : ℕ} (hP : Squarefree P) (muPlus : ℕ → ℝ) :
    (tangentIntervalReciprocalSieve P lo hi hP).errSum muPlus ≤
      ∑ D ∈ P.divisors, |muPlus D| :=
  tangentIntervalReciprocalSieve_errSum_le_l1 hP muPlus

example {P lo hi : ℕ} (hP : Squarefree P) (muPlus : ℕ → ℝ)
    (hmuPlus : BoundingSieve.IsUpperMoebius muPlus) :
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
      ((hi - lo : ℕ) : ℝ) *
          (tangentIntervalReciprocalSieve P lo hi hP).mainSum muPlus +
        ∑ D ∈ P.divisors, |muPlus D| :=
  reducedResidueIoc_card_le_abstractSelberg_l1
    hP muPlus hmuPlus

example (X0 u : ℕ) :
    tangentExceptionalSmoothIndices X0 u =
      (Finset.Icc 1 X0).filter (fun b ↦ u * b < X0) :=
  rfl

example {n K h X0 y u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    (tangentExceptionalMultipliers n X0 y
      (tangentCommonMultiplierInterval n K h u v)).card ≤
      ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
        (tangentExceptionalRoughCandidates n K h y u v b).card :=
  card_tangentExceptionalMultipliers_le_sieveSum hu hv

example {X0 u : ℕ} (hu : 0 < u) :
    (tangentExceptionalSmoothIndices X0 u).card ≤ X0 / u :=
  card_tangentExceptionalSmoothIndices_le_div hu

example (X0 y u : ℕ) (muPlus : ℕ → ℝ) :
    (∑ _b ∈ tangentExceptionalSmoothIndices X0 u,
        ∑ D ∈ (roughHeadModulus y).divisors, |muPlus D|) =
      ((tangentExceptionalSmoothIndices X0 u).card : ℝ) *
        ∑ D ∈ (roughHeadModulus y).divisors, |muPlus D| :=
  tangentExceptional_l1_accumulation_eq X0 y u muPlus

example {X0 y u : ℕ} (hu : 0 < u) (muPlus : ℕ → ℝ) :
    (∑ _b ∈ tangentExceptionalSmoothIndices X0 u,
        ∑ D ∈ (roughHeadModulus y).divisors, |muPlus D|) ≤
      ((X0 / u : ℕ) : ℝ) *
        ∑ D ∈ (roughHeadModulus y).divisors, |muPlus D| :=
  tangentExceptional_l1_accumulation_le_div hu muPlus

example {X0 y u : ℕ} (hu : 0 < u) (muPlus : ℕ → ℝ) {B : ℝ}
    (hB : (∑ D ∈ (roughHeadModulus y).divisors, |muPlus D|) ≤ B) :
    (∑ _b ∈ tangentExceptionalSmoothIndices X0 u,
        ∑ D ∈ (roughHeadModulus y).divisors, |muPlus D|) ≤
      ((X0 / u : ℕ) : ℝ) * B :=
  tangentExceptional_l1_accumulation_le_of_bound hu muPlus hB

example (n K h y u v b : ℕ) :
    tangentExceptionalRoughCandidates n K h y u v b =
      reducedResidueIoc (roughHeadModulus y)
        (n / (v * b)) (tangentBroadUpper n K h / (u * b)) :=
  rfl

example (n K h X0 y u v : ℕ) :
    tangentExceptionalSievePairs n K h X0 y u v =
      (tangentExceptionalSmoothIndices X0 u).sigma
        (tangentExceptionalRoughCandidates n K h y u v) :=
  rfl

example (y a : ℕ) :
    tangentRoughDecompositionIndex y a =
      ⟨completeSmoothPart y a, completeRoughLabel y a⟩ :=
  rfl

example (y : ℕ) :
    Function.Injective (tangentRoughDecompositionIndex y) :=
  tangentRoughDecompositionIndex_injective y

example {n K h X0 y u v a : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (ha : a ∈ tangentExceptionalMultipliers n X0 y
      (tangentCommonMultiplierInterval n K h u v)) :
    tangentRoughDecompositionIndex y a ∈
      tangentExceptionalSievePairs n K h X0 y u v :=
  tangentRoughDecompositionIndex_mem_exceptionalSievePairs hu hv ha

example (n K h X0 y u v : ℕ) (muPlus : ℕ → ℝ) :
    tangentExceptionalAbstractSelbergMajorant
        n K h X0 y u v muPlus =
      ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
        let s := tangentIntervalReciprocalSieve
          (roughHeadModulus y)
          (n / (v * b)) (tangentBroadUpper n K h / (u * b))
          (roughHeadModulus_squarefree y)
        s.totalMass * s.mainSum muPlus + s.errSum muPlus :=
  rfl

example {n K h X0 y u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (muPlus : ℕ → ℝ)
    (hmuPlus : BoundingSieve.IsUpperMoebius muPlus) :
    ((tangentExceptionalMultipliers n X0 y
      (tangentCommonMultiplierInterval n K h u v)).card : ℝ) ≤
      tangentExceptionalAbstractSelbergMajorant
        n K h X0 y u v muPlus :=
  tangentExceptionalMultipliers_card_cast_le_abstractSelbergMajorant
    hu hv muPlus hmuPlus

example (n K h X0 y u v : ℕ) (muPlus : ℕ → ℝ) :
    tangentExceptionalAbstractSelbergL1Majorant
        n K h X0 y u v muPlus =
      ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
        let lo := n / (v * b)
        let hi := tangentBroadUpper n K h / (u * b)
        let s := tangentIntervalReciprocalSieve
          (roughHeadModulus y) lo hi (roughHeadModulus_squarefree y)
        ((hi - lo : ℕ) : ℝ) * s.mainSum muPlus +
          ∑ D ∈ (roughHeadModulus y).divisors, |muPlus D| :=
  rfl

example {n K h X0 y u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (muPlus : ℕ → ℝ)
    (hmuPlus : BoundingSieve.IsUpperMoebius muPlus) :
    ((tangentExceptionalMultipliers n X0 y
      (tangentCommonMultiplierInterval n K h u v)).card : ℝ) ≤
      tangentExceptionalAbstractSelbergL1Majorant
        n K h X0 y u v muPlus :=
  tangentExceptionalMultipliers_card_cast_le_abstractSelbergL1Majorant
    hu hv muPlus hmuPlus

example (n K h X0 y u v : ℕ) (muPlus : ℕ → ℝ) :
    tangentExceptionalAbstractSelbergNatMajorant
        n K h X0 y u v muPlus =
      ⌈tangentExceptionalAbstractSelbergMajorant
        n K h X0 y u v muPlus⌉₊ :=
  rfl

example {n K h X0 y u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (muPlus : ℕ → ℝ)
    (hmuPlus : BoundingSieve.IsUpperMoebius muPlus) :
    (tangentExceptionalMultipliers n X0 y
      (tangentCommonMultiplierInterval n K h u v)).card ≤
      tangentExceptionalAbstractSelbergNatMajorant
        n K h X0 y u v muPlus :=
  tangentExceptionalMultipliers_card_le_abstractSelbergNatMajorant
    hu hv muPlus hmuPlus

example {n K h Phead X0 y u v : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (dedicatedRows numericalGuards : Finset ℕ)
    (muPlus : ℕ → ℝ)
    (hmuPlus : BoundingSieve.IsUpperMoebius muPlus) :
    (tangentCommonMultiplierInterval n K h u v).card ≤
      (tangentCleanCommonMultiplierList
        n K h Phead X0 y u v dedicatedRows numericalGuards).card +
      (tangentHeadBadMultipliers Phead
        (tangentCommonMultiplierInterval n K h u v)).card +
      tangentExceptionalAbstractSelbergNatMajorant
        n K h X0 y u v muPlus +
      (tangentDedicatedRowMultipliers y dedicatedRows
        (tangentCommonMultiplierInterval n K h u v)).card +
      2 * numericalGuards.card :=
  tangentCommonMultiplier_abstractSelberg_finite_deletion_ledger
    hu hv dedicatedRows numericalGuards muPlus hmuPlus

example
    {c : ℝ} {depth n M W K h Phead X0 u v : ℕ}
    {left right : ℕ → ℕ} {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime)
    (muPlus : ℕ → ℝ)
    (hmuPlus : BoundingSieve.IsUpperMoebius muPlus) :
    (tangentCommonMultiplierInterval n K h u v).card ≤
      (tangentCleanCommonMultiplierList n K h Phead X0 (yNat n) u v
        R.tangentPaperDedicatedRows
        (R.tangentPaperNumericalGuardSet certificate fixedExceptional)).card +
      (tangentHeadBadMultipliers Phead
        (tangentCommonMultiplierInterval n K h u v)).card +
      tangentExceptionalAbstractSelbergNatMajorant
        n K h X0 (yNat n) u v muPlus +
      4 + 4 * bankPaperSharpMarkerBudget n :=
  R.tangentPaperCommonMultiplier_abstractSelberg_sharp_ledger
    certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
      hyCutoff huPrime hvPrime muPlus hmuPlus

example (n : ℕ) :
    y n ^ 4 = (n : ℝ) ^ (8 / 9 : ℝ) :=
  tangentExceptional_y_pow_four n

example (n : ℕ) :
    (yNat n : ℝ) ^ 4 ≤ (n : ℝ) ^ (8 / 9 : ℝ) :=
  tangentExceptional_yNat_pow_four_le n

example {deltaStar : ℝ} (hdeltaStar : deltaStar < 1 / 18) :
    deltaStar + 8 / 9 - 1 < -(1 / 18 : ℝ) :=
  tangentExceptional_deltaStar_remainder_exponent hdeltaStar

example {deltaStar : ℝ} (hdeltaStar : deltaStar < 1 / 18) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ (deltaStar + 8 / 9 - 1))
      atTop (nhds 0) :=
  tangentExceptional_remainderPower_tendsto_zero hdeltaStar

end

end Erdos390.WholePaper
