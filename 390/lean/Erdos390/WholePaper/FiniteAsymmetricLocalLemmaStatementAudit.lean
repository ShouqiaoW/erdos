import Erdos390.WholePaper.FiniteAsymmetricLocalLemma

/-! # Expanded statement audit for the finite asymmetric local lemma -/

open MeasureTheory Set
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example {I Omega : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : I -> Set Omega) (Gamma : I -> Finset I) (x : I -> Real)
    (hA : ∀ i, MeasurableSet (A i))
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hindep : ∀ (i : I) (s : Finset I), i ∉ s ->
      Disjoint s (Gamma i) ->
      mu.real (A i ∩ (⋂ j ∈ s, (A j)ᶜ)) =
        mu.real (A i) * mu.real (⋂ j ∈ s, (A j)ᶜ))
    (hprobability : ∀ i,
      mu.real (A i) ≤
        x i * ∏ j ∈ Gamma i, (1 - x j)) :
    ∀ (s : Finset I) (i : I), i ∉ s ->
      mu.real (A i ∩ (⋂ j ∈ s, (A j)ᶜ)) ≤
        x i * mu.real (⋂ j ∈ s, (A j)ᶜ) := by
  apply finiteAsymmetricLocalLemma_conditionalBound
    mu A Gamma x hA hx
  · intro i s hi hdisjoint
    simpa only [avoidEvents] using hindep i s hi hdisjoint
  · exact hprobability

example {I Omega : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : I -> Set Omega) (Gamma : I -> Finset I) (x : I -> Real)
    (hA : ∀ i, MeasurableSet (A i))
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hindep : ∀ (i : I) (s : Finset I), i ∉ s ->
      Disjoint s (Gamma i) ->
      mu.real (A i ∩ (⋂ j ∈ s, (A j)ᶜ)) =
        mu.real (A i) * mu.real (⋂ j ∈ s, (A j)ᶜ))
    (hprobability : ∀ i,
      mu.real (A i) ≤
        x i * ∏ j ∈ Gamma i, (1 - x j)) :
    ∀ s : Finset I,
      (∏ i ∈ s, (1 - x i)) ≤
        mu.real (⋂ i ∈ s, (A i)ᶜ) := by
  apply finiteAsymmetricLocalLemma_lowerBound
    mu A Gamma x hA hx
  · intro i s hi hdisjoint
    simpa only [avoidEvents] using hindep i s hi hdisjoint
  · exact hprobability

example {I Omega : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : I -> Set Omega) (Gamma : I -> Finset I) (x : I -> Real)
    (hA : ∀ i, MeasurableSet (A i))
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hindep : ∀ (i : I) (s : Finset I), i ∉ s ->
      Disjoint s (Gamma i) ->
      mu.real (A i ∩ (⋂ j ∈ s, (A j)ᶜ)) =
        mu.real (A i) * mu.real (⋂ j ∈ s, (A j)ᶜ))
    (hprobability : ∀ i,
      mu.real (A i) ≤
        x i * ∏ j ∈ Gamma i, (1 - x j)) :
    0 < mu.real (⋂ i : I, (A i)ᶜ) := by
  apply finiteAsymmetricLocalLemma_iInter_positive
    mu A Gamma x hA hx
  · intro i s hi hdisjoint
    simpa only [avoidEvents] using hindep i s hi hdisjoint
  · exact hprobability

example {I Omega : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : I -> Set Omega) (Gamma : I -> Finset I) (x : I -> Real)
    (hA : ∀ i, MeasurableSet (A i))
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hindep : ∀ (i : I) (s : Finset I), i ∉ s ->
      Disjoint s (Gamma i) ->
      mu.real (A i ∩ (⋂ j ∈ s, (A j)ᶜ)) =
        mu.real (A i) * mu.real (⋂ j ∈ s, (A j)ᶜ))
    (hprobability : ∀ i,
      mu.real (A i) ≤
        x i * ∏ j ∈ Gamma i, (1 - x j)) :
    (⋂ i : I, (A i)ᶜ).Nonempty := by
  apply finiteAsymmetricLocalLemma_iInter_nonempty
    mu A Gamma x hA hx
  · intro i s hi hdisjoint
    simpa only [avoidEvents] using hindep i s hi hdisjoint
  · exact hprobability

example {I Omega : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : I -> Set Omega) (Gamma : I -> Finset I) (x : I -> Real)
    (hA : ∀ i, MeasurableSet (A i))
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hindep : ∀ (i : I) (s : Finset I), i ∉ s ->
      Disjoint s (Gamma i) ->
      mu.real (A i ∩ (⋂ j ∈ s, (A j)ᶜ)) =
        mu.real (A i) * mu.real (⋂ j ∈ s, (A j)ᶜ))
    (hprobability : ∀ i,
      mu.real (A i) ≤
        x i * ∏ j ∈ Gamma i, (1 - x j)) :
    ∃ omega : Omega, ∀ i : I, omega ∉ A i := by
  apply finiteAsymmetricLocalLemma mu A Gamma x hA hx
  · intro i s hi hdisjoint
    simpa only [avoidEvents] using hindep i s hi hdisjoint
  · exact hprobability

end

end Erdos390.WholePaper
