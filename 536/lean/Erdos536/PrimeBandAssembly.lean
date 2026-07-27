import Erdos536.AlternativeBandParameters
import Erdos536.PrimeBandPlacement

/-!
# Assembly of uniform prime-band estimates

This file performs the last finite parameter selection around the analytic
prime-band input.  A uniform event construction valid at every sufficiently
large scale is placed on finitely many disjoint bands.  Alternative-band
flattening and the one-coordinate reduction then finish the theorem.
-/

namespace Erdos536

open PrimeBandTimeChange

/-- The exact eventual analytic input needed from one prime band.  The
second-moment constant is uniform in the scale, while the event itself may
depend on the scale. -/
def HasEventuallyUniformPrimeBandEstimates : Prop :=
  ∀ (η : ℝ), 0 < η →
    ∃ (a K : ℝ) (T₀ : ℕ),
      0 ≤ K ∧
      ∀ T : ℕ, T₀ ≤ T →
        ∃ B : FiveConfiguration (broadPrimeBand T a) → Bool,
          FiveEventHasPetals (broadPrimeBand T a) B ∧
          0 < fiveEventMass
            (broadPrimeBand T a) reciprocalBernoulli B ∧
          FiveEventPetalLogBalanced
            (broadPrimeBand T a) B η ∧
          ∀ s : Fin 3,
            rootedSecondMoment Finset.univ
              (subtypeBernoulliWeight
                (broadPrimeBand T a) reciprocalBernoulli)
              (rootedBayesDensity
                (fiveEventMass
                  (broadPrimeBand T a) reciprocalBernoulli B)
                (fiveRootLikelihood
                  (broadPrimeBand T a) reciprocalBernoulli B s)) ≤ K

/-- Eventual uniform one-band estimates supply arbitrarily accurate
alternative-band certificates. -/
theorem alternativeBandCertificates_of_eventuallyUniformPrimeBandEstimates
    (hband : HasEventuallyUniformPrimeBandEstimates) :
    HasArbitrarilyGoodAlternativeBandCertificates := by
  intro A ε δ hε hδ
  obtain ⟨η, hη, hηδ⟩ :=
    exists_logTolerance_exp_sub_one_eq hδ
  obtain ⟨a, K, T₀, hK, hbandη⟩ := hband η hη
  obtain ⟨M, hM, hMK⟩ :=
    exists_alternativeCount_sqrt_div_lt hK hε
  let A' : ℕ := max A T₀
  have hAA' : A ≤ A' := Nat.le_max_left _ _
  have hT₀A' : T₀ ≤ A' := Nat.le_max_right _ _
  have hscale (j : Fin M) :
      T₀ ≤ placedPrimeBandScale A' a j.1 := by
    exact hT₀A'.trans
      (placedPrimeBandScale_above A' a j.1).le
  let B :
      ∀ j : Fin M,
        FiveConfiguration (placedPrimeBands A' M a j) → Bool :=
    fun j ↦ Classical.choose
      (hbandη (placedPrimeBandScale A' a j.1) (hscale j))
  have hB (j : Fin M) :
      FiveEventHasPetals (placedPrimeBands A' M a j) (B j) ∧
      0 < fiveEventMass
        (placedPrimeBands A' M a j) reciprocalBernoulli (B j) ∧
      FiveEventPetalLogBalanced
        (placedPrimeBands A' M a j) (B j) η ∧
      ∀ s : Fin 3,
        rootedSecondMoment Finset.univ
          (subtypeBernoulliWeight
            (placedPrimeBands A' M a j) reciprocalBernoulli)
          (rootedBayesDensity
            (fiveEventMass
              (placedPrimeBands A' M a j) reciprocalBernoulli (B j))
            (fiveRootLikelihood
              (placedPrimeBands A' M a j) reciprocalBernoulli
              (B j) s)) ≤ K := by
    exact Classical.choose_spec
      (hbandη (placedPrimeBandScale A' a j.1) (hscale j))
  let C' : AlternativeBandCertificate A' M η K :=
    alternativeBandCertificateOfPlacedBands hM B
      (fun j ↦ (hB j).1)
      (fun j ↦ (hB j).2.1)
      (fun j ↦ (hB j).2.2.1)
      hK
      (fun j s ↦ (hB j).2.2.2 s)
  let C : AlternativeBandCertificate A M η K :=
    C'.lowerCutoff_mono hAA'
  exact
    ⟨M, η, K, ⟨C⟩, hMK.le, hηδ.le⟩

/-- The final theorem-facing assembly: proving the displayed uniform
prime-band estimate proves Erdős 536. -/
theorem mainTheorem_of_eventuallyUniformPrimeBandEstimates
    (hband : HasEventuallyUniformPrimeBandEstimates) :
    MainTheorem :=
  mainTheorem_of_alternativeBandCertificates
    (alternativeBandCertificates_of_eventuallyUniformPrimeBandEstimates
      hband)

end Erdos536
