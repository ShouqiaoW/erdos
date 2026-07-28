import Erdos390.Full.FixedFiniteMixtureFullUniform
import Erdos390.Full.FiniteProbabilityMixtureTilt

/-!
# Paper-literal global-tilt form of Lemma 7.5

The paper first forms a finite mixture of uniform structured-cell laws and
then applies one exponential tilt to that tagged mixture.  A global tilt
changes the cell weights by their partition functions.  This file identifies
that law exactly with the post-tilt component mixture used by
`FixedFiniteMixtureFullUniform`, and exports the same five simultaneous
prime-power estimates for the paper's literal law.
-/

open Filter Topology

namespace Erdos390.Full.FixedFiniteMixtureGlobalTiltLemma75

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open StructuredCellValuationLaw ValuationScoreDomination
open FixedFiniteMixtureFullUniform PaperPrimePowerLemma75

noncomputable section

variable {Cell : Type*} [Fintype Cell]

/-- Extensionality of bounded valuation laws by their probability and value
fields; the positivity and endpoint fields are propositions and hence proof
irrelevant. -/
private theorem boundedValuationLaw_ext
    {Omega : Type*} [Fintype Omega] {M : ℕ}
    {law₁ law₂ : BoundedValuationLaw Omega M}
    (hprob : law₁.probability = law₂.probability)
    (hvalue : law₁.value = law₂.value) : law₁ = law₂ := by
  cases law₁ with
  | mk probability₁ value₁ value_pos₁ value_le₁ =>
    cases law₂ with
    | mk probability₂ value₂ value_pos₂ value_le₂ =>
      dsimp only at hprob hvalue
      subst probability₂
      subst value₂
      rfl

/-- The actual un-tilted tagged mixture of uniform structured cells, widened
to one common physical endpoint. -/
def uniformStructuredMixtureLaw
    (H : Cell → Pattern) (A C : Cell → ℝ) (Cmax : ℝ)
    (n : ℕ)
    (hC_le : ∀ c, C c ≤ Cmax)
    (hS : ∀ c, (structuredCell (H c)
      (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)).Nonempty)
    (weight : FiniteProbability Cell) :
    BoundedValuationLaw
      (Sigma fun c ↦ structuredCell (H c)
        (physicalBound (A c) n) (physicalBound (C c) n) (yNat n))
      (physicalBound Cmax n) :=
  sigmaMixture weight fun c ↦
    widen
      (ofProbability (H c) (physicalBound (A c) n)
        (physicalBound (C c) n) (yNat n)
        (uniformOnFinset
          (structuredCell (H c) (physicalBound (A c) n)
            (physicalBound (C c) n) (yNat n)) (hS c)))
      (physicalBound_mono (hC_le c) n)

/-- The common paper score on the tagged finite mixture. -/
def taggedValuationScore
    (H : Cell → Pattern) (A C : Cell → ℝ) (n W : ℕ)
    (eta : ℕ → ℝ) :
    (Sigma fun c ↦ structuredCell (H c)
      (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)) → ℝ :=
  fun x ↦ valuationScore (primeBand n W) eta (L n) x.2

/-- The paper-literal law: first take the tagged convex mixture of uniform
cells, then apply one global exponential tilt. -/
def globallyTiltedStructuredMixtureLaw
    (H : Cell → Pattern) (A C : Cell → ℝ) (Cmax : ℝ)
    (n W : ℕ) (eta : ℕ → ℝ)
    (hC_le : ∀ c, C c ≤ Cmax)
    (hS : ∀ c, (structuredCell (H c)
      (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)).Nonempty)
    (weight : FiniteProbability Cell) :
    BoundedValuationLaw
      (Sigma fun c ↦ structuredCell (H c)
        (physicalBound (A c) n) (physicalBound (C c) n) (yNat n))
      (physicalBound Cmax n) where
  probability :=
    (uniformStructuredMixtureLaw H A C Cmax n hC_le hS weight).probability
      |>.exponentialTilt (taggedValuationScore H A C n W eta)
  value := (uniformStructuredMixtureLaw H A C Cmax n hC_le hS weight).value
  value_pos :=
    (uniformStructuredMixtureLaw H A C Cmax n hC_le hS weight).value_pos
  value_le :=
    (uniformStructuredMixtureLaw H A C Cmax n hC_le hS weight).value_le

/-- The exact partition-function-reweighted cell law produced by the global
tilt. -/
def globallyTiltedCellWeight
    (H : Cell → Pattern) (A C : Cell → ℝ) (n W : ℕ)
    (eta : ℕ → ℝ)
    (hS : ∀ c, (structuredCell (H c)
      (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)).Nonempty)
    (weight : FiniteProbability Cell) : FiniteProbability Cell :=
  tiltedSigmaWeight weight
    (fun c ↦ uniformOnFinset
      (structuredCell (H c) (physicalBound (A c) n)
        (physicalBound (C c) n) (yNat n)) (hS c))
    (taggedValuationScore H A C n W eta)

/-- A global tilt of the initial mixture is exactly a tagged mixture of the
componentwise tilted laws with the partition-function-reweighted cell
weights.  This equality is at the level of `BoundedValuationLaw`, hence all
expectations and covariances are identified, not merely bounded. -/
theorem globallyTiltedStructuredMixtureLaw_eq_sigmaMixture
    (H : Cell → Pattern) (A C : Cell → ℝ) (Cmax : ℝ)
    (n W : ℕ) (eta : ℕ → ℝ)
    (hC_le : ∀ c, C c ≤ Cmax)
    (hS : ∀ c, (structuredCell (H c)
      (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)).Nonempty)
    (weight : FiniteProbability Cell) :
    globallyTiltedStructuredMixtureLaw H A C Cmax n W eta hC_le hS weight =
      sigmaMixture (globallyTiltedCellWeight H A C n W eta hS weight)
        (fun c ↦ widen
          (valuationTilt (H c) (physicalBound (A c) n)
            (physicalBound (C c) n) (yNat n) (hS c)
            (primeBand n W) eta (L n))
          (physicalBound_mono (hC_le c) n)) := by
  apply boundedValuationLaw_ext
  · change
      ((FiniteProbability.sigmaMixture weight
          (fun c ↦ uniformOnFinset
            (structuredCell (H c) (physicalBound (A c) n)
              (physicalBound (C c) n) (yNat n)) (hS c))).exponentialTilt
        (taggedValuationScore H A C n W eta)) = _
    rw [FiniteProbability.exponentialTilt_sigmaMixture]
    rfl
  · rfl

/-- **Paper-literal global-tilt export of Lemma 7.5.**

`C_pow` is chosen before both `W` and `B`.  For every fixed `W,B`, one
nonnegative function `epsilon_BW` tends to zero and occurs simultaneously in
the three sums of absolute prime-power covariances, the diagonal second
moment, and the genuine weighted row supremum.  The probability law in the
conclusion is literally the global exponential tilt of the initial convex
mixture, so the between-cell covariance and partition-function reweighting
are both included. -/
theorem boxIndependent_globalTilt_primePower_transfer
    (H : Cell → Pattern) (A C : Cell → ℝ) (Cmax : ℝ)
    (hA : ∀ c, 0 < A c) (hAC : ∀ c, A c < C c)
    (hC : ∀ c, 0 < C c) (hCmax : 0 < Cmax)
    (hC_le : ∀ c, C c ≤ Cmax) :
    0 < boxIndependentPrimePowerConstant ∧
      ∀ W : ℕ, 1 < W →
      (∀ c, ∀ p ∈ (H c).primes, p ≤ W) →
      ∀ B : ℝ, 0 ≤ B →
      ∃ epsilon_BW : ℕ → ℝ,
        (∀ n, 0 ≤ epsilon_BW n) ∧
        Tendsto epsilon_BW atTop (nhds 0) ∧
        Tendsto (fun n : ℕ ↦ epsilon_BW n * Real.log (L n))
          atTop (nhds 0) ∧
        ∃ N₀ : ℕ, ∀ {n : ℕ} (eta : ℕ → ℝ), N₀ ≤ n →
          (∀ z ∈ primeBand n W, |eta z| ≤ B) →
          let S := fun c ↦ structuredCell (H c)
            (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
          ( ∀ c, (S c).Nonempty) ∧
            ∀ hS : ∀ c, (S c).Nonempty,
            ∀ weight : FiniteProbability Cell,
              PrimePowerTransferBounds
                (globallyTiltedStructuredMixtureLaw H A C Cmax n W eta
                  hC_le hS weight)
                n W boxIndependentPrimePowerConstant (epsilon_BW n) := by
  obtain ⟨hCpow, hmain⟩ :=
    exists_boxIndependent_fixedFiniteMixture_primePower_transfer
      H A C Cmax hA hAC hC hCmax hC_le
  refine ⟨hCpow, ?_⟩
  intro W hW hsupport B hB
  obtain ⟨epsilon_BW, hepsilon0, hepsilonT, hepsilonRate, N₀, hN₀⟩ :=
    hmain W hW hsupport B hB
  refine ⟨epsilon_BW, hepsilon0, hepsilonT, hepsilonRate, N₀, ?_⟩
  intro n eta hn heta
  obtain ⟨hS, hbounds⟩ := hN₀ eta hn heta
  refine ⟨hS, ?_⟩
  intro hS weight
  have hpost := hbounds hS
    (globallyTiltedCellWeight H A C n W eta hS weight)
  rw [globallyTiltedStructuredMixtureLaw_eq_sigmaMixture
    H A C Cmax n W eta hC_le hS weight]
  exact hpost

/-- Existential presentation of the preceding explicit universal constant.
The witness is definitionally independent of the cell type and head
patterns. -/
theorem exists_boxIndependent_globalTilt_primePower_transfer
    (H : Cell → Pattern) (A C : Cell → ℝ) (Cmax : ℝ)
    (hA : ∀ c, 0 < A c) (hAC : ∀ c, A c < C c)
    (hC : ∀ c, 0 < C c) (hCmax : 0 < Cmax)
    (hC_le : ∀ c, C c ≤ Cmax) :
    ∃ C_pow : ℝ, 0 < C_pow ∧
      ∀ W : ℕ, 1 < W →
      (∀ c, ∀ p ∈ (H c).primes, p ≤ W) →
      ∀ B : ℝ, 0 ≤ B →
      ∃ epsilon_BW : ℕ → ℝ,
        (∀ n, 0 ≤ epsilon_BW n) ∧
        Tendsto epsilon_BW atTop (nhds 0) ∧
        Tendsto (fun n : ℕ ↦ epsilon_BW n * Real.log (L n))
          atTop (nhds 0) ∧
        ∃ N₀ : ℕ, ∀ {n : ℕ} (eta : ℕ → ℝ), N₀ ≤ n →
          (∀ z ∈ primeBand n W, |eta z| ≤ B) →
          let S := fun c ↦ structuredCell (H c)
            (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
          (∀ c, (S c).Nonempty) ∧
            ∀ hS : ∀ c, (S c).Nonempty,
            ∀ weight : FiniteProbability Cell,
              PrimePowerTransferBounds
                (globallyTiltedStructuredMixtureLaw H A C Cmax n W eta
                  hC_le hS weight)
                n W C_pow (epsilon_BW n) := by
  obtain ⟨hCpow, hmain⟩ := boxIndependent_globalTilt_primePower_transfer
    H A C Cmax hA hAC hC hCmax hC_le
  exact ⟨boxIndependentPrimePowerConstant, hCpow, hmain⟩

end

end Erdos390.Full.FixedFiniteMixtureGlobalTiltLemma75
