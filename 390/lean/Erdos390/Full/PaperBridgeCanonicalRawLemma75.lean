import Erdos390.Full.PaperBridgeCanonicalGuardPowerCorrection
import Erdos390.Full.FixedFiniteMixtureFullUniform

/-!
# Attaching the raw canonical bridge mixture to Lemma 7.5

The unguarded reference law used in the canonical guard comparison is a
finite mixture of the literal structured-cell valuation tilts.  Its mixture
weights are the actual post-tilt bridge weights, but Lemma 7.5 is uniform in
those weights.  This file records the exact specialization, including the
order of choices: the prime-power constant is selected before the cutoff and
coefficient box, and the eventual threshold is uniform in the bridge data,
tilt point, and component weights.
-/

open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperGuardCensus

namespace BridgeData

variable {Head : Type*} [Fintype Head] [DecidableEq Head]

/-- The canonical raw reference mixture satisfies the literal five-field
prime-power transfer of Lemma 7.5.  No condition on the post-tilt component
weights is needed: the fixed-finite-mixture theorem is uniform over every
finite probability on `Cell Head`.

The returned remainder is common to all five estimates and retains the
moving-low rate `epsilon(n) * log L(n) -> 0`. -/
theorem boxIndependent_canonicalRaw_primePower_transfer
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax) :
    0 < FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant ∧
      ∀ W : ℕ, 1 < W →
        (∀ h, ∀ p ∈ (P h).primes, p ≤ W) →
      ∀ Acoef : ℝ, 0 ≤ Acoef →
      ∃ epsilon : ℕ → ℝ,
        (∀ n, 0 ≤ epsilon n) ∧
        Tendsto epsilon atTop (nhds 0) ∧
        Tendsto (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
          atTop (nhds 0) ∧
        ∃ N₀ : ℕ,
          ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
            (B : BridgeData Head Band) (xi : B.ParamSpace),
            N₀ ≤ B.sampleData.n →
            B.sampleData.W = W →
            (∀ p : BandPrime B.sampleData.n B.sampleData.W,
              |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
            ∀ hS : ∀ c : Cell Head,
              (rawCell P I B.sampleData.n c).Nonempty,
              PaperPrimePowerLemma75.PrimePowerTransferBounds
                (B.canonicalRawMediumReferenceLaw P I Cmax xi hupperMax hS)
                B.sampleData.n B.sampleData.W
                  FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
                  (epsilon B.sampleData.n) := by
  let H : Cell Head → HeadPattern.Pattern := fun c ↦ P c.1
  let Alower : Cell Head → ℝ := fun c ↦ I.lower c.2
  let Cupper : Cell Head → ℝ := fun c ↦ I.upper c.2
  have hCmax : 0 < Cmax :=
    (I.lower_pos .minus).trans
      ((I.lower_lt_upper .minus).trans_le (hupperMax .minus))
  obtain ⟨hCpow, hmain⟩ :=
    FixedFiniteMixtureFullUniform.exists_boxIndependent_fixedFiniteMixture_primePower_transfer
      H Alower Cupper Cmax
      (fun c ↦ I.lower_pos c.2)
      (fun c ↦ I.lower_lt_upper c.2)
      (fun c ↦ lt_trans (I.lower_pos c.2) (I.lower_lt_upper c.2))
      hCmax (fun c ↦ hupperMax c.2)
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  refine ⟨hCpow, ?_⟩
  intro W hW hsupport Acoef hAcoef
  obtain ⟨epsilon, hepsilon0, hepsilonT, hepsilonRate, N₀, hN₀⟩ :=
    hmain W hW (fun c ↦ hsupport c.1) Acoef hAcoef
  refine ⟨epsilon, hepsilon0, hepsilonT, hepsilonRate, N₀, ?_⟩
  intro Band _instBand _instBandDec B xi hN hBW heta hS
  subst W
  have hetaNat : ∀ z ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.effectiveNatCoefficient xi z| ≤ Acoef := by
    intro z hz
    rw [B.effectiveNatCoefficient_of_mem xi hz]
    exact heta ⟨z, hz⟩
  obtain ⟨_hSauto, hbounds⟩ :=
    hN₀ (B.effectiveNatCoefficient xi) hN hetaNat
  have hbound := hbounds hS
    (tiltedSigmaWeight B.baselineCellProbability
      B.guardedCellProbability (B.scaledBridgeScore xi))
  simpa [H, Alower, Cupper, rawCell,
    canonicalRawMediumReferenceLaw, canonicalRawMediumComponentLaw]
    using hbound

/-- Backwards-compatible existential packaging of the preceding theorem.
The witness is definitionally the universal Dickman prime-power constant,
so clients which need to choose `W` before the head family should use
`boxIndependent_canonicalRaw_primePower_transfer` directly. -/
theorem exists_boxIndependent_canonicalRaw_primePower_transfer
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax) :
    ∃ Cpow : ℝ, 0 < Cpow ∧
      ∀ W : ℕ, 1 < W →
        (∀ h, ∀ p ∈ (P h).primes, p ≤ W) →
      ∀ Acoef : ℝ, 0 ≤ Acoef →
      ∃ epsilon : ℕ → ℝ,
        (∀ n, 0 ≤ epsilon n) ∧
        Tendsto epsilon atTop (nhds 0) ∧
        Tendsto (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
          atTop (nhds 0) ∧
        ∃ N₀ : ℕ,
          ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
            (B : BridgeData Head Band) (xi : B.ParamSpace),
            N₀ ≤ B.sampleData.n →
            B.sampleData.W = W →
            (∀ p : BandPrime B.sampleData.n B.sampleData.W,
              |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
            ∀ hS : ∀ c : Cell Head,
              (rawCell P I B.sampleData.n c).Nonempty,
              PaperPrimePowerLemma75.PrimePowerTransferBounds
                (B.canonicalRawMediumReferenceLaw P I Cmax xi hupperMax hS)
                B.sampleData.n B.sampleData.W Cpow
                  (epsilon B.sampleData.n) := by
  obtain ⟨hCpow, hmain⟩ :=
    boxIndependent_canonicalRaw_primePower_transfer P I Cmax hupperMax
  exact ⟨FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant,
    hCpow, hmain⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
