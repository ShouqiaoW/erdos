import Erdos390.Full.PaperHeadPrimeMarkedExact
import Erdos390.Full.PaperProposition87CanonicalMarkedProfilesEventually

/-!
# Exact split between fixed head primes and moving band primes

The fixed branch `p ≤ W` is killed identically by the head coordinates.
Only the moving branch `W < p ≤ y(n)` uses the analytic marked-row bound.
-/

open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Combine the exact head-prime row and the analytic moving-prime row.
The hypotheses make the finite split and its quantifiers fully explicit. -/
theorem uniform_allPrime_markedRow_of_exactHead_and_moving
    [Nonempty Head]
    (hhead : ∀ h : Head, ∀ r : ℕ,
      r ∈ (B.sampleData.pattern h).primes ↔
        r.Prime ∧ r ≤ B.sampleData.W)
    (Delta : Band → ℝ) (a : NNReal)
    {gammaFull Crow : ℝ}
    (hgammaFull : 0 < gammaFull)
    (hFull : ∀ z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ),
      B.vectorFamily.HasCovarianceGap gammaFull
        (B.effectiveParamEquiv z))
    (hCrow : 0 ≤ Crow)
    (monitoredPrimes : Finset ℕ)
    (hprime : ∀ p ∈ monitoredPrimes, p.Prime)
    (hleY : ∀ p ∈ monitoredPrimes, p ≤ yNat B.sampleData.n)
    (hmoving : ∀ p ∈ monitoredPrimes,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
        |B.vectorFamily.scalarFamily.covariance
          (B.markedValuation p)
          (fun m ↦ B.vectorFamily.scalarFamily.score m
            (B.vectorFamily.vectorField (B.targetVector Delta)
              (B.effectiveParamEquiv z)))
          (B.effectiveParamEquiv z)| ≤ Crow / (p : ℝ)) :
    ∀ p ∈ monitoredPrimes,
      ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
        |B.vectorFamily.scalarFamily.covariance
          (B.markedValuation p)
          (fun m ↦ B.vectorFamily.scalarFamily.score m
            (B.vectorFamily.vectorField (B.targetVector Delta)
              (B.effectiveParamEquiv z)))
          (B.effectiveParamEquiv z)| ≤ Crow / (p : ℝ) := by
  intro p hp z hz
  by_cases hpW : p ≤ B.sampleData.W
  · have hzero := B.covariance_headPrimeMarkedValuation_vectorField_eq_zero
      hhead (B.effectiveParamEquiv z) Delta hgammaFull
        (hFull z hz) (hprime p hp) hpW
    rw [hzero, abs_zero]
    exact div_nonneg hCrow (by positivity)
  · apply hmoving p hp
      (mem_primeBand.mpr ⟨hprime p hp, Nat.lt_of_not_ge hpW,
        hleY p hp⟩) z hz

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
