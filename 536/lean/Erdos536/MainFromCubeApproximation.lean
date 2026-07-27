import Erdos536.CapacityFromCubes
import Erdos536.FinitePrimeReduction
import Erdos536.PrimeTail

/-!
# Final abstract interface for the prime-band construction

All arithmetic and cap-set arguments reduce the main theorem to the following
finite approximation property: in every requested dimension, arbitrarily far
out in the primes, there are multiplicatively balanced cube laws whose word
marginals approach the reciprocal squarefree law.
-/

namespace Erdos536

/-- One finite balanced cube approximation with explicit error parameters. -/
structure BalancedCubeApproximation
    (H A : ℕ) (ε δ : ℝ) where
  Sample : Type
  sampleDecidableEq : DecidableEq Sample
  primes : Finset ℕ
  primes_prime : IsPrimeSupport primes
  primes_above : ∀ p ∈ primes, A < p
  law : @FiniteCubeLaw Sample sampleDecidableEq H primes
  marginal_close :
    ∀ ω : Fin H → ZMod 3, law.wordSupportDistance ω ≤ ε
  balanced : law.MultiplicativelyBalanced δ

/-- The sole remaining analytic assertion, phrased without asymptotics or
measure theory. -/
def HasArbitrarilyGoodBalancedCubeApproximations : Prop :=
  ∀ (H A : ℕ) (ε δ : ℝ), 0 < ε → 0 < δ →
    Nonempty (BalancedCubeApproximation H A ε δ)

/-- The finite balanced-cube approximation property implies Erdős 536. -/
theorem mainTheorem_of_balancedCubeApproximations
    (happrox : HasArbitrarilyGoodBalancedCubeApproximations) :
    MainTheorem := by
  apply mainTheorem_of_finite_squarefree_capacity
  intro ζ hζ
  obtain ⟨n, hn⟩ :=
    exists_nat_one_div_lt (K := ℝ) (half_pos hζ)
  let A := n + 1
  have hA : 1 ≤ A := by omega
  have hAtail : 1 / (A : ℝ) < ζ / 2 := by
    simpa [A, Nat.cast_add, Nat.cast_one] using hn
  obtain ⟨H, hH⟩ :=
    exists_dimension_squarefreeCapacity_le_of_balancedCubeLaw
      (ζ / 8) (by positivity)
  obtain ⟨P⟩ :=
    happrox H A (ζ / 8) (ζ / 16) (by positivity) (by positivity)
  letI : DecidableEq P.Sample := P.sampleDecidableEq
  have hcapacity :
      squarefreeI P.primes / squarefreeZ P.primes ≤
        ζ / 8 + (ζ / 8 + 2 * (ζ / 16)) := by
    exact hH P.Sample P.primes P.law P.primes_prime
      P.marginal_close (by positivity) P.balanced
  have htail :
      (∑ p ∈ P.primes, (p : ℝ)⁻¹ ^ 2) ≤ 1 / (A : ℝ) :=
    sum_primeSupport_inv_sq_le P.primes_prime hA P.primes_above
  refine ⟨P.primes, P.primes_prime, ?_⟩
  calc
    squarefreeI P.primes / squarefreeZ P.primes +
        (∑ p ∈ P.primes, (p : ℝ)⁻¹ ^ 2) ≤
      (ζ / 8 + (ζ / 8 + 2 * (ζ / 16))) +
        1 / (A : ℝ) :=
      add_le_add hcapacity htail
    _ < ζ := by linarith

end Erdos536
