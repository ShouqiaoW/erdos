import Erdos390.WholePaper.CentralCarryAnchors
import Erdos390.WholePaper.ResidualCentralFactors

/-!
# Collision guards for the three central-anchor families

The prefix and row-zero anchors carry a marker prime above a fixed cutoff.
Every promoted residual factor is supported only at `2` and its base prime,
both below that cutoff.  The lemmas below turn this unique-factorization
observation into literal natural-number noncollision statements.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- A prime divisor of `A_p = 2^k p^e` is either `2` or the base prime
`p`. -/
theorem prime_dvd_promotedCentralFactor
    {n p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime)
    (hdiv : ℓ ∣ promotedCentralFactor n p) :
    ℓ = 2 ∨ ℓ = p := by
  rw [promotedCentralFactor, promotedBlock, centralPrimeBlock] at hdiv
  rcases hℓ.dvd_mul.mp hdiv with htwo | hpPow
  · left
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp
      (hℓ.dvd_of_dvd_pow htwo)
  · right
    exact (Nat.prime_dvd_prime_iff_eq hℓ hp).mp
      (hℓ.dvd_of_dvd_pow hpPow)

/-- A marker prime above `X` cannot divide a promoted factor whose base
prime is at most `X`, provided `2 ≤ X`. -/
theorem markerPrime_not_dvd_promotedCentralFactor
    {n X P p : ℕ} (hP : P.Prime) (hp : p.Prime)
    (hXTwo : 2 ≤ X) (hPLarge : X < P) (hpSmall : p ≤ X) :
    ¬ P ∣ promotedCentralFactor n p := by
  intro hdiv
  rcases prime_dvd_promotedCentralFactor hp hP hdiv with hP2 | hPp
  · omega
  · omega

/-- No prefix-style marker--cofactor product can collide with a promoted
residual factor. -/
theorem marker_mul_ne_promotedCentralFactor
    {n X P q p : ℕ} (hP : P.Prime) (hp : p.Prime)
    (hXTwo : 2 ≤ X) (hPLarge : X < P) (hpSmall : p ≤ X) :
    P * q ≠ promotedCentralFactor n p := by
  intro heq
  apply markerPrime_not_dvd_promotedCentralFactor hP hp hXTwo hPLarge hpSmall
  rw [← heq]
  exact dvd_mul_right P q

/-- In particular, a large row-zero prime singleton cannot be a promoted
factor. -/
theorem markerPrime_ne_promotedCentralFactor
    {n X P p : ℕ} (hP : P.Prime) (hp : p.Prime)
    (hXTwo : 2 ≤ X) (hPLarge : X < P) (hpSmall : p ≤ X) :
    P ≠ promotedCentralFactor n p := by
  simpa only [mul_one] using
    marker_mul_ne_promotedCentralFactor (n := n) (q := 1)
      hP hp hXTwo hPLarge hpSmall

/-- A prefix anchor with cofactor at least two cannot equal a row-zero
prime when both markers lie above the cofactor cutoff. -/
theorem marker_mul_ne_markerPrime
    {X P P' q : ℕ} (hP : P.Prime) (hP' : P'.Prime)
    (hPLarge : X < P) (hqLower : 2 ≤ q) (hXPos : 0 < X) :
    P * q ≠ P' := by
  intro heq
  have hcollision := prime_mul_cofactor_eq_iff_of_marker_large
    (X := X) hP hP' hPLarge (by norm_num : 0 < (1 : ℕ))
      (by omega : (1 : ℕ) ≤ X)
      (by simpa only [mul_one] using heq)
  omega

end

end Erdos390.WholePaper
