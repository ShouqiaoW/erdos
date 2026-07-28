import Erdos390.WholePaper.CentralAnchorCollision

/-! # Expanded statement audit for central-anchor collision guards -/

namespace Erdos390.WholePaper

example {n p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime)
    (hdiv : ℓ ∣
      2 ^ promotionExponent n
          (p ^ (Nat.choose (2 * n) n).factorization p) *
        p ^ (Nat.choose (2 * n) n).factorization p) :
    ℓ = 2 ∨ ℓ = p := by
  simpa only [promotedCentralFactor, promotedBlock, centralPrimeBlock] using
    prime_dvd_promotedCentralFactor hp hℓ hdiv

example {n X P q p : ℕ} (hP : P.Prime) (hp : p.Prime)
    (hXTwo : 2 ≤ X) (hPLarge : X < P) (hpSmall : p ≤ X) :
    P * q ≠
      2 ^ promotionExponent n
          (p ^ (Nat.choose (2 * n) n).factorization p) *
        p ^ (Nat.choose (2 * n) n).factorization p := by
  simpa only [promotedCentralFactor, promotedBlock, centralPrimeBlock] using
    marker_mul_ne_promotedCentralFactor
      (n := n) (q := q) hP hp hXTwo hPLarge hpSmall

example {X P P' q : ℕ} (hP : P.Prime) (hP' : P'.Prime)
    (hPLarge : X < P) (hqLower : 2 ≤ q) (hXPos : 0 < X) :
    P * q ≠ P' := by
  exact marker_mul_ne_markerPrime hP hP' hPLarge hqLower hXPos

end Erdos390.WholePaper
