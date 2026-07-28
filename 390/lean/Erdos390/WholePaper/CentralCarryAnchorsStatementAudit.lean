import Erdos390.WholePaper.CentralCarryAnchors

/-! # Expanded statement audit for fixed-prefix central carry anchors -/

namespace Erdos390.WholePaper

noncomputable section

example {n r p : ℕ}
    (hpPrime : p.Prime) (hpLower : n < p * (r + 1))
    (hpUpper : p * (2 * r + 1) ≤ 2 * n) :
    n / p = r ∧ (2 * n) / p = 2 * r + 1 := by
  apply stationaryPrimeLayer_floor_values
  exact mem_stationaryPrimeLayer.mpr ⟨hpPrime, hpLower, hpUpper⟩

example {n r p : ℕ} (hn : 0 < n)
    (hpPrime : p.Prime) (hpLower : n < p * (r + 1))
    (hpUpper : p * (2 * r + 1) ≤ 2 * n) (hpSq : 2 * n < p ^ 2) :
    (Nat.choose (2 * n) n).factorization p = 1 := by
  exact centralChoose_factorization_eq_one_of_mem_stationaryPrimeLayer_of_sq
    hn (mem_stationaryPrimeLayer.mpr ⟨hpPrime, hpLower, hpUpper⟩) hpSq

example {n r p q : ℕ}
    (hpPrime : p.Prime) (hpLower : n < p * (r + 1))
    (hpUpper : p * (2 * r + 1) ≤ 2 * n)
    (hqLower : r + 1 ≤ q) (hqUpper : q ≤ 2 * r + 1) :
    p * q ∈ Finset.Ioc n (2 * n) := by
  exact stationaryPrimeLayer_mul_cofactor_mem_centralInterval
    (mem_stationaryPrimeLayer.mpr ⟨hpPrime, hpLower, hpUpper⟩)
    hqLower hqUpper

example {X p p' q q' : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    (hpLarge : X < p) (hq'Pos : 0 < q') (hq'Upper : q' ≤ X)
    (hproduct : p * q = p' * q') :
    p = p' ∧ q = q' := by
  exact prime_mul_cofactor_eq_iff_of_marker_large
    hp hp' hpLarge hq'Pos hq'Upper hproduct

end

end Erdos390.WholePaper
