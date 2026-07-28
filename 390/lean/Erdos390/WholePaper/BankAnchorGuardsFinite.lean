import Erdos390.WholePaper.CentralAnchorCollision

/-!
# Finite anchor modifications and collision guards

This module isolates the exact combinatorial part of Section 5's anchor
modification.  It chooses a replacement from three literal cofactors and
derives collision avoidance from the existing central-anchor arithmetic.
No reserve estimate or prime-distribution input appears here.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- Choose the first of `r+1`, `r+2`, `r+3` which avoids both incident
cores. -/
def prefixReplacementCofactor (r left right : ℕ) : ℕ :=
  if r + 1 ≠ left ∧ r + 1 ≠ right then r + 1
  else if r + 2 ≠ left ∧ r + 2 ≠ right then r + 2
  else r + 3

/-- The three explicit candidates always contain a legal cofactor distinct
from both incident cores. -/
theorem prefixReplacementCofactor_spec
    {r left right : ℕ} (hr : 2 ≤ r) :
    r + 1 ≤ prefixReplacementCofactor r left right ∧
      prefixReplacementCofactor r left right ≤ 2 * r + 1 ∧
      prefixReplacementCofactor r left right ≠ left ∧
      prefixReplacementCofactor r left right ≠ right := by
  unfold prefixReplacementCofactor
  split
  next h => exact ⟨by omega, by omega, h.1, h.2⟩
  next hfirst =>
    split
    next h => exact ⟨by omega, by omega, h.1, h.2⟩
    next hsecond =>
      have hfirst' : r + 1 = left ∨ r + 1 = right := by
        by_cases hleft : r + 1 = left
        · exact Or.inl hleft
        · exact Or.inr (by
            by_contra hright
            exact hfirst ⟨hleft, hright⟩)
      have hsecond' : r + 2 = left ∨ r + 2 = right := by
        by_cases hleft : r + 2 = left
        · exact Or.inl hleft
        · exact Or.inr (by
            by_contra hright
            exact hsecond ⟨hleft, hright⟩)
      rcases hfirst' with hfirst' | hfirst' <;>
        rcases hsecond' with hsecond' | hsecond' <;> omega

/-- Finset form of legality in the row interval `[r+1,2r+1]`. -/
theorem prefixReplacementCofactor_mem_legalRange
    {r left right : ℕ} (hr : 2 ≤ r) :
    prefixReplacementCofactor r left right ∈
      Finset.Icc (r + 1) (2 * r + 1) := by
  exact Finset.mem_Icc.mpr
    ⟨(prefixReplacementCofactor_spec hr).1,
      (prefixReplacementCofactor_spec hr).2.1⟩

/-- The selected cofactor produces a legal central anchor in its stationary
carry row. -/
theorem prefixReplacementAnchor_mem_centralInterval
    {n r P left right : ℕ} (hr : 2 ≤ r)
    (hP : P ∈ stationaryPrimeLayer n r) :
    P * prefixReplacementCofactor r left right ∈
      Finset.Ioc n (2 * n) := by
  exact stationaryPrimeLayer_mul_cofactor_mem_centralInterval hP
    (prefixReplacementCofactor_spec hr).1
    (prefixReplacementCofactor_spec hr).2.1

/-- Equality with an incident marker factor would recover both marker and
cofactor, contradicting the three-candidate choice. -/
theorem prefixReplacementAnchor_ne_incidentMarkerFactor
    {X P P' r left right core : ℕ} (hr : 2 ≤ r)
    (hP : P.Prime) (hP' : P'.Prime) (hPLarge : X < P)
    (hcorePos : 0 < core) (hcoreUpper : core ≤ X)
    (hincident : core = left ∨ core = right) :
    P * prefixReplacementCofactor r left right ≠ P' * core := by
  intro heq
  have hrecover := prime_mul_cofactor_eq_iff_of_marker_large
    hP hP' hPLarge hcorePos hcoreUpper heq
  have hchoice := prefixReplacementCofactor_spec
    (r := r) (left := left) (right := right) hr
  rcases hincident with hleft | hright
  · exact hchoice.2.2.1 (hrecover.2.trans hleft)
  · exact hchoice.2.2.2 (hrecover.2.trans hright)

/-- Different large marker primes give distinct prefix anchors. -/
theorem prefixMarkerAnchors_ne_of_marker_ne
    {X P P' q q' : ℕ} (hP : P.Prime) (hP' : P'.Prime)
    (hPLarge : X < P) (hq'Pos : 0 < q') (hq'Upper : q' ≤ X)
    (hmarkers : P ≠ P') :
    P * q ≠ P' * q' := by
  intro heq
  exact hmarkers (prime_mul_cofactor_eq_iff_of_marker_large
    hP hP' hPLarge hq'Pos hq'Upper heq).1

/-- The selected prefix anchor cannot collide with a promoted central
factor supported at `2` and a small base prime. -/
theorem prefixReplacementAnchor_ne_promotedCentralFactor
    {n X P p r left right : ℕ}
    (hP : P.Prime) (hp : p.Prime) (hXTwo : 2 ≤ X)
    (hPLarge : X < P) (hpSmall : p ≤ X) :
    P * prefixReplacementCofactor r left right ≠
      promotedCentralFactor n p := by
  exact marker_mul_ne_promotedCentralFactor hP hp hXTwo hPLarge hpSmall

/-- The selected prefix anchor cannot collide with a row-zero marker prime. -/
theorem prefixReplacementAnchor_ne_rowZeroMarker
    {X P P₀ r left right : ℕ} (hr : 2 ≤ r)
    (hP : P.Prime) (hP₀ : P₀.Prime) (hPLarge : X < P)
    (hXTwo : 2 ≤ X) :
    P * prefixReplacementCofactor r left right ≠ P₀ := by
  exact marker_mul_ne_markerPrime hP hP₀ hPLarge
    (by
      have hlower := (prefixReplacementCofactor_spec
        (r := r) (left := left) (right := right) hr).1
      omega)
    (by omega)

/-- The forced cofactor `3` is literally distinct from every core used in
the two bottom anchor modifications. -/
theorem forcedThreeAnchor_ne_bottomStates {P : ℕ} (hP : 0 < P) :
    P * 3 ≠ P * 5 ∧ P * 3 ≠ P * 4 ∧ P * 3 ≠ P * 2 := by
  constructor
  · intro h
    exact (by omega : (3 : ℕ) ≠ 5) (Nat.mul_left_cancel hP h)
  constructor
  · intro h
    exact (by omega : (3 : ℕ) ≠ 4) (Nat.mul_left_cancel hP h)
  · intro h
    exact (by omega : (3 : ℕ) ≠ 2) (Nat.mul_left_cancel hP h)

/-- A bundled literal collision terminal for one modified prefix anchor. -/
theorem prefixReplacementAnchor_collisionFree
    {n X P P' P₀ p r left right core : ℕ}
    (hr : 2 ≤ r) (hstationary : P ∈ stationaryPrimeLayer n r)
    (hPLarge : X < P) (hXTwo : 2 ≤ X)
    (hP' : P'.Prime) (hcorePos : 0 < core) (hcoreUpper : core ≤ X)
    (hincident : core = left ∨ core = right)
    (hP₀ : P₀.Prime) (hp : p.Prime) (hpSmall : p ≤ X) :
    P * prefixReplacementCofactor r left right ∈ Finset.Ioc n (2 * n) ∧
      P * prefixReplacementCofactor r left right ≠ P' * core ∧
      P * prefixReplacementCofactor r left right ≠
        promotedCentralFactor n p ∧
      P * prefixReplacementCofactor r left right ≠ P₀ := by
  have hP : P.Prime := (mem_stationaryPrimeLayer.mp hstationary).1
  exact ⟨prefixReplacementAnchor_mem_centralInterval hr hstationary,
    prefixReplacementAnchor_ne_incidentMarkerFactor hr hP hP'
      hPLarge hcorePos hcoreUpper hincident,
    prefixReplacementAnchor_ne_promotedCentralFactor hP hp hXTwo
      hPLarge hpSmall,
    prefixReplacementAnchor_ne_rowZeroMarker hr hP hP₀ hPLarge hXTwo⟩

end

end Erdos390.WholePaper
