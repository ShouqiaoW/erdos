import Erdos390.WholePaper.BankAnchorGuardsFinite

/-!
# Expanded statement audit for finite anchor modifications and guards

The examples below expose the literal three-candidate selector, the exact
stationary-layer inequalities, and every finite collision guard.  No
asymptotic reserve estimate is hidden in these statements.
-/

namespace Erdos390.WholePaper

noncomputable section

example (r left right : ℕ) :
    prefixReplacementCofactor r left right =
      if r + 1 ≠ left ∧ r + 1 ≠ right then r + 1
      else if r + 2 ≠ left ∧ r + 2 ≠ right then r + 2
      else r + 3 := rfl

example {r left right : ℕ} (hr : 2 ≤ r) :
    r + 1 ≤
        (if r + 1 ≠ left ∧ r + 1 ≠ right then r + 1
        else if r + 2 ≠ left ∧ r + 2 ≠ right then r + 2
        else r + 3) ∧
      (if r + 1 ≠ left ∧ r + 1 ≠ right then r + 1
        else if r + 2 ≠ left ∧ r + 2 ≠ right then r + 2
        else r + 3) ≤ 2 * r + 1 ∧
      (if r + 1 ≠ left ∧ r + 1 ≠ right then r + 1
        else if r + 2 ≠ left ∧ r + 2 ≠ right then r + 2
        else r + 3) ≠ left ∧
      (if r + 1 ≠ left ∧ r + 1 ≠ right then r + 1
        else if r + 2 ≠ left ∧ r + 2 ≠ right then r + 2
        else r + 3) ≠ right := by
  simpa only [prefixReplacementCofactor] using
    (prefixReplacementCofactor_spec
      (r := r) (left := left) (right := right) hr)

example {n r P left right : ℕ} (hr : 2 ≤ r)
    (hP : P.Prime) (hlower : n < P * (r + 1))
    (hupper : P * (2 * r + 1) ≤ 2 * n) :
    P *
        (if r + 1 ≠ left ∧ r + 1 ≠ right then r + 1
        else if r + 2 ≠ left ∧ r + 2 ≠ right then r + 2
        else r + 3) ∈ Finset.Ioc n (2 * n) := by
  have hstationary : P ∈ stationaryPrimeLayer n r :=
    mem_stationaryPrimeLayer.mpr ⟨hP, hlower, hupper⟩
  simpa only [prefixReplacementCofactor] using
    prefixReplacementAnchor_mem_centralInterval hr hstationary

example {X P P' r left right core : ℕ} (hr : 2 ≤ r)
    (hP : P.Prime) (hP' : P'.Prime) (hPLarge : X < P)
    (hcorePos : 0 < core) (hcoreUpper : core ≤ X)
    (hincident : core = left ∨ core = right) :
    P *
        (if r + 1 ≠ left ∧ r + 1 ≠ right then r + 1
        else if r + 2 ≠ left ∧ r + 2 ≠ right then r + 2
        else r + 3) ≠
      P' * core := by
  simpa only [prefixReplacementCofactor] using
    prefixReplacementAnchor_ne_incidentMarkerFactor hr hP hP'
      hPLarge hcorePos hcoreUpper hincident

example {X P P' q q' : ℕ} (hP : P.Prime) (hP' : P'.Prime)
    (hPLarge : X < P) (hq'Pos : 0 < q') (hq'Upper : q' ≤ X)
    (hmarkers : P ≠ P') :
    P * q ≠ P' * q' :=
  prefixMarkerAnchors_ne_of_marker_ne hP hP' hPLarge hq'Pos
    hq'Upper hmarkers

example {n X P p r left right : ℕ}
    (hP : P.Prime) (hp : p.Prime) (hXTwo : 2 ≤ X)
    (hPLarge : X < P) (hpSmall : p ≤ X) :
    P *
        (if r + 1 ≠ left ∧ r + 1 ≠ right then r + 1
        else if r + 2 ≠ left ∧ r + 2 ≠ right then r + 2
        else r + 3) ≠
      promotedCentralFactor n p := by
  simpa only [prefixReplacementCofactor] using
    prefixReplacementAnchor_ne_promotedCentralFactor hP hp hXTwo
      hPLarge hpSmall

example {X P P₀ r left right : ℕ} (hr : 2 ≤ r)
    (hP : P.Prime) (hP₀ : P₀.Prime) (hPLarge : X < P)
    (hXTwo : 2 ≤ X) :
    P *
        (if r + 1 ≠ left ∧ r + 1 ≠ right then r + 1
        else if r + 2 ≠ left ∧ r + 2 ≠ right then r + 2
        else r + 3) ≠
      P₀ := by
  simpa only [prefixReplacementCofactor] using
    prefixReplacementAnchor_ne_rowZeroMarker hr hP hP₀ hPLarge hXTwo

example {P : ℕ} (hP : 0 < P) :
    P * 3 ≠ P * 5 ∧ P * 3 ≠ P * 4 ∧ P * 3 ≠ P * 2 :=
  forcedThreeAnchor_ne_bottomStates hP

example {n X P P' P₀ p r left right core : ℕ}
    (hr : 2 ≤ r) (hstationary : P ∈ stationaryPrimeLayer n r)
    (hPLarge : X < P) (hXTwo : 2 ≤ X)
    (hP' : P'.Prime) (hcorePos : 0 < core) (hcoreUpper : core ≤ X)
    (hincident : core = left ∨ core = right)
    (hP₀ : P₀.Prime) (hp : p.Prime) (hpSmall : p ≤ X) :
    P * prefixReplacementCofactor r left right ∈ Finset.Ioc n (2 * n) ∧
      P * prefixReplacementCofactor r left right ≠ P' * core ∧
      P * prefixReplacementCofactor r left right ≠
        promotedCentralFactor n p ∧
      P * prefixReplacementCofactor r left right ≠ P₀ :=
  prefixReplacementAnchor_collisionFree hr hstationary hPLarge hXTwo
    hP' hcorePos hcoreUpper hincident hP₀ hp hpSmall

end

end Erdos390.WholePaper
