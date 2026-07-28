import Erdos390.WholePaper.CentralAnchorProduct

/-!
# The fixed-prefix central-anchor cutoff

For a fixed prefix depth `R`, the paper splits the central prime blocks at
`n / (R + 1)`.  This file gives an explicit sufficient threshold for all
scale separations and then connects that literal cutoff directly to the
large-prime routing and central-anchor product APIs.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The paper's fixed-`R` central-anchor cutoff `X_R^{anc}`. -/
def centralAnchorCutoff (R n : ℕ) : ℕ :=
  n / (R + 1)

/-- One explicit threshold sufficient for both cutoff separations. -/
def centralAnchorCutoffThreshold (R : ℕ) : ℕ :=
  4 * (R + 1) ^ 2

theorem centralAnchorCutoffThreshold_pos (R : ℕ) :
    0 < centralAnchorCutoffThreshold R := by
  simp [centralAnchorCutoffThreshold]

/-- At the explicit threshold, the cutoff is at least `4(R+1)`. -/
theorem four_mul_succ_le_centralAnchorCutoff
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    4 * (R + 1) ≤ centralAnchorCutoff R n := by
  rw [centralAnchorCutoff, Nat.le_div_iff_mul_le (by omega)]
  simpa only [centralAnchorCutoffThreshold, pow_two, mul_assoc] using hn

/-- The cutoff lies strictly above every cofactor in rows `1,…,R`. -/
theorem two_mul_add_one_lt_centralAnchorCutoff
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    2 * R + 1 < centralAnchorCutoff R n := by
  have hfour := four_mul_succ_le_centralAnchorCutoff hn
  omega

/-- The explicit threshold also puts `2n` strictly below the cutoff square. -/
theorem two_mul_lt_centralAnchorCutoff_sq
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    2 * n < (centralAnchorCutoff R n) ^ 2 := by
  let X := centralAnchorCutoff R n
  have hX : 4 * (R + 1) ≤ X := by
    simpa only [X] using four_mul_succ_le_centralAnchorCutoff hn
  have hXPos : 0 < X := by omega
  have hnUpper : n < (R + 1) * (X + 1) := by
    simpa only [X, centralAnchorCutoff] using
      Nat.lt_mul_div_succ n (by omega : 0 < R + 1)
  have hlinear : 2 * (R + 1) * (X + 1) ≤ X ^ 2 := by
    calc
      2 * (R + 1) * (X + 1) ≤ 2 * (R + 1) * (2 * X) := by
        exact Nat.mul_le_mul_left (2 * (R + 1)) (by omega)
      _ = (4 * (R + 1)) * X := by ring
      _ ≤ X * X := Nat.mul_le_mul_right X hX
      _ = X ^ 2 := by ring
  calc
    2 * n < 2 * ((R + 1) * (X + 1)) :=
      (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hnUpper
    _ = 2 * (R + 1) * (X + 1) := by ring
    _ ≤ X ^ 2 := hlinear

/-- Both scale inequalities, with no asymptotic contract hidden. -/
theorem centralAnchorCutoff_scaleSeparation
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    2 * R + 1 < centralAnchorCutoff R n ∧
      2 * n < (centralAnchorCutoff R n) ^ 2 :=
  ⟨two_mul_add_one_lt_centralAnchorCutoff hn,
    two_mul_lt_centralAnchorCutoff_sq hn⟩

theorem two_le_centralAnchorCutoff
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    2 ≤ centralAnchorCutoff R n := by
  have hsep := two_mul_add_one_lt_centralAnchorCutoff hn
  omega

/-- The displayed scale separation holds eventually for every fixed `R`. -/
theorem eventually_centralAnchorCutoff_scaleSeparation (R : ℕ) :
    ∀ᶠ n in atTop,
      2 * R + 1 < centralAnchorCutoff R n ∧
        2 * n < (centralAnchorCutoff R n) ^ 2 := by
  filter_upwards [eventually_ge_atTop (centralAnchorCutoffThreshold R)] with n hn
  exact centralAnchorCutoff_scaleSeparation hn

theorem eventually_two_mul_add_one_lt_centralAnchorCutoff (R : ℕ) :
    ∀ᶠ n in atTop, 2 * R + 1 < centralAnchorCutoff R n :=
  (eventually_centralAnchorCutoff_scaleSeparation R).mono fun _ h ↦ h.1

theorem eventually_two_mul_lt_centralAnchorCutoff_sq (R : ℕ) :
    ∀ᶠ n in atTop, 2 * n < (centralAnchorCutoff R n) ^ 2 :=
  (eventually_centralAnchorCutoff_scaleSeparation R).mono fun _ h ↦ h.2

/-- A prime above `n/(R+1)` has quotient row at most `R`. -/
theorem div_le_fixedPrefix_of_centralAnchorCutoff_lt
    {R n p : ℕ} (hp : centralAnchorCutoff R n < p) :
    n / p ≤ R := by
  have hpPos : 0 < p := by omega
  have hdiv : n / (R + 1) < p := by
    simpa only [centralAnchorCutoff] using hp
  have hnUpper : n < p * (R + 1) :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < R + 1)).1 hdiv
  have hrow : n / p < R + 1 :=
    (Nat.div_lt_iff_lt_mul hpPos).2 (by
      simpa only [Nat.mul_comm] using hnUpper)
  omega

theorem largeCentralPrime_div_le_fixedPrefix
    {R n p : ℕ}
    (hp : p ∈ largeCentralPrimes n (centralAnchorCutoff R n)) :
    n / p ≤ R :=
  div_le_fixedPrefix_of_centralAnchorCutoff_lt
    (largeCentralPrimes_gt hp)

/-- Routing at the literal cutoff lands in row zero or a positive row no
larger than the fixed prefix depth. -/
theorem largeCentralPrime_rowZero_or_fixedPrefix
    {R n p : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n)
    (hp : p ∈ largeCentralPrimes n (centralAnchorCutoff R n)) :
    (Nat.choose (2 * n) n).factorization p = 1 ∧
      ((n < p ∧ p ≤ 2 * n) ∨
        ∃ r : ℕ, 1 ≤ r ∧ r ≤ R ∧ r = n / p ∧
          p ∈ stationaryPrimeLayer n r) := by
  have hnPos : 0 < n :=
    (centralAnchorCutoffThreshold_pos R).trans_le hn
  have hroute := largeCentralPrime_rowZero_or_stationary hnPos
    (two_mul_lt_centralAnchorCutoff_sq hn) hp
  refine ⟨hroute.1, ?_⟩
  rcases hroute.2 with hzero | ⟨r, hrPos, hr, hpRow⟩
  · exact Or.inl hzero
  · exact Or.inr ⟨r, hrPos, by
      rw [hr]
      exact largeCentralPrime_div_le_fixedPrefix hp, hr, hpRow⟩

/-- Every routed cofactor above the literal cutoff is in the fixed
cofactor prefix `[1,2R+1]`. -/
theorem largeCentralCofactor_le_fixedPrefix
    {R n : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q)
    {p : ℕ} (hp : p ∈ largeCentralPrimes n (centralAnchorCutoff R n)) :
    q p ≤ 2 * R + 1 := by
  rcases hq p hp with hzero |
      ⟨r, _hrPos, hr, _hpRow, _hqLower, hqUpper⟩
  · omega
  · have hrUpper : r ≤ R := by
      rw [hr]
      exact largeCentralPrime_div_le_fixedPrefix hp
    omega

/-- The full route and cofactor interval, now with the fixed-prefix bound
made literal. -/
theorem largeCentralCofactor_eq_one_or_fixedPrefix
    {R n : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q)
    {p : ℕ} (hp : p ∈ largeCentralPrimes n (centralAnchorCutoff R n)) :
    (n < p ∧ p ≤ 2 * n ∧ q p = 1) ∨
      ∃ r : ℕ, 1 ≤ r ∧ r ≤ R ∧ r = n / p ∧
        p ∈ stationaryPrimeLayer n r ∧
          r + 1 ≤ q p ∧ q p ≤ 2 * r + 1 := by
  rcases hq p hp with hzero |
      ⟨r, hrPos, hr, hpRow, hqLower, hqUpper⟩
  · exact Or.inl hzero
  · exact Or.inr ⟨r, hrPos, by
      rw [hr]
      exact largeCentralPrime_div_le_fixedPrefix hp,
      hr, hpRow, hqLower, hqUpper⟩

theorem largeCentralPrime_gt_fixedPrefixCofactors
    {R n p : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n)
    (hp : p ∈ largeCentralPrimes n (centralAnchorCutoff R n)) :
    2 * R + 1 < p :=
  (two_mul_add_one_lt_centralAnchorCutoff hn).trans
    (largeCentralPrimes_gt hp)

/-- Every actual routed cofactor is strictly below its marker prime. -/
theorem largeCentralCofactor_lt_marker
    {R n : ℕ} {q : ℕ → ℕ}
    (hn : centralAnchorCutoffThreshold R ≤ n)
    (hq : IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q)
    {p : ℕ} (hp : p ∈ largeCentralPrimes n (centralAnchorCutoff R n)) :
    q p < p :=
  (largeCentralCofactor_le_fixedPrefix hq hp).trans_lt
    (largeCentralPrime_gt_fixedPrefixCofactors hn hp)

/-- The canonical routed choice is available at the explicit threshold. -/
theorem canonicalLargeCentralCofactor_isChoice_centralAnchorCutoff
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    IsLargeCentralCofactorChoice n (centralAnchorCutoff R n)
      (canonicalLargeCentralCofactor n) := by
  exact canonicalLargeCentralCofactor_isChoice
    ((centralAnchorCutoffThreshold_pos R).trans_le hn)
    (two_mul_lt_centralAnchorCutoff_sq hn)

theorem canonicalLargeCentralCofactor_le_fixedPrefix
    {R n p : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n)
    (hp : p ∈ largeCentralPrimes n (centralAnchorCutoff R n)) :
    canonicalLargeCentralCofactor n p ≤ 2 * R + 1 :=
  largeCentralCofactor_le_fixedPrefix
    (canonicalLargeCentralCofactor_isChoice_centralAnchorCutoff hn) hp

/-- Marker recovery at the literal cutoff: fixed-prefix cofactors cannot
hide a different prime marker. -/
theorem prime_mul_cofactor_eq_of_centralAnchorCutoff
    {R n p p' q q' : ℕ}
    (hn : centralAnchorCutoffThreshold R ≤ n)
    (hp : p.Prime) (hp' : p'.Prime)
    (hpLarge : centralAnchorCutoff R n < p)
    (hq'Pos : 0 < q') (hq'Upper : q' ≤ 2 * R + 1)
    (heq : p * q = p' * q') : p = p' ∧ q = q' := by
  exact prime_mul_cofactor_eq_iff_of_marker_large hp hp' hpLarge hq'Pos
    (hq'Upper.trans (two_mul_add_one_lt_centralAnchorCutoff hn).le) heq

/-- The cutoff-square inequality specializes the existing literal
large-marker collision theorem. -/
theorem largeCentralAnchor_injOn_centralAnchorCutoff
    {R n : ℕ} {q : ℕ → ℕ}
    (hn : centralAnchorCutoffThreshold R ≤ n)
    (hq : IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q) :
    Set.InjOn (largeCentralAnchor q)
      (largeCentralPrimes n (centralAnchorCutoff R n)) :=
  largeCentralAnchor_injOn (two_mul_lt_centralAnchorCutoff_sq hn) hq

theorem largeCentralAnchors_card_centralAnchorCutoff
    {R n : ℕ} {q : ℕ → ℕ}
    (hn : centralAnchorCutoffThreshold R ≤ n)
    (hq : IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q) :
    (largeCentralAnchors n (centralAnchorCutoff R n) q).card =
      (largeCentralPrimes n (centralAnchorCutoff R n)).card :=
  largeCentralAnchors_card (two_mul_lt_centralAnchorCutoff_sq hn) hq

/-- Direct exact-product corollary at the fixed-`R` cutoff. -/
theorem fullCentralAnchors_prod_centralAnchorCutoff
    {R n : ℕ} {q : ℕ → ℕ}
    (hn : centralAnchorCutoffThreshold R ≤ n)
    (hq : IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q) :
    (fullCentralAnchors n (centralAnchorCutoff R n) q).prod id =
      Nat.choose (2 * n) n *
        centralAnchorDivisor n (centralAnchorCutoff R n) q := by
  exact fullCentralAnchors_prod
    ((centralAnchorCutoffThreshold_pos R).trans_le hn)
    (two_le_centralAnchorCutoff hn)
    (two_mul_lt_centralAnchorCutoff_sq hn) hq

theorem fullCentralAnchors_prod_canonical_centralAnchorCutoff
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    (fullCentralAnchors n (centralAnchorCutoff R n)
        (canonicalLargeCentralCofactor n)).prod id =
      Nat.choose (2 * n) n *
        centralAnchorDivisor n (centralAnchorCutoff R n)
          (canonicalLargeCentralCofactor n) :=
  fullCentralAnchors_prod_centralAnchorCutoff hn
    (canonicalLargeCentralCofactor_isChoice_centralAnchorCutoff hn)

end

end Erdos390.WholePaper
