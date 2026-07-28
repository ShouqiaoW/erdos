import Erdos390.WholePaper.CentralAnchorGuardedChoice

/-!
# Central-anchor certificate after a finite bank guard

This module packages the preceding finite modification into the same kind of
literal object used by the central-anchor existence theorem.  A sixth of the
original `c-C0` valuation margin pays for all changed cofactors; another
sixth remains visible prime by prime.  The modified divisor is then proved to
divide the actual factorial tail, rather than merely satisfying a real-valued
estimate.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

/-- The complete central-anchor object after guarding a finite set of bank
markers.  The last field exposes the exact cofactor-level collision guard at
every changed marker. -/
structure GuardedCentralAnchorCertificate
    (c : ℝ) (R n : ℕ) (left right : ℕ → ℕ)
    (changed : Finset ℕ) where
  q : ℕ → ℕ
  anchors : Finset ℕ
  isCofactorChoice :
    IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q
  anchors_eq :
    anchors = fullCentralAnchors n (centralAnchorCutoff R n) q
  anchors_subset : anchors ⊆ Finset.Ioc n (2 * n)
  anchors_prod :
    anchors.prod id = Nat.choose (2 * n) n *
      centralAnchorDivisor n (centralAnchorCutoff R n) q
  divisor_prime_support :
    ∀ ℓ : ℕ, ℓ.Prime →
      ℓ ∣ centralAnchorDivisor n (centralAnchorCutoff R n) q →
        ℓ ∈ primesUpTo (2 * R + 1)
  divisor_reserve :
    ∀ ℓ ∈ primesUpTo (2 * R + 1),
      (c - C0) / (6 * (((ℓ - 1 : ℕ) : ℝ))) *
            secondOrderScale n +
          ((centralAnchorDivisor n
            (centralAnchorCutoff R n) q).factorization ℓ : ℝ) ≤
        (upperTailValuation c n ℓ : ℝ)
  divisor_dvd_tail :
    centralAnchorDivisor n (centralAnchorCutoff R n) q ∣
      centralTailProduct n (upperTailLength c n)
  guarded_incident_cores :
    ∀ p ∈ changed,
      q p ≠ left p ∧ q p ≠ right p

/-- Spend at most one sixth of the original reserve on a literal finite
cofactor modification.  All support, exact-product, interval, divisibility,
and collision conclusions concern the newly constructed function itself. -/
theorem guardedCentralAnchorCertificate_of_changeCost
    {c : ℝ} {R n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (hc : C0 < c) (hR : 1 ≤ R)
    (hnCutoff : centralAnchorCutoffThreshold R ≤ n)
    (certificate : CentralAnchorCertificate c R n)
    (hchanged : changed ⊆
      largeCentralPrimes n (centralAnchorCutoff R n))
    (hchangedLe : ∀ p ∈ changed, p ≤ n)
    (hrowOneAvoid : ∀ p ∈ changed, n / p = 1 →
      3 ≠ left p ∧ 3 ≠ right p)
    (hchangeCost : ∀ ℓ ∈ primesUpTo (2 * R + 1),
      ((changed.card * Nat.log 2 (2 * R + 1) : ℕ) : ℝ) ≤
        (c - C0) / (6 * (((ℓ - 1 : ℕ) : ℝ))) *
          secondOrderScale n) :
    Nonempty
      (GuardedCentralAnchorCertificate c R n left right changed) := by
  let q' : ℕ → ℕ :=
    guardedCentralCofactor n certificate.q left right changed
  have hq' : IsLargeCentralCofactorChoice n
      (centralAnchorCutoff R n) q' := by
    simpa only [q'] using guardedCentralCofactor_isChoice
      certificate.isCofactorChoice hchanged hchangedLe
  have hq'Bound : ∀ p ∈
      largeCentralPrimes n (centralAnchorCutoff R n),
      q' p ≤ 2 * R + 1 := by
    simpa only [q'] using guardedCentralCofactor_le_fixedPrefix
      certificate.isCofactorChoice hchanged hchangedLe
  have hsame : ∀ p ∈
      largeCentralPrimes n (centralAnchorCutoff R n),
      p ∉ changed → q' p = certificate.q p := by
    simpa only [q'] using
      (guardedCentralCofactor_eq_off_changed
        (R := R) (n := n) (q := certificate.q)
        (left := left) (right := right) (changed := changed))
  have hmax : max 2 (2 * R + 1) = 2 * R + 1 := by omega
  have hreserve : ∀ ℓ ∈ primesUpTo (2 * R + 1),
      (c - C0) / (6 * (((ℓ - 1 : ℕ) : ℝ))) *
            secondOrderScale n +
          ((centralAnchorDivisor n
            (centralAnchorCutoff R n) q').factorization ℓ : ℝ) ≤
        (upperTailValuation c n ℓ : ℝ) := by
    intro ℓ hℓ
    have hℓPrime := (mem_primesUpTo.mp hℓ).1
    have htransfer :=
      centralAnchorReserve_transfer_after_changed_cost
        (n := n) (X := centralAnchorCutoff R n)
        (B := 2 * R + 1) (ℓ := ℓ)
        (q := certificate.q) (q' := q') (changed := changed)
        (reserve :=
          (c - C0) / (3 * (((ℓ - 1 : ℕ) : ℝ))) *
            secondOrderScale n)
        (loss :=
          (c - C0) / (6 * (((ℓ - 1 : ℕ) : ℝ))) *
            secondOrderScale n)
        (tail := (upperTailValuation c n ℓ : ℝ))
        hℓPrime certificate.isCofactorChoice hq' hchanged hsame
        hq'Bound (hchangeCost ℓ hℓ) (certificate.divisor_reserve ℓ hℓ)
    calc
      (c - C0) / (6 * (((ℓ - 1 : ℕ) : ℝ))) *
              secondOrderScale n +
            ((centralAnchorDivisor n
              (centralAnchorCutoff R n) q').factorization ℓ : ℝ) =
          ((c - C0) / (3 * (((ℓ - 1 : ℕ) : ℝ))) *
              secondOrderScale n -
            (c - C0) / (6 * (((ℓ - 1 : ℕ) : ℝ))) *
              secondOrderScale n) +
            ((centralAnchorDivisor n
              (centralAnchorCutoff R n) q').factorization ℓ : ℝ) := by
                congr 1
                ring
      _ ≤ (upperTailValuation c n ℓ : ℝ) := htransfer
  have hsupport : ∀ ℓ : ℕ, ℓ.Prime →
      ℓ ∣ centralAnchorDivisor n (centralAnchorCutoff R n) q' →
        ℓ ∈ primesUpTo (2 * R + 1) := by
    intro ℓ hℓPrime hℓDivisor
    rw [mem_primesUpTo]
    refine ⟨hℓPrime, ?_⟩
    have hbound := prime_dvd_centralAnchorDivisor_le hq' hq'Bound
      hℓPrime hℓDivisor
    simpa only [hmax] using hbound
  have hdivisor :
      centralAnchorDivisor n (centralAnchorCutoff R n) q' ∣
        centralTailProduct n (upperTailLength c n) := by
    apply centralAnchorDivisor_dvd_upperTail_of_support_bounds hq' hq'Bound
    intro ℓ hℓ
    have hℓPrefix : ℓ ∈ primesUpTo (2 * R + 1) := by
      simpa only [hmax] using hℓ
    have hres := hreserve ℓ hℓPrefix
    have hdenPos : 0 < (((ℓ - 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.sub_pos_of_lt
        (mem_primesUpTo.mp hℓPrefix).1.one_lt
    have hmarginNonneg :
        0 ≤ (c - C0) /
            (6 * (((ℓ - 1 : ℕ) : ℝ))) * secondOrderScale n := by
      have hnTwo : 2 ≤ n := by
        have hthresholdTwo : 2 ≤ centralAnchorCutoffThreshold R := by
          rw [centralAnchorCutoffThreshold]
          have hsq : 1 ≤ (R + 1) ^ 2 :=
            one_le_pow₀ (by omega : 1 ≤ R + 1)
          calc
            2 ≤ 4 := by omega
            _ = 4 * 1 := by norm_num
            _ ≤ 4 * (R + 1) ^ 2 := Nat.mul_le_mul_left 4 hsq
        exact hthresholdTwo.trans hnCutoff
      exact mul_nonneg
        (div_nonneg (sub_nonneg.mpr hc.le)
          (mul_nonneg (by norm_num) hdenPos.le))
        (secondOrderScale_pos hnTwo).le
    have hvaluationReal :
        ((centralAnchorDivisor n
          (centralAnchorCutoff R n) q').factorization ℓ : ℝ) ≤
          (upperTailValuation c n ℓ : ℝ) := by linarith
    exact_mod_cast hvaluationReal
  let anchors' : Finset ℕ :=
    fullCentralAnchors n (centralAnchorCutoff R n) q'
  refine ⟨{
    q := q'
    anchors := anchors'
    isCofactorChoice := hq'
    anchors_eq := rfl
    anchors_subset := ?_
    anchors_prod := ?_
    divisor_prime_support := hsupport
    divisor_reserve := hreserve
    divisor_dvd_tail := hdivisor
    guarded_incident_cores := ?_
  }⟩
  · have hnPos : 0 < n :=
      (centralAnchorCutoffThreshold_pos R).trans_le hnCutoff
    simpa only [anchors'] using
      fullCentralAnchors_subset_centralInterval hnPos hq'
  · simpa only [anchors'] using
      fullCentralAnchors_prod_centralAnchorCutoff hnCutoff hq'
  · intro p hpChanged
    have hpLarge := hchanged hpChanged
    simpa only [q'] using
      guardedCentralCofactor_ne_incidentCores
        certificate.isCofactorChoice hchangedLe hrowOneAvoid
          hpLarge hpChanged

end

end Erdos390.WholePaper
