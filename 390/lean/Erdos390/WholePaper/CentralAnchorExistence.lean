import Erdos390.WholePaper.CentralAnchorReserveAlgebra
import Erdos390.WholePaper.CentralPromotionCostAsymptotic
import Erdos390.WholePaper.StationaryPrefixCentralCofactorChoice

/-!
# Eventual existence of the complete central-anchor family

For every `c > C0`, one fixed prefix depth is chosen.  The promotion cost,
actual stationary-prefix allocation, and factorial-tail reserve are then
combined into an honest routed cofactor function and an honest finite set
of central anchors.  The certificate records interval containment, the
exact product identity, and literal divisibility of the anchor divisor into
the upper tail product.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- A canonical positive-support coordinate in every positive row. -/
noncomputable def stationaryPrefixDistinguished (r : ℕ) : ℕ :=
  dite (1 ≤ r)
    (fun hr ↦
      Classical.choose
        (infiniteAllocationPositiveSupport_nonempty r hr))
    (fun _ ↦ 0)

theorem stationaryPrefixDistinguished_mem
    {r : ℕ} (hr : 1 ≤ r) :
    stationaryPrefixDistinguished r ∈
      infiniteAllocationPositiveSupport r := by
  rw [stationaryPrefixDistinguished, dif_pos hr]
  exact Classical.choose_spec
    (infiniteAllocationPositiveSupport_nonempty r hr)

/-- The complete finite object produced by the central-anchor argument at
one `n`.  Besides the exact anchor product, it exposes the fixed prime
support and the quantitative one-third tail reserve needed when later bank
guards modify finitely many prefix cofactors. -/
structure CentralAnchorCertificate (c : ℝ) (R n : ℕ) where
  q : ℕ → ℕ
  anchors : Finset ℕ
  isCofactorChoice :
    IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q
  anchors_eq :
    anchors = fullCentralAnchors n (centralAnchorCutoff R n) q
  anchors_subset : anchors ⊆ Finset.Ioc n (2 * n)
  anchors_prod :
    anchors.prod id =
      Nat.choose (2 * n) n *
        centralAnchorDivisor n (centralAnchorCutoff R n) q
  divisor_prime_support :
    ∀ ℓ : ℕ, ℓ.Prime →
      ℓ ∣ centralAnchorDivisor n (centralAnchorCutoff R n) q →
        ℓ ∈ primesUpTo (2 * R + 1)
  divisor_reserve :
    ∀ ℓ ∈ primesUpTo (2 * R + 1),
      (c - C0) / (3 * (((ℓ - 1 : ℕ) : ℝ))) *
            secondOrderScale n +
          ((centralAnchorDivisor n
            (centralAnchorCutoff R n) q).factorization ℓ : ℝ) ≤
        (upperTailValuation c n ℓ : ℝ)
  divisor_dvd_tail :
    centralAnchorDivisor n (centralAnchorCutoff R n) q ∣
      centralTailProduct n (upperTailLength c n)

/-- Terminal central-anchor existence theorem.  The prefix depth (and hence
the finite support) is fixed before `n`; all remaining data and every
quantitative reserve inequality are actual finite statements at that `n`. -/
theorem exists_eventually_centralAnchorCertificate
    {c : ℝ} (hc : C0 < c) :
    ∃ R : ℕ, 201 ≤ R ∧
      ∀ᶠ n : ℕ in atTop,
        Nonempty (CentralAnchorCertificate c R n) := by
  let epsilon : ℝ := c - C0
  have hepsilon : 0 < epsilon := by
    simpa only [epsilon] using sub_pos.mpr hc
  have hcEq : c = C0 + epsilon := by
    simp only [epsilon]
    ring
  have hC0Pos : (0 : ℝ) < C0 := by
    norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
  have hpromotionTolerance : 0 < epsilon / 4 := by
    positivity
  obtain ⟨R, hR, hpromotion⟩ :=
    residualPromotionCost_eventually_cast_le_mul
      hpromotionTolerance
  let distinguished : ℕ → ℕ := stationaryPrefixDistinguished
  have hdistinguished :
      ∀ r ∈ Finset.Icc 1 R,
        distinguished r ∈ infiniteAllocationPositiveSupport r := by
    intro r hr
    exact stationaryPrefixDistinguished_mem
      (Finset.mem_Icc.mp hr).1
  obtain ⟨parts, hactual, hparts⟩ :=
    exists_stationaryPrefixParts_on_finset
      (Finset.Icc 1 R)
      (fun r hr ↦ (Finset.mem_Icc.mp hr).1)
      distinguished hdistinguished
  have hrouted :=
    eventually_stationaryPrefixCofactorChoice_certificate
      R distinguished parts hactual
  have hcofactor :=
    eventually_stationaryPrefixCofactorChoice_factorization_le_on_primesUpTo
      R distinguished (show 0 < epsilon / 6 by positivity)
      parts hactual hparts
  have htailReserve :
      ∀ᶠ n : ℕ in atTop,
        ∀ ell ∈ primesUpTo (2 * R + 1),
          (c / (((ell - 1 : ℕ) : ℝ)) -
              epsilon / (6 * (((ell - 1 : ℕ) : ℝ)))) *
              secondOrderScale n ≤
            (upperTailValuation c n ell : ℝ) := by
    apply eventually_upperTailValuation_ge_mul_scale_on_finset
      hcPos (primesUpTo (2 * R + 1))
      (fun ell ↦
        c / (((ell - 1 : ℕ) : ℝ)) -
          epsilon / (6 * (((ell - 1 : ℕ) : ℝ))))
    · intro ell hell
      exact (mem_primesUpTo.mp hell).1
    · intro ell hell
      have hellPrime := (mem_primesUpTo.mp hell).1
      have hdenominator : 0 < (((ell - 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.sub_pos_of_lt hellPrime.one_lt
      have hreservePos :
          0 < epsilon /
            (6 * (((ell - 1 : ℕ) : ℝ))) :=
        div_pos hepsilon (mul_pos (by norm_num) hdenominator)
      exact sub_lt_self _ hreservePos
  have hmax : max 2 (2 * R + 1) = 2 * R + 1 := by
    omega
  refine ⟨R, hR, ?_⟩
  filter_upwards [hrouted, hcofactor, hpromotion, htailReserve,
    eventually_secondOrderScale_pos,
    eventually_ge_atTop (centralAnchorCutoffThreshold R)] with n
    hroutedN hcofactorN hpromotionN htailN hscale hnCutoff
  let q : ℕ → ℕ :=
    stationaryPrefixCofactorChoice R n (parts n)
  have hqChoice :
      IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q := by
    simpa only [q] using hroutedN.1
  have hqBound :
      ∀ p ∈ largeCentralPrimes n (centralAnchorCutoff R n),
        q p ≤ 2 * R + 1 := by
    intro p hp
    exact largeCentralCofactor_le_fixedPrefix hqChoice hp
  have hcofactorSum :
      ∀ ell ∈ primesUpTo (max 2 (2 * R + 1)),
        ((∑ p ∈ largeCentralPrimes n (centralAnchorCutoff R n),
            (q p).factorization ell : ℕ) : ℝ) ≤
          (C0 / (((ell - 1 : ℕ) : ℝ)) +
              epsilon /
                (6 * (((ell - 1 : ℕ) : ℝ)))) *
            secondOrderScale n := by
    intro ell hell
    have hellPrefix : ell ∈ primesUpTo (2 * R + 1) := by
      simpa only [hmax] using hell
    have hproductBound := (hcofactorN ell hellPrefix).1
    have hfactorization :=
      largeCentralCofactorProduct_factorization_eq_sum
        (ell := ell) hqChoice
    rw [← hfactorization]
    calc
      (((largeCentralCofactorProduct n (centralAnchorCutoff R n)
          q).factorization ell : ℕ) : ℝ) ≤
          ((C0 + epsilon / 6) /
              (((ell - 1 : ℕ) : ℝ))) *
            secondOrderScale n := by
        simpa only [q] using hproductBound
      _ = (C0 / (((ell - 1 : ℕ) : ℝ)) +
              epsilon /
                (6 * (((ell - 1 : ℕ) : ℝ)))) *
            secondOrderScale n := by
        ring
  have hpromotionCutoff :
      (residualPromotionCost n (centralAnchorCutoff R n) : ℝ) ≤
        epsilon / 4 * secondOrderScale n := by
    simpa only [centralAnchorCutoff] using hpromotionN
  have htail :
      ∀ ell ∈ primesUpTo (max 2 (2 * R + 1)),
        (c / (((ell - 1 : ℕ) : ℝ)) -
            epsilon /
              (6 * (((ell - 1 : ℕ) : ℝ)))) *
            secondOrderScale n ≤
          (upperTailValuation c n ell : ℝ) := by
    intro ell hell
    exact htailN ell (by simpa only [hmax] using hell)
  have hdivisor :
      centralAnchorDivisor n (centralAnchorCutoff R n) q ∣
        centralTailProduct n (upperTailLength c n) := by
    exact centralAnchorDivisor_dvd_upperTail_of_slack
      (c := c) (epsilon := epsilon) (scale := secondOrderScale n)
      (n := n) (X := centralAnchorCutoff R n) (B := 2 * R + 1)
      (q := q) hcEq hepsilon hscale.le hqChoice hqBound
      hcofactorSum hpromotionCutoff htail
  have hdivisorSupport :
      ∀ ℓ : ℕ, ℓ.Prime →
        ℓ ∣ centralAnchorDivisor n (centralAnchorCutoff R n) q →
          ℓ ∈ primesUpTo (2 * R + 1) := by
    intro ℓ hℓPrime hℓDivisor
    apply mem_primesUpTo.mpr
    refine ⟨hℓPrime, ?_⟩
    have hbound := prime_dvd_centralAnchorDivisor_le hqChoice hqBound
      hℓPrime hℓDivisor
    simpa only [hmax] using hbound
  have hdivisorReserve :
      ∀ ℓ ∈ primesUpTo (2 * R + 1),
        (c - C0) / (3 * (((ℓ - 1 : ℕ) : ℝ))) *
              secondOrderScale n +
            ((centralAnchorDivisor n
              (centralAnchorCutoff R n) q).factorization ℓ : ℝ) ≤
          (upperTailValuation c n ℓ : ℝ) := by
    intro ℓ hℓ
    have hℓMax : ℓ ∈ primesUpTo (max 2 (2 * R + 1)) := by
      simpa only [hmax] using hℓ
    have hreserve :=
      centralAnchorDivisor_factorization_add_reserve_le_upperTailValuation_of_slack
        (c := c) (epsilon := epsilon) (scale := secondOrderScale n)
        (n := n) (X := centralAnchorCutoff R n) (ℓ := ℓ) (q := q)
        hcEq hepsilon hscale.le (mem_primesUpTo.mp hℓ).1 hqChoice
        (hcofactorSum ℓ hℓMax) hpromotionCutoff (htail ℓ hℓMax)
    have hepsilonEq : c - C0 = epsilon := by
      rw [hcEq]
      ring
    simpa only [hepsilonEq] using hreserve
  have hnPos : 0 < n :=
    (centralAnchorCutoffThreshold_pos R).trans_le hnCutoff
  let anchors : Finset ℕ :=
    fullCentralAnchors n (centralAnchorCutoff R n) q
  refine ⟨{
    q := q
    anchors := anchors
    isCofactorChoice := hqChoice
    anchors_eq := rfl
    anchors_subset := ?_
    anchors_prod := ?_
    divisor_prime_support := hdivisorSupport
    divisor_reserve := hdivisorReserve
    divisor_dvd_tail := hdivisor
  }⟩
  · simpa only [anchors] using
      fullCentralAnchors_subset_centralInterval hnPos hqChoice
  · simpa only [anchors] using
      fullCentralAnchors_prod_centralAnchorCutoff hnCutoff hqChoice

end

end Erdos390.WholePaper
