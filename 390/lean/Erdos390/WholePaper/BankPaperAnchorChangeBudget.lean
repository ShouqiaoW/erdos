import Erdos390.WholePaper.BankPaperAnchorGuards

/-!
# The cost of guarding every realized bank marker is negligible

The deliberately coarse global marker bound is `O(yNat²)`.  Since
`yNat² = o(n/log n)`, even changing every realized bank marker which meets
the fixed central prefix consumes only an arbitrarily small fixed fraction
of the central valuation reserve.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- A realization-independent numerical upper bound for all changed bank
markers. -/
def bankPaperAnchorMarkerBudget (n : ℕ) : ℕ :=
  (bankOrdinaryPaperRequests n).card + 8 * bankBottomPaperDemand n

theorem bankPaperAnchorMarkerBudget_isBigO_yNat_sq :
    (fun n : ℕ ↦ (bankPaperAnchorMarkerBudget n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (yNat n : ℝ) ^ 2) := by
  have hySq :
      (fun n : ℕ ↦ (yNat n : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (yNat n : ℝ) ^ 2) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_bankBottom_six_le_yNat] with n hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ yNat n),
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (yNat n : ℝ)), one_mul]
    have hyOne : (1 : ℝ) ≤ yNat n := by exact_mod_cast (show 1 ≤ yNat n by omega)
    nlinarith [sq_nonneg ((yNat n : ℝ) - 1)]
  have hdemandSq := bankBottomPaperDemand_isBigO_yNat.trans hySq
  have hsum := bankOrdinaryPaperRequests_card_isBigO_yNat_sq.add
    (hdemandSq.const_mul_left (8 : ℝ))
  apply hsum.congr'
  · exact Eventually.of_forall fun n ↦ by
      simp only [bankPaperAnchorMarkerBudget, Nat.cast_add,
        Nat.cast_mul, Nat.cast_ofNat]
  · exact Eventually.of_forall fun _n ↦ rfl

/-- The coarse all-marker budget itself is little-o of the central scale. -/
theorem bankPaperAnchorMarkerBudget_isLittleO_secondOrderScale :
    (fun n : ℕ ↦ (bankPaperAnchorMarkerBudget n : ℝ)) =o[atTop]
      secondOrderScale := by
  have hyLittle :
      (fun n : ℕ ↦ (yNat n : ℝ) ^ 2) =o[atTop]
        secondOrderScale := by
    apply (isLittleO_iff_tendsto' ?_).mpr
      yNat_sq_div_secondOrderScale_tendsto_zero
    filter_upwards [eventually_secondOrderScale_pos] with n hscale hzero
    exact (hscale.ne' hzero).elim
  exact bankPaperAnchorMarkerBudget_isBigO_yNat_sq.trans_isLittleO hyLittle

/-- Multiplying by the fixed worst-case cofactor valuation still gives a
vanishing normalized change cost. -/
theorem bankPaperAnchorChangeCost_normalized_tendsto_zero (depth : ℕ) :
    Tendsto
      (fun n : ℕ ↦
        ((bankPaperAnchorMarkerBudget n * Nat.log 2 (2 * depth + 1) : ℕ) : ℝ) /
          secondOrderScale n)
      atTop (nhds 0) := by
  have hscaled :=
    bankPaperAnchorMarkerBudget_isLittleO_secondOrderScale.const_mul_left
      ((Nat.log 2 (2 * depth + 1) : ℕ) : ℝ)
  have hlimit := hscaled.tendsto_div_nhds_zero
  apply hlimit.congr'
  exact Eventually.of_forall fun n ↦ by
    push_cast
    ring

/-- Uniformly over every realization and endpoint, the literal changed-set
cost is eventually below any prescribed positive multiple of the central
scale. -/
theorem eventually_bankPaper_centralChangedMarkers_changeCost_le
    (depth : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, ∀ (M : ℕ) (R : BankPaperRealization n M),
      (((R.centralChangedMarkers depth).card *
          Nat.log 2 (2 * depth + 1) : ℕ) : ℝ) ≤
        delta * secondOrderScale n := by
  have hsmall := (bankPaperAnchorChangeCost_normalized_tendsto_zero depth).eventually
    (eventually_lt_nhds hdelta)
  filter_upwards [hsmall, eventually_secondOrderScale_pos] with n hn hscale
  have hbudget :
      ((bankPaperAnchorMarkerBudget n * Nat.log 2 (2 * depth + 1) : ℕ) : ℝ) ≤
        delta * secondOrderScale n := by
    have hratio := (div_lt_iff₀ hscale).mp hn
    exact hratio.le
  intro M R
  have hcard : (R.centralChangedMarkers depth).card ≤
      bankPaperAnchorMarkerBudget n := by
    simpa only [bankPaperAnchorMarkerBudget] using
      R.centralChangedMarkers_card_le depth
  have hcostNat :
      (R.centralChangedMarkers depth).card * Nat.log 2 (2 * depth + 1) ≤
        bankPaperAnchorMarkerBudget n * Nat.log 2 (2 * depth + 1) :=
    Nat.mul_le_mul_right _ hcard
  exact (by exact_mod_cast hcostNat :
      (((R.centralChangedMarkers depth).card *
        Nat.log 2 (2 * depth + 1) : ℕ) : ℝ) ≤
      ((bankPaperAnchorMarkerBudget n *
        Nat.log 2 (2 * depth + 1) : ℕ) : ℝ)).trans hbudget

/-- Prime-by-prime form matching the guarded central certificate.  The
finite support is handled uniformly using its largest possible denominator.
-/
theorem eventually_bankPaper_changeCost_le_sixth_reserve
    {c : ℝ} (hc : C0 < c) {depth : ℕ} (hdepth : 1 ≤ depth) :
    ∀ᶠ n : ℕ in atTop, ∀ (M : ℕ) (R : BankPaperRealization n M),
      ∀ ℓ ∈ primesUpTo (2 * depth + 1),
        (((R.centralChangedMarkers depth).card *
            Nat.log 2 (2 * depth + 1) : ℕ) : ℝ) ≤
          (c - C0) / (6 * (((ℓ - 1 : ℕ) : ℝ))) *
            secondOrderScale n := by
  let delta : ℝ :=
    (c - C0) / (6 * (((2 * depth + 1 - 1 : ℕ) : ℝ)))
  have hepsilon : 0 < c - C0 := sub_pos.mpr hc
  have hlargest : 0 < (((2 * depth + 1 - 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show 0 < 2 * depth + 1 - 1 by omega)
  have hdelta : 0 < delta := by
    exact div_pos hepsilon (mul_pos (by norm_num) hlargest)
  have hbase :=
    eventually_bankPaper_centralChangedMarkers_changeCost_le depth hdelta
  filter_upwards [hbase, eventually_secondOrderScale_pos] with n hn hscale
  intro M R ℓ hℓ
  have hℓPrime := (mem_primesUpTo.mp hℓ).1
  have hℓBound := (mem_primesUpTo.mp hℓ).2
  have hsmall : 0 < (((ℓ - 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.sub_pos_of_lt hℓPrime.one_lt
  have hdenLe : (((ℓ - 1 : ℕ) : ℝ)) ≤
      (((2 * depth + 1 - 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show ℓ - 1 ≤ 2 * depth + 1 - 1 by omega)
  have hcoefficient : delta ≤
      (c - C0) / (6 * (((ℓ - 1 : ℕ) : ℝ))) := by
    dsimp [delta]
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hlargest)
      (mul_pos (by norm_num) hsmall)).2
    nlinarith
  exact (hn M R).trans
    (mul_le_mul_of_nonneg_right hcoefficient hscale.le)

end

end Erdos390.WholePaper
