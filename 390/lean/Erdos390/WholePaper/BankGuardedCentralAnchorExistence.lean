import Erdos390.WholePaper.BankPaperAnchorChangeBudget

/-!
# Eventual central anchors guarded against every realized bank component

The bank is realized first at the paper endpoint.  Its literal marker set is
intersected with the large central-prime set, all those cofactors are changed,
and the `O(yNat²)=o(n/log n)` budget pays for the modification.  The result is
an actual modified anchor family, not a compatibility package.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

/-- Terminal anchor-guard existence statement for the actual combined bank.
The returned certificate retains a positive one-sixth valuation reserve and
its exact divisor divides the literal factorial tail. -/
theorem exists_eventually_bankGuardedCentralAnchorCertificate
    {c : ℝ} (hc : C0 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ bank : BankPaperRealization n
            (upperEndpoint n (upperTailLength c n)),
          Nonempty
            (GuardedCentralAnchorCertificate c depth n
              bank.anchorGuardLeftCore bank.anchorGuardRightCore
              (bank.centralChangedMarkers depth)) := by
  obtain ⟨depth, hdepth, hcentral⟩ :=
    exists_eventually_centralAnchorCertificate hc
  have hdepthOne : 1 ≤ depth := by omega
  have hC0Pos : (0 : ℝ) < C0 := by norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
  have hbank := eventually_exists_bankPaperRealization hcPos
  have hendpoint := eventually_upperScaledEndpoint_bounds hcPos
  have hendpointFive :=
    BankPaperRealization.eventually_two_mul_upperEndpoint_le_five_mul hcPos
  have hcost := eventually_bankPaper_changeCost_le_sixth_reserve
    hc hdepthOne
  refine ⟨depth, hdepth, ?_⟩
  filter_upwards [hcentral, hbank, hendpoint, hendpointFive, hcost,
      eventually_ge_atTop (centralAnchorCutoffThreshold depth)]
      with n hcentralN hbankN hendpointN hendpointFiveN hcostN hnCutoff
  obtain ⟨central⟩ := hcentralN
  obtain ⟨bank⟩ := hbankN
  refine ⟨bank, ?_⟩
  apply guardedCentralAnchorCertificate_of_changeCost
    hc hdepthOne hnCutoff central
    (bank.centralChangedMarkers_subset_largeCentralPrimes depth)
    (bank.centralChangedMarker_le_n hendpointN.2)
    (bank.centralChangedMarker_rowOne_avoids_three
      hnCutoff hendpointN.2 hendpointFiveN)
    (hcostN _ bank)

end

end Erdos390.WholePaper
