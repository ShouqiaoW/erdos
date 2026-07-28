import Erdos390.WholePaper.BankPaperAnchorGuards

namespace Erdos390.WholePaper

example {n M : ℕ} (R : BankPaperRealization n M)
    (P : ↑R.ordinary.markers) :
    R.anchorGuardIncidentCores P.1 =
      (bankOrdinaryPaperRequestSource (R.ordinary.requestForMarker P).1,
        bankOrdinaryPaperRequestTarget
          (R.ordinary.requestForMarker P).1) := by
  exact R.anchorGuardIncidentCores_of_ordinary P

example {n M : ℕ} (R : BankPaperRealization n M)
    (P : ↑R.bottom.relevantMarkers) :
    R.anchorGuardIncidentCores P.1 =
      R.bottom.relevantMarkerIncidentStateCores P := by
  exact R.anchorGuardIncidentCores_of_bottom P

example {n M depth : ℕ} (R : BankPaperRealization n M) :
    (R.allMarkers ∩ largeCentralPrimes n (n / (depth + 1))) ⊆
      largeCentralPrimes n (n / (depth + 1)) ∧
    (R.allMarkers ∩ largeCentralPrimes n (n / (depth + 1))) ⊆
      R.allMarkers ∧
    (R.allMarkers ∩ largeCentralPrimes n (n / (depth + 1))).card ≤
      (bankOrdinaryPaperRequests n).card +
        8 * bankBottomPaperDemand n := by
  constructor
  · simpa only [BankPaperRealization.centralChangedMarkers,
      centralAnchorCutoff] using
      R.centralChangedMarkers_subset_largeCentralPrimes depth
  · constructor
    · simpa only [BankPaperRealization.centralChangedMarkers,
        centralAnchorCutoff] using
        R.centralChangedMarkers_subset_allMarkers depth
    · simpa only [BankPaperRealization.centralChangedMarkers,
        centralAnchorCutoff] using R.centralChangedMarkers_card_le depth

example {n M depth : ℕ} (R : BankPaperRealization n M)
    (hM : M ≤ 3 * n) :
    ∀ p ∈ R.allMarkers ∩ largeCentralPrimes n (n / (depth + 1)),
      p ≤ n := by
  simpa only [BankPaperRealization.centralChangedMarkers,
    centralAnchorCutoff] using R.centralChangedMarker_le_n hM

example {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop,
      2 * upperEndpoint n (upperTailLength c n) ≤ 5 * n := by
  exact BankPaperRealization.eventually_two_mul_upperEndpoint_le_five_mul hc

example {n M depth : ℕ} (R : BankPaperRealization n M)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hMThree : M ≤ 3 * n) (hMFive : 2 * M ≤ 5 * n) :
    ∀ p ∈ R.allMarkers ∩ largeCentralPrimes n (n / (depth + 1)),
      n / p = 1 →
        3 ≠ (R.anchorGuardIncidentCores p).1 ∧
          3 ≠ (R.anchorGuardIncidentCores p).2 := by
  simpa only [BankPaperRealization.centralChangedMarkers,
    centralAnchorCutoff, BankPaperRealization.anchorGuardLeftCore,
    BankPaperRealization.anchorGuardRightCore] using
      R.centralChangedMarker_rowOne_avoids_three
        hnCutoff hMThree hMFive

end Erdos390.WholePaper
