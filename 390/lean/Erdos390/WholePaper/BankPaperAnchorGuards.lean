import Erdos390.WholePaper.BankPaperComponents
import Erdos390.WholePaper.CentralAnchorGuardedCertificate

/-!
# Actual bank markers as central-anchor guards

This is the finite composition layer between the realized bank components
and the guarded central-cofactor construction.  The set of changed markers
is literally the intersection of the realized bank marker set with the
large-central-prime set.  Its two forbidden cores are recovered from the
unique incident component.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

namespace BankPaperRealization

/-- The two incident state cores attached to a realized bank marker.  The
ordinary and bottom branches are disjoint; the final branch is irrelevant
outside `allMarkers` and merely makes the function total. -/
def anchorGuardIncidentCores
    {n M : ℕ} (R : BankPaperRealization n M) (p : ℕ) : ℕ × ℕ :=
  if hpOrdinary : p ∈ R.ordinary.markers then
    let request := R.ordinary.requestForMarker ⟨p, hpOrdinary⟩
    (bankOrdinaryPaperRequestSource request.1,
      bankOrdinaryPaperRequestTarget request.1)
  else if hpBottom : p ∈ R.bottom.relevantMarkers then
    R.bottom.relevantMarkerIncidentStateCores ⟨p, hpBottom⟩
  else (0, 0)

def anchorGuardLeftCore
    {n M : ℕ} (R : BankPaperRealization n M) (p : ℕ) : ℕ :=
  (R.anchorGuardIncidentCores p).1

def anchorGuardRightCore
    {n M : ℕ} (R : BankPaperRealization n M) (p : ℕ) : ℕ :=
  (R.anchorGuardIncidentCores p).2

/-- Exactly the realized bank markers which actually occur in the large
central divisor. -/
def centralChangedMarkers
    {n M : ℕ} (R : BankPaperRealization n M) (depth : ℕ) : Finset ℕ :=
  R.allMarkers ∩ largeCentralPrimes n (centralAnchorCutoff depth n)

theorem centralChangedMarkers_subset_largeCentralPrimes
    {n M : ℕ} (R : BankPaperRealization n M) (depth : ℕ) :
    R.centralChangedMarkers depth ⊆
      largeCentralPrimes n (centralAnchorCutoff depth n) := by
  exact Finset.inter_subset_right

theorem centralChangedMarkers_subset_allMarkers
    {n M : ℕ} (R : BankPaperRealization n M) (depth : ℕ) :
    R.centralChangedMarkers depth ⊆ R.allMarkers := by
  exact Finset.inter_subset_left

theorem centralChangedMarkers_card_le
    {n M : ℕ} (R : BankPaperRealization n M) (depth : ℕ) :
    (R.centralChangedMarkers depth).card ≤
      (bankOrdinaryPaperRequests n).card +
        8 * bankBottomPaperDemand n := by
  calc
    (R.centralChangedMarkers depth).card ≤ R.allMarkers.card :=
      Finset.card_le_card (R.centralChangedMarkers_subset_allMarkers depth)
    _ = (bankOrdinaryPaperRequests n).card +
        (bankBottomRelevantPaperRequests n).card := R.allMarkers_card
    _ ≤ (bankOrdinaryPaperRequests n).card +
        8 * bankBottomPaperDemand n := by
      exact Nat.add_le_add_left
        (by
          rw [← R.bottom.card_relevantMarkers]
          exact R.bottom.card_relevantMarkers_le_demand)
        _

/-- Membership in the ordinary marker set unfolds the canonical incident
cores to the actual request source and target. -/
theorem anchorGuardIncidentCores_of_ordinary
    {n M : ℕ} (R : BankPaperRealization n M)
    (P : ↑R.ordinary.markers) :
    R.anchorGuardIncidentCores P.1 =
      (bankOrdinaryPaperRequestSource (R.ordinary.requestForMarker P).1,
        bankOrdinaryPaperRequestTarget (R.ordinary.requestForMarker P).1) := by
  simp [anchorGuardIncidentCores, P.property]

/-- Membership in the bottom marker set unfolds to the unique relevant
bottom request's two actual state cores. -/
theorem anchorGuardIncidentCores_of_bottom
    {n M : ℕ} (R : BankPaperRealization n M)
    (P : ↑R.bottom.relevantMarkers) :
    R.anchorGuardIncidentCores P.1 =
      R.bottom.relevantMarkerIncidentStateCores P := by
  have hnotOrdinary : P.1 ∉ R.ordinary.markers := by
    intro hpOrdinary
    exact (Finset.disjoint_left.mp
      R.ordinaryMarkers_disjoint_bottomMarkers) hpOrdinary P.property
  simp [anchorGuardIncidentCores, hnotOrdinary, P.property]

/-- Every changed marker lies below `n`.  This is immediate for ordinary
markers from `3P<n`; for every bottom row it follows from `M≤3n` and the
literal upper endpoint of that row. -/
theorem centralChangedMarker_le_n
    {n M depth : ℕ} (R : BankPaperRealization n M)
    (hM : M ≤ 3 * n) :
    ∀ p ∈ R.centralChangedMarkers depth, p ≤ n := by
  intro p hpChanged
  have hpAll := R.centralChangedMarkers_subset_allMarkers depth hpChanged
  rw [allMarkers, ordinaryMarkers, bottomMarkers,
    Finset.mem_union] at hpAll
  rcases hpAll with hpOrdinary | hpBottom
  · let P : ↑R.ordinary.markers := ⟨p, hpOrdinary⟩
    have hsmall := R.ordinary.three_mul_marker_lt_n
      (R.ordinary.requestForMarker P)
    have hmarker :
        R.ordinary.marker (R.ordinary.requestForMarker P) = p := by
      simpa only [P] using R.ordinary.marker_requestForMarker P
    rw [hmarker] at hsmall
    omega
  · let P : ↑R.bottom.relevantMarkers := ⟨p, hpBottom⟩
    let request := bankBottomRelevantRequestToPaperRequest
      (R.bottom.requestForRelevantMarker P)
    have hbound := R.bottom.marker_le_n
      R.ordinary.two_mul_n_le_M hM request
    have hmarker : R.bottom.marker request = p := by
      exact R.bottom.marker_requestForRelevantMarker P
    simpa only [hmarker] using hbound

/-- Eventually the paper endpoint is already below `5n/2`.  This slightly
sharper elementary endpoint bound is used only to identify the unique
row-one bottom move. -/
theorem eventually_two_mul_upperEndpoint_le_five_mul
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      2 * upperEndpoint n (upperTailLength c n) ≤ 5 * n := by
  have hsmall := (upperTailLength_ratio_tendsto_zero hc).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hn htail
  have hnPos : (0 : ℝ) < n := by exact_mod_cast htail
  have hcast : (2 * upperTailLength c n : ℕ) ≤ n := by
    have hreal : (2 : ℝ) * upperTailLength c n < n := by
      have := (div_lt_iff₀ hnPos).mp hn
      nlinarith
    exact_mod_cast hreal.le
  simp only [upperEndpoint]
  omega

/-- At a changed row-one marker, neither actual incident state core is `3`.
For ordinary components both cores are at least five.  Among the four bottom
rows, the literal marker intervals and central stationary-row inequalities
leave only `2→1`, whose cores are `(2,4)`. -/
theorem centralChangedMarker_rowOne_avoids_three
    {n M depth : ℕ} (R : BankPaperRealization n M)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hMThree : M ≤ 3 * n) (hMFive : 2 * M ≤ 5 * n) :
    ∀ p ∈ R.centralChangedMarkers depth, n / p = 1 →
      3 ≠ R.anchorGuardLeftCore p ∧
        3 ≠ R.anchorGuardRightCore p := by
  intro p hpChanged hrowOne
  have hpAll := R.centralChangedMarkers_subset_allMarkers depth hpChanged
  have hpLarge := R.centralChangedMarkers_subset_largeCentralPrimes depth hpChanged
  rw [allMarkers, ordinaryMarkers, bottomMarkers,
    Finset.mem_union] at hpAll
  rcases hpAll with hpOrdinary | hpBottom
  · let P : ↑R.ordinary.markers := ⟨p, hpOrdinary⟩
    have hspec := bankOrdinaryPaperRequest_component_spec
      (R.ordinary.requestForMarker P).1
    have hsourceSix := hspec.1
    have htargetFive := hspec.2.2.2.1
    have hcores :
        R.anchorGuardIncidentCores p =
          (bankOrdinaryPaperRequestSource
              (R.ordinary.requestForMarker P).1,
            bankOrdinaryPaperRequestTarget
              (R.ordinary.requestForMarker P).1) := by
      simpa only [P] using R.anchorGuardIncidentCores_of_ordinary P
    simp only [anchorGuardLeftCore, anchorGuardRightCore, hcores]
    constructor <;> omega
  · let P : ↑R.bottom.relevantMarkers := ⟨p, hpBottom⟩
    let relevantRequest := R.bottom.requestForRelevantMarker P
    let request := bankBottomRelevantRequestToPaperRequest relevantRequest
    have hmarker : R.bottom.marker request = p := by
      exact R.bottom.marker_requestForRelevantMarker P
    have hpRoute :=
      (largeCentralPrime_rowZero_or_fixedPrefix hnCutoff hpLarge).2
    have hpLe : p ≤ n :=
      R.centralChangedMarker_le_n hMThree p hpChanged
    have hpStationary : p ∈ stationaryPrimeLayer n 1 := by
      rcases hpRoute with hzero |
          ⟨r, _hrPos, _hrDepth, hrEq, hpStationary⟩
      · exact (not_lt_of_ge hpLe hzero.1).elim
      · have hrOne : r = 1 := by omega
        simpa only [hrOne] using hpStationary
    have hpStationaryData := mem_stationaryPrimeLayer.mp hpStationary
    have hmarkerRow := R.bottom.marker_mem_row
      R.ordinary.two_mul_n_le_M request
    rw [hmarker] at hmarkerRow
    have hmove : R.bottom.move request = .twoToOne := by
      cases hmoveCases : R.bottom.move request
      · have hupper := (Finset.mem_Ioc.mp hmarkerRow).2
        simp only [hmoveCases,
          bankBottomMarkerUpper] at hupper
        exfalso
        omega
      · have hupper := (Finset.mem_Ioc.mp hmarkerRow).2
        simp only [hmoveCases,
          bankBottomMarkerUpper] at hupper
        exfalso
        omega
      · have hlower := (Finset.mem_Ioc.mp hmarkerRow).1
        simp only [hmoveCases,
          bankBottomMarkerLower] at hlower
        have htwoNltRaw :=
          (Nat.div_lt_iff_lt_mul (by omega : 0 < 3)).mp hlower
        have htwoNlt : 2 * n < 3 * p := by
          omega
        exfalso
        omega
      · rfl
    have hcoresBottom := R.anchorGuardIncidentCores_of_bottom P
    have hcanonicalCores :
        R.bottom.relevantMarkerIncidentStateCores P = (2, 4) := by
      change bankBottomIncidentStateCores
        (R.bottom.move request) = (2, 4)
      rw [hmove]
      rfl
    rw [anchorGuardLeftCore, anchorGuardRightCore,
      hcoresBottom, hcanonicalCores]
    norm_num

end BankPaperRealization

end

end Erdos390.WholePaper
