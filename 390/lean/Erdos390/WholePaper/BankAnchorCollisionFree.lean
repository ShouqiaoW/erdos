import Erdos390.WholePaper.BankPaperAnchorGuards
import Erdos390.WholePaper.CentralAnchorCollision

/-!
# Collision freedom between the complete central anchors and the actual bank

The large-anchor branch recovers the common prime marker from the complete
rough factorization above `yNat`.  Once the marker is recovered, the guarded
central-cofactor certificate excludes the two incident state cores.

The residual branch uses the more rigid shape
`2^k * p^e`.  A bottom marker is already above the residual cutoff.  For an
ordinary marker, divisibility first forces the residual base prime to be the
marker; its marker valuation is then one, so cancellation would make the
ordinary state core a power of two, contrary to the path certificate.

Donor-only occurrences do not create an extra case: ordinary donors and the
two nonterminal bottom donors lie above `2n`, while terminal bottom donors
are literally their upper endpoint state.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## The two eventual scale separations used by marker recovery -/

/-- The elementary square bound behind the separation
`yNat n < centralAnchorCutoff depth n`. -/
theorem bankAnchor_yNat_mul_self_le_self
    {n : ℕ} (hn : 1 ≤ n) : yNat n * yNat n ≤ n := by
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (by positivity) _
  have hyFloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
  have hyFloorNonneg : (0 : ℝ) ≤ yNat n := by positivity
  have hsq : (yNat n : ℝ) ^ 2 ≤ y n ^ 2 :=
    (sq_le_sq₀ hyFloorNonneg hyNonneg).2 hyFloor
  have hpow : (n : ℝ) ^ (4 / 9 : ℝ) ≤ (n : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hnOne
        (by norm_num : (4 / 9 : ℝ) ≤ 1)
  rw [Erdos390.Full.Scale.y_pow_two] at hsq
  have hcast : ((yNat n * yNat n : ℕ) : ℝ) ≤ (n : ℝ) := by
    push_cast
    simpa only [pow_two] using hsq.trans hpow
  exact_mod_cast hcast

/-- The smooth cutoff tends to infinity, exposed here because a fixed anchor
prefix contributes only the cofactors `1,…,2*depth+1`. -/
theorem bankAnchor_yNat_tendsto_atTop : Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_nat_floor_atTop.comp hy

theorem eventually_bankAnchor_fixed_le_yNat (B : ℕ) :
    ∀ᶠ n : ℕ in atTop, B ≤ yNat n :=
  bankAnchor_yNat_tendsto_atTop.eventually (eventually_ge_atTop B)

/-- At the literal central-anchor threshold, the moving smooth cutoff is
strictly below the residual/large-prime cutoff. -/
theorem yNat_lt_centralAnchorCutoff_of_threshold
    {depth n : ℕ} (hn : 1 ≤ n)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n) :
    yNat n < centralAnchorCutoff depth n := by
  have hySq := bankAnchor_yNat_mul_self_le_self hn
  have hcutSq := two_mul_lt_centralAnchorCutoff_sq hnCutoff
  nlinarith

theorem eventually_yNat_lt_centralAnchorCutoff (depth : ℕ) :
    ∀ᶠ n : ℕ in atTop, yNat n < centralAnchorCutoff depth n := by
  filter_upwards [eventually_ge_atTop 1,
      eventually_ge_atTop (centralAnchorCutoffThreshold depth)]
      with n hn hnCutoff
  exact yNat_lt_centralAnchorCutoff_of_threshold hn hnCutoff

/-! ## Arithmetic collision kernels -/

/-- An odd prime marker above the smooth cutoff cannot turn a certified
non-power-of-two smooth core into a promoted residual factor. -/
theorem marker_mul_nonpower_smooth_ne_promotedCentralFactor
    {n yNatValue P core p : ℕ}
    (hP : P.Prime) (hp : p.Prime)
    (hyTwo : 2 ≤ yNatValue) (hPy : yNatValue < P)
    (hcoreSmooth : core ∈ Nat.smoothNumbers (yNatValue + 1))
    (hcoreNonpower : ¬ IsPowerOfTwo core) :
    P * core ≠ promotedCentralFactor n p := by
  intro heq
  have hPDiv : P ∣ promotedCentralFactor n p := by
    rw [← heq]
    exact dvd_mul_right P core
  rcases prime_dvd_promotedCentralFactor hp hP hPDiv with hPTwo | hPp
  · omega
  · subst p
    have hPOdd : P ≠ 2 := by omega
    have hcoreNe : core ≠ 0 :=
      Nat.ne_zero_of_mem_smoothNumbers hcoreSmooth
    have hcoreFactorization : core.factorization P = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hPcore
      have hsmall :=
        (Nat.mem_smoothNumbers').mp hcoreSmooth P hP hPcore
      omega
    have hcoordinate := congrArg (fun value : ℕ ↦ value.factorization P) heq
    change (P * core).factorization P =
      (promotedCentralFactor n P).factorization P at hcoordinate
    rw [Nat.factorization_mul hP.ne_zero hcoreNe,
      Finsupp.add_apply, hP.factorization_self, hcoreFactorization,
      promotedCentralFactor_factorization_odd hP hPOdd] at hcoordinate
    simp only [add_zero] at hcoordinate
    have hexponent :
        (Nat.choose (2 * n) n).factorization P = 1 := hcoordinate.symm
    have hblock : centralPrimeBlock n P = P := by
      simp [centralPrimeBlock, hexponent]
    have hpromoted :
        promotedCentralFactor n P =
          P * 2 ^ promotionExponent n P := by
      simp [promotedCentralFactor, promotedBlock, hblock, Nat.mul_comm]
    have hproduct : P * core = P * 2 ^ promotionExponent n P :=
      heq.trans hpromoted
    have hcorePower : core = 2 ^ promotionExponent n P :=
      Nat.mul_left_cancel hP.pos hproduct
    exact hcoreNonpower
      ((isPowerOfTwo_iff core).2
        ⟨promotionExponent n P, hcorePower⟩)

namespace BankPaperRealization

/-- A large central anchor cannot equal a bank state once that state's core
is one of the two guarded incident cores. -/
theorem guardedLargeCentralAnchor_ne_marker_mul_incidentCore
    {c : ℝ} {depth n M P core p : ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (hfixed : 2 * depth + 1 ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hpLarge : p ∈ largeCentralPrimes n (centralAnchorCutoff depth n))
    (hPPrime : P.Prime) (hPy : yNat n < P)
    (hcoreSmooth : core ∈ Nat.smoothNumbers (yNat n + 1))
    (hPAll : P ∈ R.allMarkers)
    (hincident : core = R.anchorGuardLeftCore P ∨
      core = R.anchorGuardRightCore P) :
    largeCentralAnchor certificate.q p ≠ P * core := by
  intro heq
  have hpPrime := largeCentralPrimes_prime hpLarge
  have hpY : yNat n < p :=
    hyCutoff.trans (largeCentralPrimes_gt hpLarge)
  have hqPos : 0 < certificate.q p :=
    largeCentralCofactor_pos certificate.isCofactorChoice hpLarge
  have hqLe : certificate.q p ≤ 2 * depth + 1 :=
    largeCentralCofactor_le_fixedPrefix
      certificate.isCofactorChoice hpLarge
  have hqSmooth : certificate.q p ∈
      Nat.smoothNumbers (yNat n + 1) := by
    exact Nat.mem_smoothNumbers_of_lt hqPos
      (Nat.lt_succ_of_le (hqLe.trans hfixed))
  have hmarker : p = P :=
    primeMarker_mul_smooth_marker_eq hpPrime hPPrime hpY hPy
      hqSmooth hcoreSmooth (by
        simpa only [largeCentralAnchor] using heq)
  have hpAll : p ∈ R.allMarkers := by
    simpa only [hmarker] using hPAll
  have hpChanged : p ∈ R.centralChangedMarkers depth :=
    Finset.mem_inter.mpr ⟨hpAll, hpLarge⟩
  have hqCore : certificate.q p = core := by
    apply Nat.mul_left_cancel hpPrime.pos
    calc
      p * certificate.q p = largeCentralAnchor certificate.q p := rfl
      _ = P * core := heq
      _ = p * core := by rw [hmarker]
  have hguard := certificate.guarded_incident_cores p hpChanged
  rcases hincident with hleft | hright
  · apply hguard.1
    calc
      certificate.q p = core := hqCore
      _ = R.anchorGuardLeftCore P := hleft
      _ = R.anchorGuardLeftCore p := by rw [hmarker]
  · apply hguard.2
    calc
      certificate.q p = core := hqCore
      _ = R.anchorGuardRightCore P := hright
      _ = R.anchorGuardRightCore p := by rw [hmarker]

/-! ## Literal recovery of the incident cores from actual requests -/

theorem anchorGuardIncidentCores_ordinaryMarker
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.anchorGuardIncidentCores (R.ordinary.marker request) =
      (bankOrdinaryPaperRequestSource request.1,
        bankOrdinaryPaperRequestTarget request.1) := by
  let P : ↑R.ordinary.markers :=
    ⟨R.ordinary.marker request, R.ordinary.marker_mem_markers request⟩
  have hcores := R.anchorGuardIncidentCores_of_ordinary P
  have hrequest : R.ordinary.requestForMarker P = request := by
    symm
    exact R.ordinary.requestForMarker_unique P request rfl
  simpa only [P, hrequest] using hcores

theorem anchorGuardLeftCore_ordinaryMarker
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.anchorGuardLeftCore (R.ordinary.marker request) =
      bankOrdinaryPaperRequestSource request.1 := by
  exact congrArg Prod.fst (R.anchorGuardIncidentCores_ordinaryMarker request)

theorem anchorGuardRightCore_ordinaryMarker
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.anchorGuardRightCore (R.ordinary.marker request) =
      bankOrdinaryPaperRequestTarget request.1 := by
  exact congrArg Prod.snd (R.anchorGuardIncidentCores_ordinaryMarker request)

theorem anchorGuardIncidentCores_bottomMarker
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : ↑(bankBottomRelevantPaperRequests n)) :
    R.anchorGuardIncidentCores
        (R.bottom.marker
          (bankBottomRelevantRequestToPaperRequest request)) =
      R.bottom.incidentStateCores
        (bankBottomRelevantRequestToPaperRequest request) := by
  let P : ↑R.bottom.relevantMarkers :=
    ⟨R.bottom.marker (bankBottomRelevantRequestToPaperRequest request),
      R.bottom.relevantMarker_mem_relevantMarkers request⟩
  calc
    R.anchorGuardIncidentCores P.1 =
        R.bottom.relevantMarkerIncidentStateCores P :=
      R.anchorGuardIncidentCores_of_bottom P
    _ = R.bottom.incidentStateCores
        (bankBottomRelevantRequestToPaperRequest request) := by
      simpa only [P] using
        R.bottom.relevantMarkerIncidentStateCores_of_request request

theorem anchorGuardLeftCore_bottomMarker
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : ↑(bankBottomRelevantPaperRequests n)) :
    R.anchorGuardLeftCore
        (R.bottom.marker
          (bankBottomRelevantRequestToPaperRequest request)) =
      bankBottomLowerStateMultiplier
        (R.bottom.move
          (bankBottomRelevantRequestToPaperRequest request)) := by
  have hcores := R.anchorGuardIncidentCores_bottomMarker request
  exact congrArg Prod.fst hcores

theorem anchorGuardRightCore_bottomMarker
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : ↑(bankBottomRelevantPaperRequests n)) :
    R.anchorGuardRightCore
        (R.bottom.marker
          (bankBottomRelevantRequestToPaperRequest request)) =
      bankBottomUpperStateMultiplier
        (R.bottom.move
          (bankBottomRelevantRequestToPaperRequest request)) := by
  have hcores := R.anchorGuardIncidentCores_bottomMarker request
  exact congrArg Prod.snd hcores

theorem ordinaryMarker_mem_allMarkers
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.ordinary.marker request ∈ R.allMarkers := by
  rw [allMarkers, ordinaryMarkers, bottomMarkers, Finset.mem_union]
  exact Or.inl (R.ordinary.marker_mem_markers request)

theorem bottomMarker_mem_allMarkers
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : ↑(bankBottomRelevantPaperRequests n)) :
    R.bottom.marker (bankBottomRelevantRequestToPaperRequest request) ∈
      R.allMarkers := by
  rw [allMarkers, ordinaryMarkers, bottomMarkers, Finset.mem_union]
  exact Or.inr (R.bottom.relevantMarker_mem_relevantMarkers request)

/-- Every relevant bottom marker lies above the residual cutoff as soon as
the fixed prefix contains at least the first two rows. -/
theorem centralAnchorCutoff_lt_bottomMarker
    {n M depth : ℕ} (R : BankPaperRealization n M)
    (hdepth : 2 ≤ depth)
    (request : ↑(bankBottomPaperRequests n)) :
    centralAnchorCutoff depth n < R.bottom.marker request := by
  rw [centralAnchorCutoff]
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < depth + 1)).2
  have hnMarker := R.bottom.n_lt_three_mul_marker
    R.ordinary.two_mul_n_le_M request
  have hthree :
      3 * R.bottom.marker request ≤
        R.bottom.marker request * (depth + 1) := by
    calc
      3 * R.bottom.marker request =
          R.bottom.marker request * 3 := Nat.mul_comm _ _
      _ ≤ R.bottom.marker request * (depth + 1) :=
        Nat.mul_le_mul_left _ (by omega)
  exact hnMarker.trans_le hthree

/-- The two bottom donors which are not endpoint states lie strictly above
`2n`; the other two donors are literally the upper endpoint. -/
theorem bottomDonor_eq_upperState_or_two_mul_n_lt
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : ↑(bankBottomPaperRequests n)) :
    R.bottom.donorFactor request = R.bottom.upperStateFactor request ∨
      2 * n < R.bottom.donorFactor request := by
  have hrow := R.bottom.marker_mem_row
    R.ordinary.two_mul_n_le_M request
  have hlower := (Finset.mem_Ioc.mp hrow).1
  cases hmove : R.bottom.move request
  · right
    simp only [hmove, bankBottomMarkerLower] at hlower
    have hnMarker : n < R.bottom.marker request * 3 :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < 3)).1 hlower
    simp only [BankBottomPaperRealization.donorFactor, hmove,
      bankBottomDonor, bankBottomDonorMultiplier]
    omega
  · right
    simp only [hmove, bankBottomMarkerLower] at hlower
    have hnMarker : 2 * n < R.bottom.marker request * 5 :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < 5)).1 hlower
    simpa only [BankBottomPaperRealization.donorFactor, hmove,
      bankBottomDonor, bankBottomDonorMultiplier,
      Nat.mul_comm] using hnMarker
  · left
    simp [BankBottomPaperRealization.donorFactor,
      BankBottomPaperRealization.upperStateFactor,
      bankBottomDonor, bankBottomUpperState, hmove,
      bankBottomDonorMultiplier, bankBottomUpperStateMultiplier]
  · left
    simp [BankBottomPaperRealization.donorFactor,
      BankBottomPaperRealization.upperStateFactor,
      bankBottomDonor, bankBottomUpperState, hmove,
      bankBottomDonorMultiplier, bankBottomUpperStateMultiplier]

/-! ## Complete finite collision theorem -/

/-- The complete guarded central-anchor set is disjoint from every actual
ordinary or relevant-bottom bank occurrence.  The occurrence census includes
both endpoint states and donors, but excludes the diagnostic bare markers. -/
theorem guardedCentralAnchors_disjoint_allComponentOccurrences
    {c : ℝ} {depth n M : ℕ}
    (R : BankPaperRealization n M) (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hfixed : 2 * depth + 1 ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)) :
    Disjoint certificate.anchors R.allComponentOccurrences := by
  classical
  rw [Finset.disjoint_left]
  intro anchor hanchor hoccurrence
  have hanchorUpper : anchor ≤ 2 * n :=
    (Finset.mem_Ioc.mp (certificate.anchors_subset hanchor)).2
  have hanchorSplit : anchor ∈
      residualPromotedFactors n (centralAnchorCutoff depth n) ∪
        largeCentralAnchors n (centralAnchorCutoff depth n) certificate.q := by
    simpa only [certificate.anchors_eq, fullCentralAnchors] using hanchor
  rw [allComponentOccurrences, Finset.mem_union] at hoccurrence
  rcases hoccurrence with hordinary | hbottom
  · rw [ordinaryComponentOccurrences, Finset.mem_biUnion] at hordinary
    obtain ⟨request, _hrequest, hrequestOccurrence⟩ := hordinary
    rw [BankOrdinaryPaperRealization.componentOccurrences,
      Finset.mem_image] at hrequestOccurrence
    obtain ⟨kind, _hkind, hvalue⟩ := hrequestOccurrence
    have hspec := bankOrdinaryPaperRequest_component_spec request.1
    rcases Finset.mem_union.mp hanchorSplit with hresidual | hlarge
    · obtain ⟨p, hpResidual, hpromoted⟩ :=
        Finset.mem_image.mp hresidual
      have hpPrime := residualCentralPrimes_prime hpResidual
      cases kind with
      | sourceState =>
          apply marker_mul_nonpower_smooth_ne_promotedCentralFactor
            (R.ordinary.marker_prime request) hpPrime
            (by omega : 2 ≤ yNat n)
            (R.ordinary.yNat_lt_marker request)
            (R.ordinary.sourceCore_smooth request) hspec.2.1
          calc
            R.ordinary.marker request *
                bankOrdinaryPaperRequestSource request.1 = anchor := by
              simpa only [BankOrdinaryPaperRealization.occurrenceValue,
                BankOrdinaryPaperRealization.occurrenceCofactor] using hvalue
            _ = promotedCentralFactor n p := hpromoted.symm
      | targetState =>
          apply marker_mul_nonpower_smooth_ne_promotedCentralFactor
            (R.ordinary.marker_prime request) hpPrime
            (by omega : 2 ≤ yNat n)
            (R.ordinary.yNat_lt_marker request)
            (R.ordinary.targetCore_smooth request) hspec.2.2.1
          calc
            R.ordinary.marker request *
                bankOrdinaryPaperRequestTarget request.1 = anchor := by
              simpa only [BankOrdinaryPaperRealization.occurrenceValue,
                BankOrdinaryPaperRealization.occurrenceCofactor] using hvalue
            _ = promotedCentralFactor n p := hpromoted.symm
      | donor =>
          have hdonor := R.ordinary.two_mul_n_lt_donorValue request
          have hdonorEq : R.ordinary.donorValue request = anchor := by
            simpa only [BankOrdinaryPaperRealization.occurrenceValue_donor]
              using hvalue
          omega
    · obtain ⟨p, hpLarge, hlargeAnchor⟩ := Finset.mem_image.mp hlarge
      cases kind with
      | sourceState =>
          have hne :=
            R.guardedLargeCentralAnchor_ne_marker_mul_incidentCore
              certificate hfixed hyCutoff hpLarge
              (R.ordinary.marker_prime request)
              (R.ordinary.yNat_lt_marker request)
              (R.ordinary.sourceCore_smooth request)
              (R.ordinaryMarker_mem_allMarkers request)
              (Or.inl (R.anchorGuardLeftCore_ordinaryMarker request).symm)
          apply hne
          calc
            largeCentralAnchor certificate.q p = anchor := hlargeAnchor
            _ = R.ordinary.marker request *
                bankOrdinaryPaperRequestSource request.1 := by
              simpa only [BankOrdinaryPaperRealization.occurrenceValue,
                BankOrdinaryPaperRealization.occurrenceCofactor] using
                  hvalue.symm
      | targetState =>
          have hne :=
            R.guardedLargeCentralAnchor_ne_marker_mul_incidentCore
              certificate hfixed hyCutoff hpLarge
              (R.ordinary.marker_prime request)
              (R.ordinary.yNat_lt_marker request)
              (R.ordinary.targetCore_smooth request)
              (R.ordinaryMarker_mem_allMarkers request)
              (Or.inr (R.anchorGuardRightCore_ordinaryMarker request).symm)
          apply hne
          calc
            largeCentralAnchor certificate.q p = anchor := hlargeAnchor
            _ = R.ordinary.marker request *
                bankOrdinaryPaperRequestTarget request.1 := by
              simpa only [BankOrdinaryPaperRealization.occurrenceValue,
                BankOrdinaryPaperRealization.occurrenceCofactor] using
                  hvalue.symm
      | donor =>
          have hdonor := R.ordinary.two_mul_n_lt_donorValue request
          have hdonorEq : R.ordinary.donorValue request = anchor := by
            simpa only [BankOrdinaryPaperRealization.occurrenceValue_donor]
              using hvalue
          omega
  · rw [bottomComponentOccurrences,
      BankBottomPaperRealization.relevantComponentOccurrences,
      Finset.mem_biUnion] at hbottom
    obtain ⟨relevantRequest, _hrequest, hrequestOccurrence⟩ := hbottom
    let request :=
      bankBottomRelevantRequestToPaperRequest relevantRequest
    rw [R.bottom.componentOccurrences_eq_states_insert_donor request]
      at hrequestOccurrence
    simp only [Finset.mem_insert, Finset.mem_singleton]
      at hrequestOccurrence
    have hmarkerPrime := R.bottom.marker_prime request
    have hmarkerY := R.bottom.yNat_lt_marker
      R.ordinary.two_mul_n_le_M R.three_mul_yNat_le_n request
    have hmarkerCutoff :=
      R.centralAnchorCutoff_lt_bottomMarker hdepth request
    have hmarkerAll : R.bottom.marker request ∈ R.allMarkers := by
      simpa only [request] using R.bottomMarker_mem_allMarkers relevantRequest
    have hlowerSmooth :
        bankBottomLowerStateMultiplier (R.bottom.move request) ∈
          Nat.smoothNumbers (yNat n + 1) := by
      exact Nat.mem_smoothNumbers_of_lt
        (by cases R.bottom.move request <;>
            norm_num [bankBottomLowerStateMultiplier])
        (lt_of_le_of_lt
          (by cases R.bottom.move request <;>
              norm_num [bankBottomLowerStateMultiplier])
          (Nat.lt_succ_of_le R.six_le_yNat))
    have hupperSmooth :
        bankBottomUpperStateMultiplier (R.bottom.move request) ∈
          Nat.smoothNumbers (yNat n + 1) := by
      exact Nat.mem_smoothNumbers_of_lt
        (by cases R.bottom.move request <;>
            norm_num [bankBottomUpperStateMultiplier])
        (lt_of_le_of_lt
          (by cases R.bottom.move request <;>
              norm_num [bankBottomUpperStateMultiplier])
          (Nat.lt_succ_of_le R.six_le_yNat))
    rcases Finset.mem_union.mp hanchorSplit with hresidual | hlarge
    · obtain ⟨p, hpResidual, hpromoted⟩ :=
        Finset.mem_image.mp hresidual
      have hpPrime := residualCentralPrimes_prime hpResidual
      have hpSmall := residualCentralPrimes_le hpResidual
      have hlowerNe : anchor ≠ R.bottom.lowerStateFactor request := by
        intro heq
        apply marker_mul_ne_promotedCentralFactor hmarkerPrime hpPrime
          (two_le_centralAnchorCutoff hnCutoff) hmarkerCutoff hpSmall
        calc
          R.bottom.marker request *
              bankBottomLowerStateMultiplier (R.bottom.move request) =
              R.bottom.lowerStateFactor request := by
                simp [BankBottomPaperRealization.lowerStateFactor,
                  bankBottomLowerState, Nat.mul_comm]
          _ = anchor := heq.symm
          _ = promotedCentralFactor n p := hpromoted.symm
      have hupperNe : anchor ≠ R.bottom.upperStateFactor request := by
        intro heq
        apply marker_mul_ne_promotedCentralFactor hmarkerPrime hpPrime
          (two_le_centralAnchorCutoff hnCutoff) hmarkerCutoff hpSmall
        calc
          R.bottom.marker request *
              bankBottomUpperStateMultiplier (R.bottom.move request) =
              R.bottom.upperStateFactor request := by
                simp [BankBottomPaperRealization.upperStateFactor,
                  bankBottomUpperState, Nat.mul_comm]
          _ = anchor := heq.symm
          _ = promotedCentralFactor n p := hpromoted.symm
      rcases hrequestOccurrence with hlower | hupper | hdonor
      · exact hlowerNe hlower
      · exact hupperNe hupper
      · rcases R.bottomDonor_eq_upperState_or_two_mul_n_lt request with
          hterminal | hdonorLarge
        · exact hupperNe (hdonor.trans hterminal)
        · omega
    · obtain ⟨p, hpLarge, hlargeAnchor⟩ := Finset.mem_image.mp hlarge
      have hlowerNe : anchor ≠ R.bottom.lowerStateFactor request := by
        have hne :=
          R.guardedLargeCentralAnchor_ne_marker_mul_incidentCore
            certificate hfixed hyCutoff hpLarge hmarkerPrime hmarkerY
            hlowerSmooth hmarkerAll
            (Or.inl (by
              simpa only [request] using
                (R.anchorGuardLeftCore_bottomMarker relevantRequest).symm))
        intro heq
        apply hne
        calc
          largeCentralAnchor certificate.q p = anchor := hlargeAnchor
          _ = R.bottom.lowerStateFactor request := heq
          _ = R.bottom.marker request *
              bankBottomLowerStateMultiplier (R.bottom.move request) := by
                simp [BankBottomPaperRealization.lowerStateFactor,
                  bankBottomLowerState, Nat.mul_comm]
      have hupperNe : anchor ≠ R.bottom.upperStateFactor request := by
        have hne :=
          R.guardedLargeCentralAnchor_ne_marker_mul_incidentCore
            certificate hfixed hyCutoff hpLarge hmarkerPrime hmarkerY
            hupperSmooth hmarkerAll
            (Or.inr (by
              simpa only [request] using
                (R.anchorGuardRightCore_bottomMarker relevantRequest).symm))
        intro heq
        apply hne
        calc
          largeCentralAnchor certificate.q p = anchor := hlargeAnchor
          _ = R.bottom.upperStateFactor request := heq
          _ = R.bottom.marker request *
              bankBottomUpperStateMultiplier (R.bottom.move request) := by
                simp [BankBottomPaperRealization.upperStateFactor,
                  bankBottomUpperState, Nat.mul_comm]
      rcases hrequestOccurrence with hlower | hupper | hdonor
      · exact hlowerNe hlower
      · exact hupperNe hupper
      · rcases R.bottomDonor_eq_upperState_or_two_mul_n_lt request with
          hterminal | hdonorLarge
        · exact hupperNe (hdonor.trans hterminal)
        · omega

/-- Eventual terminal at every fixed anchor depth.  All quantifiers over the
paper endpoint, the realized bank, and the guarded certificate remain inside
the eventual statement. -/
theorem eventually_guardedCentralAnchors_disjoint_allComponentOccurrences
    (c : ℝ) (depth : ℕ) (hdepth : 2 ≤ depth) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (M : ℕ) (R : BankPaperRealization n M)
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth)),
        Disjoint certificate.anchors R.allComponentOccurrences := by
  filter_upwards [eventually_ge_atTop (centralAnchorCutoffThreshold depth),
      eventually_bankAnchor_fixed_le_yNat (2 * depth + 1),
      eventually_yNat_lt_centralAnchorCutoff depth]
      with n hnCutoff hfixed hyCutoff
  intro M R certificate
  exact R.guardedCentralAnchors_disjoint_allComponentOccurrences
    hdepth hnCutoff hfixed hyCutoff certificate

end BankPaperRealization

end

end Erdos390.WholePaper
