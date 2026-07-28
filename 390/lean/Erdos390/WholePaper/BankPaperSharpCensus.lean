import Erdos390.WholePaper.TangentPaperNumericalGuards

/-!
# Sharp census for the actual paper bank

The earlier all-marker budget bounded one ordinary core path by its starting
prime and consequently gave `O(yNat²)`.  The constructed path is much
shorter.  Its sources are routed through the literal geometric grid
`Q_j=4(4/3)^j`; every grid fiber has bounded congestion, and only
logarithmically many indices occur below `yNat`.

This file counts the actual sigma-type request family.  It first records the
exact weighted path ledger

`|ordinary requests| = 2 ∑_{p≤y} β_p |coreSources(p)|`,

then bounds every path by an explicit logarithmic grid budget.  Combining
this finite count with the already proved `O(yNat)` beta demand gives the
paper-sized `O(yNat * L)` marker budget.  The only prime-counting input is
the existing audited theorem `bankBottomPaperDemand_isBigO_yNat`, whose
proof uses the safe PNT; no new counting hypothesis is introduced here.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Exact ordinary request ledger -/

/-- The unsigned weighted number of nonterminal ordinary path edges.  The
factor two for the two orientations is deliberately kept outside. -/
def bankOrdinaryWeightedPathDemand (n : ℕ) : ℕ :=
  ∑ p ∈ bankRoundingPrimeSupport n,
    bankRoundingBeta n p * (bankOrdinaryCoreSources p).card

/-- The actual dependent request type has exactly two signed copies of the
weighted path ledger. -/
theorem card_bankOrdinaryPaperRequests_eq_weightedPathDemand (n : ℕ) :
    (bankOrdinaryPaperRequests n).card =
      2 * bankOrdinaryWeightedPathDemand n := by
  rw [bankOrdinaryPaperRequests, Finset.card_univ,
    Fintype.card_sigma, bankOrdinaryWeightedPathDemand]
  simp only [Fintype.card_coe]
  change
    (∑ slot : SignedBankSlot (bankRoundingBetaOnSupport n),
      (bankOrdinaryCoreSources slot.1.1).card) =
        2 * ∑ p ∈ bankRoundingPrimeSupport n,
          bankRoundingBeta n p * (bankOrdinaryCoreSources p).card
  simp only [Fintype.sum_sigma, Fintype.card_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id, bankRoundingBetaOnSupport]
  have hattach :
      (∑ p : ↑(bankRoundingPrimeSupport n),
        bankRoundingBeta n p.1 *
          (bankOrdinaryCoreSources p.1).card) =
        ∑ p ∈ bankRoundingPrimeSupport n,
          bankRoundingBeta n p *
            (bankOrdinaryCoreSources p).card := by
    simpa only using
      (Finset.sum_attach (bankRoundingPrimeSupport n)
        (fun p ↦ bankRoundingBeta n p *
          (bankOrdinaryCoreSources p).card))
  rw [← hattach, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  ring_nf

/-! ## A literal logarithmic path budget -/

/-- Monotonicity of the least geometric-grid index, in the range in which
the grid-cell certificate has its strict lower endpoint. -/
theorem bankOrdinaryScaleIndex_mono_of_five_le
    {a b : ℕ} (ha : 5 ≤ a) (hab : a ≤ b) :
    bankOrdinaryScaleIndex a ≤ bankOrdinaryScaleIndex b := by
  have hb : 5 ≤ b := ha.trans hab
  have haCell := bankOrdinaryScaleIndex_cell ha
  have hbCell := bankOrdinaryScaleIndex_cell hb
  by_contra hindex
  have hsucc : bankOrdinaryScaleIndex b + 1 ≤
      bankOrdinaryScaleIndex a := by omega
  have hscaleMono := bankOrdinaryScale_mono hsucc
  have hbUpper : (b : ℚ) ≤
      bankOrdinaryScale (bankOrdinaryScaleIndex b + 1) := by
    have hupper := hbCell.2
    rw [← bankOrdinaryScale_succ] at hupper
    exact hupper
  have habQ : (a : ℚ) ≤ b := by exact_mod_cast hab
  have haUpper : (a : ℚ) ≤
      bankOrdinaryScale (bankOrdinaryScaleIndex a) :=
    habQ.trans (hbUpper.trans hscaleMono)
  exact (not_lt_of_ge haUpper) haCell.1

/-- The sharp literal path budget supplied by the constructed grid census.
The complete small-table segment has at most `17` sources in total.  Above
it, precisely the possible indices `6,...,scaleIndex(yNat)` remain, with at
most two sources at each index. -/
def bankOrdinaryPathComponentBudget (n : ℕ) : ℕ :=
  17 + 2 * (bankOrdinaryScaleIndex (yNat n) - 5)

theorem one_le_bankOrdinaryComponentScaleIndex_of_mem
    {n p s : ℕ} (hp : p ∈ bankRoundingPrimeSupport n)
    (hs : s ∈ bankOrdinaryCoreSources p) :
    1 ≤ bankOrdinaryComponentScaleIndex s := by
  by_cases hpSmall : p ≤ 5
  · rw [bankOrdinaryCoreSources_of_le_five hpSmall] at hs
    simp at hs
  · have hpPrime := bankRoundingPrimeSupport_prime hp
    have hpPower : ¬ IsPowerOfTwo p :=
      prime_not_isPowerOfTwo_of_five_le hpPrime (by omega)
    have hspec := bankOrdinaryCoreSource_spec
      (show 5 ≤ p by omega) hpPower hs
    exact one_le_bankOrdinaryComponentScaleIndex hspec.1

/-- A source routed above the small table has grid index no larger than the
index of `yNat`.  This is where monotonicity of the *actual* constructed
path, rather than the coarse bound by its starting prime, enters. -/
theorem bankOrdinaryComponentScaleIndex_le_yNatScaleIndex_of_six_le
    {n p s : ℕ} (hp : p ∈ bankRoundingPrimeSupport n)
    (hs : s ∈ bankOrdinaryCoreSources p)
    (hscale : 6 ≤ bankOrdinaryComponentScaleIndex s) :
    bankOrdinaryComponentScaleIndex s ≤
      bankOrdinaryScaleIndex (yNat n) := by
  have hpPrime := bankRoundingPrimeSupport_prime hp
  have hpFive : 5 ≤ p := by
    by_contra hpSmall
    have hpLe : p ≤ 5 := by omega
    rw [bankOrdinaryCoreSources_of_le_five hpLe] at hs
    simp at hs
  have hpPower : ¬ IsPowerOfTwo p :=
    prime_not_isPowerOfTwo_of_five_le hpPrime hpFive
  have hspec := bankOrdinaryCoreSource_spec hpFive hpPower hs
  have hsSix : 6 ≤ s := hspec.1
  have hsLarge : ¬ s ≤ 22 := by
    intro hsSmall
    rw [bankOrdinaryComponentScaleIndex, if_pos hsSmall] at hscale
    have hsmall := smallDescentScaleIndex_le_five
      (smallDescentScaleForSource s)
    omega
  have hsStart := bankOrdinaryCoreSource_le_start hs
  have hpY := bankRoundingPrimeSupport_le_yNat hp
  have hsY : s ≤ yNat n := hsStart.trans hpY
  rw [bankOrdinaryComponentScaleIndex, if_neg hsLarge]
  exact bankOrdinaryScaleIndex_mono_of_five_le
    (show 5 ≤ s by omega) hsY

/-- Every actual source is either in the one finite small-table block, or
in one of the explicitly enumerated large grid fibers.  This is the finite
injection/counting reduction behind the sharp census. -/
theorem bankOrdinaryCoreSources_subset_smallLargePathFibers
    {n p : ℕ} (hp : p ∈ bankRoundingPrimeSupport n) :
    bankOrdinaryCoreSources p ⊆
      (bankOrdinaryCoreSources p).filter
          (fun s ↦ bankOrdinaryComponentScaleIndex s ≤ 5) ∪
        (Finset.Icc 6 (bankOrdinaryScaleIndex (yNat n))).biUnion
          (bankOrdinaryCoreSourcesAtScale p) := by
  intro s hs
  apply Finset.mem_union.mpr
  by_cases hscale : bankOrdinaryComponentScaleIndex s ≤ 5
  · exact Or.inl (Finset.mem_filter.mpr ⟨hs, hscale⟩)
  · apply Or.inr
    apply Finset.mem_biUnion.mpr
    refine ⟨bankOrdinaryComponentScaleIndex s, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨by omega,
        bankOrdinaryComponentScaleIndex_le_yNatScaleIndex_of_six_le
          hp hs (by omega)⟩
    · exact Finset.mem_filter.mpr ⟨hs, rfl⟩

/-- The actual deterministic path of every supported prime has at most the
literal logarithmic budget above. -/
theorem bankOrdinaryCoreSources_card_le_pathComponentBudget
    {n p : ℕ} (hp : p ∈ bankRoundingPrimeSupport n) :
    (bankOrdinaryCoreSources p).card ≤
      bankOrdinaryPathComponentBudget n := by
  by_cases hpSmall : p ≤ 5
  · rw [bankOrdinaryCoreSources_of_le_five hpSmall]
    simp [bankOrdinaryPathComponentBudget]
  · have hpPrime := bankRoundingPrimeSupport_prime hp
    have hpFive : 5 ≤ p := by omega
    have hpPower : ¬ IsPowerOfTwo p :=
      prime_not_isPowerOfTwo_of_five_le hpPrime hpFive
    let smallSources := (bankOrdinaryCoreSources p).filter
      (fun s ↦ bankOrdinaryComponentScaleIndex s ≤ 5)
    let largeIndices :=
      Finset.Icc 6 (bankOrdinaryScaleIndex (yNat n))
    let largeSources := largeIndices.biUnion
      (bankOrdinaryCoreSourcesAtScale p)
    have hcover := bankOrdinaryCoreSources_subset_smallLargePathFibers hp
    change bankOrdinaryCoreSources p ⊆
      smallSources ∪ largeSources at hcover
    have hsmallSubset : smallSources ⊆ Finset.Icc 6 22 := by
      intro s hs
      have hsData := Finset.mem_filter.mp hs
      have hspec := bankOrdinaryCoreSource_spec hpFive hpPower hsData.1
      exact Finset.mem_Icc.mpr ⟨hspec.1,
        bankOrdinaryComponentSource_le_twentyTwo_of_scaleIndex_le_five
          hspec.1 hsData.2⟩
    have hsmallCard : smallSources.card ≤ 17 := by
      exact (Finset.card_le_card hsmallSubset).trans (by norm_num)
    have hlargeFiber : ∀ j ∈ largeIndices,
        (bankOrdinaryCoreSourcesAtScale p j).card ≤ 2 := by
      intro j hj
      exact bankOrdinaryCoreSourcesAtLargeScale_card_le_two
        hpFive hpPower (Finset.mem_Icc.mp hj).1
    have hlargeIndexCard : largeIndices.card =
        bankOrdinaryScaleIndex (yNat n) - 5 := by
      dsimp only [largeIndices]
      rw [Nat.card_Icc]
      omega
    have hlargeCard : largeSources.card ≤
        2 * (bankOrdinaryScaleIndex (yNat n) - 5) := by
      calc
        largeSources.card ≤ ∑ j ∈ largeIndices,
            (bankOrdinaryCoreSourcesAtScale p j).card := by
          dsimp only [largeSources]
          exact Finset.card_biUnion_le
        _ ≤ ∑ _j ∈ largeIndices, 2 := by
          exact Finset.sum_le_sum hlargeFiber
        _ = 2 * (bankOrdinaryScaleIndex (yNat n) - 5) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id,
            hlargeIndexCard]
          ring_nf
    calc
      (bankOrdinaryCoreSources p).card ≤
          (smallSources ∪ largeSources).card := by
        exact Finset.card_le_card hcover
      _ ≤ smallSources.card + largeSources.card :=
        Finset.card_union_le _ _
      _ ≤ 17 + 2 * (bankOrdinaryScaleIndex (yNat n) - 5) :=
        Nat.add_le_add hsmallCard hlargeCard
      _ = bankOrdinaryPathComponentBudget n := rfl

theorem bankOrdinaryWeightedPathDemand_le
    (n : ℕ) :
    bankOrdinaryWeightedPathDemand n ≤
      bankBottomPaperDemand n * bankOrdinaryPathComponentBudget n := by
  rw [bankOrdinaryWeightedPathDemand, bankBottomPaperDemand]
  calc
    (∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p * (bankOrdinaryCoreSources p).card) ≤
      ∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p * bankOrdinaryPathComponentBudget n := by
          apply Finset.sum_le_sum
          intro p hp
          exact Nat.mul_le_mul_left _
            (bankOrdinaryCoreSources_card_le_pathComponentBudget hp)
    _ = (∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p) * bankOrdinaryPathComponentBudget n := by
          rw [Finset.sum_mul]

theorem card_bankOrdinaryPaperRequests_le_sharp
    (n : ℕ) :
    (bankOrdinaryPaperRequests n).card ≤
      2 * bankBottomPaperDemand n *
        bankOrdinaryPathComponentBudget n := by
  rw [card_bankOrdinaryPaperRequests_eq_weightedPathDemand]
  have hweighted := bankOrdinaryWeightedPathDemand_le n
  calc
    2 * bankOrdinaryWeightedPathDemand n ≤
        2 * (bankBottomPaperDemand n *
          bankOrdinaryPathComponentBudget n) :=
      Nat.mul_le_mul_left 2 hweighted
    _ = 2 * bankBottomPaperDemand n *
        bankOrdinaryPathComponentBudget n := by ring

/-! ## The full actual marker/component census -/

/-- Literal sharp realization-independent budget for all ordinary and
bottom marker components. -/
def bankPaperSharpMarkerBudget (n : ℕ) : ℕ :=
  bankBottomPaperDemand n *
    (2 * bankOrdinaryPathComponentBudget n + 8)

theorem card_bankPaperMarkerRequest_eq_weightedPathLedger
    (n : ℕ) :
    Fintype.card (BankPaperMarkerRequest n) =
      (bankBottomRelevantPaperRequests n).card +
        2 * bankOrdinaryWeightedPathDemand n := by
  rw [BankPaperRealization.card_bankPaperMarkerRequest,
    card_bankOrdinaryPaperRequests_eq_weightedPathDemand]

theorem card_bankPaperMarkerRequest_le_sharpMarkerBudget
    (n : ℕ) :
    Fintype.card (BankPaperMarkerRequest n) ≤
      bankPaperSharpMarkerBudget n := by
  have hbottom : (bankBottomRelevantPaperRequests n).card ≤
      8 * bankBottomPaperDemand n := by
    calc
      (bankBottomRelevantPaperRequests n).card ≤
          (bankBottomPaperRequests n).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 8 * bankBottomPaperDemand n :=
        card_bankBottomPaperRequests n
  have hordinary := card_bankOrdinaryPaperRequests_le_sharp n
  rw [BankPaperRealization.card_bankPaperMarkerRequest,
    bankPaperSharpMarkerBudget]
  calc
    (bankBottomRelevantPaperRequests n).card +
          (bankOrdinaryPaperRequests n).card ≤
        8 * bankBottomPaperDemand n +
          2 * bankBottomPaperDemand n *
            bankOrdinaryPathComponentBudget n :=
      Nat.add_le_add hbottom hordinary
    _ = bankBottomPaperDemand n *
        (2 * bankOrdinaryPathComponentBudget n + 8) := by ring

namespace BankPaperRealization

theorem prechargeComponentCount_le_sharpMarkerBudget
    {n M : ℕ} (_R : BankPaperRealization n M) :
    Fintype.card (BankPaperMarkerRequest n) ≤
      bankPaperSharpMarkerBudget n :=
  card_bankPaperMarkerRequest_le_sharpMarkerBudget n

theorem tangentPaperBankRows_card_le_sharpMarkerBudget
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.tangentPaperBankRows.card ≤ bankPaperSharpMarkerBudget n := by
  rw [R.tangentPaperBankRows_card_eq_componentCount]
  exact R.prechargeComponentCount_le_sharpMarkerBudget

end BankPaperRealization

/-! ## The paper-sized `O(yL)` asymptotic -/

/-- The moving geometric-grid index below `yNat` is logarithmic. -/
theorem bankOrdinaryScaleIndex_yNat_le_log
    {n : ℕ} (hy : 6 ≤ yNat n) (hgeometry : 3 * yNat n ≤ n) :
    (bankOrdinaryScaleIndex (yNat n) : ℝ) ≤
      L n / Real.log (4 / 3 : ℝ) := by
  let j := bankOrdinaryScaleIndex (yNat n)
  have hcell := bankOrdinaryScaleIndex_cell
    (show 5 ≤ yNat n by omega)
  have hscaleQ : bankOrdinaryScale j < (yNat n : ℚ) := by
    simpa only [j] using hcell.1
  have hscaleR : (bankOrdinaryScale j : ℝ) < (yNat n : ℝ) := by
    exact_mod_cast hscaleQ
  have hscaleExpanded :
      (4 : ℝ) * (4 / 3 : ℝ) ^ j < (yNat n : ℝ) := by
    simpa only [bankOrdinaryScale, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_ofNat, Rat.cast_div] using hscaleR
  have hpowPos : 0 < (4 / 3 : ℝ) ^ j := by positivity
  have hpowLt : (4 / 3 : ℝ) ^ j < (yNat n : ℝ) := by
    have hpowLe : (4 / 3 : ℝ) ^ j ≤
        4 * (4 / 3 : ℝ) ^ j := by nlinarith
    exact hpowLe.trans_lt hscaleExpanded
  have hlogPow := Real.log_lt_log hpowPos hpowLt
  rw [Real.log_pow] at hlogPow
  have hbaseLog : 0 < Real.log (4 / 3 : ℝ) :=
    Real.log_pos (by norm_num)
  have hyLe : yNat n ≤ n := by omega
  have hyPos : (0 : ℝ) < yNat n := by positivity
  have hlogY : Real.log (yNat n : ℝ) ≤ L n := by
    rw [L]
    exact Real.log_le_log hyPos (by exact_mod_cast hyLe)
  apply (le_div_iff₀ hbaseLog).2
  have hcast : (j : ℝ) =
      (bankOrdinaryScaleIndex (yNat n) : ℝ) := rfl
  rw [← hcast]
  exact hlogPow.le.trans hlogY

theorem bankOrdinaryPathComponentBudget_isBigO_L :
    (fun n : ℕ ↦ (bankOrdinaryPathComponentBudget n : ℝ))
      =O[atTop] L := by
  let C : ℝ := 2 * (1 / Real.log (4 / 3 : ℝ)) + 17
  apply IsBigO.of_bound C
  filter_upwards [eventually_bankBottom_six_le_yNat,
      eventually_bankBottom_three_mul_yNat_le_self,
      eventually_ge_atTop 3] with n hy hgeometry hn
  have hindex := bankOrdinaryScaleIndex_yNat_le_log hy hgeometry
  have hL : 1 ≤ L n := by
    rw [L]
    have hnR : (Real.exp 1 : ℝ) ≤ n :=
      Real.exp_one_lt_three.le.trans (by exact_mod_cast hn)
    exact (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < n)).2 hnR
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ bankOrdinaryPathComponentBudget n),
    Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hL)]
  have hindex' : (bankOrdinaryScaleIndex (yNat n) : ℝ) ≤
      (1 / Real.log (4 / 3 : ℝ)) * L n := by
    simpa only [one_div, inv_mul_eq_div] using hindex
  dsimp only [C]
  calc
    (bankOrdinaryPathComponentBudget n : ℝ) =
        17 + 2 *
          ((bankOrdinaryScaleIndex (yNat n) - 5 : ℕ) : ℝ) := by
      simp only [bankOrdinaryPathComponentBudget, Nat.cast_add,
        Nat.cast_mul, Nat.cast_ofNat]
    _ ≤ 17 + 2 *
        (bankOrdinaryScaleIndex (yNat n) : ℝ) := by
      gcongr
      exact_mod_cast
        (Nat.sub_le (bankOrdinaryScaleIndex (yNat n)) 5)
    _ ≤ 17 + 2 *
        ((1 / Real.log (4 / 3 : ℝ)) * L n) := by
      gcongr
    _ ≤ 17 * L n + 2 *
        ((1 / Real.log (4 / 3 : ℝ)) * L n) := by
      nlinarith
    _ = (2 * (1 / Real.log (4 / 3 : ℝ)) + 17) * L n := by
      ring

/-- The sharp actual marker budget has size `O(yNat * L)` as soon as the
one-sided beta demand is `O(yNat)`.  All finite path and component counting
has already been discharged before this analytic input is introduced. -/
theorem bankPaperSharpMarkerBudget_isBigO_yNat_mul_L_of_demand
    (hDemand :
      (fun n : ℕ ↦ (bankBottomPaperDemand n : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (yNat n : ℝ))) :
    (fun n : ℕ ↦ (bankPaperSharpMarkerBudget n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (yNat n : ℝ) * L n) := by
  have htwoPath :=
    bankOrdinaryPathComponentBudget_isBigO_L.const_mul_left (2 : ℝ)
  have height : (fun _n : ℕ ↦ (8 : ℝ)) =O[atTop] L := by
    apply IsBigO.of_bound 8
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hL : 1 ≤ L n := by
      rw [L]
      have hnR : (Real.exp 1 : ℝ) ≤ n :=
        Real.exp_one_lt_three.le.trans (by exact_mod_cast hn)
      exact (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < n)).2 hnR
    rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8),
      Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hL)]
    nlinarith
  have hfactorModel := htwoPath.add height
  have hfactor :
      (fun n : ℕ ↦
        ((2 * bankOrdinaryPathComponentBudget n + 8 : ℕ) : ℝ))
          =O[atTop] L := by
    apply hfactorModel.congr'
    · exact Eventually.of_forall fun n ↦ by
        push_cast
        rfl
    · exact Eventually.of_forall fun _n ↦ rfl
  have hproduct := hDemand.mul hfactor
  apply hproduct.congr'
  · exact Eventually.of_forall fun n ↦ by
      simp only [bankPaperSharpMarkerBudget, Nat.cast_mul,
        Nat.cast_add, Nat.cast_ofNat]
  · exact Eventually.of_forall fun _n ↦ rfl

/-- The unconditional paper-sized census.  Its sole prime-counting input is
the existing safe-PNT consequence `bankBottomPaperDemand_isBigO_yNat`. -/
theorem bankPaperSharpMarkerBudget_isBigO_yNat_mul_L :
    (fun n : ℕ ↦ (bankPaperSharpMarkerBudget n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (yNat n : ℝ) * L n) :=
  bankPaperSharpMarkerBudget_isBigO_yNat_mul_L_of_demand
    bankBottomPaperDemand_isBigO_yNat

/-! ## Sharp numerical-guard corollaries -/

namespace BankPaperRealization

theorem tangentPaperNumericalGuardSet_card_le_sharpMarkerBudget
    {c : ℝ} {depth n M : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n) :
    (R.tangentPaperNumericalGuardSet certificate fixedExceptional).card ≤
      (residualCentralPrimes n
          (centralAnchorCutoff depth n)).card +
        (largeCentralPrimes n
          (centralAnchorCutoff depth n)).card +
        fixedExceptional.card + 3 * bankPaperSharpMarkerBudget n := by
  have hglobal := R.tangentPaperNumericalGuardSet_card_le
    certificate fixedExceptional hnCutoff
  have hsharp := R.prechargeComponentCount_le_sharpMarkerBudget
  omega

theorem tangentPaperPairNumericalGuards_card_le_sharpMarkerBudget
    {c : ℝ} {depth n M W K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (R.tangentPaperPairNumericalGuards certificate fixedExceptional
      K h u v).card ≤ 2 + 2 * bankPaperSharpMarkerBudget n := by
  have hpair := R.tangentPaperPairNumericalGuards_card_le_componentCount
    (W := W) (K := K) (h := h) (u := u) (v := v)
      certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
        hyCutoff huPrime hvPrime
  have hsharp := R.prechargeComponentCount_le_sharpMarkerBudget
  omega

theorem card_tangentEndpointGuardDeletedMultipliers_numericalGuardSet_le_sharp
    {c : ℝ} {depth n M W K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (tangentEndpointGuardDeletedMultipliers u v
      (R.tangentPaperNumericalGuardSet certificate fixedExceptional)
      (tangentCommonMultiplierInterval n K h u v)).card ≤
        4 + 4 * bankPaperSharpMarkerBudget n := by
  have hguard :=
    R.card_tangentEndpointGuardDeletedMultipliers_numericalGuardSet_le
      (W := W) (K := K) (h := h) (u := u) (v := v)
        certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
          hyCutoff huPrime hvPrime
  have hsharp := R.prechargeComponentCount_le_sharpMarkerBudget
  omega

/-- The deterministic common-list ledger with the paper-sized sharp bank
budget substituted.  The head-residue and exceptional-row cardinalities
remain the only analytic list estimates. -/
theorem tangentPaperCommonMultiplier_sharp_finite_deletion_ledger
    {c : ℝ} {depth n M W K h Phead X0 u v : ℕ}
    {left right : ℕ → ℕ} {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (tangentCommonMultiplierInterval n K h u v).card ≤
      (tangentCleanCommonMultiplierList n K h Phead X0 (yNat n) u v
        R.tangentPaperDedicatedRows
        (R.tangentPaperNumericalGuardSet certificate fixedExceptional)).card +
      (tangentHeadBadMultipliers Phead
        (tangentCommonMultiplierInterval n K h u v)).card +
      (tangentExceptionalMultipliers n X0 (yNat n)
        (tangentCommonMultiplierInterval n K h u v)).card +
      4 + 4 * bankPaperSharpMarkerBudget n := by
  let interval := tangentCommonMultiplierInterval n K h u v
  let numericalGuards :=
    R.tangentPaperNumericalGuardSet certificate fixedExceptional
  let dedicatedRows := R.tangentPaperDedicatedRows
  let bad := tangentCommonMultiplierBadSet
    n K h Phead X0 (yNat n) u v dedicatedRows numericalGuards
  let clean := tangentCleanCommonMultiplierList
    n K h Phead X0 (yNat n) u v dedicatedRows numericalGuards
  have hpartition : clean.card + bad.card = interval.card := by
    dsimp only [clean, bad, interval]
    rw [tangentCleanCommonMultiplierList_eq_sdiff_badSet]
    exact Finset.card_sdiff_add_card_eq_card
      (tangentCommonMultiplierBadSet_subset_interval
        n K h Phead X0 (yNat n) u v dedicatedRows numericalGuards)
  have hbad := card_tangentCommonMultiplierBadSet_le
    n K h Phead X0 (yNat n) u v dedicatedRows numericalGuards
  have hdedicated :
      (tangentDedicatedRowMultipliers (yNat n) dedicatedRows
        interval).card = 0 := by
    dsimp only [dedicatedRows, interval]
    simp
  have hguard :=
    R.card_tangentEndpointGuardDeletedMultipliers_numericalGuardSet_le_sharp
      (W := W) (K := K) (h := h) (u := u) (v := v)
        certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
          hyCutoff huPrime hvPrime
  dsimp only [interval, numericalGuards, dedicatedRows, bad, clean] at hpartition hbad hdedicated hguard ⊢
  omega

end BankPaperRealization

end

end Erdos390.WholePaper
