import Erdos390.WholePaper.BankOrdinaryDonorRelation
import Erdos390.WholePaper.BankPathAlgebra

/-!
# Actual terminating ordinary-bank core paths

This file turns the large-core rule and the certified fifteen-row small table
into one deterministic finite path.  Sources `6,...,22` use the displayed
table, sources above `22` use `largeCoreStep`, and `5` is absorbing.  The
resulting finite source set is the literal set of ordinary component requests
made by one path.

The rational geometric grid is indexed here as well.  Minimality of the index
puts every source in its unique grid cell.  The finite small part contributes
at most seventeen sources at any scale, while the two-step contraction gives
the sharp bound two at every grid scale above the small table.
-/

namespace Erdos390.WholePaper

open scoped BigOperators

noncomputable section

/-! ## One deterministic descent step -/

/-- The target in the displayed small table, with an irrelevant predecessor
fallback away from the certified non-power sources. -/
def bankSmallCoreStep : ℕ → ℕ
  | 6 => 5
  | 7 => 6
  | 9 => 7
  | 10 => 9
  | 11 => 9
  | 12 => 10
  | 13 => 11
  | 14 => 12
  | 15 => 12
  | 17 => 14
  | 18 => 15
  | 19 => 15
  | 20 => 15
  | 21 => 17
  | 22 => 18
  | q => q - 1

/-- The actual ordinary-core transition.  The terminal core `5` is absorbing,
the literal small table is used through `22`, and all larger sources use the
large-core rule. -/
def bankOrdinaryCoreStep (q : ℕ) : ℕ :=
  if q ≤ 5 then 5
  else if q ≤ 22 then bankSmallCoreStep q
  else largeCoreStep q

@[simp] theorem bankOrdinaryCoreStep_five :
    bankOrdinaryCoreStep 5 = 5 := by
  simp [bankOrdinaryCoreStep]

theorem bankOrdinaryCoreStep_eq_largeCoreStep
    {q : ℕ} (hq : 22 < q) :
    bankOrdinaryCoreStep q = largeCoreStep q := by
  rw [bankOrdinaryCoreStep, if_neg (by omega), if_neg (by omega)]

theorem bankSmallCoreStep_mem_table
    {q : ℕ} (hq6 : 6 ≤ q) (hq22 : q ≤ 22)
    (hqPower : ¬ IsPowerOfTwo q) :
    (q, bankSmallCoreStep q) ∈ smallDescentTable := by
  have hq8 : q ≠ 8 := by
    rintro rfl
    exact hqPower (by decide)
  have hq16 : q ≠ 16 := by
    rintro rfl
    exact hqPower (by decide)
  interval_cases q <;> first | contradiction | decide

theorem bankSmallCoreStep_certified
    {q : ℕ} (hq6 : 6 ≤ q) (hq22 : q ≤ 22)
    (hqPower : ¬ IsPowerOfTwo q) :
    IsCertifiedSmallDescentEntry (smallDescentScaleForSource q)
      q (bankSmallCoreStep q) := by
  have hq8 : q ≠ 8 := by
    rintro rfl
    exact hqPower (by decide)
  have hq16 : q ≠ 16 := by
    rintro rfl
    exact hqPower (by decide)
  interval_cases q <;> first | contradiction | decide

theorem bankOrdinaryCoreStep_ge_five
    {q : ℕ} (hq : 5 ≤ q) :
    5 ≤ bankOrdinaryCoreStep q := by
  by_cases hq5 : q ≤ 5
  · have : q = 5 := by omega
    subst q
    simp
  · by_cases hq22 : q ≤ 22
    · interval_cases q <;> simp_all [bankOrdinaryCoreStep, bankSmallCoreStep]
    · rw [bankOrdinaryCoreStep_eq_largeCoreStep (by omega)]
      exact largeCoreStep_ge_five (by omega)

theorem bankOrdinaryCoreStep_lt_self
    {q : ℕ} (hq : 5 < q) :
    bankOrdinaryCoreStep q < q := by
  by_cases hq22 : q ≤ 22
  · interval_cases q <;> simp_all [bankOrdinaryCoreStep, bankSmallCoreStep]
  · rw [bankOrdinaryCoreStep_eq_largeCoreStep (by omega)]
    exact largeCoreStep_lt_self (by omega)

/-! ## Exact indexing of the rational geometric grid -/

theorem bankOrdinaryScale_nat_add_four_le (j : ℕ) :
    (j : ℚ) + 4 ≤ bankOrdinaryScale j := by
  induction j with
  | zero => norm_num [bankOrdinaryScale]
  | succ j ih =>
      rw [bankOrdinaryScale_succ]
      have hscale : (4 : ℚ) ≤ bankOrdinaryScale j := by
        linarith
      push_cast
      linarith

private theorem bankOrdinaryScaleIndex_exists (q : ℕ) :
    ∃ j : ℕ, (q : ℚ) ≤ 4 * bankOrdinaryScale j / 3 := by
  refine ⟨q, ?_⟩
  have hlarge := bankOrdinaryScale_nat_add_four_le q
  have hpos := bankOrdinaryScale_pos q
  push_cast at hlarge
  linarith

/-- The least grid index whose upper cell endpoint contains `q`. -/
def bankOrdinaryScaleIndex (q : ℕ) : ℕ :=
  Nat.find (bankOrdinaryScaleIndex_exists q)

theorem bankOrdinaryScaleIndex_upper (q : ℕ) :
    (q : ℚ) ≤ 4 * bankOrdinaryScale (bankOrdinaryScaleIndex q) / 3 := by
  exact Nat.find_spec (bankOrdinaryScaleIndex_exists q)

theorem bankOrdinaryScaleIndex_cell
    {q : ℕ} (hq : 5 ≤ q) :
    CoreInGeometricCell (bankOrdinaryScale (bankOrdinaryScaleIndex q)) q := by
  refine ⟨?_, bankOrdinaryScaleIndex_upper q⟩
  by_cases hzero : bankOrdinaryScaleIndex q = 0
  · rw [hzero]
    norm_num [bankOrdinaryScale]
    exact_mod_cast hq
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    have hminimal : ¬ (q : ℚ) ≤ 4 * bankOrdinaryScale j / 3 := by
      intro hbound
      have hle : bankOrdinaryScaleIndex q ≤ j :=
        Nat.find_min' (bankOrdinaryScaleIndex_exists q) hbound
      rw [hj] at hle
      omega
    rw [hj, bankOrdinaryScale_succ]
    exact lt_of_not_ge (by simpa only [mul_assoc] using hminimal)

theorem bankOrdinaryScale_strictMono : StrictMono bankOrdinaryScale := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [bankOrdinaryScale_succ]
  have hpos := bankOrdinaryScale_pos j
  linarith

theorem bankOrdinaryScale_mono : Monotone bankOrdinaryScale :=
  bankOrdinaryScale_strictMono.monotone

theorem bankOrdinaryScaleIndex_ge_six
    {q : ℕ} (hq : 23 ≤ q) :
    6 ≤ bankOrdinaryScaleIndex q := by
  by_contra h
  have hindex : bankOrdinaryScaleIndex q ≤ 5 := by omega
  have hscale := bankOrdinaryScale_mono hindex
  have hupper := bankOrdinaryScaleIndex_upper q
  have hqQ : (23 : ℚ) ≤ q := by exact_mod_cast hq
  simp only [bankOrdinaryScale] at hupper
  norm_num [bankOrdinaryScale] at hscale
  linarith

theorem twenty_lt_bankOrdinaryScale_of_six_le
    {j : ℕ} (hj : 6 ≤ j) :
    (20 : ℚ) < bankOrdinaryScale j := by
  have hscale := bankOrdinaryScale_mono hj
  norm_num [bankOrdinaryScale] at hscale ⊢
  linarith

theorem twentyTwo_lt_bankOrdinaryScale_of_six_le
    {j : ℕ} (hj : 6 ≤ j) :
    (22 : ℚ) < bankOrdinaryScale j := by
  have hscale := bankOrdinaryScale_mono hj
  norm_num [bankOrdinaryScale] at hscale ⊢
  linarith

/-! ## The scale and certificate carried by every component -/

/-- The natural grid indices `1,...,5` corresponding to the five constructors
of `SmallDescentScale`. -/
def smallDescentScaleIndex : SmallDescentScale → ℕ
  | .one => 1
  | .two => 2
  | .three => 3
  | .four => 4
  | .five => 5

theorem smallDescentScaleValue_eq_bankOrdinaryScale
    (scale : SmallDescentScale) :
    smallDescentScaleValue scale =
      bankOrdinaryScale (smallDescentScaleIndex scale) := by
  cases scale <;>
    norm_num [smallDescentScaleValue, smallDescentScaleNumerator,
      smallDescentScaleDenominator, smallDescentScaleIndex,
      bankOrdinaryScale]

theorem one_le_smallDescentScaleIndex (scale : SmallDescentScale) :
    1 ≤ smallDescentScaleIndex scale := by
  cases scale <;> decide

theorem smallDescentScaleIndex_le_five (scale : SmallDescentScale) :
    smallDescentScaleIndex scale ≤ 5 := by
  cases scale <;> decide

/-- The grid label attached to the component leaving `q`. -/
def bankOrdinaryComponentScaleIndex (q : ℕ) : ℕ :=
  if q ≤ 22 then smallDescentScaleIndex (smallDescentScaleForSource q)
  else bankOrdinaryScaleIndex q

theorem one_le_bankOrdinaryComponentScaleIndex
    {q : ℕ} (_hq : 6 ≤ q) :
    1 ≤ bankOrdinaryComponentScaleIndex q := by
  by_cases hq22 : q ≤ 22
  · rw [bankOrdinaryComponentScaleIndex, if_pos hq22]
    exact one_le_smallDescentScaleIndex _
  · rw [bankOrdinaryComponentScaleIndex, if_neg hq22]
    exact (show 1 ≤ bankOrdinaryScaleIndex q by
      have := bankOrdinaryScaleIndex_ge_six (show 23 ≤ q by omega)
      omega)

/-- The complete local certificate needed by an actual ordinary-bank
component. -/
def IsBankOrdinaryCoreComponent (q b : ℕ) : Prop :=
  6 ≤ q ∧
    ¬ IsPowerOfTwo q ∧
    ¬ IsPowerOfTwo b ∧
    5 ≤ b ∧
    b < q ∧
    b = bankOrdinaryCoreStep q ∧
    InGeometricDescentCell
      (bankOrdinaryScale (bankOrdinaryComponentScaleIndex q)) q b

theorem bankOrdinaryCoreStep_spec
    {q : ℕ} (hq : 6 ≤ q) (hqPower : ¬ IsPowerOfTwo q) :
    IsBankOrdinaryCoreComponent q (bankOrdinaryCoreStep q) := by
  by_cases hq22 : q ≤ 22
  · have hentry := bankSmallCoreStep_certified hq hq22 hqPower
    have hstep : bankOrdinaryCoreStep q = bankSmallCoreStep q := by
      rw [bankOrdinaryCoreStep, if_neg (by omega), if_pos hq22]
    have hcellSmall : InSmallGeometricDescentCell
        (smallDescentScaleForSource q) q (bankSmallCoreStep q) :=
      (inSmallGeometricDescentCellCross_iff _ _ _).mp hentry.2.2.2.2.2
    rw [IsBankOrdinaryCoreComponent]
    refine ⟨hq, hqPower, ?_, ?_, ?_, rfl, ?_⟩
    · simpa only [hstep] using hentry.2.2.1
    · simpa only [hstep] using hentry.2.2.2.1
    · simpa only [hstep] using hentry.2.2.2.2.1
    · rw [bankOrdinaryComponentScaleIndex, if_pos hq22,
        ← smallDescentScaleValue_eq_bankOrdinaryScale]
      rcases hcellSmall with ⟨hsourceLower, hsourceUpper, htargetLower⟩
      rw [InGeometricDescentCell, CoreInGeometricCell, hstep]
      exact ⟨⟨hsourceLower, hsourceUpper⟩, htargetLower⟩
  · have hq23 : 23 ≤ q := by omega
    have hindex := bankOrdinaryScaleIndex_ge_six hq23
    have hQ := twenty_lt_bankOrdinaryScale_of_six_le hindex
    have hcell := bankOrdinaryScaleIndex_cell (show 5 ≤ q by omega)
    have hlarge := largeCoreStep_spec hQ hq hqPower hcell
    have hstep := bankOrdinaryCoreStep_eq_largeCoreStep (by omega : 22 < q)
    rw [IsBankOrdinaryCoreComponent]
    refine ⟨hq, hqPower, ?_, ?_, ?_, rfl, ?_⟩
    · simpa only [hstep] using hlarge.2.1
    · simpa only [hstep] using hlarge.2.2.1
    · simpa only [hstep] using hlarge.2.2.2.1
    · rw [bankOrdinaryComponentScaleIndex, if_neg hq22]
      simpa only [hstep] using hlarge.2.2.2.2.1

theorem prime_not_isPowerOfTwo_of_five_le
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ IsPowerOfTwo p := by
  rw [isPowerOfTwo_iff]
  rintro ⟨k, hk⟩
  have hdata := hp.pow_eq_iff.mp hk.symm
  omega

/-! ## A literal finite terminating path -/

/-- Vertices of the deterministic core path.  This is well founded because
every nonterminal transition is strictly decreasing. -/
def bankOrdinaryCoreVertices (q : ℕ) : List ℕ :=
  if q ≤ 5 then [5]
  else q :: bankOrdinaryCoreVertices (bankOrdinaryCoreStep q)
termination_by q
decreasing_by
  exact bankOrdinaryCoreStep_lt_self (by omega)

/-- Actual nonterminal sources traversed by the same path. -/
def bankOrdinaryCoreSources (q : ℕ) : Finset ℕ :=
  if q ≤ 5 then ∅
  else insert q (bankOrdinaryCoreSources (bankOrdinaryCoreStep q))
termination_by q
decreasing_by
  exact bankOrdinaryCoreStep_lt_self (by omega)

theorem bankOrdinaryCoreVertices_of_le_five
    {q : ℕ} (hq : q ≤ 5) :
    bankOrdinaryCoreVertices q = [5] := by
  rw [bankOrdinaryCoreVertices]
  simp [hq]

theorem bankOrdinaryCoreVertices_of_six_le
    {q : ℕ} (hq : 6 ≤ q) :
    bankOrdinaryCoreVertices q =
      q :: bankOrdinaryCoreVertices (bankOrdinaryCoreStep q) := by
  rw [bankOrdinaryCoreVertices]
  rw [if_neg (by omega)]

theorem bankOrdinaryCoreSources_of_le_five
    {q : ℕ} (hq : q ≤ 5) :
    bankOrdinaryCoreSources q = ∅ := by
  rw [bankOrdinaryCoreSources]
  simp [hq]

theorem bankOrdinaryCoreSources_of_six_le
    {q : ℕ} (hq : 6 ≤ q) :
    bankOrdinaryCoreSources q =
      insert q (bankOrdinaryCoreSources (bankOrdinaryCoreStep q)) := by
  rw [bankOrdinaryCoreSources]
  rw [if_neg (by omega)]

theorem bankOrdinaryCoreVertices_ne_nil (q : ℕ) :
    bankOrdinaryCoreVertices q ≠ [] := by
  by_cases hq : q ≤ 5
  · simp [bankOrdinaryCoreVertices_of_le_five hq]
  · rw [bankOrdinaryCoreVertices_of_six_le (q := q) (by omega)]
    exact List.cons_ne_nil q _

/-- The constructed path really starts at its prescribed source. -/
theorem bankOrdinaryCoreVertices_head?_eq
    {q : ℕ} (hq : 5 ≤ q) :
    (bankOrdinaryCoreVertices q).head? = some q := by
  by_cases hq5 : q ≤ 5
  · have : q = 5 := by omega
    subst q
    simp [bankOrdinaryCoreVertices_of_le_five]
  · rw [bankOrdinaryCoreVertices_of_six_le (q := q) (by omega)]
    rfl

/-- The well-founded construction has no endpoint hypothesis: its final
vertex is the literal terminal core `5`. -/
theorem bankOrdinaryCoreVertices_getLast?_eq_five
    {q : ℕ} (hq : 5 ≤ q) :
    (bankOrdinaryCoreVertices q).getLast? = some 5 := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
      by_cases hq5 : q ≤ 5
      · have : q = 5 := by omega
        subst q
        simp [bankOrdinaryCoreVertices_of_le_five]
      · have hq6 : 6 ≤ q := by omega
        have hstepLt := bankOrdinaryCoreStep_lt_self (by omega : 5 < q)
        have hstepGe := bankOrdinaryCoreStep_ge_five (show 5 ≤ q by omega)
        rw [bankOrdinaryCoreVertices_of_six_le hq6]
        rw [List.getLast?_cons,
          ih (bankOrdinaryCoreStep q) hstepLt hstepGe]
        rfl

/-- Consecutive vertices are exactly the certified deterministic steps. -/
theorem bankOrdinaryCoreVertices_isChain
    {q : ℕ} (hq : 5 ≤ q) (hqPower : ¬ IsPowerOfTwo q) :
    List.IsChain
      (fun source target ↦
        target = bankOrdinaryCoreStep source ∧
          IsBankOrdinaryCoreComponent source target)
      (bankOrdinaryCoreVertices q) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
      by_cases hq5 : q ≤ 5
      · have : q = 5 := by omega
        subst q
        simp [bankOrdinaryCoreVertices_of_le_five]
      · have hq6 : 6 ≤ q := by omega
        have hspec := bankOrdinaryCoreStep_spec hq6 hqPower
        have htail := ih (bankOrdinaryCoreStep q) hspec.2.2.2.2.1
          hspec.2.2.2.1 hspec.2.2.1
        rw [bankOrdinaryCoreVertices_of_six_le hq6]
        apply htail.cons
        intro target htarget
        rw [bankOrdinaryCoreVertices_head?_eq hspec.2.2.2.1] at htarget
        have htargetEq : bankOrdinaryCoreStep q = target := by
          simpa only [Option.mem_some_iff] using htarget
        subst target
        exact ⟨rfl, hspec⟩

theorem bankOrdinaryCoreSource_le_start
    {q s : ℕ} (hs : s ∈ bankOrdinaryCoreSources q) :
    s ≤ q := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
      by_cases hq5 : q ≤ 5
      · simp [bankOrdinaryCoreSources_of_le_five hq5] at hs
      · have hq6 : 6 ≤ q := by omega
        rw [bankOrdinaryCoreSources_of_six_le hq6] at hs
        rcases Finset.mem_insert.mp hs with rfl | hs
        · exact le_rfl
        · exact (ih _ (bankOrdinaryCoreStep_lt_self (by omega)) hs).trans
            (bankOrdinaryCoreStep_lt_self (by omega)).le

/-- The new head of a nonterminal path is not already present in its tail.
This is the exact no-duplication fact needed to sum over the source finset. -/
theorem bankOrdinaryCoreStep_tail_not_mem
    {q : ℕ} (hq : 5 < q) :
    q ∉ bankOrdinaryCoreSources (bankOrdinaryCoreStep q) := by
  intro hmem
  have hle := bankOrdinaryCoreSource_le_start hmem
  have hlt := bankOrdinaryCoreStep_lt_self hq
  omega

/-- Every source reached from a legal starting core carries the complete
component certificate, including its actual grid cell and actual target. -/
theorem bankOrdinaryCoreSource_spec
    {q s : ℕ} (hq : 5 ≤ q) (hqPower : ¬ IsPowerOfTwo q)
    (hs : s ∈ bankOrdinaryCoreSources q) :
    IsBankOrdinaryCoreComponent s (bankOrdinaryCoreStep s) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
      by_cases hq5 : q ≤ 5
      · simp [bankOrdinaryCoreSources_of_le_five hq5] at hs
      · have hq6 : 6 ≤ q := by omega
        have hspec := bankOrdinaryCoreStep_spec hq6 hqPower
        rw [bankOrdinaryCoreSources_of_six_le hq6] at hs
        rcases Finset.mem_insert.mp hs with rfl | hs
        · exact hspec
        · exact ih (bankOrdinaryCoreStep q) hspec.2.2.2.2.1
            hspec.2.2.2.1 hspec.2.2.1 hs

/-! ## The actual finite path telescopes -/

/-- Sum of the valuation changes over the actual finite source set. -/
def bankOrdinaryFinitePathChange (q : ℕ) : BankVector ℕ :=
  ∑ s ∈ bankOrdinaryCoreSources q,
    factorMoveChange s (bankOrdinaryCoreStep s)

theorem bankOrdinaryFinitePathChange_of_six_le
    {q : ℕ} (hq : 6 ≤ q) :
    bankOrdinaryFinitePathChange q =
      factorMoveChange q (bankOrdinaryCoreStep q) +
        bankOrdinaryFinitePathChange (bankOrdinaryCoreStep q) := by
  rw [bankOrdinaryFinitePathChange,
    bankOrdinaryCoreSources_of_six_le hq,
    Finset.sum_insert (bankOrdinaryCoreStep_tail_not_mem (by omega))]
  rfl

/-- Exact telescope for the constructed terminating path.  There is no
endpoint or chain hypothesis: both are consequences of the deterministic
well-founded constructor. -/
theorem bankOrdinaryFinitePathChange_telescope
    {q : ℕ} (hq : 5 ≤ q) (hqPower : ¬ IsPowerOfTwo q) :
    bankOrdinaryFinitePathChange q = factorMoveChange q 5 := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
      by_cases hq5 : q ≤ 5
      · have : q = 5 := by omega
        subst q
        simp [bankOrdinaryFinitePathChange,
          bankOrdinaryCoreSources_of_le_five, factorMoveChange]
      · have hq6 : 6 ≤ q := by omega
        have hspec := bankOrdinaryCoreStep_spec hq6 hqPower
        rw [bankOrdinaryFinitePathChange_of_six_le hq6,
          ih (bankOrdinaryCoreStep q) hspec.2.2.2.2.1
            hspec.2.2.2.1 hspec.2.2.1]
        unfold factorMoveChange
        abel

/-- Prime-to-five form of the actual finite telescope, matching the endpoint
statement in `BankPathAlgebra`. -/
theorem bankOrdinaryFinitePathChange_prime_to_five
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    bankOrdinaryFinitePathChange p =
      coordinateUnit 5 - coordinateUnit p := by
  rw [bankOrdinaryFinitePathChange_telescope hp5
      (prime_not_isPowerOfTwo_of_five_le hp hp5),
    factorMoveChange, integerValuationVector_prime hp]
  have hfive : Nat.Prime 5 := by norm_num
  rw [integerValuationVector_prime hfive]

/-- Adding the four concrete bottom moves to the constructed ordinary path
gives the required negative prime unit; reversing it gives the other bank
orientation. -/
theorem bankOrdinaryFiniteFullPathChange_eq_neg_unit
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    bankOrdinaryFinitePathChange p + fourBottomMovesChange =
      -coordinateUnit p := by
  rw [bankOrdinaryFinitePathChange_prime_to_five hp hp5,
    fourBottomMovesChange_eq_neg_unit_five]
  abel

theorem reverse_bankOrdinaryFiniteFullPathChange_eq_unit
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    -(bankOrdinaryFinitePathChange p + fourBottomMovesChange) =
      coordinateUnit p := by
  rw [bankOrdinaryFiniteFullPathChange_eq_neg_unit hp hp5]
  simp

/-- Indices at or below the small table can only label literal small-table
sources. -/
theorem bankOrdinaryComponentSource_le_twentyTwo_of_scaleIndex_le_five
    {q : ℕ} (_hq : 6 ≤ q)
    (hindex : bankOrdinaryComponentScaleIndex q ≤ 5) :
    q ≤ 22 := by
  by_contra hq22
  have hq23 : 23 ≤ q := by omega
  have hge := bankOrdinaryScaleIndex_ge_six hq23
  rw [bankOrdinaryComponentScaleIndex, if_neg (by omega : ¬q ≤ 22)]
      at hindex
  omega

/-- The actual component sources of one path routed to grid index `j`. -/
def bankOrdinaryCoreSourcesAtScale (q j : ℕ) : Finset ℕ :=
  (bankOrdinaryCoreSources q).filter fun s ↦
    bankOrdinaryComponentScaleIndex s = j

private instance decidableCoreInGeometricCellLocal (Q : ℚ) (q : ℕ) :
    Decidable (CoreInGeometricCell Q q) := by
  unfold CoreInGeometricCell
  infer_instance

/-- The entire small-table portion of one path has an absolute, literal
bound.  In particular each of its five scale fibers has this bound. -/
theorem bankOrdinaryCoreSourcesAtSmallScale_card_le
    {q j : ℕ} (hq : 5 ≤ q) (hqPower : ¬ IsPowerOfTwo q)
    (hj : j ≤ 5) :
    (bankOrdinaryCoreSourcesAtScale q j).card ≤ 17 := by
  have hsubset : bankOrdinaryCoreSourcesAtScale q j ⊆ Finset.Icc 6 22 := by
    intro s hs
    have hsData := Finset.mem_filter.mp hs
    have hspec := bankOrdinaryCoreSource_spec hq hqPower hsData.1
    have hsmall : bankOrdinaryComponentScaleIndex s ≤ 5 := by
      rw [hsData.2]
      exact hj
    exact Finset.mem_Icc.mpr ⟨hspec.1,
      bankOrdinaryComponentSource_le_twentyTwo_of_scaleIndex_le_five
        hspec.1 hsmall⟩
  calc
    (bankOrdinaryCoreSourcesAtScale q j).card ≤
        (Finset.Icc 6 22).card := Finset.card_le_card hsubset
    _ = 17 := by norm_num

private theorem bankOrdinaryCoreSources_in_largeCell_card_le_two
    {q j : ℕ} (hq : 5 ≤ q) (hqPower : ¬ IsPowerOfTwo q)
    (hj : 6 ≤ j) :
    ((bankOrdinaryCoreSources q).filter fun s ↦
        CoreInGeometricCell (bankOrdinaryScale j) s).card ≤ 2 := by
  classical
  induction q using Nat.strong_induction_on with
  | h q ih =>
      by_cases hq5 : q ≤ 5
      · rw [bankOrdinaryCoreSources_of_le_five hq5]
        simp
      · have hq6 : 6 ≤ q := by omega
        let b := bankOrdinaryCoreStep q
        have hspec := bankOrdinaryCoreStep_spec hq6 hqPower
        have hb5 : 5 ≤ b := hspec.2.2.2.1
        have hbLt : b < q := hspec.2.2.2.2.1
        have hbPower : ¬ IsPowerOfTwo b := hspec.2.2.1
        have hQ20 := twenty_lt_bankOrdinaryScale_of_six_le hj
        by_cases hqLow : (q : ℚ) ≤ bankOrdinaryScale j
        · have hempty :
              (bankOrdinaryCoreSources q).filter (fun s ↦
                CoreInGeometricCell (bankOrdinaryScale j) s) = ∅ := by
            apply Finset.filter_eq_empty_iff.mpr
            intro s hs hcell
            have hsle := bankOrdinaryCoreSource_le_start hs
            have hsleQ : (s : ℚ) ≤ q := by exact_mod_cast hsle
            exact (not_lt_of_ge (hsleQ.trans hqLow)) hcell.1
          rw [hempty]
          simp
        · by_cases hqUpper :
              (q : ℚ) ≤ 4 * bankOrdinaryScale j / 3
          · have hqCell : CoreInGeometricCell (bankOrdinaryScale j) q :=
              ⟨lt_of_not_ge hqLow, hqUpper⟩
            by_cases hbLow : (b : ℚ) ≤ bankOrdinaryScale j
            · have hsubset :
                  (bankOrdinaryCoreSources q).filter (fun s ↦
                      CoreInGeometricCell (bankOrdinaryScale j) s) ⊆
                    {q} := by
                intro s hs
                have hsSource := (Finset.mem_filter.mp hs).1
                rw [bankOrdinaryCoreSources_of_six_le hq6] at hsSource
                rcases Finset.mem_insert.mp hsSource with rfl | hsTail
                · simp
                · have hsle := bankOrdinaryCoreSource_le_start hsTail
                  have hsleQ : (s : ℚ) ≤ b := by exact_mod_cast hsle
                  exact False.elim ((not_lt_of_ge (hsleQ.trans hbLow))
                    (Finset.mem_filter.mp hs).2.1)
              calc
                ((bankOrdinaryCoreSources q).filter fun s ↦
                    CoreInGeometricCell (bankOrdinaryScale j) s).card ≤
                    ({q} : Finset ℕ).card := Finset.card_le_card hsubset
                _ = 1 := Finset.card_singleton q
                _ ≤ 2 := by norm_num
            · have hbCell : CoreInGeometricCell (bankOrdinaryScale j) b := by
                refine ⟨lt_of_not_ge hbLow, ?_⟩
                have hbq : (b : ℚ) < q := by exact_mod_cast hbLt
                exact hbq.le.trans hqUpper
              have hQ22 := twentyTwo_lt_bankOrdinaryScale_of_six_le hj
              have hq22 : 22 < q := by
                have : (22 : ℚ) < q := hQ22.trans hqCell.1
                exact_mod_cast this
              have hb22 : 22 < b := by
                have : (22 : ℚ) < b := hQ22.trans hbCell.1
                exact_mod_cast this
              have hqLarge := bankOrdinaryCoreStep_eq_largeCoreStep hq22
              have hbLarge := bankOrdinaryCoreStep_eq_largeCoreStep hb22
              have hleave := two_consecutive_largeCoreSteps_leave_cell
                hQ20 hqCell (by simpa only [b, hqLarge] using hbCell)
              have hleave' :
                  ((bankOrdinaryCoreStep b : ℕ) : ℚ) <
                    bankOrdinaryScale j := by
                rw [hbLarge]
                simpa only [b, hqLarge] using hleave
              have hsubset :
                  (bankOrdinaryCoreSources q).filter (fun s ↦
                      CoreInGeometricCell (bankOrdinaryScale j) s) ⊆
                    {q, b} := by
                intro s hs
                have hsSource := (Finset.mem_filter.mp hs).1
                rw [bankOrdinaryCoreSources_of_six_le hq6] at hsSource
                rcases Finset.mem_insert.mp hsSource with rfl | hsTail
                · simp
                · rw [bankOrdinaryCoreSources_of_six_le (by omega : 6 ≤ b)]
                      at hsTail
                  rcases Finset.mem_insert.mp hsTail with rfl | hsAfter
                  · simp
                  · have hsle := bankOrdinaryCoreSource_le_start hsAfter
                    have hsleQ : (s : ℚ) ≤ bankOrdinaryCoreStep b := by
                      exact_mod_cast hsle
                    exact False.elim ((not_lt_of_ge hsleQ)
                      (hleave'.trans (Finset.mem_filter.mp hs).2.1))
              calc
                ((bankOrdinaryCoreSources q).filter fun s ↦
                    CoreInGeometricCell (bankOrdinaryScale j) s).card ≤
                    ({q, b} : Finset ℕ).card := Finset.card_le_card hsubset
                _ ≤ 2 := Finset.card_le_two
          · have hqNotCell :
                ¬ CoreInGeometricCell (bankOrdinaryScale j) q := by
              intro hcell
              exact hqUpper hcell.2
            have htail := ih b hbLt hb5 hbPower
            rw [bankOrdinaryCoreSources_of_six_le hq6,
              Finset.filter_insert, if_neg hqNotCell]
            simpa only [b] using htail

/-- Sharp per-path congestion at a large grid scale: at most two actual
ordinary components of a path use that scale. -/
theorem bankOrdinaryCoreSourcesAtLargeScale_card_le_two
    {q j : ℕ} (hq : 5 ≤ q) (hqPower : ¬ IsPowerOfTwo q)
    (hj : 6 ≤ j) :
    (bankOrdinaryCoreSourcesAtScale q j).card ≤ 2 := by
  classical
  have hsubset : bankOrdinaryCoreSourcesAtScale q j ⊆
      (bankOrdinaryCoreSources q).filter (fun s ↦
        CoreInGeometricCell (bankOrdinaryScale j) s) := by
    intro s hs
    have hsData := Finset.mem_filter.mp hs
    have hspec := bankOrdinaryCoreSource_spec hq hqPower hsData.1
    apply Finset.mem_filter.mpr
    refine ⟨hsData.1, ?_⟩
    rw [← hsData.2]
    exact hspec.2.2.2.2.2.2.1
  exact (Finset.card_le_card hsubset).trans
    (bankOrdinaryCoreSources_in_largeCell_card_le_two hq hqPower hj)

end

end Erdos390.WholePaper
