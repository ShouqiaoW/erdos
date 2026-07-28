import Erdos390.WholePaper.RoughSaiasCanonicalRowBridge

/-!
# Finite constant-pool correction of one canonical rough row

The Saias-facing quantity `roughCanonicalRawRowQuotaError` is a row-mass
error.  The paper corrects such an error by spreading it uniformly over a
nonempty clean broad subpool in the same complete-signature row.  This file
formalizes that finite operation directly.

No selector handoff, feasibility conclusion, prime-residual estimate, or
asymptotic pool lower bound is assumed.  Exact row mass is an algebraic
consequence of nonemptiness and containment of the correction pool.
Feasibility is then *derived* from two explicit numerical facts: the raw
coordinates have a stated two-sided margin and the constant correction
density is no larger than that margin.

The final specialization uses the literal upper-row cardinality as target,
the literal head-compatible raw weight as baseline, and the head-free broad
fiber as correction pool.  Establishing the paper's uniform lower bound for
that pool after all guards, and the corresponding `o(1 / log n)` density
bound, remains a separate arithmetic task.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Generic finite constant-pool correction -/

/-- The signed amount added to every member of a correction pool. -/
def bankPaperConstantPoolCorrectionDensity
    (row pool : Finset ℕ) (x : ℕ → ℝ) (target : ℝ) : ℝ :=
  (target - ∑ a ∈ row, x a) / (pool.card : ℝ)

/-- Add the same correction density on `pool` and leave every other
coordinate unchanged. -/
def bankPaperConstantPoolCorrection
    (row pool : Finset ℕ) (x : ℕ → ℝ) (target : ℝ)
    (a : ℕ) : ℝ :=
  x a + if a ∈ pool then
    bankPaperConstantPoolCorrectionDensity row pool x target
  else 0

@[simp]
theorem bankPaperConstantPoolCorrection_apply_of_mem
    {row pool : Finset ℕ} {x : ℕ → ℝ} {target : ℝ} {a : ℕ}
    (ha : a ∈ pool) :
    bankPaperConstantPoolCorrection row pool x target a =
      x a + bankPaperConstantPoolCorrectionDensity row pool x target := by
  simp [bankPaperConstantPoolCorrection, ha]

@[simp]
theorem bankPaperConstantPoolCorrection_apply_of_not_mem
    {row pool : Finset ℕ} {x : ℕ → ℝ} {target : ℝ} {a : ℕ}
    (ha : a ∉ pool) :
    bankPaperConstantPoolCorrection row pool x target a = x a := by
  simp [bankPaperConstantPoolCorrection, ha]

/-- Spreading the row error over a nonempty subpool makes the row sum
exactly equal to the requested target. -/
theorem sum_bankPaperConstantPoolCorrection_eq_target
    {row pool : Finset ℕ} {x : ℕ → ℝ} {target : ℝ}
    (hpool : pool ⊆ row) (hpoolNonempty : pool.Nonempty) :
    ∑ a ∈ row, bankPaperConstantPoolCorrection row pool x target a =
      target := by
  have hfilter : row.filter (fun a ↦ a ∈ pool) = pool := by
    ext a
    simp only [Finset.mem_filter]
    constructor
    · exact fun ha ↦ ha.2
    · exact fun ha ↦ ⟨hpool ha, ha⟩
  have hcardNat : pool.card ≠ 0 :=
    Finset.card_ne_zero.mpr hpoolNonempty
  have hcardReal : (pool.card : ℝ) ≠ 0 := by
    exact_mod_cast hcardNat
  have hcorrectionSum :
      (∑ a ∈ row,
        if a ∈ pool then
          bankPaperConstantPoolCorrectionDensity row pool x target
        else 0) =
        (pool.card : ℝ) *
          bankPaperConstantPoolCorrectionDensity row pool x target := by
    rw [← Finset.sum_filter, hfilter]
    simp
  have hcancel :
      (pool.card : ℝ) *
          ((target - ∑ a ∈ row, x a) / (pool.card : ℝ)) =
        target - ∑ a ∈ row, x a := by
    rw [mul_comm, div_mul_cancel₀ _ hcardReal]
  calc
    ∑ a ∈ row, bankPaperConstantPoolCorrection row pool x target a =
        (∑ a ∈ row, x a) +
          ∑ a ∈ row,
            if a ∈ pool then
              bankPaperConstantPoolCorrectionDensity row pool x target
            else 0 := by
      simp only [bankPaperConstantPoolCorrection]
      rw [Finset.sum_add_distrib]
    _ = (∑ a ∈ row, x a) +
        (pool.card : ℝ) *
          bankPaperConstantPoolCorrectionDensity row pool x target := by
      rw [hcorrectionSum]
    _ = (∑ a ∈ row, x a) +
        (pool.card : ℝ) *
          ((target - ∑ a ∈ row, x a) / (pool.card : ℝ)) := by
      rw [bankPaperConstantPoolCorrectionDensity]
    _ = target := by
      rw [hcancel]
      ring

/-- Feasibility of the corrected row follows from explicit signed room at
each corrected coordinate.  It is not taken as a selector premise. -/
theorem bankPaperConstantPoolCorrection_mem_unitInterval
    {row pool : Finset ℕ} {x : ℕ → ℝ} {target : ℝ}
    (hx : ∀ a ∈ row, 0 ≤ x a ∧ x a ≤ 1)
    (hroom : ∀ a ∈ pool,
      -x a ≤ bankPaperConstantPoolCorrectionDensity row pool x target ∧
        bankPaperConstantPoolCorrectionDensity row pool x target ≤
          1 - x a)
    {a : ℕ} (ha : a ∈ row) :
    0 ≤ bankPaperConstantPoolCorrection row pool x target a ∧
      bankPaperConstantPoolCorrection row pool x target a ≤ 1 := by
  by_cases haPool : a ∈ pool
  · rw [bankPaperConstantPoolCorrection_apply_of_mem haPool]
    have hroomA := hroom a haPool
    constructor <;> linarith
  · rw [bankPaperConstantPoolCorrection_apply_of_not_mem haPool]
    exact hx a ha

/-- A symmetric margin and an absolute correction-density bound imply the
signed room required by the preceding theorem. -/
theorem bankPaperConstantPoolCorrection_mem_unitInterval_of_abs_density_le
    {row pool : Finset ℕ} {x : ℕ → ℝ} {target margin : ℝ}
    (hx : ∀ a ∈ row, 0 ≤ x a ∧ x a ≤ 1)
    (hmargin : ∀ a ∈ pool,
      margin ≤ x a ∧ x a ≤ 1 - margin)
    (hdensity :
      |bankPaperConstantPoolCorrectionDensity row pool x target| ≤ margin)
    {a : ℕ} (ha : a ∈ row) :
    0 ≤ bankPaperConstantPoolCorrection row pool x target a ∧
      bankPaperConstantPoolCorrection row pool x target a ≤ 1 := by
  apply bankPaperConstantPoolCorrection_mem_unitInterval hx
  · intro b hb
    have hdensityBounds := abs_le.mp hdensity
    have hmarginB := hmargin b hb
    constructor <;> linarith
  · exact ha

/-! ## Literal canonical rough-row specialization -/

/-- Before numerical guards, the paper's broad correction pool in one
complete rough row consists of the head-free broad candidates in that row. -/
def roughCanonicalBroadCorrectionPool
    (W n h K y label : ℕ) : Finset ℕ :=
  completeRoughRowFiber y
    (roughHeadFree W (roughBroadLowerBlock n h K)) label

/-- The broad correction pool is contained in the corresponding literal
raw-candidate row. -/
theorem roughCanonicalBroadCorrectionPool_subset_rawRow
    (W n h K y label : ℕ) :
    roughCanonicalBroadCorrectionPool W n h K y label ⊆
      completeRoughRowFiber y (roughRawCandidateSet n h K) label := by
  intro a ha
  have haData := mem_completeRoughRowFiber.mp ha
  have haHead := mem_roughHeadFree.mp haData.1
  apply mem_completeRoughRowFiber.mpr
  refine ⟨?_, haData.2⟩
  simp only [roughRawCandidateSet]
  exact Finset.mem_union_right _ haHead.1

/-- Every coordinate of the literal broad correction pool has exactly the
broad raw weight `beta / L`. -/
theorem roughHeadCompatibleRawWeight_eq_broad_of_mem_correctionPool
    {W n h K y label a : ℕ} {alpha beta L : ℝ}
    (ha : a ∈ roughCanonicalBroadCorrectionPool W n h K y label) :
    roughHeadCompatibleRawWeight W n h K alpha beta L a = beta / L := by
  have haData := mem_completeRoughRowFiber.mp ha
  have haHead := mem_roughHeadFree.mp haData.1
  have haHigh : a ∉ roughHighLowerBlock n h K := by
    intro haHigh
    exact Finset.disjoint_left.mp
      (roughHighLowerBlock_disjoint_roughBroadLowerBlock n h K)
      haHigh haHead.1
  simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
    haHead.2, haHigh, haHead.1]

/-- The actual finite row correction used before guards: its target is the
literal upper-row cardinality and its baseline is the literal raw weight. -/
def roughCanonicalRawRowCorrectedWeight
    (W n h K y label : ℕ) (alpha beta L : ℝ) (a : ℕ) : ℝ :=
  bankPaperConstantPoolCorrection
    (completeRoughRowFiber y (roughRawCandidateSet n h K) label)
    (roughCanonicalBroadCorrectionPool W n h K y label)
    (roughHeadCompatibleRawWeight W n h K alpha beta L)
    (roughUpperCompleteRoughRowTarget n h y label : ℝ) a

/-- On a canonical row, the constant correction density is exactly the
Saias-facing quota error divided by the literal broad-pool cardinality. -/
theorem roughCanonicalRawRowCorrectionDensity_eq_quotaError_div
    (W n h K y : ℕ) (alpha beta L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) :
    bankPaperConstantPoolCorrectionDensity
        (completeRoughRowFiber y (roughRawCandidateSet n h K) row.1)
        (roughCanonicalBroadCorrectionPool W n h K y row.1)
        (roughHeadCompatibleRawWeight W n h K alpha beta L)
        (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) =
      roughCanonicalRawRowQuotaError W n h K y alpha beta L row /
        ((roughCanonicalBroadCorrectionPool W n h K y row.1).card : ℝ) := by
  rw [bankPaperConstantPoolCorrectionDensity,
    roughCanonicalRawRowQuotaError_eq_target_sub_rawRowMass]
  rfl

/-- A nonempty literal broad pool suffices for exact integer mass on this
complete rough row.  No selector existence premise is used. -/
theorem sum_roughCanonicalRawRowCorrectedWeight_eq_upperTarget
    (W n h K y : ℕ) (alpha beta L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hpool :
      (roughCanonicalBroadCorrectionPool W n h K y row.1).Nonempty) :
    ∑ a ∈ completeRoughRowFiber y
        (roughRawCandidateSet n h K) row.1,
      roughCanonicalRawRowCorrectedWeight
        W n h K y row.1 alpha beta L a =
      (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) := by
  exact sum_bankPaperConstantPoolCorrection_eq_target
    (roughCanonicalBroadCorrectionPool_subset_rawRow
      W n h K y row.1) hpool

/-- The raw parameter box, a two-sided broad margin, and a bound on the
literal correction density prove feasibility of the constructed row. -/
theorem roughCanonicalRawRowCorrectedWeight_mem_unitInterval
    {W n h K y : ℕ} {alpha beta L margin : ℝ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (halpha : 0 ≤ alpha ∧ alpha ≤ 1)
    (hbeta : 0 ≤ beta / L ∧ beta / L ≤ 1)
    (hmarginLower : margin ≤ beta / L)
    (hmarginUpper : margin ≤ 1 - beta / L)
    (hdensity :
      |bankPaperConstantPoolCorrectionDensity
        (completeRoughRowFiber y (roughRawCandidateSet n h K) row.1)
        (roughCanonicalBroadCorrectionPool W n h K y row.1)
        (roughHeadCompatibleRawWeight W n h K alpha beta L)
        (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ)| ≤ margin)
    {a : ℕ}
    (ha : a ∈ completeRoughRowFiber y
      (roughRawCandidateSet n h K) row.1) :
    0 ≤ roughCanonicalRawRowCorrectedWeight
        W n h K y row.1 alpha beta L a ∧
      roughCanonicalRawRowCorrectedWeight
        W n h K y row.1 alpha beta L a ≤ 1 := by
  apply bankPaperConstantPoolCorrection_mem_unitInterval_of_abs_density_le
    (target := (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ))
    (margin := margin)
  · intro b _hb
    exact roughHeadCompatibleRawWeight_mem_unitInterval halpha hbeta b
  · intro b hb
    rw [roughHeadCompatibleRawWeight_eq_broad_of_mem_correctionPool hb]
    constructor <;> linarith
  · exact hdensity
  · exact ha

/-- The exact-row and feasible-coordinate conclusions can be consumed
together once the two concrete pool facts have been established. -/
theorem roughCanonicalRawRowCorrection_exact_and_feasible
    {W n h K y : ℕ} {alpha beta L margin : ℝ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hpool :
      (roughCanonicalBroadCorrectionPool W n h K y row.1).Nonempty)
    (halpha : 0 ≤ alpha ∧ alpha ≤ 1)
    (hbeta : 0 ≤ beta / L ∧ beta / L ≤ 1)
    (hmarginLower : margin ≤ beta / L)
    (hmarginUpper : margin ≤ 1 - beta / L)
    (hdensity :
      |bankPaperConstantPoolCorrectionDensity
        (completeRoughRowFiber y (roughRawCandidateSet n h K) row.1)
        (roughCanonicalBroadCorrectionPool W n h K y row.1)
        (roughHeadCompatibleRawWeight W n h K alpha beta L)
        (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ)| ≤ margin) :
    (∑ a ∈ completeRoughRowFiber y
        (roughRawCandidateSet n h K) row.1,
      roughCanonicalRawRowCorrectedWeight
        W n h K y row.1 alpha beta L a =
      (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ)) ∧
      ∀ a ∈ completeRoughRowFiber y
          (roughRawCandidateSet n h K) row.1,
        0 ≤ roughCanonicalRawRowCorrectedWeight
            W n h K y row.1 alpha beta L a ∧
          roughCanonicalRawRowCorrectedWeight
            W n h K y row.1 alpha beta L a ≤ 1 := by
  constructor
  · exact sum_roughCanonicalRawRowCorrectedWeight_eq_upperTarget
      W n h K y alpha beta L row hpool
  · intro a ha
    exact roughCanonicalRawRowCorrectedWeight_mem_unitInterval row
      halpha hbeta hmarginLower hmarginUpper hdensity ha

/-! ## Assembly over all attained complete rough rows -/

/-- Apply the literal constant-pool correction belonging to the complete
rough row of `a`.  This is an explicit global fractional selector, not an
existential handoff. -/
def roughCanonicalRawCorrectedSelector
    (W n h K y : ℕ) (alpha beta L : ℝ) (a : ℕ) : ℝ :=
  roughCanonicalRawRowCorrectedWeight W n h K y
    (completeRoughLabel y a) alpha beta L a

/-- On a specified row fiber, the global selector is definitionally the
single-row correction with that row's label. -/
theorem roughCanonicalRawCorrectedSelector_eq_rowCorrected_of_mem
    {W n h K y label a : ℕ} {alpha beta L : ℝ}
    (ha : a ∈ completeRoughRowFiber y
      (roughRawCandidateSet n h K) label) :
    roughCanonicalRawCorrectedSelector W n h K y alpha beta L a =
      roughCanonicalRawRowCorrectedWeight
        W n h K y label alpha beta L a := by
  rw [roughCanonicalRawCorrectedSelector,
    completeRoughLabel_eq_of_mem_rowFiber ha]

/-- Every attained row with a nonempty broad correction pool has exactly
its literal upper-row target under the explicit global selector. -/
theorem sum_roughCanonicalRawCorrectedSelector_eq_upperTarget
    (W n h K y : ℕ) (alpha beta L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hpool :
      (roughCanonicalBroadCorrectionPool W n h K y row.1).Nonempty) :
    ∑ a ∈ completeRoughRowFiber y
        (roughRawCandidateSet n h K) row.1,
      roughCanonicalRawCorrectedSelector W n h K y alpha beta L a =
      (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) := by
  calc
    ∑ a ∈ completeRoughRowFiber y
        (roughRawCandidateSet n h K) row.1,
      roughCanonicalRawCorrectedSelector W n h K y alpha beta L a =
        ∑ a ∈ completeRoughRowFiber y
            (roughRawCandidateSet n h K) row.1,
          roughCanonicalRawRowCorrectedWeight
            W n h K y row.1 alpha beta L a := by
      apply Finset.sum_congr rfl
      intro a ha
      exact
        roughCanonicalRawCorrectedSelector_eq_rowCorrected_of_mem ha
    _ = (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) :=
      sum_roughCanonicalRawRowCorrectedWeight_eq_upperTarget
        W n h K y alpha beta L row hpool

/-- Quantitative rowwise density bounds prove pointwise feasibility of the
explicit global selector on the entire raw candidate set. -/
theorem roughCanonicalRawCorrectedSelector_mem_unitInterval
    {W n h K y : ℕ} {alpha beta L margin : ℝ}
    (halpha : 0 ≤ alpha ∧ alpha ≤ 1)
    (hbeta : 0 ≤ beta / L ∧ beta / L ≤ 1)
    (hmarginLower : margin ≤ beta / L)
    (hmarginUpper : margin ≤ 1 - beta / L)
    (hdensity : ∀ row : CanonicalCompleteRoughRow y
        (roughRawCandidateSet n h K),
      |bankPaperConstantPoolCorrectionDensity
        (completeRoughRowFiber y (roughRawCandidateSet n h K) row.1)
        (roughCanonicalBroadCorrectionPool W n h K y row.1)
        (roughHeadCompatibleRawWeight W n h K alpha beta L)
        (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ)| ≤ margin)
    {a : ℕ} (ha : a ∈ roughRawCandidateSet n h K) :
    0 ≤ roughCanonicalRawCorrectedSelector
        W n h K y alpha beta L a ∧
      roughCanonicalRawCorrectedSelector
        W n h K y alpha beta L a ≤ 1 := by
  let row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K) :=
    ⟨completeRoughLabel y a,
      mem_completeRoughLabelSet.mpr ⟨a, ha, rfl⟩⟩
  have haRow : a ∈ completeRoughRowFiber y
      (roughRawCandidateSet n h K) row.1 := by
    exact mem_completeRoughRowFiber.mpr ⟨ha, rfl⟩
  have hrowFeasible :=
    roughCanonicalRawRowCorrectedWeight_mem_unitInterval row
      halpha hbeta hmarginLower hmarginUpper (hdensity row) haRow
  rw [roughCanonicalRawCorrectedSelector_eq_rowCorrected_of_mem
    (W := W) (alpha := alpha) (beta := beta) (L := L) haRow]
  exact hrowFeasible

/-- Hence nonempty correction pools on all attained rows give literal
integer row sums for the explicit global selector. -/
theorem roughCanonicalRawCorrectedSelector_rowSums_integer
    {W n h K y : ℕ} {alpha beta L : ℝ}
    (hpools : ∀ row : CanonicalCompleteRoughRow y
        (roughRawCandidateSet n h K),
      (roughCanonicalBroadCorrectionPool W n h K y row.1).Nonempty) :
    ∀ label ∈ completeRoughLabelSet y (roughRawCandidateSet n h K),
      ∃ k : ℤ,
        ∑ a ∈ completeRoughRowFiber y
            (roughRawCandidateSet n h K) label,
          roughCanonicalRawCorrectedSelector
            W n h K y alpha beta L a = (k : ℝ) := by
  intro label hlabel
  let row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K) := ⟨label, hlabel⟩
  refine ⟨(roughUpperCompleteRoughRowTarget n h y label : ℤ), ?_⟩
  have hsum := sum_roughCanonicalRawCorrectedSelector_eq_upperTarget
    W n h K y alpha beta L row (hpools row)
  have hsum' :
      ∑ a ∈ completeRoughRowFiber y
          (roughRawCandidateSet n h K) label,
        roughCanonicalRawCorrectedSelector
          W n h K y alpha beta L a =
        (roughUpperCompleteRoughRowTarget n h y label : ℝ) := by
    simpa only [row] using hsum
  have hcast :
      (((roughUpperCompleteRoughRowTarget n h y label : ℕ) : ℤ) : ℝ) =
        (roughUpperCompleteRoughRowTarget n h y label : ℝ) := by
    norm_num
  exact hsum'.trans hcast.symm

/-- Honest finite selector package obtained from the row quotas.  It proves
only feasibility and exact complete-row integrality; it deliberately makes
no claim about head moments, ordinary logarithm, prime-band balance,
pointwise prime residuals, or ratio-cell prefix residuals. -/
theorem roughCanonicalRawCorrectedSelector_finiteState
    {W n h K y : ℕ} {alpha beta L margin : ℝ}
    (hpools : ∀ row : CanonicalCompleteRoughRow y
        (roughRawCandidateSet n h K),
      (roughCanonicalBroadCorrectionPool W n h K y row.1).Nonempty)
    (halpha : 0 ≤ alpha ∧ alpha ≤ 1)
    (hbeta : 0 ≤ beta / L ∧ beta / L ≤ 1)
    (hmarginLower : margin ≤ beta / L)
    (hmarginUpper : margin ≤ 1 - beta / L)
    (hdensity : ∀ row : CanonicalCompleteRoughRow y
        (roughRawCandidateSet n h K),
      |bankPaperConstantPoolCorrectionDensity
        (completeRoughRowFiber y (roughRawCandidateSet n h K) row.1)
        (roughCanonicalBroadCorrectionPool W n h K y row.1)
        (roughHeadCompatibleRawWeight W n h K alpha beta L)
        (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ)| ≤ margin) :
    (∀ a ∈ roughRawCandidateSet n h K,
      0 ≤ roughCanonicalRawCorrectedSelector
          W n h K y alpha beta L a ∧
        roughCanonicalRawCorrectedSelector
          W n h K y alpha beta L a ≤ 1) ∧
      (∀ label ∈ completeRoughLabelSet y
          (roughRawCandidateSet n h K),
        ∃ k : ℤ,
          ∑ a ∈ completeRoughRowFiber y
              (roughRawCandidateSet n h K) label,
            roughCanonicalRawCorrectedSelector
              W n h K y alpha beta L a = (k : ℝ)) ∧
      ∀ row : CanonicalCompleteRoughRow y
          (roughRawCandidateSet n h K),
        ∑ a ∈ completeRoughRowFiber y
            (roughRawCandidateSet n h K) row.1,
          roughCanonicalRawCorrectedSelector
            W n h K y alpha beta L a =
          (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    exact roughCanonicalRawCorrectedSelector_mem_unitInterval
      halpha hbeta hmarginLower hmarginUpper hdensity ha
  · exact roughCanonicalRawCorrectedSelector_rowSums_integer hpools
  · intro row
    exact sum_roughCanonicalRawCorrectedSelector_eq_upperTarget
      W n h K y alpha beta L row (hpools row)

/-! ## Unconditional capped-quota selector -/

/-- The largest part of the literal upper-row quota that can be placed in
the raw lower row without any arithmetic capacity theorem. -/
def roughCanonicalCappedUpperQuota
    (n h K y label : ℕ) : ℕ :=
  min (roughUpperCompleteRoughRowTarget n h y label)
    (completeRoughRowFiber y
      (roughRawCandidateSet n h K) label).card

/-- An unconditional row-constant selector carrying the capped quota.  It
is zero off the literal raw candidate set. -/
def roughCanonicalCappedUpperQuotaSelector
    (n h K y : ℕ) (a : ℕ) : ℝ :=
  if a ∈ roughRawCandidateSet n h K then
    (roughCanonicalCappedUpperQuota n h K y
        (completeRoughLabel y a) : ℝ) /
      ((completeRoughRowFiber y (roughRawCandidateSet n h K)
        (completeRoughLabel y a)).card : ℝ)
  else 0

@[simp]
theorem roughCanonicalCappedUpperQuotaSelector_apply_of_mem
    {n h K y a : ℕ} (ha : a ∈ roughRawCandidateSet n h K) :
    roughCanonicalCappedUpperQuotaSelector n h K y a =
      (roughCanonicalCappedUpperQuota n h K y
          (completeRoughLabel y a) : ℝ) /
        ((completeRoughRowFiber y (roughRawCandidateSet n h K)
          (completeRoughLabel y a)).card : ℝ) := by
  simp [roughCanonicalCappedUpperQuotaSelector, ha]

@[simp]
theorem roughCanonicalCappedUpperQuotaSelector_apply_of_not_mem
    {n h K y a : ℕ} (ha : a ∉ roughRawCandidateSet n h K) :
    roughCanonicalCappedUpperQuotaSelector n h K y a = 0 := by
  simp [roughCanonicalCappedUpperQuotaSelector, ha]

/-- Feasibility of the capped selector is unconditional: the cap is no
larger than the cardinality of its attained row. -/
theorem roughCanonicalCappedUpperQuotaSelector_mem_unitInterval
    {n h K y a : ℕ} (ha : a ∈ roughRawCandidateSet n h K) :
    0 ≤ roughCanonicalCappedUpperQuotaSelector n h K y a ∧
      roughCanonicalCappedUpperQuotaSelector n h K y a ≤ 1 := by
  rw [roughCanonicalCappedUpperQuotaSelector_apply_of_mem ha]
  have haFiber : a ∈ completeRoughRowFiber y
      (roughRawCandidateSet n h K) (completeRoughLabel y a) :=
    mem_completeRoughRowFiber.mpr ⟨ha, rfl⟩
  have hcardPos : 0 < (completeRoughRowFiber y
      (roughRawCandidateSet n h K) (completeRoughLabel y a)).card :=
    Finset.card_pos.mpr ⟨a, haFiber⟩
  have hdenPos : (0 : ℝ) < (completeRoughRowFiber y
      (roughRawCandidateSet n h K)
      (completeRoughLabel y a)).card := by
    exact_mod_cast hcardPos
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hdenPos.le
  · apply (div_le_iff₀ hdenPos).2
    simp only [one_mul, roughCanonicalCappedUpperQuota]
    exact_mod_cast (Nat.min_le_right
      (roughUpperCompleteRoughRowTarget n h y
        (completeRoughLabel y a))
      (completeRoughRowFiber y (roughRawCandidateSet n h K)
        (completeRoughLabel y a)).card)

/-- Every attained row sum is exactly its capped natural-number quota. -/
theorem sum_roughCanonicalCappedUpperQuotaSelector_eq_cappedQuota
    (n h K y : ℕ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) :
    ∑ a ∈ completeRoughRowFiber y
        (roughRawCandidateSet n h K) row.1,
      roughCanonicalCappedUpperQuotaSelector n h K y a =
      (roughCanonicalCappedUpperQuota n h K y row.1 : ℝ) := by
  have hrowNonempty : (completeRoughRowFiber y
      (roughRawCandidateSet n h K) row.1).Nonempty :=
    mem_completeRoughLabelSet_iff_rowFiber_nonempty.mp row.2
  have hcardNat : (completeRoughRowFiber y
      (roughRawCandidateSet n h K) row.1).card ≠ 0 :=
    Finset.card_ne_zero.mpr hrowNonempty
  have hcardReal : ((completeRoughRowFiber y
      (roughRawCandidateSet n h K) row.1).card : ℝ) ≠ 0 := by
    exact_mod_cast hcardNat
  calc
    ∑ a ∈ completeRoughRowFiber y
        (roughRawCandidateSet n h K) row.1,
      roughCanonicalCappedUpperQuotaSelector n h K y a =
        ∑ _a ∈ completeRoughRowFiber y
            (roughRawCandidateSet n h K) row.1,
          (roughCanonicalCappedUpperQuota n h K y row.1 : ℝ) /
            ((completeRoughRowFiber y
              (roughRawCandidateSet n h K) row.1).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [roughCanonicalCappedUpperQuotaSelector_apply_of_mem
        ((completeRoughRowFiber_subset y
          (roughRawCandidateSet n h K) row.1) ha)]
      rw [completeRoughLabel_eq_of_mem_rowFiber ha]
    _ = ((completeRoughRowFiber y
          (roughRawCandidateSet n h K) row.1).card : ℝ) *
        ((roughCanonicalCappedUpperQuota n h K y row.1 : ℝ) /
          ((completeRoughRowFiber y
            (roughRawCandidateSet n h K) row.1).card : ℝ)) := by
      simp
    _ = (roughCanonicalCappedUpperQuota n h K y row.1 : ℝ) := by
      rw [mul_comm, div_mul_cancel₀ _ hcardReal]

/-- The capped selector therefore has integer sum on every complete rough
row, with no premise at all. -/
theorem roughCanonicalCappedUpperQuotaSelector_rowSums_integer
    (n h K y : ℕ) :
    ∀ label ∈ completeRoughLabelSet y (roughRawCandidateSet n h K),
      ∃ k : ℤ,
        ∑ a ∈ completeRoughRowFiber y
            (roughRawCandidateSet n h K) label,
          roughCanonicalCappedUpperQuotaSelector n h K y a = (k : ℝ) := by
  intro label hlabel
  let row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K) := ⟨label, hlabel⟩
  refine ⟨(roughCanonicalCappedUpperQuota n h K y label : ℤ), ?_⟩
  have hsum :=
    sum_roughCanonicalCappedUpperQuotaSelector_eq_cappedQuota
      n h K y row
  have hsum' :
      ∑ a ∈ completeRoughRowFiber y
          (roughRawCandidateSet n h K) label,
        roughCanonicalCappedUpperQuotaSelector n h K y a =
        (roughCanonicalCappedUpperQuota n h K y label : ℝ) := by
    simpa only [row] using hsum
  have hcast :
      (((roughCanonicalCappedUpperQuota n h K y label : ℕ) : ℤ) : ℝ) =
        (roughCanonicalCappedUpperQuota n h K y label : ℝ) := by
    norm_num
  exact hsum'.trans hcast.symm

/-- The cap disappears exactly when the literal lower row has the required
upper-quota capacity. -/
theorem roughCanonicalCappedUpperQuota_eq_upperTarget_of_capacity
    {n h K y label : ℕ}
    (hcapacity : roughUpperCompleteRoughRowTarget n h y label ≤
      (completeRoughRowFiber y
        (roughRawCandidateSet n h K) label).card) :
    roughCanonicalCappedUpperQuota n h K y label =
      roughUpperCompleteRoughRowTarget n h y label := by
  exact Nat.min_eq_left hcapacity

/-- Under the concrete row-capacity inequality, the unconditional selector
already realizes the uncapped paper quota. -/
theorem sum_roughCanonicalCappedUpperQuotaSelector_eq_upperTarget_of_capacity
    (n h K y : ℕ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hcapacity : roughUpperCompleteRoughRowTarget n h y row.1 ≤
      (completeRoughRowFiber y
        (roughRawCandidateSet n h K) row.1).card) :
    ∑ a ∈ completeRoughRowFiber y
        (roughRawCandidateSet n h K) row.1,
      roughCanonicalCappedUpperQuotaSelector n h K y a =
      (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) := by
  rw [sum_roughCanonicalCappedUpperQuotaSelector_eq_cappedQuota,
    roughCanonicalCappedUpperQuota_eq_upperTarget_of_capacity hcapacity]

/-- Smallest unconditional finite selector state available from the current
quota and row-cardinality APIs.  The third component displays the cap, so it
cannot be mistaken for the still-missing arithmetic capacity theorem. -/
theorem roughCanonicalCappedUpperQuotaSelector_finiteState
    (n h K y : ℕ) :
    (∀ a ∈ roughRawCandidateSet n h K,
      0 ≤ roughCanonicalCappedUpperQuotaSelector n h K y a ∧
        roughCanonicalCappedUpperQuotaSelector n h K y a ≤ 1) ∧
      (∀ label ∈ completeRoughLabelSet y
          (roughRawCandidateSet n h K),
        ∃ k : ℤ,
          ∑ a ∈ completeRoughRowFiber y
              (roughRawCandidateSet n h K) label,
            roughCanonicalCappedUpperQuotaSelector n h K y a = (k : ℝ)) ∧
      ∀ row : CanonicalCompleteRoughRow y
          (roughRawCandidateSet n h K),
        ∑ a ∈ completeRoughRowFiber y
            (roughRawCandidateSet n h K) row.1,
          roughCanonicalCappedUpperQuotaSelector n h K y a =
          ((min (roughUpperCompleteRoughRowTarget n h y row.1)
            (completeRoughRowFiber y
              (roughRawCandidateSet n h K) row.1).card : ℕ) : ℝ) := by
  refine ⟨?_, roughCanonicalCappedUpperQuotaSelector_rowSums_integer
    n h K y, ?_⟩
  · intro a ha
    exact roughCanonicalCappedUpperQuotaSelector_mem_unitInterval ha
  · intro row
    simpa only [roughCanonicalCappedUpperQuota] using
      sum_roughCanonicalCappedUpperQuotaSelector_eq_cappedQuota
        n h K y row

end

end Erdos390.WholePaper
