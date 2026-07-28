import Erdos390.Full.ContinuumSharpArithmeticTransfer
import Erdos390.Full.ContinuumCellGraphReversible
import Erdos390.Full.ContinuumRawLowRow

/-!
# Low--high geometry for the ordinary continuum inverse

The ordinary inverse cannot be obtained from the sharp inverse by dividing
by the least cell centre: the centre of the moving low cell tends to zero.
This file instead records the exact estimates used after splitting a finite
continuum mesh into an arbitrary low block and a high block.  The product
kernel bound makes every edge entering a low cell proportional to both the
ordinary length and the centre of that cell.  Consequently all constants
below depend on the total low length, not on the number of low cells or on
their least endpoint.

No inverse, coercivity, or convergence statement is assumed here.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph
namespace IntervalMesh

open ConditionedPoissonLimit
open FiniteGraphQuotientInverse

variable {Band Low High : Type*}
  [Fintype Band] [Fintype Low]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

/-- Relabel the continuum sharp edge along a low--high decomposition. -/
def splitSharpEdge (e : Sum Low High ≃ Band)
    (x y : Sum Low High) : ℝ :=
  M.sharpKernelEdge (e x) (e y)

/-- Relabel a band vector along a low--high decomposition. -/
def splitVector (e : Sum Low High ≃ Band) (x : Band → ℝ) :
    Sum Low High → ℝ := fun i ↦ x (e i)

/-- Relabelled sharp-gauge weight `H_i alpha_i^2`. -/
def splitSharpWeight (e : Sum Low High ≃ Band)
    (x : Sum Low High) : ℝ :=
  M.harmonicMass (e x) * M.center (e x) ^ 2

section Anchor

variable [DecidableEq Band]

/-- Interior anchor measure after restricting the relabelled graph to the
high block. -/
def splitHighAnchor (e : Sum Low High ≃ Band) (j : High) : ℝ :=
  M.anchor (e (.inr j))

omit [Fintype Low] in
/-- The high induced graph sees exactly the same fixed interior anchor. -/
theorem gap_mul_splitHighAnchor_le_highEdge
    (e : Sum Low High ≃ Band) {kappa : ℝ}
    (hgap : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc epsilon (1 - epsilon),
        kappa ≤ -covarianceKernelQuotient t s)
    (i j : High) :
    kappa * splitHighAnchor M e j ≤
      M.splitSharpEdge e (.inr i) (.inr j) := by
  exact M.gap_mul_anchor_le_sharpKernelEdge hgap
    (e (.inr i)) (e (.inr j))

omit [Fintype Low] in
/-- The sharp gauge weight of the high block is bounded below by its anchor
length times the least high centre.  This estimate is independent of the
number of low cells. -/
theorem amin_mul_highAnchor_le_highSharpWeight
    [Fintype High]
    (e : Sum Low High ≃ Band) {amin : ℝ}
    (hAmin : 0 ≤ amin)
    (hHighCenter : ∀ i : High, amin ≤ M.center (e (.inr i))) :
    amin * (∑ i : High, splitHighAnchor M e i) ≤
      ∑ i : High,
        M.harmonicMass (e (.inr i)) * M.center (e (.inr i)) ^ 2 := by
  have hAnchorLe (i : High) :
      splitHighAnchor M e i ≤ M.length (e (.inr i)) := by
    unfold splitHighAnchor anchor
    split_ifs
    · exact le_rfl
    · exact (M.length_pos _).le
  calc
    amin * (∑ i : High, splitHighAnchor M e i) =
        ∑ i : High, amin * splitHighAnchor M e i := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i : High, amin * M.length (e (.inr i)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hAnchorLe i) hAmin
    _ ≤ ∑ i : High,
        M.length (e (.inr i)) * M.center (e (.inr i)) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        amin * M.length (e (.inr i)) =
            M.length (e (.inr i)) * amin := by ring
        _ ≤ M.length (e (.inr i)) * M.center (e (.inr i)) :=
          mul_le_mul_of_nonneg_left (hHighCenter i) (M.length_pos _).le
    _ = ∑ i : High,
        M.harmonicMass (e (.inr i)) * M.center (e (.inr i)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (M.harmonicMass_mul_center_sq_eq (e (.inr i))).symm

omit [Fintype Low] in
/-- A positive uniform anchor floor makes the total high sharp weight
strictly positive. -/
theorem highSharpWeight_pos_of_anchorFloor
    [Fintype High]
    (e : Sum Low High ≃ Band) {amin anchorFloor : ℝ}
    (hAmin : 0 < amin) (hAnchorFloor : 0 < anchorFloor)
    (hHighCenter : ∀ i : High, amin ≤ M.center (e (.inr i)))
    (hAnchor : anchorFloor ≤ ∑ i : High, splitHighAnchor M e i) :
    0 < ∑ i : High, splitSharpWeight M e (.inr i) := by
  have hlower := M.amin_mul_highAnchor_le_highSharpWeight e hAmin.le
    hHighCenter
  have hpositive : 0 < amin * anchorFloor := mul_pos hAmin hAnchorFloor
  have hfirst : amin * anchorFloor ≤
      amin * (∑ i : High, splitHighAnchor M e i) :=
    mul_le_mul_of_nonneg_left hAnchor hAmin.le
  exact hpositive.trans_le (hfirst.trans (by
    simpa only [splitSharpWeight] using hlower))

/-- The low contribution to the exact sharp gauge is controlled by the low
raw-coordinate budget and the high anchor floor.  The identity
`H_i alpha_i^2 q_i = length_i (alpha_i q_i)` is exact. -/
theorem abs_lowSharpGaugeSum_le
    [Fintype High]
    (e : Sum Low High ≃ Band)
    {amin anchorFloor lowLength gaugeRatio lowBudget : ℝ}
    (hAmin : 0 < amin)
    (hGaugeRatio : 0 ≤ gaugeRatio) (hLowBudgetNonneg : 0 ≤ lowBudget)
    (hHighCenter : ∀ i : High, amin ≤ M.center (e (.inr i)))
    (hAnchor : anchorFloor ≤ ∑ i : High, splitHighAnchor M e i)
    (hLowLength : ∑ l : Low, M.length (e (.inl l)) ≤ lowLength)
    (hRatio : lowLength ≤ gaugeRatio * (amin * anchorFloor))
    (q : Sum Low High → ℝ)
    (hLowBudget : ∀ l : Low,
      |M.center (e (.inl l)) * q (.inl l)| ≤ lowBudget) :
    |∑ l : Low, splitSharpWeight M e (.inl l) * q (.inl l)| ≤
      gaugeRatio * (∑ i : High, splitSharpWeight M e (.inr i)) *
        lowBudget := by
  have hlengthNonneg (l : Low) : 0 ≤ M.length (e (.inl l)) :=
    (M.length_pos _).le
  have hhighLower := M.amin_mul_highAnchor_le_highSharpWeight e hAmin.le
    hHighCenter
  have hanchorScaled : amin * anchorFloor ≤
      ∑ i : High, splitSharpWeight M e (.inr i) := by
    calc
      amin * anchorFloor ≤
          amin * (∑ i : High, splitHighAnchor M e i) :=
        mul_le_mul_of_nonneg_left hAnchor hAmin.le
      _ ≤ ∑ i : High, splitSharpWeight M e (.inr i) := by
        simpa only [splitSharpWeight] using hhighLower
  have hratioHigh : lowLength ≤
      gaugeRatio * (∑ i : High, splitSharpWeight M e (.inr i)) :=
    hRatio.trans (mul_le_mul_of_nonneg_left hanchorScaled hGaugeRatio)
  have hterm (l : Low) :
      |splitSharpWeight M e (.inl l) * q (.inl l)| ≤
        M.length (e (.inl l)) * lowBudget := by
    rw [splitSharpWeight,
      M.harmonicMass_mul_center_sq_eq (e (.inl l))]
    calc
      |(M.length (e (.inl l)) * M.center (e (.inl l))) * q (.inl l)| =
          M.length (e (.inl l)) *
            |M.center (e (.inl l)) * q (.inl l)| := by
        simp only [abs_mul, abs_of_pos (M.length_pos (e (.inl l))),
          abs_of_pos (M.center_pos (e (.inl l)))]
        ring
      _ ≤ M.length (e (.inl l)) * lowBudget :=
        mul_le_mul_of_nonneg_left (hLowBudget l) (hlengthNonneg l)
  calc
    |∑ l : Low, splitSharpWeight M e (.inl l) * q (.inl l)| ≤
        ∑ l : Low, |splitSharpWeight M e (.inl l) * q (.inl l)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l : Low, M.length (e (.inl l)) * lowBudget :=
      Finset.sum_le_sum fun l hl ↦ hterm l
    _ = (∑ l : Low, M.length (e (.inl l))) * lowBudget := by
      rw [Finset.sum_mul]
    _ ≤ lowLength * lowBudget :=
      mul_le_mul_of_nonneg_right hLowLength hLowBudgetNonneg
    _ ≤ (gaugeRatio *
          (∑ i : High, splitSharpWeight M e (.inr i))) * lowBudget :=
      mul_le_mul_of_nonneg_right hratioHigh hLowBudgetNonneg
    _ = gaugeRatio *
        (∑ i : High, splitSharpWeight M e (.inr i)) * lowBudget := by ring

end Anchor

/-- The product-kernel estimate gives the sharper edge bound needed for an
arbitrarily refined low block.  The usual bounded-quotient estimate only
gives `O(length j)`; here the additional factor `center j` is essential. -/
theorem sharpKernelEdge_le_productCenterLength_of_cell
    {C : ℝ}
    (hCell : ∀ i j,
      |M.normalizedKernelCell i j| ≤ C * M.center i * M.length j)
    (i j : Band) :
    M.sharpKernelEdge i j ≤ C * M.center j * M.length j := by
  have hi : 0 < M.center i := M.center_pos i
  have hj : 0 < M.center j := M.center_pos j
  have hcell := hCell i j
  have hedge := M.sharpKernelEdge_eq_normalizedKernelCell i j
  have hedgeAbs : M.sharpKernelEdge i j =
      |M.normalizedKernelCell i j| * (M.center j / M.center i) := by
    calc
      M.sharpKernelEdge i j = |M.sharpKernelEdge i j| :=
        (abs_of_nonneg (M.sharpKernelEdge_nonneg i j)).symm
      _ = |-M.normalizedKernelCell i j *
          (M.center j / M.center i)| := by rw [← hedge]
      _ = |M.normalizedKernelCell i j| *
          (M.center j / M.center i) := by
        rw [abs_mul, abs_neg, abs_of_pos (div_pos hj hi)]
  rw [hedgeAbs]
  calc
    |M.normalizedKernelCell i j| * (M.center j / M.center i) ≤
        (C * M.center i * M.length j) *
          (M.center j / M.center i) :=
      mul_le_mul_of_nonneg_right hcell (div_pos hj hi).le
    _ = C * M.center j * M.length j := by
      field_simp [ne_of_gt hi]

/-- Kernel-level form of the preceding edge estimate. -/
theorem sharpKernelEdge_le_productCenterLength
    {C : ℝ}
    (hKernel : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel s t| ≤ C * s * t)
    (i j : Band) :
    M.sharpKernelEdge i j ≤ C * M.center j * M.length j := by
  exact M.sharpKernelEdge_le_productCenterLength_of_cell
    (M.abs_normalizedKernelCell_le_center_mul_length hKernel) i j

/-- Sum of all sharp edges from one output row into the low block. -/
theorem sum_splitSharpEdge_low_le
    (e : Sum Low High ≃ Band)
    {C lowCenter lowLength : ℝ}
    (hC : 0 ≤ C) (hLowCenterNonneg : 0 ≤ lowCenter)
    (hCell : ∀ i j,
      |M.normalizedKernelCell i j| ≤ C * M.center i * M.length j)
    (hLowCenter : ∀ l : Low, M.center (e (.inl l)) ≤ lowCenter)
    (hLowLength : ∑ l : Low, M.length (e (.inl l)) ≤ lowLength)
    (i : High) :
    ∑ l : Low, M.splitSharpEdge e (.inr i) (.inl l) ≤
      C * lowCenter * lowLength := by
  have hlengthNonneg : ∀ l : Low, 0 ≤ M.length (e (.inl l)) :=
    fun l ↦ (M.length_pos (e (.inl l))).le
  calc
    ∑ l : Low, M.splitSharpEdge e (.inr i) (.inl l) ≤
        ∑ l : Low,
          C * M.center (e (.inl l)) * M.length (e (.inl l)) := by
      apply Finset.sum_le_sum
      intro l hl
      exact M.sharpKernelEdge_le_productCenterLength_of_cell hCell
        (e (.inr i)) (e (.inl l))
    _ ≤ ∑ l : Low, C * lowCenter * M.length (e (.inl l)) := by
      apply Finset.sum_le_sum
      intro l hl
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hLowCenter l) hC)
        (hlengthNonneg l)
    _ = (C * lowCenter) *
        (∑ l : Low, M.length (e (.inl l))) := by
      rw [Finset.mul_sum]
    _ ≤ (C * lowCenter) * lowLength :=
      mul_le_mul_of_nonneg_left hLowLength
        (mul_nonneg hC hLowCenterNonneg)
    _ = C * lowCenter * lowLength := by ring

/-- Exact cross-row estimate from one high cell into all low cells.  The
first term uses the full raw supremum bound, while the second uses the
already established low-coordinate budget. -/
theorem abs_splitSharpEdge_cross_low_le
    (e : Sum Low High ≃ Band)
    {C lowCenter lowLength amin B lowBudget : ℝ}
    (hC : 0 ≤ C) (hLowCenterNonneg : 0 ≤ lowCenter)
    (hBNonneg : 0 ≤ B) (hLowBudgetNonneg : 0 ≤ lowBudget)
    (hCell : ∀ i j,
      |M.normalizedKernelCell i j| ≤ C * M.center i * M.length j)
    (hLowCenter : ∀ l : Low, M.center (e (.inl l)) ≤ lowCenter)
    (hLowLength : ∑ l : Low, M.length (e (.inl l)) ≤ lowLength)
    (hAmin : 0 < amin)
    (hHighCenter : ∀ i : High, amin ≤ M.center (e (.inr i)))
    (q : Sum Low High → ℝ)
    (hB : ∀ x, |M.center (e x) * q x| ≤ B)
    (hLowBudget : ∀ l : Low,
      |M.center (e (.inl l)) * q (.inl l)| ≤ lowBudget)
    (i : High) :
    |∑ l : Low, M.splitSharpEdge e (.inr i) (.inl l) *
        (q (.inr i) - q (.inl l))| ≤
      (C * lowCenter * lowLength) * B / amin +
        (C * lowLength) * lowBudget := by
  have hi : 0 < M.center (e (.inr i)) := M.center_pos _
  have hiLower : amin ≤ M.center (e (.inr i)) := hHighCenter i
  have hqi : |q (.inr i)| ≤ B / amin := by
    have hscaled : |q (.inr i)| ≤ B / M.center (e (.inr i)) := by
      apply (le_div_iff₀ hi).2
      rw [← abs_of_pos hi, ← abs_mul]
      simpa only [mul_comm] using hB (.inr i)
    exact hscaled.trans
      (div_le_div_of_nonneg_left hBNonneg hAmin hiLower)
  have hedgeNonneg (l : Low) :
      0 ≤ M.splitSharpEdge e (.inr i) (.inl l) :=
    M.sharpKernelEdge_nonneg _ _
  have hedgeBound (l : Low) :
      M.splitSharpEdge e (.inr i) (.inl l) ≤
        C * M.center (e (.inl l)) * M.length (e (.inl l)) :=
    M.sharpKernelEdge_le_productCenterLength_of_cell hCell _ _
  have hlowTerm (l : Low) :
      M.splitSharpEdge e (.inr i) (.inl l) * |q (.inl l)| ≤
        C * M.length (e (.inl l)) * lowBudget := by
    have hlength : 0 ≤ M.length (e (.inl l)) := (M.length_pos _).le
    have hcenter : 0 < M.center (e (.inl l)) := M.center_pos _
    calc
      M.splitSharpEdge e (.inr i) (.inl l) * |q (.inl l)| ≤
          (C * M.center (e (.inl l)) * M.length (e (.inl l))) *
            |q (.inl l)| :=
        mul_le_mul_of_nonneg_right (hedgeBound l) (abs_nonneg _)
      _ = C * M.length (e (.inl l)) *
          |M.center (e (.inl l)) * q (.inl l)| := by
        rw [abs_mul, abs_of_pos hcenter]
        ring
      _ ≤ C * M.length (e (.inl l)) * lowBudget :=
        mul_le_mul_of_nonneg_left (hLowBudget l)
          (mul_nonneg hC hlength)
  have hterm (l : Low) :
      |M.splitSharpEdge e (.inr i) (.inl l) *
          (q (.inr i) - q (.inl l))| ≤
        M.splitSharpEdge e (.inr i) (.inl l) * (B / amin) +
          C * M.length (e (.inl l)) * lowBudget := by
    rw [abs_mul, abs_of_nonneg (hedgeNonneg l)]
    calc
      M.splitSharpEdge e (.inr i) (.inl l) *
          |q (.inr i) - q (.inl l)| ≤
        M.splitSharpEdge e (.inr i) (.inl l) *
          (|q (.inr i)| + |q (.inl l)|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (hedgeNonneg l)
      _ = M.splitSharpEdge e (.inr i) (.inl l) * |q (.inr i)| +
          M.splitSharpEdge e (.inr i) (.inl l) * |q (.inl l)| := by
        ring
      _ ≤ M.splitSharpEdge e (.inr i) (.inl l) * (B / amin) +
          C * M.length (e (.inl l)) * lowBudget :=
        add_le_add
          (mul_le_mul_of_nonneg_left hqi (hedgeNonneg l)) (hlowTerm l)
  have hedgeSum := M.sum_splitSharpEdge_low_le e hC hLowCenterNonneg
    hCell hLowCenter hLowLength i
  have hedgeSumNonneg :
      0 ≤ ∑ l : Low, M.splitSharpEdge e (.inr i) (.inl l) :=
    Finset.sum_nonneg fun l hl ↦ hedgeNonneg l
  calc
    |∑ l : Low, M.splitSharpEdge e (.inr i) (.inl l) *
        (q (.inr i) - q (.inl l))| ≤
      ∑ l : Low, |M.splitSharpEdge e (.inr i) (.inl l) *
        (q (.inr i) - q (.inl l))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l : Low,
        (M.splitSharpEdge e (.inr i) (.inl l) * (B / amin) +
          C * M.length (e (.inl l)) * lowBudget) :=
      Finset.sum_le_sum fun l hl ↦ hterm l
    _ = (∑ l : Low, M.splitSharpEdge e (.inr i) (.inl l)) *
          (B / amin) +
        (C * (∑ l : Low, M.length (e (.inl l)))) * lowBudget := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        ← Finset.mul_sum]
    _ ≤ (C * lowCenter * lowLength) * (B / amin) +
        (C * lowLength) * lowBudget := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hedgeSum
          (div_nonneg hBNonneg hAmin.le)
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLowLength hC) hLowBudgetNonneg
    _ = (C * lowCenter * lowLength) * B / amin +
        (C * lowLength) * lowBudget := by ring

end IntervalMesh
end Erdos390.Full.ContinuumCellGraph
