import Erdos390.Full.PoissonDickmanWeightedInverse
import Erdos390.Full.FiniteGraphStableInverse

/-!
# Continuum cell compression as a finite graph

This is the mesh-uniform bridge from the weighted Poisson--Dickman operator
to a finite matrix.  Every row is the ordinary-cell average of the graph
kernel `-K(t,s)/s`.  A fixed collection of cells lying in one interior
interval supplies a common anchor measure.  The positive edge constant is
derived from the Dickman kernel theorem; it is not mesh data.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph

open MeasureTheory
open ConditionedPoissonLimit
open PoissonDickmanWeightedInverse

variable {Band : Type*} [Fintype Band] [DecidableEq Band]

/-- Elementary interval geometry for a finite mesh.  `interiorCells` only
records which cells lie in the fixed compact interval; its positive total
length is a geometric coverage statement, not an operator gap. -/
structure IntervalMesh (epsilon : ℝ) (Band : Type*) [Fintype Band] where
  lower : Band → ℝ
  upper : Band → ℝ
  lower_pos : ∀ i, 0 < lower i
  lower_lt_upper : ∀ i, lower i < upper i
  upper_le_one : ∀ i, upper i ≤ 1
  interiorCells : Finset Band
  interior_lower : ∀ i ∈ interiorCells, epsilon ≤ lower i
  interior_upper : ∀ i ∈ interiorCells, upper i ≤ 1 - epsilon
  interiorTotal_pos :
    0 < ∑ i ∈ interiorCells, (upper i - lower i)

namespace IntervalMesh

variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

def length (i : Band) : ℝ := M.upper i - M.lower i

omit [DecidableEq Band] in
theorem length_pos (i : Band) : 0 < M.length i :=
  sub_pos.mpr (M.lower_lt_upper i)

def anchor (j : Band) : ℝ :=
  if j ∈ M.interiorCells then M.length j else 0

theorem anchor_nonneg (j : Band) : 0 ≤ M.anchor j := by
  unfold anchor
  split_ifs
  · exact (M.length_pos j).le
  · exact le_rfl

theorem sum_anchor_pos : 0 < ∑ j, M.anchor j := by
  have hsum : (∑ j, M.anchor j) =
      ∑ j ∈ M.interiorCells, M.length j := by
    unfold anchor
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext j
      simp
    · intro j hj
      rfl
  rw [hsum]
  simpa only [length] using M.interiorTotal_pos

omit [DecidableEq Band] in
theorem cell_mem_unit {i : Band} {s : ℝ}
    (hs : s ∈ Icc (M.lower i) (M.upper i)) :
    s ∈ Icc (0 : ℝ) 1 :=
  ⟨(M.lower_pos i).le.trans hs.1, hs.2.trans (M.upper_le_one i)⟩

omit [DecidableEq Band] in
theorem interior_cell_mem {j : Band} (hj : j ∈ M.interiorCells)
    {t : ℝ} (ht : t ∈ Icc (M.lower j) (M.upper j)) :
    t ∈ Icc epsilon (1 - epsilon) :=
  ⟨(M.interior_lower j hj).trans ht.1,
    ht.2.trans (M.interior_upper j hj)⟩

/-- Ordinary-coordinate compression of the weighted graph edge. -/
def edge (i j : Band) : ℝ :=
  (∫ s in M.lower i..M.upper i,
      ∫ t in M.lower j..M.upper j,
        -covarianceKernelQuotient t s) / M.length i

omit [DecidableEq Band] in
private theorem continuous_innerEdge (j : Band) :
    Continuous (fun s : ℝ =>
      ∫ t in M.lower j..M.upper j,
        -covarianceKernelQuotient t s) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (a₀ := M.lower j) (b₀ := M.upper j)
  exact (continuous_uncurry_covarianceKernelQuotient.comp
    (continuous_snd.prodMk continuous_fst)).neg

omit [DecidableEq Band] in
theorem edge_nonneg (i j : Band) : 0 ≤ M.edge i j := by
  have hinner (s : ℝ) (hs : s ∈ Icc (M.lower i) (M.upper i)) :
      0 ≤ ∫ t in M.lower j..M.upper j,
        -covarianceKernelQuotient t s := by
    apply intervalIntegral.integral_nonneg
      (le_of_lt (M.lower_lt_upper j))
    intro t ht
    exact neg_nonneg.mpr (covarianceKernelQuotient_transpose_nonpos
      (M.cell_mem_unit hs) (M.cell_mem_unit ht))
  have houter : 0 ≤ ∫ s in M.lower i..M.upper i,
      ∫ t in M.lower j..M.upper j,
        -covarianceKernelQuotient t s := by
    exact intervalIntegral.integral_nonneg
      (le_of_lt (M.lower_lt_upper i)) hinner
  exact div_nonneg houter (M.length_pos i).le

/-- The uniform Dickman edge gap gives every output row the same anchor
measure. -/
theorem gap_mul_anchor_le_edge
    {kappa : ℝ}
    (hgap : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc epsilon (1 - epsilon),
        kappa ≤ -covarianceKernelQuotient t s)
    (i j : Band) :
    kappa * M.anchor j ≤ M.edge i j := by
  by_cases hj : j ∈ M.interiorCells
  · have hinner (s : ℝ) (hs : s ∈ Icc (M.lower i) (M.upper i)) :
        kappa * M.length j ≤
          ∫ t in M.lower j..M.upper j,
            -covarianceKernelQuotient t s := by
      have hleft : IntervalIntegrable (fun _ : ℝ => kappa) volume
          (M.lower j) (M.upper j) :=
        continuous_const.intervalIntegrable _ _
      have hright : IntervalIntegrable
          (fun t : ℝ => -covarianceKernelQuotient t s) volume
          (M.lower j) (M.upper j) :=
        ((continuous_uncurry_covarianceKernelQuotient.comp
          (continuous_id.prodMk continuous_const)).neg).intervalIntegrable _ _
      have hmono := intervalIntegral.integral_mono_on
        (le_of_lt (M.lower_lt_upper j)) hleft hright
        (fun t ht => hgap s (M.cell_mem_unit hs) t
          (M.interior_cell_mem hj ht))
      calc
        kappa * M.length j =
            ∫ _t in M.lower j..M.upper j, kappa := by
          simp [length]
          ring
        _ ≤ ∫ t in M.lower j..M.upper j,
            -covarianceKernelQuotient t s := hmono
    have hleftOuter : IntervalIntegrable
        (fun _ : ℝ => kappa * M.length j) volume
        (M.lower i) (M.upper i) :=
      continuous_const.intervalIntegrable _ _
    have hrightOuter : IntervalIntegrable (fun s : ℝ =>
        ∫ t in M.lower j..M.upper j,
          -covarianceKernelQuotient t s) volume
        (M.lower i) (M.upper i) :=
      (M.continuous_innerEdge j).intervalIntegrable _ _
    have houter := intervalIntegral.integral_mono_on
      (le_of_lt (M.lower_lt_upper i)) hleftOuter hrightOuter hinner
    have hscaled :
        M.length i * (kappa * M.length j) ≤
          ∫ s in M.lower i..M.upper i,
            ∫ t in M.lower j..M.upper j,
              -covarianceKernelQuotient t s := by
      calc
        M.length i * (kappa * M.length j) =
            ∫ _s in M.lower i..M.upper i,
              kappa * M.length j := by
          simp [length]
          ring
        _ ≤ _ := houter
    unfold edge anchor
    rw [if_pos hj]
    apply (le_div_iff₀ (M.length_pos i)).2
    nlinarith
  · unfold anchor
    rw [if_neg hj, mul_zero]
    exact M.edge_nonneg i j

/-- All finite graph constants are now derived from the Dickman kernel and
the elementary mesh geometry. -/
theorem exists_edge_geometry
    (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2) :
    ∃ kappa : ℝ, 0 < kappa ∧
      (∀ i j, 0 ≤ M.edge i j) ∧
      (∀ i j, kappa * M.anchor j ≤ M.edge i j) ∧
      0 < ∑ j, M.anchor j := by
  obtain ⟨kappa, hkappa, hgap⟩ :=
    exists_transposeQuotient_uniform_gap hepsilon hhalf
  exact ⟨kappa, hkappa, M.edge_nonneg,
    M.gap_mul_anchor_le_edge hgap, M.sum_anchor_pos⟩

/-! ## The exact edge matrix of the sharp continuum kernel block -/

/-- Harmonic mass `∫ dt/t` of a cell. -/
def harmonicMass (i : Band) : ℝ :=
  ∫ t in M.lower i..M.upper i, 1 / t

omit [DecidableEq Band] in
theorem harmonicMass_pos (i : Band) : 0 < M.harmonicMass i := by
  unfold harmonicMass
  rw [integral_one_div_of_pos
    (M.lower_pos i) ((M.lower_pos i).trans (M.lower_lt_upper i))]
  apply Real.log_pos
  exact (one_lt_div (M.lower_pos i)).2 (M.lower_lt_upper i)

/-- Continuum center: ordinary length divided by harmonic mass. -/
def center (i : Band) : ℝ := M.length i / M.harmonicMass i

omit [DecidableEq Band] in
theorem center_pos (i : Band) : 0 < M.center i :=
  div_pos (M.length_pos i) (M.harmonicMass_pos i)

/-- Row-normalized continuum covariance-kernel cell, written using the
removable quotient so the moving-low endpoint is harmless. -/
def normalizedKernelCell (i j : Band) : ℝ :=
  (∫ s in M.lower i..M.upper i,
      ∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s / t) / M.harmonicMass i

/-- Its sharp-conjugate positive graph edge. -/
def sharpKernelEdge (i j : Band) : ℝ :=
  (M.center j / M.length i) *
    ∫ s in M.lower i..M.upper i,
      ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / t

omit [DecidableEq Band] in
theorem sharpKernelEdge_eq_normalizedKernelCell (i j : Band) :
    M.sharpKernelEdge i j =
      -M.normalizedKernelCell i j * (M.center j / M.center i) := by
  have hmassI : M.harmonicMass i ≠ 0 :=
    ne_of_gt (M.harmonicMass_pos i)
  have hlengthI : M.length i ≠ 0 := ne_of_gt (M.length_pos i)
  unfold sharpKernelEdge normalizedKernelCell center
  have hneg : (∫ s in M.lower i..M.upper i,
      ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / t) =
      -(∫ s in M.lower i..M.upper i,
        ∫ t in M.lower j..M.upper j,
          covarianceKernelQuotient t s / t) := by
    calc
      (∫ s in M.lower i..M.upper i,
          ∫ t in M.lower j..M.upper j,
            (-covarianceKernelQuotient t s) / t) =
          ∫ s in M.lower i..M.upper i,
            -(∫ t in M.lower j..M.upper j,
              covarianceKernelQuotient t s / t) := by
        apply intervalIntegral.integral_congr
        intro s hs
        change (∫ t in M.lower j..M.upper j,
          (-covarianceKernelQuotient t s) / t) =
            -(∫ t in M.lower j..M.upper j,
              covarianceKernelQuotient t s / t)
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro t ht
        ring
      _ = _ := intervalIntegral.integral_neg
  rw [hneg]
  field_simp [hmassI, hlengthI]

omit [DecidableEq Band] in
theorem sharpKernelEdge_nonneg (i j : Band) :
    0 ≤ M.sharpKernelEdge i j := by
  have hinner (s : ℝ) (hs : s ∈ Icc (M.lower i) (M.upper i)) :
      0 ≤ ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / t := by
    apply intervalIntegral.integral_nonneg
      (le_of_lt (M.lower_lt_upper j))
    intro t ht
    exact div_nonneg
      (neg_nonneg.mpr (covarianceKernelQuotient_transpose_nonpos
        (M.cell_mem_unit hs) (M.cell_mem_unit ht)))
      (le_trans (M.lower_pos j).le ht.1)
  have hdouble : 0 ≤ ∫ s in M.lower i..M.upper i,
      ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / t :=
    intervalIntegral.integral_nonneg
      (le_of_lt (M.lower_lt_upper i)) hinner
  exact mul_nonneg
    (div_nonneg (M.center_pos j).le (M.length_pos i).le) hdouble

omit [DecidableEq Band] in
private theorem continuous_innerSharpEdge (j : Band) :
    Continuous (fun s : ℝ =>
      ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / t) := by
  let d : ℝ → ℝ := fun t => max t (M.lower j / 2)
  have hdcont : Continuous d :=
    continuous_id.max
      (continuous_const : Continuous fun _ : ℝ => M.lower j / 2)
  have hd0 (t : ℝ) : d t ≠ 0 := by
    have hdpos : 0 < d t := by
      dsimp only [d]
      exact (half_pos (M.lower_pos j)).trans_le (le_max_right _ _)
    exact ne_of_gt hdpos
  have hsurrogate : Continuous (fun s : ℝ =>
      ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / d t) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := M.lower j) (b₀ := M.upper j)
    exact (continuous_uncurry_covarianceKernelQuotient.comp
      (continuous_snd.prodMk continuous_fst)).neg.div
        (hdcont.comp continuous_snd) (fun z => hd0 z.2)
  have heq : (fun s : ℝ =>
      ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / t) =
      (fun s : ℝ =>
        ∫ t in M.lower j..M.upper j,
          (-covarianceKernelQuotient t s) / d t) := by
    funext s
    apply intervalIntegral.integral_congr
    intro t ht
    have htcc : t ∈ Icc (M.lower j) (M.upper j) := by
      simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper j))] using ht
    have hhalf : M.lower j / 2 ≤ t := by
      linarith [M.lower_pos j, htcc.1]
    change (-covarianceKernelQuotient t s) / t =
      (-covarianceKernelQuotient t s) / d t
    rw [show d t = t by simp [d, max_eq_left hhalf]]
  rw [heq]
  exact hsurrogate

/-- The sharp kernel-cell edge inherits the same mesh-independent anchor
domination, now in the exact normalization used by the arithmetic matrix. -/
theorem gap_mul_anchor_le_sharpKernelEdge
    {kappa : ℝ}
    (hgap : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc epsilon (1 - epsilon),
        kappa ≤ -covarianceKernelQuotient t s)
    (i j : Band) :
    kappa * M.anchor j ≤ M.sharpKernelEdge i j := by
  by_cases hj : j ∈ M.interiorCells
  · have hinner (s : ℝ) (hs : s ∈ Icc (M.lower i) (M.upper i)) :
        kappa * M.harmonicMass j ≤
          ∫ t in M.lower j..M.upper j,
            (-covarianceKernelQuotient t s) / t := by
      have hleft : IntervalIntegrable (fun t : ℝ => kappa / t) volume
          (M.lower j) (M.upper j) := by
        apply ContinuousOn.intervalIntegrable_of_Icc
          (le_of_lt (M.lower_lt_upper j))
        intro t ht
        exact (continuousAt_const.div continuousAt_id
          (ne_of_gt ((M.lower_pos j).trans_le ht.1))).continuousWithinAt
      have hright : IntervalIntegrable
          (fun t : ℝ => (-covarianceKernelQuotient t s) / t) volume
          (M.lower j) (M.upper j) := by
        apply ContinuousOn.intervalIntegrable_of_Icc
          (le_of_lt (M.lower_lt_upper j))
        intro t ht
        exact ((continuous_uncurry_covarianceKernelQuotient.comp
          (continuous_id.prodMk continuous_const)).neg.continuousAt.div
            continuousAt_id
            (ne_of_gt ((M.lower_pos j).trans_le ht.1))).continuousWithinAt
      have hmono := intervalIntegral.integral_mono_on
        (le_of_lt (M.lower_lt_upper j)) hleft hright
        (fun t ht => div_le_div_of_nonneg_right
          (hgap s (M.cell_mem_unit hs) t (M.interior_cell_mem hj ht))
          (le_trans (M.lower_pos j).le ht.1))
      calc
        kappa * M.harmonicMass j =
            ∫ t in M.lower j..M.upper j, kappa / t := by
          unfold harmonicMass
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro t ht
          ring
        _ ≤ _ := hmono
    have hleftOuter : IntervalIntegrable
        (fun _ : ℝ => kappa * M.harmonicMass j) volume
        (M.lower i) (M.upper i) :=
      continuous_const.intervalIntegrable _ _
    have hrightOuter : IntervalIntegrable (fun s : ℝ =>
        ∫ t in M.lower j..M.upper j,
          (-covarianceKernelQuotient t s) / t) volume
        (M.lower i) (M.upper i) := by
      exact (M.continuous_innerSharpEdge j).intervalIntegrable _ _
    have houter := intervalIntegral.integral_mono_on
      (le_of_lt (M.lower_lt_upper i)) hleftOuter hrightOuter hinner
    have hdouble :
        M.length i * (kappa * M.harmonicMass j) ≤
          ∫ s in M.lower i..M.upper i,
            ∫ t in M.lower j..M.upper j,
              (-covarianceKernelQuotient t s) / t := by
      calc
        M.length i * (kappa * M.harmonicMass j) =
            ∫ _s in M.lower i..M.upper i,
              kappa * M.harmonicMass j := by
          simp [length]
          ring
        _ ≤ _ := houter
    have hlengthI : 0 < M.length i := M.length_pos i
    have hmassJ : 0 < M.harmonicMass j := M.harmonicMass_pos j
    unfold anchor
    rw [if_pos hj]
    unfold sharpKernelEdge
    calc
      kappa * M.length j =
          (M.center j / M.length i) *
            (M.length i * (kappa * M.harmonicMass j)) := by
        unfold center
        field_simp [ne_of_gt hlengthI, ne_of_gt hmassJ]
      _ ≤ (M.center j / M.length i) *
          (∫ s in M.lower i..M.upper i,
            ∫ t in M.lower j..M.upper j,
              (-covarianceKernelQuotient t s) / t) :=
        mul_le_mul_of_nonneg_left hdouble
          (div_nonneg (M.center_pos j).le hlengthI.le)
  · unfold anchor
    rw [if_neg hj, mul_zero]
    exact M.sharpKernelEdge_nonneg i j

theorem exists_sharpKernelEdge_geometry
    (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2) :
    ∃ kappa : ℝ, 0 < kappa ∧
      (∀ i j, 0 ≤ M.sharpKernelEdge i j) ∧
      (∀ i j, kappa * M.anchor j ≤ M.sharpKernelEdge i j) ∧
      0 < ∑ j, M.anchor j := by
  obtain ⟨kappa, hkappa, hgap⟩ :=
    exists_transposeQuotient_uniform_gap hepsilon hhalf
  exact ⟨kappa, hkappa, M.sharpKernelEdge_nonneg,
    M.gap_mul_anchor_le_sharpKernelEdge hgap, M.sum_anchor_pos⟩

end IntervalMesh

end Erdos390.Full.ContinuumCellGraph
