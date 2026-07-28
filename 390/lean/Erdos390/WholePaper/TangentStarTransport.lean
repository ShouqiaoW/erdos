import Erdos390.WholePaper.TangentFlowAlgebra

/-!
# Exact finite star transport for tangent residuals

A zero-sum residual on a finite vertex type is transported through one
chosen pivot.  Positive residual leaves its vertex for the pivot; negative
residual is supplied from the pivot.  The construction is literal,
nonnegative, supported on the star, and has exactly the requested
divergence.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Nonnegative directed star flow.  The diagonal test comes first so the
pivot loop is zero. -/
def tangentStarFlow {V : Type*} [DecidableEq V]
    (pivot : V) (residual : V → ℝ) (source target : V) : ℝ :=
  if source = target then 0
  else if target = pivot then max (residual source) 0
  else if source = pivot then max (-residual target) 0
  else 0

/-- Outgoing mass minus incoming mass at one vertex. -/
def tangentFlowDivergence {V : Type*} [Fintype V]
    (flow : V → V → ℝ) (v : V) : ℝ :=
  (∑ w : V, flow v w) - ∑ w : V, flow w v

/-- Total directed traffic of a flow on a finite vertex type. -/
def tangentFlowTraffic {V : Type*} [Fintype V]
    (flow : V → V → ℝ) : ℝ :=
  ∑ source : V, ∑ target : V, flow source target

variable {V : Type*} [DecidableEq V]

/-! ## Pointwise support and sign -/

theorem tangentStarFlow_nonneg
    (pivot : V) (residual : V → ℝ) (source target : V) :
    0 ≤ tangentStarFlow pivot residual source target := by
  unfold tangentStarFlow
  split_ifs <;> positivity

@[simp]
theorem tangentStarFlow_self
    (pivot : V) (residual : V → ℝ) (v : V) :
    tangentStarFlow pivot residual v v = 0 := by
  simp [tangentStarFlow]

theorem tangentStarFlow_to_pivot
    {pivot v : V} {residual : V → ℝ} (hv : v ≠ pivot) :
    tangentStarFlow pivot residual v pivot = max (residual v) 0 := by
  simp [tangentStarFlow, hv]

theorem tangentStarFlow_from_pivot
    {pivot v : V} {residual : V → ℝ} (hv : v ≠ pivot) :
    tangentStarFlow pivot residual pivot v = max (-residual v) 0 := by
  simp [tangentStarFlow, hv, Ne.symm hv]

/-- Every strictly positive edge has exactly one endpoint equal to the
pivot. -/
theorem tangentStarFlow_pos_incident_pivot
    {pivot source target : V} {residual : V → ℝ}
    (hflow : 0 < tangentStarFlow pivot residual source target) :
    (source = pivot ∧ target ≠ pivot) ∨
      (source ≠ pivot ∧ target = pivot) := by
  by_cases hdiagonal : source = target
  · simp [tangentStarFlow, hdiagonal] at hflow
  by_cases htarget : target = pivot
  · exact Or.inr ⟨fun hsource ↦
      hdiagonal (hsource.trans htarget.symm), htarget⟩
  by_cases hsource : source = pivot
  · exact Or.inl ⟨hsource, htarget⟩
  · simp [tangentStarFlow, hdiagonal, htarget, hsource] at hflow

/-! ## Exact outgoing and incoming sums -/

variable [Fintype V]

theorem tangentStarFlow_sum_out_of_ne
    {pivot v : V} {residual : V → ℝ} (hv : v ≠ pivot) :
    (∑ w : V, tangentStarFlow pivot residual v w) =
      max (residual v) 0 := by
  classical
  rw [Finset.sum_eq_single pivot]
  · exact tangentStarFlow_to_pivot hv
  · intro w _hw hwPivot
    simp [tangentStarFlow, hv, hwPivot]
  · simp

theorem tangentStarFlow_sum_in_of_ne
    {pivot v : V} {residual : V → ℝ} (hv : v ≠ pivot) :
    (∑ w : V, tangentStarFlow pivot residual w v) =
      max (-residual v) 0 := by
  classical
  rw [Finset.sum_eq_single pivot]
  · exact tangentStarFlow_from_pivot hv
  · intro w _hw hwPivot
    simp [tangentStarFlow, hv, hwPivot]
  · simp

theorem tangentStarFlow_divergence_of_ne
    {pivot v : V} {residual : V → ℝ} (hv : v ≠ pivot) :
    tangentFlowDivergence (tangentStarFlow pivot residual) v =
      residual v := by
  rw [tangentFlowDivergence,
    tangentStarFlow_sum_out_of_ne hv,
    tangentStarFlow_sum_in_of_ne hv,
    max_zero_sub_max_neg_zero_eq_self]

theorem tangentStarFlow_sum_out_pivot
    (pivot : V) (residual : V → ℝ) :
    (∑ w : V, tangentStarFlow pivot residual pivot w) =
      ∑ w ∈ (Finset.univ : Finset V).erase pivot,
        max (-residual w) 0 := by
  classical
  calc
    (∑ w : V, tangentStarFlow pivot residual pivot w) =
        (∑ w ∈ (Finset.univ : Finset V).erase pivot,
          tangentStarFlow pivot residual pivot w) +
            tangentStarFlow pivot residual pivot pivot :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ pivot)).symm
    _ = ∑ w ∈ (Finset.univ : Finset V).erase pivot,
          max (-residual w) 0 := by
      rw [tangentStarFlow_self, add_zero]
      apply Finset.sum_congr rfl
      intro w hw
      have hwPivot : w ≠ pivot := Finset.ne_of_mem_erase hw
      exact tangentStarFlow_from_pivot hwPivot

theorem tangentStarFlow_sum_in_pivot
    (pivot : V) (residual : V → ℝ) :
    (∑ w : V, tangentStarFlow pivot residual w pivot) =
      ∑ w ∈ (Finset.univ : Finset V).erase pivot,
        max (residual w) 0 := by
  classical
  calc
    (∑ w : V, tangentStarFlow pivot residual w pivot) =
        (∑ w ∈ (Finset.univ : Finset V).erase pivot,
          tangentStarFlow pivot residual w pivot) +
            tangentStarFlow pivot residual pivot pivot :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ pivot)).symm
    _ = ∑ w ∈ (Finset.univ : Finset V).erase pivot,
          max (residual w) 0 := by
      rw [tangentStarFlow_self, add_zero]
      apply Finset.sum_congr rfl
      intro w hw
      have hwPivot : w ≠ pivot := Finset.ne_of_mem_erase hw
      exact tangentStarFlow_to_pivot hwPivot

/-- The zero-sum condition supplies the pivot coordinate of the divergence. -/
theorem tangentStarFlow_divergence_pivot
    {pivot : V} {residual : V → ℝ}
    (hsum : (∑ v : V, residual v) = 0) :
    tangentFlowDivergence (tangentStarFlow pivot residual) pivot =
      residual pivot := by
  rw [tangentFlowDivergence,
    tangentStarFlow_sum_out_pivot,
    tangentStarFlow_sum_in_pivot]
  have hsplit :
      (∑ v ∈ (Finset.univ : Finset V).erase pivot, residual v) +
          residual pivot = 0 := by
    calc
      (∑ v ∈ (Finset.univ : Finset V).erase pivot, residual v) +
          residual pivot = ∑ v : V, residual v :=
        Finset.sum_erase_add _ _ (Finset.mem_univ pivot)
      _ = 0 := hsum
  have hparts :
      (∑ v ∈ (Finset.univ : Finset V).erase pivot,
          (max (residual v) 0 - max (-residual v) 0)) +
        residual pivot = 0 := by
    simpa only [max_zero_sub_max_neg_zero_eq_self] using hsplit
  rw [Finset.sum_sub_distrib] at hparts
  linarith

/-- Every coordinate has exactly the prescribed residual divergence. -/
theorem tangentStarFlow_divergence_eq
    {pivot : V} {residual : V → ℝ}
    (hsum : (∑ v : V, residual v) = 0) (v : V) :
    tangentFlowDivergence (tangentStarFlow pivot residual) v =
      residual v := by
  by_cases hv : v = pivot
  · subst v
    exact tangentStarFlow_divergence_pivot hsum
  · exact tangentStarFlow_divergence_of_ne hv

/-! ## Traffic -/

/-- Exact traffic formula: the star transports one positive or negative
part for every non-pivot residual coordinate. -/
theorem tangentStarFlow_traffic_eq_sum_erase_abs
    (pivot : V) (residual : V → ℝ) :
    tangentFlowTraffic (tangentStarFlow pivot residual) =
      ∑ v ∈ (Finset.univ : Finset V).erase pivot, |residual v| := by
  classical
  have houtOff :
      (∑ v ∈ (Finset.univ : Finset V).erase pivot,
          ∑ w : V, tangentStarFlow pivot residual v w) =
        ∑ v ∈ (Finset.univ : Finset V).erase pivot,
          max (residual v) 0 := by
    apply Finset.sum_congr rfl
    intro v hv
    exact tangentStarFlow_sum_out_of_ne
      (Finset.ne_of_mem_erase hv)
  rw [tangentFlowTraffic]
  calc
    (∑ source : V,
        ∑ target : V, tangentStarFlow pivot residual source target) =
        (∑ source ∈ (Finset.univ : Finset V).erase pivot,
          ∑ target : V,
            tangentStarFlow pivot residual source target) +
          ∑ target : V,
            tangentStarFlow pivot residual pivot target :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ pivot)).symm
    _ = (∑ v ∈ (Finset.univ : Finset V).erase pivot,
          max (residual v) 0) +
        ∑ v ∈ (Finset.univ : Finset V).erase pivot,
          max (-residual v) 0 := by
      rw [houtOff, tangentStarFlow_sum_out_pivot]
    _ = ∑ v ∈ (Finset.univ : Finset V).erase pivot,
          (max (residual v) 0 + max (-residual v) 0) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ v ∈ (Finset.univ : Finset V).erase pivot,
          |residual v| := by
      apply Finset.sum_congr rfl
      intro v _hv
      simp only [max_zero_add_max_neg_zero_eq_abs_self]

/-- In particular, total traffic is at most the full `ℓ1` residual mass. -/
theorem tangentStarFlow_traffic_le_sum_abs
    (pivot : V) (residual : V → ℝ) :
    tangentFlowTraffic (tangentStarFlow pivot residual) ≤
      ∑ v : V, |residual v| := by
  rw [tangentStarFlow_traffic_eq_sum_erase_abs]
  calc
    (∑ v ∈ (Finset.univ : Finset V).erase pivot, |residual v|) ≤
        (∑ v ∈ (Finset.univ : Finset V).erase pivot,
          |residual v|) + |residual pivot| :=
      le_add_of_nonneg_right (abs_nonneg _)
    _ = ∑ v : V, |residual v| :=
      Finset.sum_erase_add _ _ (Finset.mem_univ pivot)

/-! ## Boundary identities consumed by `TangentFlowAlgebra` -/

/-- Finite integration by parts for any directed flow. -/
theorem tangentFlow_weightedBoundary_eq_divergence
    {W : Type*} [Fintype W]
    (flow : W → W → ℝ) (value : W → ℝ) :
    (∑ source : W, ∑ target : W,
        flow source target * (value source - value target)) =
      ∑ v : W, tangentFlowDivergence flow v * value v := by
  classical
  have hout :
      (∑ source : W, ∑ target : W,
          flow source target * value source) =
        ∑ source : W,
          (∑ target : W, flow source target) * value source := by
    apply Finset.sum_congr rfl
    intro source _hsource
    rw [Finset.sum_mul]
  have hin :
      (∑ source : W, ∑ target : W,
          flow source target * value target) =
        ∑ target : W,
          (∑ source : W, flow source target) * value target := by
    calc
      (∑ source : W, ∑ target : W,
          flow source target * value target) =
          ∑ target : W, ∑ source : W,
            flow source target * value target := by
        rw [Finset.sum_comm]
      _ = ∑ target : W,
          (∑ source : W, flow source target) * value target := by
        apply Finset.sum_congr rfl
        intro target _htarget
        rw [Finset.sum_mul]
  calc
    (∑ source : W, ∑ target : W,
        flow source target * (value source - value target)) =
        (∑ source : W, ∑ target : W,
          flow source target * value source) -
        ∑ source : W, ∑ target : W,
          flow source target * value target := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
    _ = (∑ source : W,
          (∑ target : W, flow source target) * value source) -
        ∑ target : W,
          (∑ source : W, flow source target) * value target := by
      rw [hout, hin]
    _ = ∑ v : W, tangentFlowDivergence flow v * value v := by
      simp only [tangentFlowDivergence, sub_mul,
        Finset.sum_sub_distrib]

/-- Scalar residual boundary furnished by the zero-sum star flow. -/
theorem tangentStarFlow_weightedBoundary_eq_residual
    {pivot : V} {residual : V → ℝ}
    (hsum : (∑ v : V, residual v) = 0) (value : V → ℝ) :
    (∑ source : V, ∑ target : V,
        tangentStarFlow pivot residual source target *
          (value source - value target)) =
      ∑ v : V, residual v * value v := by
  rw [tangentFlow_weightedBoundary_eq_divergence]
  apply Finset.sum_congr rfl
  intro v _hv
  rw [tangentStarFlow_divergence_eq hsum v]

/-- Product-edge form, directly matching a finite tangent edge family with
`source = Prod.fst` and `target = Prod.snd`. -/
theorem tangentStarFlow_pairBoundary_eq_residual
    {pivot : V} {residual : V → ℝ}
    (hsum : (∑ v : V, residual v) = 0) (value : V → ℝ) :
    (∑ edge : V × V,
        tangentStarFlow pivot residual edge.1 edge.2 *
          (value edge.1 - value edge.2)) =
      ∑ v : V, residual v * value v := by
  rw [Fintype.sum_prod_type]
  exact tangentStarFlow_weightedBoundary_eq_residual hsum value

/-- Coordinate-vector residual identity.  This is the generic bridge from
the finite star to every coordinate consumed by tangent-flow algebra. -/
theorem tangentStarFlow_residualVector
    {P : Type*} {pivot : V} {residual : V → ℝ}
    (hsum : (∑ v : V, residual v) = 0)
    (coordinate : V → P → ℝ) :
    ∀ p : P,
      (∑ edge : V × V,
          tangentStarFlow pivot residual edge.1 edge.2 *
            (coordinate edge.1 p - coordinate edge.2 p)) =
        ∑ v : V, residual v * coordinate v p := by
  intro p
  exact tangentStarFlow_pairBoundary_eq_residual hsum
    (fun v ↦ coordinate v p)

/-- Specialization to the factorization vectors appearing in
`tangentUpdate_valuation`. -/
theorem tangentStarFlow_factorizationBoundary_eq_residual
    {pivot : V} {residual : V → ℝ}
    (hsum : (∑ v : V, residual v) = 0)
    (label : V → ℕ) (p : ℕ) :
    (∑ edge : V × V,
        tangentStarFlow pivot residual edge.1 edge.2 *
          (((label edge.1).factorization p : ℝ) -
            ((label edge.2).factorization p : ℝ))) =
      ∑ v : V, residual v * (label v).factorization p := by
  exact tangentStarFlow_residualVector hsum
    (fun v q ↦ ((label v).factorization q : ℝ)) p

end

end Erdos390.WholePaper
