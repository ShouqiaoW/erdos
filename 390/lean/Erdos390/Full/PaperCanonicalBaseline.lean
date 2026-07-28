import Erdos390.Full.PaperPhysicalIntervalNuisanceGap

/-!
# Canonical barycentric baseline allocation

The active bridge first fixes positive head barycentric masses and then mixes
the two separated physical pools to hit the required logarithmic moment.
This file performs that construction exactly on the literal guarded finite
cells.  The resulting common cell-mass margin is an output.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperGuardCensus

open PaperBridgeFit ArithmeticModel

noncomputable section

variable {Head : Type*} [Fintype Head] [Nonempty Head]

theorem sum_physicalSign (f : PhysicalSign → ℝ) :
    ∑ sigma : PhysicalSign, f sigma = f .minus + f .plus := by
  have huniv : (Finset.univ : Finset PhysicalSign) =
      {.minus, .plus} := by decide
  rw [huniv]
  simp

/-- Uniform physical-log mean of one actual guard-deleted cell. -/
def cellLogMean (D : StructuredSampleData Head) (c : Cell Head) : ℝ :=
  (∑ m : D.SampleAt c,
      Real.log ((m.1 : ℝ) / (D.n : ℝ))) /
    Fintype.card (D.SampleAt c)

/-- Head-barycentric mean in one physical pool. -/
def poolLogMean (D : StructuredSampleData Head)
    (beta : Head → ℝ) (sigma : PhysicalSign) : ℝ :=
  ∑ h : Head, beta h * cellLogMean D (h, sigma)

/-- The physical mixing coordinate which hits `mu`. -/
def physicalMixingWeight (D : StructuredSampleData Head)
    (beta : Head → ℝ) (mu : ℝ) : ℝ :=
  (mu - poolLogMean D beta .minus) /
    (poolLogMean D beta .plus - poolLogMean D beta .minus)

/-- Positive head barycentric data and a quantitatively interior physical
target.  These are the finite reserve choices made before the covariance
argument; no covariance or inverse conclusion is stored here. -/
structure BarycentricTarget (D : StructuredSampleData Head) where
  beta : Head → ℝ
  beta_pos : ∀ h, 0 < beta h
  beta_sum : ∑ h, beta h = 1
  betaFloor : ℝ
  betaFloor_pos : 0 < betaFloor
  betaFloor_le : ∀ h, betaFloor ≤ beta h
  mu : ℝ
  tau : ℝ
  tau_pos : 0 < tau
  pool_separated : poolLogMean D beta .minus < poolLogMean D beta .plus
  left_interior :
    tau * (poolLogMean D beta .plus - poolLogMean D beta .minus) ≤
      mu - poolLogMean D beta .minus
  right_interior :
    tau * (poolLogMean D beta .plus - poolLogMean D beta .minus) ≤
      poolLogMean D beta .plus - mu

namespace BarycentricTarget

variable {D : StructuredSampleData Head} (T : BarycentricTarget D)

omit [Nonempty Head] in
theorem denominator_pos :
    0 < poolLogMean D T.beta .plus - poolLogMean D T.beta .minus :=
  sub_pos.mpr T.pool_separated

omit [Nonempty Head] in
theorem mixingWeight_pos :
    0 < physicalMixingWeight D T.beta T.mu := by
  unfold physicalMixingWeight
  exact div_pos
    ((mul_pos T.tau_pos T.denominator_pos).trans_le T.left_interior)
    T.denominator_pos

omit [Nonempty Head] in
theorem mixingWeight_lt_one :
    physicalMixingWeight D T.beta T.mu < 1 := by
  unfold physicalMixingWeight
  apply (div_lt_one T.denominator_pos).2
  have hright : 0 < poolLogMean D T.beta .plus - T.mu :=
    (mul_pos T.tau_pos T.denominator_pos).trans_le T.right_interior
  linarith

omit [Nonempty Head] in
theorem tau_le_mixingWeight :
    T.tau ≤ physicalMixingWeight D T.beta T.mu := by
  unfold physicalMixingWeight
  exact (le_div_iff₀ T.denominator_pos).2 T.left_interior

omit [Nonempty Head] in
theorem tau_le_one_sub_mixingWeight :
    T.tau ≤ 1 - physicalMixingWeight D T.beta T.mu := by
  calc
    T.tau ≤
        (poolLogMean D T.beta .plus - T.mu) /
          (poolLogMean D T.beta .plus - poolLogMean D T.beta .minus) :=
      (le_div_iff₀ T.denominator_pos).2 T.right_interior
    _ = 1 - physicalMixingWeight D T.beta T.mu := by
      unfold physicalMixingWeight
      field_simp [T.denominator_pos.ne']
      ring

/-- Exact normalized cell mass selected by the head barycenter and physical
mixing coordinate. -/
def cellProbability (c : Cell Head) : ℝ :=
  match c.2 with
  | .minus => T.beta c.1 * (1 - physicalMixingWeight D T.beta T.mu)
  | .plus => T.beta c.1 * physicalMixingWeight D T.beta T.mu

omit [Nonempty Head] in
theorem cellProbability_pos (c : Cell Head) : 0 < T.cellProbability c := by
  cases c with
  | mk h sigma =>
      cases sigma with
      | minus =>
          exact mul_pos (T.beta_pos h) (sub_pos.mpr T.mixingWeight_lt_one)
      | plus =>
          exact mul_pos (T.beta_pos h) T.mixingWeight_pos

omit [Nonempty Head] in
theorem sum_cellProbability : ∑ c : Cell Head, T.cellProbability c = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [sum_physicalSign]
  simp only [cellProbability]
  calc
    ∑ h : Head,
        (T.beta h * (1 - physicalMixingWeight D T.beta T.mu) +
          T.beta h * physicalMixingWeight D T.beta T.mu) =
        ∑ h : Head, T.beta h := by
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ = 1 := T.beta_sum

/-- The canonical `BaselineAllocation`; its cell masses already sum to one. -/
def baseline : BaselineAllocation D where
  cellMass := T.cellProbability
  cellMass_pos := T.cellProbability_pos

omit [Nonempty Head] in
theorem baseline_totalMass : T.baseline.totalMass = 1 := by
  exact T.sum_cellProbability

omit [Nonempty Head] in
theorem baseline_normalizedCellMass (c : Cell Head) :
    T.baseline.normalizedCellMass c = T.cellProbability c := by
  unfold BaselineAllocation.normalizedCellMass
  change T.cellProbability c / T.baseline.totalMass = T.cellProbability c
  rw [T.baseline_totalMass, div_one]

/-- A positive common cell-mass margin, independent of the prime mesh. -/
def cellMassMargin : ℝ := T.betaFloor * T.tau

omit [Nonempty Head] in
theorem cellMassMargin_pos : 0 < T.cellMassMargin :=
  mul_pos T.betaFloor_pos T.tau_pos

omit [Nonempty Head] in
theorem cellMassMargin_le (c : Cell Head) :
    T.cellMassMargin ≤ T.baseline.normalizedCellMass c := by
  rw [T.baseline_normalizedCellMass]
  cases c with
  | mk h sigma =>
      cases sigma with
      | minus =>
          exact mul_le_mul (T.betaFloor_le h)
            T.tau_le_one_sub_mixingWeight T.tau_pos.le
            (T.beta_pos h).le
      | plus =>
          exact mul_le_mul (T.betaFloor_le h)
            T.tau_le_mixingWeight T.tau_pos.le
            (T.beta_pos h).le

omit [Nonempty Head] in
/-- The two physical signs sum back to the prescribed head barycenter. -/
theorem headMarginal (h : Head) :
    ∑ sigma : PhysicalSign,
        T.baseline.normalizedCellMass (h, sigma) = T.beta h := by
  simp only [T.baseline_normalizedCellMass, cellProbability]
  rw [sum_physicalSign]
  ring

omit [Nonempty Head] in
/-- Hence every prescribed head-linear moment is exact. -/
theorem headMoment (a : Head → ℝ) :
    ∑ c : Cell Head, T.baseline.normalizedCellMass c * a c.1 =
      ∑ h : Head, T.beta h * a h := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h hh
  calc
    ∑ y : PhysicalSign, T.baseline.normalizedCellMass (h, y) * a h =
        (∑ y : PhysicalSign, T.baseline.normalizedCellMass (h, y)) * a h := by
      rw [Finset.sum_mul]
    _ = T.beta h * a h := by rw [T.headMarginal h]

omit [Nonempty Head] in
/-- The physical logarithmic moment is exactly the selected target `mu`. -/
theorem physicalLogMoment :
    ∑ c : Cell Head,
        T.baseline.normalizedCellMass c * cellLogMean D c = T.mu := by
  let t := physicalMixingWeight D T.beta T.mu
  rw [Fintype.sum_prod_type]
  simp_rw [sum_physicalSign]
  simp only [T.baseline_normalizedCellMass, cellProbability]
  change (∑ h : Head,
      (T.beta h * (1 - t) * cellLogMean D (h, .minus) +
        T.beta h * t * cellLogMean D (h, .plus))) = T.mu
  rw [show
    (∑ h : Head,
      (T.beta h * (1 - t) * cellLogMean D (h, .minus) +
        T.beta h * t * cellLogMean D (h, .plus))) =
      (1 - t) * poolLogMean D T.beta .minus +
        t * poolLogMean D T.beta .plus by
      unfold poolLogMean
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro h hh
      ring]
  have hden := T.denominator_pos.ne'
  dsimp [t, physicalMixingWeight]
  field_simp [hden]
  ring

end BarycentricTarget

end

end Erdos390.Full.PaperGuardCensus
