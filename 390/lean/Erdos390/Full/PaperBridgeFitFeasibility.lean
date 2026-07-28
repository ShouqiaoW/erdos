import Erdos390.Full.PaperBridgeFit
import Erdos390.Full.PaperHeadSimplex

/-!
# Feasibility and frozen-ledger consequences of the actual bridge tilt

The nonlinear bridge changes only the active structured-cell coordinates.
This file records, for the literal finite exponential family used in
`PaperBridgeFit`, the conclusions which are independent of the analytic
covariance estimates: positivity, preservation of the active mass, an
explicit coordinate ceiling on a preselected parameter ball, and literal
preservation of every frozen top/protected coordinate and integer quota.

The coordinate ceiling is not postulated as a property of the output.  It is
deduced from the exact finite density-ratio estimate and an explicit baseline
slack inequality.  In the final Proposition 8.7 specialization that baseline
slack is discharged by the structured-cell count and the paper's `O(1/L)`
baseline-coordinate bound.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open FiniteExponentialFamily

namespace StructuredSampleData

variable {Head : Type*} [Fintype Head]

/-- The finite head patterns used by the bridge are pairwise separated when
two different tags prescribe different valuations at a common head prime. -/
def HeadPatternsSeparated (D : StructuredSampleData Head) : Prop :=
  forall h k, h ≠ k -> exists p,
    p ∈ (D.pattern h).primes ∧
    p ∈ (D.pattern k).primes ∧
    (D.pattern h).exponent p ≠ (D.pattern k).exponent p

/-- Physical separation and separated head valuations make the tagged
disjointification injective on the underlying natural-number coordinate. -/
theorem value_injective_of_headPatternsSeparated
    (D : StructuredSampleData Head) (hsep : D.HeadPatternsSeparated) :
    Function.Injective D.value := by
  intro m k hvalue
  have hsign : (D.cellOf m).2 = (D.cellOf k).2 := by
    cases hm : (D.cellOf m).2 <;> cases hk : (D.cellOf k).2
    · rfl
    · have hmhi : D.value m <= D.hi .minus := by
        simpa [hm] using D.value_le_hi m
      have hklo : D.lo .plus < D.value k := by
        simpa [hk] using D.lo_lt_value k
      rw [hvalue] at hmhi
      have hsepPhysical := D.physical_separated
      omega
    · have hmlo : D.lo .plus < D.value m := by
        simpa [hm] using D.lo_lt_value m
      have hkhi : D.value k <= D.hi .minus := by
        simpa [hk] using D.value_le_hi k
      rw [hvalue] at hmlo
      have hsepPhysical := D.physical_separated
      omega
    · rfl
  have hhead : (D.cellOf m).1 = (D.cellOf k).1 := by
    by_contra hne
    obtain ⟨p, hpm, hpk, hpne⟩ :=
      hsep (D.cellOf m).1 (D.cellOf k).1 hne
    have hmm := D.value_matches_head m p hpm
    have hkm := D.value_matches_head k p hpk
    apply hpne
    rw [← hmm, ← hkm, hvalue]
  have hcell : D.cellOf m = D.cellOf k := Prod.ext hhead hsign
  rcases m with ⟨cm, ⟨vm, hvm⟩⟩
  rcases k with ⟨ck, ⟨vk, hvk⟩⟩
  simp only [cellOf] at hcell
  simp only [value] at hvalue
  subst ck
  have hv : (⟨vm, hvm⟩ : D.SampleAt cm) = ⟨vk, hvk⟩ :=
    Subtype.ext hvalue
  cases hv
  rfl

/-- The literal `0, E e_p` head simplex used in the paper automatically
satisfies `HeadPatternsSeparated`; this is not an extra final hypothesis. -/
theorem headPatternsSeparated_of_paperHeadSimplex
    (P : Finset Nat) (hprime : ∀ p ∈ P, p.Prime)
    (E : Nat) (hE : 0 < E)
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (hpattern : D.pattern = PaperHeadSimplex.pattern P hprime E) :
    D.HeadPatternsSeparated := by
  rw [HeadPatternsSeparated, hpattern]
  exact PaperHeadSimplex.patternsSeparated P hprime E hE

end StructuredSampleData

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The actual active coordinate weight at a bridge parameter. -/
def activeCoordinateWeight [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) : Real :=
  B.vectorFamily.scalarFamily.activeWeight xi m

theorem activeCoordinateWeight_nonneg [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    0 <= B.activeCoordinateWeight xi m :=
  B.vectorFamily.scalarFamily.activeWeight_nonneg xi m

theorem activeCoordinateWeight_pos [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    0 < B.activeCoordinateWeight xi m := by
  rw [activeCoordinateWeight, FiniteExponentialFamily.activeWeight]
  apply mul_pos B.vectorFamily.baseMass_positive
  change 0 < B.vectorFamily.probabilityMass xi m
  rw [VectorExponentialFamily.probabilityMass,
    FiniteExponentialFamily.probabilityMass]
  exact div_pos
    (mul_pos (B.baseline.baseWeight_pos m) (Real.exp_pos _))
    (B.vectorFamily.scalarFamily.partition_pos xi)

/-- The active smooth-row mass is exactly fixed by every exponential tilt. -/
theorem sum_activeCoordinateWeight [Nonempty Head]
    (xi : B.ParamSpace) :
    (Finset.univ.sum fun m : B.sampleData.Sample =>
      B.activeCoordinateWeight xi m) = B.q := by
  change (Finset.univ.sum fun m : B.sampleData.Sample =>
    B.vectorFamily.scalarFamily.activeWeight xi m) = B.q
  rw [B.vectorFamily.scalarFamily.activeWeight_sum]
  exact B.vectorFamily_baseMass

/-- Exact coordinatewise density-ratio bound in unnormalized paper weights. -/
theorem activeCoordinateWeight_le_exp_twoRadius_mul_baseline
    [Nonempty Head] (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.activeCoordinateWeight xi m <=
      Real.exp (2 * B.scoreRadius xi) * B.baseline.baseWeight m := by
  rw [activeCoordinateWeight, FiniteExponentialFamily.activeWeight]
  change B.vectorFamily.baseMass * B.vectorFamily.probabilityMass xi m <=
    Real.exp (2 * B.scoreRadius xi) * B.baseline.baseWeight m
  rw [B.vectorFamily_baseMass]
  have hq : 0 <= B.q := le_of_lt B.q_pos
  calc
    B.q * B.vectorFamily.probabilityMass xi m
        <= B.q * (Real.exp (2 * B.scoreRadius xi) *
          B.vectorFamily.probabilityMass 0 m) :=
      mul_le_mul_of_nonneg_left
        (B.probabilityMass_le_exp_twoRadius_mul_baseline xi m) hq
    _ = Real.exp (2 * B.scoreRadius xi) * B.baseline.baseWeight m := by
      rw [B.probabilityMass_zero m]
      field_simp [ne_of_gt B.q_pos]

/-! The paper uses a compact *effective-score* box, not the crude sum of
all score norms.  The next estimates therefore take the correct pointwise
score bound and have constants independent of the number of active cells. -/

theorem exp_neg_effectiveBound_mul_q_le_partition
    [Nonempty Head] (xi : B.ParamSpace) (R : Real)
    (hscore : forall m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| <= R) :
    Real.exp (-R) * B.q <=
      B.vectorFamily.scalarFamily.partition xi := by
  rw [FiniteExponentialFamily.partition]
  calc
    Real.exp (-R) * B.q =
        Finset.univ.sum fun m : B.sampleData.Sample =>
          B.baseline.baseWeight m * Real.exp (-R) := by
      rw [← Finset.sum_mul, B.baseline.baseWeight_sum]
      simp [q, mul_comm]
    _ <= Finset.univ.sum fun m : B.sampleData.Sample =>
        B.vectorFamily.scalarFamily.unnormalizedWeight xi m := by
      apply Finset.sum_le_sum
      intro m _
      simp only [FiniteExponentialFamily.unnormalizedWeight,
        vectorFamily, VectorExponentialFamily.scalarFamily]
      apply mul_le_mul_of_nonneg_left _ (B.baseline.baseWeight_nonneg m)
      apply Real.exp_le_exp.mpr
      exact (neg_le_neg (hscore m)).trans
        (neg_abs_le (B.vectorFamily.scalarFamily.score m xi / B.L))

theorem probabilityMass_le_exp_twoEffectiveBound_mul_baseline
    [Nonempty Head] (xi : B.ParamSpace) (R : Real)
    (hscore : forall m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| <= R)
    (m : B.sampleData.Sample) :
    B.vectorFamily.probabilityMass xi m <=
      Real.exp (2 * R) * B.vectorFamily.probabilityMass 0 m := by
  have hq : B.q ≠ 0 := ne_of_gt B.q_pos
  have hZ : 0 < B.vectorFamily.scalarFamily.partition xi :=
    B.vectorFamily.scalarFamily.partition_pos xi
  have hexp : Real.exp (2 * R) * Real.exp (-R) = Real.exp R := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [B.probabilityMass_zero m]
  change B.vectorFamily.scalarFamily.unnormalizedWeight xi m /
      B.vectorFamily.scalarFamily.partition xi <=
    Real.exp (2 * R) * (B.baseline.baseWeight m / B.q)
  apply (div_le_iff₀ hZ).2
  calc
    B.vectorFamily.scalarFamily.unnormalizedWeight xi m =
        B.baseline.baseWeight m *
          Real.exp (B.vectorFamily.scalarFamily.score m xi / B.L) := by
      rfl
    _ <= B.baseline.baseWeight m * Real.exp R := by
      apply mul_le_mul_of_nonneg_left _ (B.baseline.baseWeight_nonneg m)
      exact Real.exp_le_exp.mpr
        ((le_abs_self _).trans (hscore m))
    _ = (Real.exp (2 * R) * (B.baseline.baseWeight m / B.q)) *
        (Real.exp (-R) * B.q) := by
      field_simp [hq]
      calc
        B.baseline.baseWeight m * Real.exp R =
            B.baseline.baseWeight m *
              (Real.exp (2 * R) * Real.exp (-R)) := by rw [hexp]
        _ = B.baseline.baseWeight m * Real.exp (2 * R) *
              Real.exp (-R) := by ring
    _ <= (Real.exp (2 * R) * (B.baseline.baseWeight m / B.q)) *
        B.vectorFamily.scalarFamily.partition xi := by
      exact mul_le_mul_of_nonneg_left
        (B.exp_neg_effectiveBound_mul_q_le_partition xi R hscore)
        (mul_nonneg (le_of_lt (Real.exp_pos _))
          (div_nonneg (B.baseline.baseWeight_nonneg m)
            (le_of_lt B.q_pos)))

theorem activeCoordinateWeight_le_exp_twoEffectiveBound_mul_baseline
    [Nonempty Head] (xi : B.ParamSpace) (R : Real)
    (hscore : forall m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| <= R)
    (m : B.sampleData.Sample) :
    B.activeCoordinateWeight xi m <=
      Real.exp (2 * R) * B.baseline.baseWeight m := by
  rw [activeCoordinateWeight, FiniteExponentialFamily.activeWeight]
  change B.vectorFamily.baseMass * B.vectorFamily.probabilityMass xi m <=
    Real.exp (2 * R) * B.baseline.baseWeight m
  rw [B.vectorFamily_baseMass]
  calc
    B.q * B.vectorFamily.probabilityMass xi m <=
        B.q * (Real.exp (2 * R) *
          B.vectorFamily.probabilityMass 0 m) :=
      mul_le_mul_of_nonneg_left
        (B.probabilityMass_le_exp_twoEffectiveBound_mul_baseline
          xi R hscore m) (le_of_lt B.q_pos)
    _ = Real.exp (2 * R) * B.baseline.baseWeight m := by
      rw [B.probabilityMass_zero m]
      field_simp [ne_of_gt B.q_pos]

/-- A pointwise `O(L)` statistic bound turns a preselected parameter ball
into the compact effective-score box used by the density-ratio argument.
Unlike `totalStatisticNorm`, this estimate does not sum over samples. -/
theorem effectiveScoreBound_of_statistic_norm
    [Nonempty Head] (xi : B.ParamSpace) (radius Cstat : Real)
    (hxi : ‖xi‖ <= radius) (hCstat : 0 <= Cstat)
    (hstat : forall m : B.sampleData.Sample,
      ‖B.statistic m‖ <= Cstat * B.L) :
    forall m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| <= Cstat * radius := by
  intro m
  have hradius : 0 <= radius := (norm_nonneg xi).trans hxi
  have hinner : |B.vectorFamily.scalarFamily.score m xi| <=
      ‖B.statistic m‖ * ‖xi‖ := by
    change |inner Real (B.statistic m) xi| <= _
    exact abs_real_inner_le_norm _ _
  rw [abs_div, abs_of_pos B.L_pos]
  calc
    |B.vectorFamily.scalarFamily.score m xi| / B.L <=
        (‖B.statistic m‖ * ‖xi‖) / B.L :=
      div_le_div_of_nonneg_right hinner (le_of_lt B.L_pos)
    _ <= ((Cstat * B.L) * radius) / B.L := by
      apply div_le_div_of_nonneg_right _ (le_of_lt B.L_pos)
      exact mul_le_mul (hstat m) hxi (norm_nonneg xi)
        (mul_nonneg hCstat (le_of_lt B.L_pos))
    _ = Cstat * radius := by
      field_simp [ne_of_gt B.L_pos]

/-- A baseline slack at radius `R` gives the literal upper bound `z_m <= 1`. -/
theorem activeCoordinateWeight_le_one_of_scoreRadius
    [Nonempty Head] (xi : B.ParamSpace) (R : Real)
    (hscore : B.scoreRadius xi <= R)
    (hslack : forall m : B.sampleData.Sample,
      Real.exp (2 * R) * B.baseline.baseWeight m <= 1)
    (m : B.sampleData.Sample) :
    B.activeCoordinateWeight xi m <= 1 := by
  calc
    B.activeCoordinateWeight xi m
        <= Real.exp (2 * B.scoreRadius xi) * B.baseline.baseWeight m :=
      B.activeCoordinateWeight_le_exp_twoRadius_mul_baseline xi m
    _ <= Real.exp (2 * R) * B.baseline.baseWeight m := by
      apply mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hscore (by norm_num)))
        (B.baseline.baseWeight_nonneg m)
    _ <= 1 := hslack m

/-- The preselected Euclidean parameter ball implies a completely explicit
score radius.  Hence the displayed baseline slack is sufficient uniformly on
the whole ball chosen before solving the ODE. -/
theorem activeCoordinateWeight_le_one_on_normBall
    [Nonempty Head] (xi : B.ParamSpace) (radius : Real)
    (hxi : ‖xi‖ <= radius)
    (hslack : forall m : B.sampleData.Sample,
      Real.exp (2 * (radius * B.totalStatisticNorm / B.L)) *
        B.baseline.baseWeight m <= 1)
    (m : B.sampleData.Sample) :
    B.activeCoordinateWeight xi m <= 1 := by
  apply B.activeCoordinateWeight_le_one_of_scoreRadius xi
    (radius * B.totalStatisticNorm / B.L) _ hslack m
  exact (B.scoreRadius_le_norm_mul_totalStatisticNorm_div_L xi).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hxi B.totalStatisticNorm_nonneg)
      (le_of_lt B.L_pos))

/-! ## Actual natural-number coordinates -/

/-- Active mass accumulated at one literal integer coordinate.  Under the
paper's disjoint-cell property the sum contains at most one term. -/
def ambientActiveWeight [Nonempty Head]
    (xi : B.ParamSpace) (a : Nat) : Real :=
  Finset.univ.sum fun m : B.sampleData.Sample =>
    if B.sampleData.value m = a then B.activeCoordinateWeight xi m else 0

theorem ambientActiveWeight_nonneg [Nonempty Head]
    (xi : B.ParamSpace) (a : Nat) :
    0 <= B.ambientActiveWeight xi a := by
  apply Finset.sum_nonneg
  intro m _
  split_ifs
  · exact B.activeCoordinateWeight_nonneg xi m
  · exact le_rfl

theorem ambientActiveWeight_eq_of_value
    [Nonempty Head]
    (hsep : B.sampleData.HeadPatternsSeparated)
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.ambientActiveWeight xi (B.sampleData.value m) =
      B.activeCoordinateWeight xi m := by
  classical
  rw [ambientActiveWeight, Finset.sum_eq_single m]
  · simp
  · intro k _ hkm
    rw [if_neg]
    intro hvalue
    exact hkm
      (B.sampleData.value_injective_of_headPatternsSeparated hsep hvalue)
  · simp

theorem ambientActiveWeight_eq_zero_of_not_value
    [Nonempty Head] (xi : B.ParamSpace) (a : Nat)
    (ha : forall m : B.sampleData.Sample, B.sampleData.value m ≠ a) :
    B.ambientActiveWeight xi a = 0 := by
  rw [ambientActiveWeight]
  apply Finset.sum_eq_zero
  intro m _
  rw [if_neg (ha m)]

/-- Total weight at a literal integer coordinate when the frozen
top/protected contribution may overlap the active smooth sample. -/
def ambientCombinedWeight [Nonempty Head]
    (frozenWeight : Nat -> Real) (xi : B.ParamSpace) (a : Nat) : Real :=
  frozenWeight a + B.ambientActiveWeight xi a

/-- Every actual coordinate stays in `[0,1]` on the preselected ball.  At an
active coordinate this uses the exact cell disjointness and the combined
frozen-plus-baseline slack; away from the active support it is just the frozen
feasibility bound. -/
theorem ambientCombinedWeight_mem_Icc_on_normBall
    [Nonempty Head]
    (hsep : B.sampleData.HeadPatternsSeparated)
    (frozenWeight : Nat -> Real)
    (hfrozen : forall a, frozenWeight a ∈ Set.Icc (0 : Real) 1)
    (xi : B.ParamSpace) (radius : Real)
    (hxi : ‖xi‖ <= radius)
    (hslack : forall m : B.sampleData.Sample,
      frozenWeight (B.sampleData.value m) +
        Real.exp (2 * (radius * B.totalStatisticNorm / B.L)) *
          B.baseline.baseWeight m <= 1) :
    forall a : Nat,
      B.ambientCombinedWeight frozenWeight xi a ∈ Set.Icc (0 : Real) 1 := by
  intro a
  constructor
  · exact add_nonneg (hfrozen a).1 (B.ambientActiveWeight_nonneg xi a)
  · by_cases ha : exists m : B.sampleData.Sample, B.sampleData.value m = a
    · obtain ⟨m, hm⟩ := ha
      rw [ambientCombinedWeight, ← hm,
        B.ambientActiveWeight_eq_of_value hsep xi m]
      calc
        frozenWeight (B.sampleData.value m) + B.activeCoordinateWeight xi m
            <= frozenWeight (B.sampleData.value m) +
              Real.exp (2 * (radius * B.totalStatisticNorm / B.L)) *
                B.baseline.baseWeight m := by
          have hactive : B.activeCoordinateWeight xi m <=
              Real.exp (2 * (radius * B.totalStatisticNorm / B.L)) *
                B.baseline.baseWeight m :=
            B.activeCoordinateWeight_le_exp_twoRadius_mul_baseline xi m |>.trans
              (mul_le_mul_of_nonneg_right
                (Real.exp_le_exp.mpr
                  (mul_le_mul_of_nonneg_left
                    ((B.scoreRadius_le_norm_mul_totalStatisticNorm_div_L xi).trans
                      (div_le_div_of_nonneg_right
                        (mul_le_mul_of_nonneg_right hxi
                          B.totalStatisticNorm_nonneg)
                        (le_of_lt B.L_pos)))
                    (by norm_num)))
                (B.baseline.baseWeight_nonneg m))
          simpa [add_comm] using
            (add_le_add_left hactive (frozenWeight (B.sampleData.value m)))
        _ <= 1 := hslack m
    · rw [ambientCombinedWeight,
        B.ambientActiveWeight_eq_zero_of_not_value xi a
          (fun m hm => ha ⟨m, hm⟩), add_zero]
      exact (hfrozen a).2

/-- Feasibility in the paper's correct compact effective-score box.  Unlike
the preceding crude Euclidean-ball corollary, this bound has no factor equal
to the number of active coordinates and is the form consumed by the final
non-circular ODE argument. -/
theorem ambientCombinedWeight_mem_Icc_of_effectiveScoreBound
    [Nonempty Head]
    (hsep : B.sampleData.HeadPatternsSeparated)
    (frozenWeight : Nat -> Real)
    (hfrozen : forall a, frozenWeight a ∈ Set.Icc (0 : Real) 1)
    (xi : B.ParamSpace) (R : Real)
    (hscore : forall m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| <= R)
    (hslack : forall m : B.sampleData.Sample,
      frozenWeight (B.sampleData.value m) +
        Real.exp (2 * R) * B.baseline.baseWeight m <= 1) :
    forall a : Nat,
      B.ambientCombinedWeight frozenWeight xi a ∈ Set.Icc (0 : Real) 1 := by
  intro a
  constructor
  · exact add_nonneg (hfrozen a).1 (B.ambientActiveWeight_nonneg xi a)
  · by_cases ha : exists m : B.sampleData.Sample, B.sampleData.value m = a
    · obtain ⟨m, hm⟩ := ha
      rw [ambientCombinedWeight, ← hm,
        B.ambientActiveWeight_eq_of_value hsep xi m]
      calc
        frozenWeight (B.sampleData.value m) + B.activeCoordinateWeight xi m
            <= frozenWeight (B.sampleData.value m) +
              Real.exp (2 * R) * B.baseline.baseWeight m := by
          simpa [add_comm] using add_le_add_left
            (B.activeCoordinateWeight_le_exp_twoEffectiveBound_mul_baseline
              xi R hscore m)
            (frozenWeight (B.sampleData.value m))
        _ <= 1 := hslack m
    · rw [ambientCombinedWeight,
        B.ambientActiveWeight_eq_zero_of_not_value xi a
          (fun m hm => ha ⟨m, hm⟩), add_zero]
      exact (hfrozen a).2

/-- Direct norm-ball corollary using a pointwise `O(L)` bound for the actual
statistic vector.  This is the finite support/ceiling statement attached to
the ODE once the paper's explicit statistic ledger supplies `hstat`. -/
theorem ambientCombinedWeight_mem_Icc_of_statisticNormBound
    [Nonempty Head]
    (hsep : B.sampleData.HeadPatternsSeparated)
    (frozenWeight : Nat -> Real)
    (hfrozen : forall a, frozenWeight a ∈ Set.Icc (0 : Real) 1)
    (xi : B.ParamSpace) (radius Cstat : Real)
    (hxi : ‖xi‖ <= radius) (hCstat : 0 <= Cstat)
    (hstat : forall m : B.sampleData.Sample,
      ‖B.statistic m‖ <= Cstat * B.L)
    (hslack : forall m : B.sampleData.Sample,
      frozenWeight (B.sampleData.value m) +
        Real.exp (2 * (Cstat * radius)) *
          B.baseline.baseWeight m <= 1) :
    forall a : Nat,
      B.ambientCombinedWeight frozenWeight xi a ∈ Set.Icc (0 : Real) 1 := by
  exact B.ambientCombinedWeight_mem_Icc_of_effectiveScoreBound
    hsep frozenWeight hfrozen xi (Cstat * radius)
      (B.effectiveScoreBound_of_statistic_norm
        xi radius Cstat hxi hCstat hstat) hslack

/-! ## Frozen top/protected coordinates and the integer ledger -/

/-- The total bridge vector on a tagged disjoint union.  The left summand is
every frozen top/protected/other coordinate; the right summand is the active
structured sample. -/
def combinedWeight [Nonempty Head]
    {Fixed : Type*} (fixedWeight : Fixed -> Real)
    (xi : B.ParamSpace) : Fixed ⊕ B.sampleData.Sample -> Real
  | Sum.inl f => fixedWeight f
  | Sum.inr m => B.activeCoordinateWeight xi m

@[simp] theorem combinedWeight_fixed [Nonempty Head]
    {Fixed : Type*} (fixedWeight : Fixed -> Real)
    (xi : B.ParamSpace) (f : Fixed) :
    B.combinedWeight fixedWeight xi (Sum.inl f) = fixedWeight f := rfl

@[simp] theorem combinedWeight_active [Nonempty Head]
    {Fixed : Type*} (fixedWeight : Fixed -> Real)
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.combinedWeight fixedWeight xi (Sum.inr m) =
      B.activeCoordinateWeight xi m := rfl

theorem combinedWeight_active_pos [Nonempty Head]
    {Fixed : Type*} (fixedWeight : Fixed -> Real)
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    0 < B.combinedWeight fixedWeight xi (Sum.inr m) :=
  B.activeCoordinateWeight_pos xi m

/-- Frozen coordinates are literally unchanged between any two bridge
parameters, not merely equal in total mass. -/
theorem combinedWeight_fixed_unchanged [Nonempty Head]
    {Fixed : Type*} (fixedWeight : Fixed -> Real)
    (xi eta : B.ParamSpace) (f : Fixed) :
    B.combinedWeight fixedWeight xi (Sum.inl f) =
      B.combinedWeight fixedWeight eta (Sum.inl f) := rfl

theorem sum_combinedWeight [Nonempty Head]
    {Fixed : Type*} [Fintype Fixed]
    (fixedWeight : Fixed -> Real) (xi : B.ParamSpace) :
    (Finset.univ.sum fun a : Fixed ⊕ B.sampleData.Sample =>
      B.combinedWeight fixedWeight xi a) =
      (Finset.univ.sum fixedWeight) + B.q := by
  rw [Fintype.sum_sum_type]
  simp only [combinedWeight]
  rw [B.sum_activeCoordinateWeight xi]

/-- The exact integer smooth-row quota is preserved because the active mass
is fixed and every other ledger entry is frozen. -/
theorem sum_combinedWeight_eq_integerQuota [Nonempty Head]
    {Fixed : Type*} [Fintype Fixed]
    (fixedWeight : Fixed -> Real) (quota : Int)
    (hquota : (quota : Real) =
      (Finset.univ.sum fixedWeight) + B.q)
    (xi : B.ParamSpace) :
    (Finset.univ.sum fun a : Fixed ⊕ B.sampleData.Sample =>
      B.combinedWeight fixedWeight xi a) = (quota : Real) := by
  rw [B.sum_combinedWeight fixedWeight xi, ← hquota]

/-- On the preselected ODE ball, every total tagged coordinate lies in
`[0,1]`: frozen coordinates keep their assumed feasible value, while active
coordinates use the density-ratio ceiling proved above. -/
theorem combinedWeight_mem_Icc_on_normBall [Nonempty Head]
    {Fixed : Type*} [Fintype Fixed]
    (fixedWeight : Fixed -> Real)
    (hfixed : forall f, fixedWeight f ∈ Set.Icc (0 : Real) 1)
    (xi : B.ParamSpace) (radius : Real)
    (hxi : ‖xi‖ <= radius)
    (hslack : forall m : B.sampleData.Sample,
      Real.exp (2 * (radius * B.totalStatisticNorm / B.L)) *
        B.baseline.baseWeight m <= 1) :
    forall a : Fixed ⊕ B.sampleData.Sample,
      B.combinedWeight fixedWeight xi a ∈ Set.Icc (0 : Real) 1 := by
  intro a
  cases a with
  | inl f => simpa only [combinedWeight] using hfixed f
  | inr m =>
      exact ⟨B.activeCoordinateWeight_nonneg xi m,
        B.activeCoordinateWeight_le_one_on_normBall
          xi radius hxi hslack m⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
