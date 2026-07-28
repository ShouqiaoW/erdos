import Erdos390.Full.PaperBridgeFitFeasibility

/-!
# Converting the baseline `O(1 / log n)` ledger into coordinate slack

The baseline active-measure lemma and the protected-floor construction give
separate `C / L` bounds.  This file contains the exact finite inequality which
turns those bounds into the combined ceiling required after a compact
effective tilt.  Thus Proposition 8.7 need not assume its final `[0,1]`
conclusion.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The quantitative content of `#C_{e,sigma,n} \asymp n` and
`q_{e,sigma,n} = O(n/L)`: every literal baseline coordinate is
`O(1/L)`, with all constants displayed. -/
theorem baseline_baseWeight_le_of_cell_density
    [Nonempty Head]
    (Cmass density : Real) (hCmass : 0 <= Cmass)
    (hdensity : 0 < density)
    (hmass : forall c : Cell Head,
      B.baseline.cellMass c <=
        Cmass * (B.sampleData.n : Real) / B.L)
    (hcard : forall c : Cell Head,
      density * (B.sampleData.n : Real) <=
        (Fintype.card (B.sampleData.SampleAt c) : Real)) :
    forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cmass / (density * B.L) := by
  intro m
  let c := B.sampleData.cellOf m
  have hn : 0 < (B.sampleData.n : Real) := by
    exact_mod_cast (Nat.zero_lt_of_lt B.n_gt_one)
  have hcardPos : 0 < (Fintype.card (B.sampleData.SampleAt c) : Real) := by
    exact_mod_cast B.sampleData.sampleAt_card_pos c
  have hden : 0 < density * B.L := mul_pos hdensity B.L_pos
  have hfactor : 0 <= Cmass / (density * B.L) :=
    div_nonneg hCmass (le_of_lt hden)
  have hscaled := mul_le_mul_of_nonneg_left (hcard c) hfactor
  rw [BaselineAllocation.baseWeight]
  apply (div_le_iff₀ hcardPos).2
  calc
    B.baseline.cellMass c <=
        Cmass * (B.sampleData.n : Real) / B.L := hmass c
    _ = (Cmass / (density * B.L)) *
        (density * (B.sampleData.n : Real)) := by
      field_simp [ne_of_gt hdensity, ne_of_gt B.L_pos]
    _ <= (Cmass / (density * B.L)) *
        (Fintype.card (B.sampleData.SampleAt c) : Real) := hscaled

/-- Separate `C/L` bounds imply the exact frozen-plus-active baseline slack
once `L` exceeds the displayed fixed constant. -/
theorem combinedBaselineSlack_of_div_log_bounds
    [Nonempty Head]
    (frozenWeight : Nat -> Real) (Cfixed Cactive R : Real)
    (hfrozen : forall m : B.sampleData.Sample,
      frozenWeight (B.sampleData.value m) <= Cfixed / B.L)
    (hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (hlarge : Cfixed + Real.exp (2 * R) * Cactive <= B.L) :
    forall m : B.sampleData.Sample,
      frozenWeight (B.sampleData.value m) +
        Real.exp (2 * R) * B.baseline.baseWeight m <= 1 := by
  intro m
  calc
    frozenWeight (B.sampleData.value m) +
        Real.exp (2 * R) * B.baseline.baseWeight m <=
      Cfixed / B.L + Real.exp (2 * R) * (Cactive / B.L) :=
        add_le_add (hfrozen m) (mul_le_mul_of_nonneg_left
          (hactive m) (le_of_lt (Real.exp_pos _)))
    _ = (Cfixed + Real.exp (2 * R) * Cactive) / B.L := by ring
    _ <= B.L / B.L :=
      div_le_div_of_nonneg_right hlarge (le_of_lt B.L_pos)
    _ = 1 := div_self (ne_of_gt B.L_pos)

/-- Ready-to-use actual-coordinate feasibility theorem after the two
`O(1/L)` ledgers and a pointwise `O(L)` statistic estimate are supplied. -/
theorem ambientCombinedWeight_mem_Icc_of_div_log_bounds
    [Nonempty Head]
    (hsep : B.sampleData.HeadPatternsSeparated)
    (frozenWeight : Nat -> Real)
    (hfrozenFeasible : forall a,
      frozenWeight a ∈ Set.Icc (0 : Real) 1)
    (xi : B.ParamSpace) (radius Cstat Cfixed Cactive : Real)
    (hxi : ‖xi‖ <= radius) (hCstat : 0 <= Cstat)
    (hstat : forall m : B.sampleData.Sample,
      ‖B.statistic m‖ <= Cstat * B.L)
    (hfrozen : forall m : B.sampleData.Sample,
      frozenWeight (B.sampleData.value m) <= Cfixed / B.L)
    (hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (hlarge : Cfixed + Real.exp (2 * (Cstat * radius)) * Cactive <= B.L) :
    forall a : Nat,
      B.ambientCombinedWeight frozenWeight xi a ∈ Set.Icc (0 : Real) 1 := by
  apply B.ambientCombinedWeight_mem_Icc_of_statisticNormBound
    hsep frozenWeight hfrozenFeasible xi radius Cstat hxi hCstat hstat
  exact B.combinedBaselineSlack_of_div_log_bounds frozenWeight
    Cfixed Cactive (Cstat * radius) hfrozen hactive hlarge

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
