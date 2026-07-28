import Erdos390.Full.PaperBridgeCellTiltDecomposition
import Erdos390.Full.LocalizedMarkedTiltCovariance
import Erdos390.Full.OmittedTiltFallback
import Erdos390.Full.PaperPhysicalIntervalNuisanceGap

/-!
# Marked fallback through the physical/head bridge tilt

On a fixed tagged bridge cell all centered-head coordinates are constant.
Consequently the residual nuisance tilt is exactly a small physical-log tilt;
the constant head factor cancels from normalization.  We combine that exact
identity with reciprocal divisibility bounds for the medium-prime tilt.

The resulting estimates retain the marked `1 / D` and `1 / (p q)` scales.
No total-variation estimate is used.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open ValuationScoreDomination OmittedTiltFallback
open DivisibilityMomentBounds

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Extend the actual effective prime fugacity by zero outside the literal
medium-prime band. -/
def effectiveNatCoefficient (xi : B.ParamSpace) (p : ℕ) : ℝ :=
  if hp : p ∈ primeBand B.sampleData.n B.sampleData.W then
    B.effectivePrimeCoefficient xi ⟨p, hp⟩
  else 0

@[simp] theorem effectiveNatCoefficient_of_mem
    (xi : B.ParamSpace) {p : ℕ}
    (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    B.effectiveNatCoefficient xi p =
      B.effectivePrimeCoefficient xi ⟨p, hp⟩ := by
  simp only [effectiveNatCoefficient, dif_pos hp]

/-- On a literal cell, the medium part of the bridge score is the genuine
valuation score used by the structured-cell estimates. -/
theorem sigmaCellScore_scaledMedium_eq_valuationScore [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (m : B.sampleData.SampleAt c) :
    sigmaCellScore (B.scaledMediumScore xi) c m =
      valuationScore (primeBand B.sampleData.n B.sampleData.W)
        (B.effectiveNatCoefficient xi) B.L m := by
  unfold sigmaCellScore scaledMediumScore valuationScore
  have hattach := Finset.sum_attach
    (primeBand B.sampleData.n B.sampleData.W)
    (fun p ↦ (B.effectiveNatCoefficient xi p / B.L) * valuation p m)
  rw [← hattach]
  apply Finset.sum_congr rfl
  intro p hp
  rw [B.effectiveNatCoefficient_of_mem xi p.2]
  simp only [StructuredSampleData.value]

/-- The component law after only the medium-prime valuation tilt. -/
def cellMediumLaw [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) :
    FiniteProbability (B.sampleData.SampleAt c) :=
  (B.guardedCellProbability c).exponentialTilt
    (sigmaCellScore (B.scaledMediumScore xi) c)

/-- The only nonconstant part of the nuisance score on a fixed cell. -/
def cellPhysicalTiltScore [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (m : B.sampleData.SampleAt c) : ℝ :=
  (xi MomentCoord.physical / B.L) * B.physicalScore ⟨c, m⟩

/-- The head contribution to the nuisance score on a tagged cell. -/
def cellHeadTiltConstant [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) : ℝ :=
  (∑ h : B.HeadIndex,
      xi (MomentCoord.head h) *
        ((if c.1 = h.1 then 1 else 0) - B.headBaselineMass h.1)) / B.L

private def nuisanceCoordEquiv (I : Type*) :
    NuisanceCoord I ≃ Unit ⊕ I where
  toFun
    | .physical => Sum.inl ()
    | .head h => Sum.inr h
  invFun
    | Sum.inl _ => .physical
    | Sum.inr h => .head h
  left_inv c := by cases c <;> rfl
  right_inv
    | Sum.inl () => rfl
    | Sum.inr h => rfl

private theorem sum_nuisanceCoord {I : Type*} [Fintype I]
    (f : NuisanceCoord I → ℝ) :
    (∑ z : NuisanceCoord I, f z) =
      f .physical + ∑ h : I, f (.head h) := by
  calc
    (∑ z : NuisanceCoord I, f z) =
        ∑ s : Unit ⊕ I, f ((nuisanceCoordEquiv I).symm s) := by
      exact Fintype.sum_equiv (nuisanceCoordEquiv I) f
        (fun s ↦ f ((nuisanceCoordEquiv I).symm s)) (fun z ↦ by simp)
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp [nuisanceCoordEquiv]

/-- The head part is literally constant on each tagged cell. -/
theorem sigmaCellScore_scaledNuisance_eq_physical_add_constant
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (m : B.sampleData.SampleAt c) :
    sigmaCellScore (B.scaledNuisanceScore xi) c m =
      B.cellPhysicalTiltScore xi c m + B.cellHeadTiltConstant xi c := by
  unfold sigmaCellScore scaledNuisanceScore cellPhysicalTiltScore
    cellHeadTiltConstant
  rw [PiLp.inner_apply, sum_nuisanceCoord]
  simp only [B.nuisanceParameter_physical, B.nuisanceStatistic_physical,
    B.nuisanceParameter_head, B.nuisanceStatistic_head]
  unfold centeredHeadScore headIndicator StructuredSampleData.cellOf
  rw [add_div]
  congr 1
  · simp only [RCLike.inner_apply, conj_trivial]
    ring
  · apply congrArg (fun z : ℝ ↦ z / B.L)
    apply Finset.sum_congr rfl
    intro h hh
    split_ifs <;> simp only [RCLike.inner_apply, conj_trivial] <;> ring

private theorem exponentialTilt_const
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (k : ℝ) :
    mu.exponentialTilt (fun _ ↦ k) = mu := by
  apply FiniteProbability.eq_of_mass_eq
  funext omega
  have hpart : mu.expPartition (fun _ ↦ k) = Real.exp k := by
    unfold expPartition expect
    calc
      (∑ x, mu.mass x * Real.exp k) =
          (∑ x, mu.mass x) * Real.exp k := by rw [Finset.sum_mul]
      _ = Real.exp k := by rw [mu.mass_sum, one_mul]
  change mu.mass omega * Real.exp k /
      mu.expPartition (fun _ ↦ k) = mu.mass omega
  rw [hpart]
  field_simp [ne_of_gt (Real.exp_pos k)]

/-- Adding the constant cell-head factor does not change a normalized
exponential tilt. -/
theorem exponentialTilt_cellNuisance_eq_physical [Nonempty Head]
    (c : Cell Head)
    (mu : FiniteProbability (B.sampleData.SampleAt c))
    (xi : B.ParamSpace) :
    mu.exponentialTilt
        (sigmaCellScore (B.scaledNuisanceScore xi) c) =
      mu.exponentialTilt (B.cellPhysicalTiltScore xi c) := by
  have hscore : sigmaCellScore (B.scaledNuisanceScore xi) c =
      fun m ↦ B.cellPhysicalTiltScore xi c m +
        B.cellHeadTiltConstant xi c := by
    funext m
    exact B.sigmaCellScore_scaledNuisance_eq_physical_add_constant xi c m
  rw [hscore, ← mu.exponentialTilt_add]
  rw [exponentialTilt_const]

/-- Exact component-law factorization: full bridge tilt equals medium tilt
followed by the small physical tilt. -/
theorem guardedCell_fullTilt_eq_medium_physicalTilt [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) :
    (B.guardedCellProbability c).exponentialTilt
        (sigmaCellScore (B.scaledBridgeScore xi) c) =
      (B.cellMediumLaw xi c).exponentialTilt
        (B.cellPhysicalTiltScore xi c) := by
  have hscore : sigmaCellScore (B.scaledBridgeScore xi) c =
      fun m ↦ sigmaCellScore (B.scaledMediumScore xi) c m +
        sigmaCellScore (B.scaledNuisanceScore xi) c m := by
    funext m
    exact B.sigmaCellScore_scaledBridge_eq xi c m
  rw [hscore, ← (B.guardedCellProbability c).exponentialTilt_add]
  exact B.exponentialTilt_cellNuisance_eq_physical
    c (B.cellMediumLaw xi c) xi

/-- The actual guard-deleted cell endpoint is positive. -/
theorem cell_hi_pos (c : Cell Head) :
    0 < B.sampleData.hi c.2 := by
  obtain ⟨m, hm⟩ := B.sampleData.cell_nonempty c
  let sample : B.sampleData.Sample := ⟨c, ⟨m, hm⟩⟩
  have hmle : m ≤ B.sampleData.hi c.2 := by
    simpa only [sample, StructuredSampleData.value,
      StructuredSampleData.cellOf] using B.sampleData.value_le_hi sample
  have hmpos : 0 < m := by
    simpa only [sample, StructuredSampleData.value] using
      B.sampleData.value_pos sample
  exact hmpos.trans_le hmle

/-- Reciprocal fallback for the literal medium-tilted, guard-deleted cell.
The required density lower bound is stated as the concrete cardinality
inequality that the guard census supplies. -/
theorem cellMediumLaw_expect_divInd_le [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    {rho A : ℝ} {D : ℕ}
    (hD : 0 < D) (hA : 0 ≤ A) (hW : 1 < B.sampleData.W)
    (hrho : 0 < rho)
    (hcard : rho * (B.sampleData.hi c.2 : ℝ) ≤
      ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ A) :
    (B.cellMediumLaw xi c).expect
        (fun m ↦ divInd D m) ≤
      Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) /
        (rho * (D : ℝ)) := by
  let S := B.sampleData.cellFinset c
  have hS : S.Nonempty := B.sampleData.cell_nonempty c
  have hpW : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      B.sampleData.W ≤ p := by
    intro p hp
    exact (cutoff_lt_of_mem_primeBand hp).le
  have hetaNat : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.effectiveNatCoefficient xi p| ≤ A := by
    intro p hp
    rw [B.effectiveNatCoefficient_of_mem xi hp]
    exact heta ⟨p, hp⟩
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    let sample : B.sampleData.Sample := ⟨c, ⟨m, hm⟩⟩
    simpa only [sample, StructuredSampleData.value] using
      B.sampleData.value_pos sample
  have hSle : ∀ m ∈ S, m ≤ B.sampleData.hi c.2 := by
    intro m hm
    let sample : B.sampleData.Sample := ⟨c, ⟨m, hm⟩⟩
    simpa only [sample, StructuredSampleData.value,
      StructuredSampleData.cellOf] using B.sampleData.value_le_hi sample
  have hraw := omittedValuationTilt_divInd_le
    S (primeBand B.sampleData.n B.sampleData.W) hS
    (B.effectiveNatCoefficient xi)
    hD (B.cell_hi_pos c) hA B.L_pos hW hrho hcard hSpos hSle hpW hetaNat
  have hscore :
      sigmaCellScore (B.scaledMediumScore xi) c =
      fun m : B.sampleData.SampleAt c ↦
        valuationScore (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ) := by
    funext m
    exact B.sigmaCellScore_scaledMedium_eq_valuationScore xi c m
  change (((uniformOnFinset S hS).exponentialTilt
      (sigmaCellScore (B.scaledMediumScore xi) c)).expect
        (fun m : B.sampleData.SampleAt c ↦ divInd D m)) ≤ _
  rw [hscore]
  exact hraw

/-- A fixed physical interval and a bounded physical parameter make the
second tilt pointwise `O(1/L)`. -/
theorem abs_cellPhysicalTiltScore_le [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    {Aphys Kphys : ℝ}
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hKphys : ∀ m : B.sampleData.SampleAt c,
      |B.physicalScore ⟨c, m⟩| ≤ Kphys) :
    ∀ m, |B.cellPhysicalTiltScore xi c m| ≤
      Aphys * Kphys / B.L := by
  intro m
  unfold cellPhysicalTiltScore
  rw [abs_mul, abs_div, abs_of_pos B.L_pos]
  calc
    (|xi MomentCoord.physical| / B.L) *
        |B.physicalScore ⟨c, m⟩| ≤
      (Aphys / B.L) * Kphys := by
        apply mul_le_mul
        · exact div_le_div_of_nonneg_right hAphys B.L_pos.le
        · exact hKphys m
        · exact abs_nonneg _
        · exact div_nonneg (le_trans (abs_nonneg _) hAphys) B.L_pos.le
    _ = Aphys * Kphys / B.L := by ring

/-- The abstract physical-score bound above is discharged by the literal
fixed intervals and their canonical floored endpoints.  In particular the
constant is `log U`, independent of `n` and of the later tilt box. -/
theorem abs_cellPhysicalTiltScore_le_fixedIntervals [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (I : PaperGuardCensus.PhysicalIntervals) {U Aphys : ℝ}
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      ArithmeticModel.physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      ArithmeticModel.physicalBound (I.upper sigma) B.sampleData.n)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys) :
    ∀ m, |B.cellPhysicalTiltScore xi c m| ≤
      Aphys * Real.log U / B.L := by
  apply B.abs_cellPhysicalTiltScore_le xi c hAphys
  intro m
  exact B.abs_physicalScore_le_log_upperBound I
    hlowerOne hupperU hlo hhi ⟨c, m⟩

/-- The physical/head second tilt changes a divisor probability at its
original reciprocal scale. -/
theorem abs_guardedCell_fullTilt_expect_divInd_sub_medium_le
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    {rho A Aphys Kphys : ℝ} {D : ℕ}
    (hD : 0 < D) (hA : 0 ≤ A) (hW : 1 < B.sampleData.W)
    (hrho : 0 < rho)
    (hcard : rho * (B.sampleData.hi c.2 : ℝ) ≤
      ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ A)
    (hAphys0 : 0 ≤ Aphys) (hKphys0 : 0 ≤ Kphys)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hKphys : ∀ m : B.sampleData.SampleAt c,
      |B.physicalScore ⟨c, m⟩| ≤ Kphys)
    (hsmall : 8 * (Aphys * Kphys / B.L) ≤ 1) :
    let epsilon := Aphys * Kphys / B.L
    let G := Real.exp (2 * ((A / B.L) *
      (Real.log (B.sampleData.hi c.2 : ℝ) /
        Real.log (B.sampleData.W : ℝ)))) / rho
    |((B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)).expect
          (fun m ↦ divInd D m) -
        (B.cellMediumLaw xi c).expect (fun m ↦ divInd D m)| ≤
      8 * epsilon * (G * (1 / (D : ℝ))) := by
  dsimp only
  let epsilon := Aphys * Kphys / B.L
  let G := Real.exp (2 * ((A / B.L) *
    (Real.log (B.sampleData.hi c.2 : ℝ) /
      Real.log (B.sampleData.W : ℝ)))) / rho
  have hepsilon0 : 0 ≤ epsilon := by
    exact div_nonneg (mul_nonneg hAphys0 hKphys0) B.L_pos.le
  have hscore : ∀ m, |B.cellPhysicalTiltScore xi c m| ≤ epsilon := by
    simpa only [epsilon] using
      B.abs_cellPhysicalTiltScore_le xi c hAphys hKphys
  have hmedium := B.cellMediumLaw_expect_divInd_le xi c
    hD hA hW hrho hcard heta
  have hmediumG :
      (B.cellMediumLaw xi c).expect (fun m ↦ divInd D m) ≤
        G * (1 / (D : ℝ)) := by
    dsimp only [G]
    calc
      (B.cellMediumLaw xi c).expect (fun m ↦ divInd D m) ≤
          Real.exp (2 * ((A / B.L) *
              (Real.log (B.sampleData.hi c.2 : ℝ) /
                Real.log (B.sampleData.W : ℝ)))) /
            (rho * (D : ℝ)) := hmedium
      _ = (Real.exp (2 * ((A / B.L) *
              (Real.log (B.sampleData.hi c.2 : ℝ) /
                Real.log (B.sampleData.W : ℝ)))) / rho) *
              (1 / (D : ℝ)) := by ring
  rw [B.guardedCell_fullTilt_eq_medium_physicalTilt xi c]
  have htwo : 2 * epsilon < 1 := by
    dsimp only [epsilon] at hsmall ⊢
    nlinarith
  have hraw :=
    FiniteProbability.abs_exponentialTilt_expect_sub_expect_le_smallTiltLoss
      (B.cellMediumLaw xi c)
      (fun m ↦ divInd D m) (B.cellPhysicalTiltScore xi c)
      (fun m ↦ divInd_nonneg D m) (fun m ↦ divInd_le_one D m)
      hepsilon0 htwo hscore hmediumG
  have hloss : smallTiltLoss epsilon ≤ 8 * epsilon :=
    smallTiltLoss_le_eight_mul hepsilon0 (by
      simpa only [epsilon] using hsmall)
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    exact div_nonneg (Real.exp_pos _).le hrho.le
  have hfactor0 : 0 ≤ G * (1 / (D : ℝ)) := by
    exact mul_nonneg hG0 (by positivity)
  exact hraw.trans (mul_le_mul_of_nonneg_right hloss hfactor0)

/-- For two distinct medium primes, the same argument gives the required
product-scale `O(1/(p q L))` covariance perturbation. -/
theorem abs_guardedCell_fullTilt_squarefreeCovariance_sub_medium_le
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    {rho A Aphys Kphys : ℝ} {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hA : 0 ≤ A) (hW : 1 < B.sampleData.W)
    (hrho : 0 < rho)
    (hcard : rho * (B.sampleData.hi c.2 : ℝ) ≤
      ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi r| ≤ A)
    (hAphys0 : 0 ≤ Aphys) (hKphys0 : 0 ≤ Kphys)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hKphys : ∀ m : B.sampleData.SampleAt c,
      |B.physicalScore ⟨c, m⟩| ≤ Kphys)
    (hsmall : 8 * (Aphys * Kphys / B.L) ≤ 1) :
    let epsilon := Aphys * Kphys / B.L
    let G := Real.exp (2 * ((A / B.L) *
      (Real.log (B.sampleData.hi c.2 : ℝ) /
        Real.log (B.sampleData.W : ℝ)))) / rho
    |((B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance
          (fun m ↦ divInd p m) (fun m ↦ divInd q m) -
        (B.cellMediumLaw xi c).covariance
          (fun m ↦ divInd p m) (fun m ↦ divInd q m)| ≤
      8 * epsilon *
        (G * (1 / ((p * q : ℕ) : ℝ)) +
          3 * (G * (1 / (p : ℝ))) * (G * (1 / (q : ℝ)))) := by
  dsimp only
  let epsilon := Aphys * Kphys / B.L
  let G := Real.exp (2 * ((A / B.L) *
    (Real.log (B.sampleData.hi c.2 : ℝ) /
      Real.log (B.sampleData.W : ℝ)))) / rho
  have hepsilon0 : 0 ≤ epsilon := by
    exact div_nonneg (mul_nonneg hAphys0 hKphys0) B.L_pos.le
  have hscore : ∀ m, |B.cellPhysicalTiltScore xi c m| ≤ epsilon := by
    simpa only [epsilon] using
      B.abs_cellPhysicalTiltScore_le xi c hAphys hKphys
  have hp0 : 0 < p := hp.pos
  have hq0 : 0 < q := hq.pos
  have hpq0 : 0 < p * q := Nat.mul_pos hp0 hq0
  have hmediumP := B.cellMediumLaw_expect_divInd_le xi c
    hp0 hA hW hrho hcard heta
  have hmediumQ := B.cellMediumLaw_expect_divInd_le xi c
    hq0 hA hW hrho hcard heta
  have hmediumPQ := B.cellMediumLaw_expect_divInd_le xi c
    hpq0 hA hW hrho hcard heta
  have hP : (B.cellMediumLaw xi c).expect (fun m ↦ divInd p m) ≤
      G * (1 / (p : ℝ)) := by
    dsimp only [G]
    calc
      _ ≤ Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) /
          (rho * (p : ℝ)) := hmediumP
      _ = _ := by ring
  have hQ : (B.cellMediumLaw xi c).expect (fun m ↦ divInd q m) ≤
      G * (1 / (q : ℝ)) := by
    dsimp only [G]
    calc
      _ ≤ Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) /
          (rho * (q : ℝ)) := hmediumQ
      _ = _ := by ring
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hmul : (fun m : B.sampleData.SampleAt c ↦
      divInd p m * divInd q m) =
      fun m : B.sampleData.SampleAt c ↦ divInd (p * q) (m : ℕ) := by
    funext m
    exact divInd_mul_eq_product_of_coprime hcop
  have hPQ : (B.cellMediumLaw xi c).expect
      (fun m ↦ divInd p m * divInd q m) ≤
      G * (1 / ((p * q : ℕ) : ℝ)) := by
    rw [hmul]
    dsimp only [G]
    calc
      _ ≤ Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) /
          (rho * ((p * q : ℕ) : ℝ)) := hmediumPQ
      _ = _ := by ring
  rw [B.guardedCell_fullTilt_eq_medium_physicalTilt xi c]
  exact FiniteProbability.abs_exponentialTilt_covariance_sub_covariance_le_eight_mul
      (B.cellMediumLaw xi c)
      (fun m ↦ divInd p m) (fun m ↦ divInd q m)
      (B.cellPhysicalTiltScore xi c)
      (fun m ↦ divInd_nonneg p m) (fun m ↦ divInd_le_one p m)
      (fun m ↦ divInd_nonneg q m) (fun m ↦ divInd_le_one q m)
      hepsilon0 hsmall hscore hP hQ hPQ

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
