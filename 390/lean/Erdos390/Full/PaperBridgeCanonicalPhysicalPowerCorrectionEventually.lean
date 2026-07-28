import Erdos390.Full.PaperBridgePhysicalPowerCorrectionRow
import Erdos390.Full.GuardSquarefreeErrorRate
import Erdos390.Full.PaperPhysicalIntervalNuisanceGap

/-!
# Eventual canonical specialization of the residual physical power row

This file discharges the density, score-envelope, small-tilt, and divisor
fallback inputs of the residual-physical comparison.  All constants are
chosen from the fixed physical cells, cutoff, and preselected coefficient
box.  The resulting row error is also proved to survive division by the
moving-low centre, via its explicit `error * log L -> 0` rate.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PrimeSums

namespace BridgeData

variable {Head : Type*} [Fintype Head] [DecidableEq Head]

/-- The fixed cellwise density used in the guarded raw-cell census. -/
def canonicalPhysicalCellDensity
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (c : Cell Head) : ℝ :=
  PaperScaleMarkedCell.paperCellDensity (P c.1)
      (I.lower c.2) (I.upper c.2) /
    (4 * I.upper c.2)

/-- One fixed fallback constant dominating every physical component in the
preselected effective-prime box.  A finite sum is used in place of a maximum
so no choice of a maximizing cell is required. -/
def canonicalPhysicalPowerCorrectionConstant
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) (W : ℕ) (Acoef : ℝ) : ℝ :=
  let K := Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W
  ∑ c : Cell Head,
    Real.exp (2 * K) / canonicalPhysicalCellDensity P I c

/-- The residual physical tilt size at ambient integer `n`. -/
def canonicalPhysicalPowerCorrectionEpsilon
    (Aphys Cmax : ℝ) (n : ℕ) : ℝ :=
  Aphys * Real.log Cmax / Scale.L n

omit [Fintype Head] [DecidableEq Head] in
theorem canonicalPhysicalCellDensity_pos
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (c : Cell Head) :
    0 < canonicalPhysicalCellDensity P I c := by
  unfold canonicalPhysicalCellDensity
  exact div_pos
    (PaperScaleMarkedCell.paperCellDensity_pos
      (P c.1) (I.lower_lt_upper c.2))
    (mul_pos (by norm_num)
      ((I.lower_pos c.2).trans (I.lower_lt_upper c.2)))

omit [DecidableEq Head] in
theorem canonicalPhysicalPowerCorrectionConstant_nonneg
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) (W : ℕ) (Acoef : ℝ) :
    0 ≤ canonicalPhysicalPowerCorrectionConstant P I Cmax W Acoef := by
  unfold canonicalPhysicalPowerCorrectionConstant
  exact Finset.sum_nonneg fun c _ ↦
    div_nonneg (Real.exp_pos _).le
      (canonicalPhysicalCellDensity_pos P I c).le

/-- A fixed multiple of `1/L` survives both harmonic losses required by the
residual-physical row lemma. -/
theorem tendsto_canonicalPhysicalPowerCorrectionEpsilon_mul_logL_sq_zero
    (Aphys Cmax : ℝ) :
    Tendsto (fun n : ℕ ↦
      canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax n *
        Real.log (Scale.L n) ^ 2) atTop (nhds 0) := by
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto
      (fun n : ℕ ↦ Real.log (Scale.L n) ^ 2 / Scale.L n)
        atTop (nhds 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hconst : Tendsto
      (fun _n : ℕ ↦ Aphys * Real.log Cmax) atTop
        (nhds (Aphys * Real.log Cmax)) := tendsto_const_nhds
  have hmul := hconst.mul hratio
  apply (show Tendsto (fun n : ℕ ↦
      (Aphys * Real.log Cmax) *
        (Real.log (Scale.L n) ^ 2 / Scale.L n))
      atTop (nhds 0) by simpa only [mul_zero] using hmul).congr'
  filter_upwards with n
  unfold canonicalPhysicalPowerCorrectionEpsilon
  ring

/-- Fully discharged canonical residual-physical row comparison.

The threshold is independent of the later band partition, bridge data, tilt
point, and prime row.  The only call-site hypotheses are the exact canonical
constructor equality and the two genuine coefficient-box inequalities. -/
theorem exists_eventually_canonicalPhysical_powerCorrection_row
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (Cprom Cbank : ℕ)
    (ledger : ∀ n, Ledger n Cprom Cbank)
    (W : ℕ) (hW : 1 < W)
    (Acoef Aphys : ℝ) (hAcoef : 0 ≤ Acoef) (hAphys0 : 0 ≤ Aphys) :
    let G := canonicalPhysicalPowerCorrectionConstant P I Cmax W Acoef
    let epsilon := canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax
    0 ≤ G ∧
      Tendsto (fun n : ℕ ↦
        physicalPowerCorrectionRowError (epsilon n) G n W *
          Real.log (Scale.L n)) atTop (nhds 0) ∧
      ∃ N₀ : ℕ,
        ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
          (B : BridgeData Head Band) (xi : B.ParamSpace),
          N₀ ≤ B.sampleData.n →
          B.sampleData.W = W →
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell P I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
            B.sampleData = canonicalSampleData (W := B.sampleData.W)
                P I (ledger B.sampleData.n) hsep hremaining →
            (∀ p : BandPrime B.sampleData.n B.sampleData.W,
              |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
            |xi MomentCoord.physical| ≤ Aphys →
            ∀ p : BandPrime B.sampleData.n B.sampleData.W,
              (p.1 : ℝ) *
                (∑ q : BandPrime B.sampleData.n B.sampleData.W,
                  |((B.actualValuationLaw xi).covVV p.1 q.1 -
                      (B.actualValuationLaw xi).covII p.1 q.1) -
                    ((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
                      (B.physicalMediumReferenceLaw xi).covII p.1 q.1)|) ≤
                physicalPowerCorrectionRowError
                  (epsilon B.sampleData.n) G
                    B.sampleData.n B.sampleData.W := by
  dsimp only
  let G := canonicalPhysicalPowerCorrectionConstant P I Cmax W Acoef
  let epsilon := canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax
  have hupperOne : ∀ sigma, 1 ≤ I.upper sigma := fun sigma ↦
    (hlowerOne sigma).trans (I.lower_lt_upper sigma).le
  have hCmax : 1 ≤ Cmax :=
    (hupperOne .minus).trans (hupperMax .minus)
  have hlogC0 : 0 ≤ Real.log Cmax := Real.log_nonneg hCmax
  have hL0 (n : ℕ) : 0 ≤ Scale.L n := by
    cases n with
    | zero => norm_num [Scale.L]
    | succ n =>
        exact Real.log_nonneg (by
          exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))
  have hG : 0 ≤ G := by
    exact canonicalPhysicalPowerCorrectionConstant_nonneg P I Cmax W Acoef
  have hepsilon0 (n : ℕ) : 0 ≤ epsilon n := by
    dsimp only [epsilon, canonicalPhysicalPowerCorrectionEpsilon]
    exact div_nonneg (mul_nonneg hAphys0 hlogC0) (hL0 n)
  have hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n) ^ 2)
        atTop (nhds 0) := by
    exact tendsto_canonicalPhysicalPowerCorrectionEpsilon_mul_logL_sq_zero
      Aphys Cmax
  have hrowRate :=
    tendsto_physicalPowerCorrectionRowError_mul_logL_zero
      epsilon G W hepsilon0 hG hepsilonRate
  have hdensityEvent :=
    GuardSquarefreeErrorRate.eventually_guarded_rawCell_endpoint_density
      P I Cprom Cbank ledger
  have hepsilonT : Tendsto (fun n : ℕ ↦ 8 * epsilon n)
      atTop (nhds 0) := by
    have hLTop : Tendsto Scale.L atTop atTop := by
      simpa only [Scale.L] using
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hInv : Tendsto (fun n : ℕ ↦ (Scale.L n)⁻¹)
        atTop (nhds 0) := tendsto_inv_atTop_zero.comp hLTop
    have hconst : Tendsto
        (fun _n : ℕ ↦ 8 * (Aphys * Real.log Cmax)) atTop
          (nhds (8 * (Aphys * Real.log Cmax))) := tendsto_const_nhds
    have hmul := hconst.mul hInv
    apply (show Tendsto (fun n : ℕ ↦
        (8 * (Aphys * Real.log Cmax)) * (Scale.L n)⁻¹)
        atTop (nhds 0) by simpa only [mul_zero] using hmul).congr'
    filter_upwards with n
    dsimp only [epsilon, canonicalPhysicalPowerCorrectionEpsilon]
    rw [div_eq_mul_inv]
    ring
  have hsmallEvent : ∀ᶠ n : ℕ in atTop, 8 * epsilon n ≤ 1 :=
    hepsilonT.eventually (eventually_le_nhds (by norm_num))
  obtain ⟨Ndensity, hNdensity⟩ := Filter.eventually_atTop.1 hdensityEvent
  obtain ⟨Nsmall, hNsmall⟩ := Filter.eventually_atTop.1 hsmallEvent
  refine ⟨hG, hrowRate, max Ndensity Nsmall, ?_⟩
  intro Band _instBand _instBandDec B xi hN hBW hsep hremaining
    hcanonical heta hphys p
  have hNdensity' : Ndensity ≤ B.sampleData.n :=
    (Nat.le_max_left _ _).trans hN
  have hNsmall' : Nsmall ≤ B.sampleData.n :=
    (Nat.le_max_right _ _).trans hN
  have hdensity := hNdensity B.sampleData.n hNdensity'
  have hsmall : 8 * epsilon B.sampleData.n ≤ 1 :=
    hNsmall B.sampleData.n hNsmall'
  have hWBridge : 1 < B.sampleData.W := by
    simpa only [hBW] using hW
  have hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hhiC : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound Cmax B.sampleData.n := by
    intro sigma
    rw [hhi sigma]
    exact FixedFiniteMixtureFullUniform.physicalBound_mono
      (hupperMax sigma) B.sampleData.n
  have hrho (c : Cell Head) :
      0 < canonicalPhysicalCellDensity P I c :=
    canonicalPhysicalCellDensity_pos P I c
  have hcard (c : Cell Head) :
      canonicalPhysicalCellDensity P I c *
          (B.sampleData.hi c.2 : ℝ) ≤
        ((B.sampleData.cellFinset c).card : ℝ) := by
    have hc := (hdensity c).2
    rw [hcanonical]
    simpa only [canonicalPhysicalCellDensity,
      canonicalSampleData_hi, canonicalSampleData_cellFinset] using hc
  have hKphys : ∀ c (m : B.sampleData.SampleAt c),
      |B.physicalScore ⟨c, m⟩| ≤ Real.log Cmax := by
    intro c m
    exact B.abs_physicalScore_le_log_upperBound I hlowerOne hupperMax
      hlo hhi ⟨c, m⟩
  have hGdom : ∀ c,
      Real.exp (2 * ((Acoef / B.L) *
        (Real.log (B.sampleData.hi c.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ)))) /
          canonicalPhysicalCellDensity P I c ≤ G := by
    intro c
    let K := Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W
    have hexponent :
        (Acoef / B.L) *
            (Real.log (B.sampleData.hi c.2 : ℝ) /
              Real.log (B.sampleData.W : ℝ)) ≤ K := by
      simpa only [K, hBW] using
        B.mediumFallbackExponent_le c hCmax hWBridge hAcoef (hhiC c.2)
    have hcell :
        Real.exp (2 * ((Acoef / B.L) *
            (Real.log (B.sampleData.hi c.2 : ℝ) /
              Real.log (B.sampleData.W : ℝ)))) /
              canonicalPhysicalCellDensity P I c ≤
          Real.exp (2 * K) /
              canonicalPhysicalCellDensity P I c := by
      exact div_le_div_of_nonneg_right
        (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hexponent (by norm_num)))
        (hrho c).le
    have hsum : Real.exp (2 * K) /
          canonicalPhysicalCellDensity P I c ≤ G := by
      dsimp only [G, canonicalPhysicalPowerCorrectionConstant]
      exact Finset.single_le_sum
        (fun d _ ↦ div_nonneg (Real.exp_pos _).le (hrho d).le)
        (Finset.mem_univ c)
    exact hcell.trans hsum
  exact B.actual_powerCorrection_physicalMedium_weightedRow_le
    xi (canonicalPhysicalCellDensity P I)
      hAcoef hAphys0 hlogC0 hG hWBridge hrho hcard heta hphys hKphys
        hsmall hGdom p

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
